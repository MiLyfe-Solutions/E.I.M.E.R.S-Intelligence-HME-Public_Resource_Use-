import V185TrunkScan23Chunk1260

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7469456 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 7, 4, 2]
def baseStart_7469456 : Nat := 118140960795 + 7469456 * 2 ^ 59
def prefixEnd_7469456 : Nat := 4983230072969 + 3 ^ 40 * 7469456 * 2
def baseEnd_7469456 : Nat := 3835421155609832952748603

theorem tailTrace_7469456 : CollatzResearch.WordTrace tailWord_7469456 prefixEnd_7469456 3835421155609832952748603 := by
  unfold tailWord_7469456
  simp only [CollatzResearch.WordTrace]
  refine ⟨136216720813722034183858111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181622294418296045578477481 136216720813722034183858111)
  ·
    refine ⟨204325081220583051275787167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136216720813722034183858111 204325081220583051275787167)
    ·
      refine ⟨306487621830874576913680751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204325081220583051275787167 306487621830874576913680751)
      ·
        refine ⟨459731432746311865370521127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306487621830874576913680751 459731432746311865370521127)
        ·
          refine ⟨689597149119467798055781691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459731432746311865370521127 689597149119467798055781691)
          ·
            refine ⟨1034395723679201697083672537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689597149119467798055781691 1034395723679201697083672537)
            ·
              refine ⟨775796792759401272812754403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034395723679201697083672537 775796792759401272812754403)
              ·
                refine ⟨1163695189139101909219131605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775796792759401272812754403 1163695189139101909219131605)
                ·
                  refine ⟨27274105995447700997323397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1163695189139101909219131605 27274105995447700997323397)
                  ·
                    refine ⟨5113894874146443936998137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27274105995447700997323397 5113894874146443936998137)
                    ·
                      refine ⟨3835421155609832952748603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113894874146443936998137 3835421155609832952748603)
                      ·
                        rfl

theorem cell23_7469456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 4, 2].length) (baseStart_7469456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469456 prefixEnd_7469456 := by exact prefixLift 7469456
  have htrace : WordTrace (prefixWord ++ tailWord_7469456) baseStart_7469456 baseEnd_7469456 := by
    simpa [prefixWord, tailWord_7469456, baseEnd_7469456] using wordTrace_append hprefix tailTrace_7469456
  have hstable : (prefixWord ++ tailWord_7469456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469456).length < 2 ^ (prefixWord ++ tailWord_7469456).sum := by decide
  have hdescent : baseEnd_7469456 < baseStart_7469456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469490 : List Nat := [3, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_7469490 : Nat := 118140960795 + 7469490 * 2 ^ 59
def prefixEnd_7469490 : Nat := 4983230072969 + 3 ^ 40 * 7469490 * 2
def baseEnd_7469490 : Nat := 3835438613952085819723447

theorem tailTrace_7469490 : CollatzResearch.WordTrace tailWord_7469490 prefixEnd_7469490 3835438613952085819723447 := by
  unfold tailWord_7469490
  simp only [CollatzResearch.WordTrace]
  refine ⟨68108670427330223043613481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181623121139547261449635949 68108670427330223043613481)
  ·
    refine ⟨51081502820497667282710111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68108670427330223043613481 51081502820497667282710111)
    ·
      refine ⟨76622254230746500924065167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51081502820497667282710111 76622254230746500924065167)
      ·
        refine ⟨114933381346119751386097751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76622254230746500924065167 114933381346119751386097751)
        ·
          refine ⟨172400072019179627079146627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114933381346119751386097751 172400072019179627079146627)
          ·
            refine ⟨258600108028769440618719941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172400072019179627079146627 258600108028769440618719941)
            ·
              refine ⟨48487520255394270116009989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258600108028769440618719941 48487520255394270116009989)
              ·
                refine ⟨9091410047886425646751873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48487520255394270116009989 9091410047886425646751873)
                ·
                  refine ⟨6818557535914819235063905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9091410047886425646751873 6818557535914819235063905)
                  ·
                    refine ⟨5113918151936114426297929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6818557535914819235063905 5113918151936114426297929)
                    ·
                      refine ⟨3835438613952085819723447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113918151936114426297929 3835438613952085819723447)
                      ·
                        rfl

theorem cell23_7469490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_7469490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469490 prefixEnd_7469490 := by exact prefixLift 7469490
  have htrace : WordTrace (prefixWord ++ tailWord_7469490) baseStart_7469490 baseEnd_7469490 := by
    simpa [prefixWord, tailWord_7469490, baseEnd_7469490] using wordTrace_append hprefix tailTrace_7469490
  have hstable : (prefixWord ++ tailWord_7469490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469490).length < 2 ^ (prefixWord ++ tailWord_7469490).sum := by decide
  have hdescent : baseEnd_7469490 < baseStart_7469490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469519 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_7469519 : Nat := 118140960795 + 7469519 * 2 ^ 59
def prefixEnd_7469519 : Nat := 4983230072969 + 3 ^ 40 * 7469519 * 2
def baseEnd_7469519 : Nat := 3835453504891066206260813

theorem tailTrace_7469519 : CollatzResearch.WordTrace tailWord_7469519 prefixEnd_7469519 3835453504891066206260813 := by
  unfold tailWord_7469519
  simp only [CollatzResearch.WordTrace]
  refine ⟨272435739426215830127259611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181623826284143886751506407 272435739426215830127259611)
  ·
    refine ⟨408653609139323745190889417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272435739426215830127259611 408653609139323745190889417)
    ·
      refine ⟨306490206854492808893167063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408653609139323745190889417 306490206854492808893167063)
      ·
        refine ⟨459735310281739213339750595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306490206854492808893167063 459735310281739213339750595)
        ·
          refine ⟨689602965422608820009625893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459735310281739213339750595 689602965422608820009625893)
          ·
            refine ⟨129300556016739153751804855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 689602965422608820009625893 129300556016739153751804855)
            ·
              refine ⟨193950834025108730627707283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129300556016739153751804855 193950834025108730627707283)
              ·
                refine ⟨290926251037663095941560925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193950834025108730627707283 290926251037663095941560925)
                ·
                  refine ⟨109097344139123660978085347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290926251037663095941560925 109097344139123660978085347)
                  ·
                    refine ⟨163646016208685491467128021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109097344139123660978085347 163646016208685491467128021)
                    ·
                      refine ⟨3835453504891066206260813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163646016208685491467128021 3835453504891066206260813)
                      ·
                        rfl

theorem cell23_7469519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_7469519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469519 prefixEnd_7469519 := by exact prefixLift 7469519
  have htrace : WordTrace (prefixWord ++ tailWord_7469519) baseStart_7469519 baseEnd_7469519 := by
    simpa [prefixWord, tailWord_7469519, baseEnd_7469519] using wordTrace_append hprefix tailTrace_7469519
  have hstable : (prefixWord ++ tailWord_7469519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469519).length < 2 ^ (prefixWord ++ tailWord_7469519).sum := by decide
  have hdescent : baseEnd_7469519 < baseStart_7469519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469580 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_7469580 : Nat := 118140960795 + 7469580 * 2 ^ 59
def prefixEnd_7469580 : Nat := 4983230072969 + 3 ^ 40 * 7469580 * 2
def baseEnd_7469580 : Nat := 3835484827210990467598033

theorem tailTrace_7469580 : CollatzResearch.WordTrace tailWord_7469580 prefixEnd_7469580 3835484827210990467598033 := by
  unfold tailWord_7469580
  simp only [CollatzResearch.WordTrace]
  refine ⟨136218982139497418772615097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181625309519329891696820129 136218982139497418772615097)
  ·
    refine ⟨102164236604623064079461323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136218982139497418772615097 102164236604623064079461323)
    ·
      refine ⟨153246354906934596119191985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102164236604623064079461323 153246354906934596119191985)
      ·
        refine ⟨114934766180200947089393989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153246354906934596119191985 114934766180200947089393989)
        ·
          refine ⟨21550268658787677579261373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114934766180200947089393989 21550268658787677579261373)
          ·
            refine ⟨8081350747045379092223015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21550268658787677579261373 8081350747045379092223015)
            ·
              refine ⟨12122026120568068638334523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081350747045379092223015 12122026120568068638334523)
              ·
                refine ⟨18183039180852102957501785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12122026120568068638334523 18183039180852102957501785)
                ·
                  refine ⟨13637279385639077218126339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18183039180852102957501785 13637279385639077218126339)
                  ·
                    refine ⟨20455919078458615827189509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13637279385639077218126339 20455919078458615827189509)
                    ·
                      refine ⟨3835484827210990467598033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20455919078458615827189509 3835484827210990467598033)
                      ·
                        rfl

theorem cell23_7469580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_7469580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469580 prefixEnd_7469580 := by exact prefixLift 7469580
  have htrace : WordTrace (prefixWord ++ tailWord_7469580) baseStart_7469580 baseEnd_7469580 := by
    simpa [prefixWord, tailWord_7469580, baseEnd_7469580] using wordTrace_append hprefix tailTrace_7469580
  have hstable : (prefixWord ++ tailWord_7469580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469580).length < 2 ^ (prefixWord ++ tailWord_7469580).sum := by decide
  have hdescent : baseEnd_7469580 < baseStart_7469580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469603 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 6]
def baseStart_7469603 : Nat := 118140960795 + 7469603 * 2 ^ 59
def prefixEnd_7469603 : Nat := 4983230072969 + 3 ^ 40 * 7469603 * 2
def baseEnd_7469603 : Nat := 426166293029560430845603

theorem tailTrace_7469603 : CollatzResearch.WordTrace tailWord_7469603 prefixEnd_7469603 426166293029560430845603 := by
  unfold tailWord_7469603
  simp only [CollatzResearch.WordTrace]
  refine ⟨272438803157911512473317463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181625868771941008315544975 272438803157911512473317463)
  ·
    refine ⟨408658204736867268709976195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272438803157911512473317463 408658204736867268709976195)
    ·
      refine ⟨612987307105300903064964293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408658204736867268709976195 612987307105300903064964293)
      ·
        refine ⟨114935120082243919324680805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 612987307105300903064964293 114935120082243919324680805)
        ·
          refine ⟨21550335015420734873377651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114935120082243919324680805 21550335015420734873377651)
          ·
            refine ⟨32325502523131102310066477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21550335015420734873377651 32325502523131102310066477)
            ·
              refine ⟨12122063446174163366274929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32325502523131102310066477 12122063446174163366274929)
              ·
                refine ⟨9091547584630622524706197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12122063446174163366274929 9091547584630622524706197)
                ·
                  refine ⟨426166293029560430845603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9091547584630622524706197 426166293029560430845603)
                  ·
                    rfl

theorem cell23_7469603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 6].length) (baseStart_7469603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469603 prefixEnd_7469603 := by exact prefixLift 7469603
  have htrace : WordTrace (prefixWord ++ tailWord_7469603) baseStart_7469603 baseEnd_7469603 := by
    simpa [prefixWord, tailWord_7469603, baseEnd_7469603] using wordTrace_append hprefix tailTrace_7469603
  have hstable : (prefixWord ++ tailWord_7469603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469603).length < 2 ^ (prefixWord ++ tailWord_7469603).sum := by decide
  have hdescent : baseEnd_7469603 < baseStart_7469603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469616 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 5, 5]
def baseStart_7469616 : Nat := 118140960795 + 7469616 * 2 ^ 59
def prefixEnd_7469616 : Nat := 4983230072969 + 3 ^ 40 * 7469616 * 2
def baseEnd_7469616 : Nat := 1278501104171517442249289

theorem tailTrace_7469616 : CollatzResearch.WordTrace tailWord_7469616 prefixEnd_7469616 1278501104171517442249289 := by
  unfold tailWord_7469616
  simp only [CollatzResearch.WordTrace]
  refine ⟨136219638653432207846770351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181626184871242943795693801 136219638653432207846770351)
  ·
    refine ⟨204329457980148311770155527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136219638653432207846770351 204329457980148311770155527)
    ·
      refine ⟨306494186970222467655233291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204329457980148311770155527 306494186970222467655233291)
      ·
        refine ⟨459741280455333701482849937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306494186970222467655233291 459741280455333701482849937)
        ·
          refine ⟨344805960341500276112137453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459741280455333701482849937 344805960341500276112137453)
          ·
            refine ⟨129302235128062603542051545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344805960341500276112137453 129302235128062603542051545)
            ·
              refine ⟨96976676346046952656538659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129302235128062603542051545 96976676346046952656538659)
              ·
                refine ⟨145465014519070428984807989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96976676346046952656538659 145465014519070428984807989)
                ·
                  refine ⟨13637345111162852717325749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145465014519070428984807989 13637345111162852717325749)
                  ·
                    refine ⟨1278501104171517442249289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13637345111162852717325749 1278501104171517442249289)
                    ·
                      rfl

theorem cell23_7469616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_7469616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469616 prefixEnd_7469616 := by exact prefixLift 7469616
  have htrace : WordTrace (prefixWord ++ tailWord_7469616) baseStart_7469616 baseEnd_7469616 := by
    simpa [prefixWord, tailWord_7469616, baseEnd_7469616] using wordTrace_append hprefix tailTrace_7469616
  have hstable : (prefixWord ++ tailWord_7469616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469616).length < 2 ^ (prefixWord ++ tailWord_7469616).sum := by decide
  have hdescent : baseEnd_7469616 < baseStart_7469616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469623 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 3, 5, 2]
def baseStart_7469623 : Nat := 118140960795 + 7469623 * 2 ^ 59
def prefixEnd_7469623 : Nat := 4983230072969 + 3 ^ 40 * 7469623 * 2
def baseEnd_7469623 : Nat := 3835506906879133799360335

theorem tailTrace_7469623 : CollatzResearch.WordTrace tailWord_7469623 prefixEnd_7469623 3835506906879133799360335 := by
  unfold tailWord_7469623
  simp only [CollatzResearch.WordTrace]
  refine ⟨272439532617839055889045523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181626355078559370592697015 272439532617839055889045523)
  ·
    refine ⟨408659298926758583833568285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272439532617839055889045523 408659298926758583833568285)
    ·
      refine ⟨153247237097534468937588107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408659298926758583833568285 153247237097534468937588107)
      ·
        refine ⟨229870855646301703406382161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153247237097534468937588107 229870855646301703406382161)
        ·
          refine ⟨172403141734726277554786621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229870855646301703406382161 172403141734726277554786621)
          ·
            refine ⟨64651178150522354083044983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172403141734726277554786621 64651178150522354083044983)
            ·
              refine ⟨96976767225783531124567475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64651178150522354083044983 96976767225783531124567475)
              ·
                refine ⟨145465150838675296686851213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96976767225783531124567475 145465150838675296686851213)
                ·
                  refine ⟨54549431564503236257569205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145465150838675296686851213 54549431564503236257569205)
                  ·
                    refine ⟨5114009209172178399147113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54549431564503236257569205 5114009209172178399147113)
                    ·
                      refine ⟨3835506906879133799360335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114009209172178399147113 3835506906879133799360335)
                      ·
                        rfl

theorem cell23_7469623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_7469623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469623 prefixEnd_7469623 := by exact prefixLift 7469623
  have htrace : WordTrace (prefixWord ++ tailWord_7469623) baseStart_7469623 baseEnd_7469623 := by
    simpa [prefixWord, tailWord_7469623, baseEnd_7469623] using wordTrace_append hprefix tailTrace_7469623
  have hstable : (prefixWord ++ tailWord_7469623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469623).length < 2 ^ (prefixWord ++ tailWord_7469623).sum := by decide
  have hdescent : baseEnd_7469623 < baseStart_7469623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469647 : List Nat := [1, 1, 2, 1, 1, 2, 7, 3, 1, 1, 3]
def baseStart_7469647 : Nat := 118140960795 + 7469647 * 2 ^ 59
def prefixEnd_7469647 : Nat := 4983230072969 + 3 ^ 40 * 7469647 * 2
def baseEnd_7469647 : Nat := 3835519230414841705460225

theorem tailTrace_7469647 : CollatzResearch.WordTrace tailWord_7469647 prefixEnd_7469647 3835519230414841705460225 := by
  unfold tailWord_7469647
  simp only [CollatzResearch.WordTrace]
  refine ⟨272440407969752107987919195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181626938646501405325279463 272440407969752107987919195)
  ·
    refine ⟨408660611954628161981878793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272440407969752107987919195 408660611954628161981878793)
    ·
      refine ⟨306495458965971121486409095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408660611954628161981878793 306495458965971121486409095)
      ·
        refine ⟨459743188448956682229613643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306495458965971121486409095 459743188448956682229613643)
        ·
          refine ⟨689614782673435023344420465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459743188448956682229613643 689614782673435023344420465)
          ·
            refine ⟨517211087005076267508315349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689614782673435023344420465 517211087005076267508315349)
            ·
              refine ⟨12122134851681475019726141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 517211087005076267508315349 12122134851681475019726141)
              ·
                refine ⟨4545800569380553132397303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12122134851681475019726141 4545800569380553132397303)
                ·
                  refine ⟨6818700854070829698595955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545800569380553132397303 6818700854070829698595955)
                  ·
                    refine ⟨10228051281106244547893933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6818700854070829698595955 10228051281106244547893933)
                    ·
                      refine ⟨3835519230414841705460225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10228051281106244547893933 3835519230414841705460225)
                      ·
                        rfl

theorem cell23_7469647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 1, 1, 3].length) (baseStart_7469647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469647 prefixEnd_7469647 := by exact prefixLift 7469647
  have htrace : WordTrace (prefixWord ++ tailWord_7469647) baseStart_7469647 baseEnd_7469647 := by
    simpa [prefixWord, tailWord_7469647, baseEnd_7469647] using wordTrace_append hprefix tailTrace_7469647
  have hstable : (prefixWord ++ tailWord_7469647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469647).length < 2 ^ (prefixWord ++ tailWord_7469647).sum := by decide
  have hdescent : baseEnd_7469647 < baseStart_7469647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469673 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 3]
def baseStart_7469673 : Nat := 118140960795 + 7469673 * 2 ^ 59
def prefixEnd_7469673 : Nat := 4983230072969 + 3 ^ 40 * 7469673 * 2
def baseEnd_7469673 : Nat := 3835532580911858603735105

theorem tailTrace_7469673 : CollatzResearch.WordTrace tailWord_7469673 prefixEnd_7469673 3835532580911858603735105 := by
  unfold tailWord_7469673
  simp only [CollatzResearch.WordTrace]
  refine ⟨272441356267657914428365673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181627570845105276285577115 272441356267657914428365673)
  ·
    refine ⟨204331017200743435821274255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272441356267657914428365673 204331017200743435821274255)
    ·
      refine ⟨306496525801115153731911383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204331017200743435821274255 306496525801115153731911383)
      ·
        refine ⟨459744788701672730597867075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306496525801115153731911383 459744788701672730597867075)
        ·
          refine ⟨689617183052509095896800613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459744788701672730597867075 689617183052509095896800613)
          ·
            refine ⟨129303221822345455480650115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 689617183052509095896800613 129303221822345455480650115)
            ·
              refine ⟨193954832733518183220975173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129303221822345455480650115 193954832733518183220975173)
              ·
                refine ⟨36366531137534659353932845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193954832733518183220975173 36366531137534659353932845)
                ·
                  refine ⟨13637449176575497257724817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36366531137534659353932845 13637449176575497257724817)
                  ·
                    refine ⟨10228086882431622943293613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13637449176575497257724817 10228086882431622943293613)
                    ·
                      refine ⟨3835532580911858603735105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10228086882431622943293613 3835532580911858603735105)
                      ·
                        rfl

theorem cell23_7469673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_7469673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469673 prefixEnd_7469673 := by exact prefixLift 7469673
  have htrace : WordTrace (prefixWord ++ tailWord_7469673) baseStart_7469673 baseEnd_7469673 := by
    simpa [prefixWord, tailWord_7469673, baseEnd_7469673] using wordTrace_append hprefix tailTrace_7469673
  have hstable : (prefixWord ++ tailWord_7469673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469673).length < 2 ^ (prefixWord ++ tailWord_7469673).sum := by decide
  have hdescent : baseEnd_7469673 < baseStart_7469673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469676 : List Nat := [2, 2, 1, 1, 3, 1, 3, 10]
def baseStart_7469676 : Nat := 118140960795 + 7469676 * 2 ^ 59
def prefixEnd_7469676 : Nat := 4983230072969 + 3 ^ 40 * 7469676 * 2
def baseEnd_7469676 : Nat := 142056819309400818222133

theorem tailTrace_7469676 : CollatzResearch.WordTrace tailWord_7469676 prefixEnd_7469676 142056819309400818222133 := by
  unfold tailWord_7469676
  simp only [CollatzResearch.WordTrace]
  refine ⟨136220732843323522970362441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181627643791098030627149921 136220732843323522970362441)
  ·
    refine ⟨102165549632492642227771831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136220732843323522970362441 102165549632492642227771831)
    ·
      refine ⟨153248324448738963341657747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102165549632492642227771831 153248324448738963341657747)
      ·
        refine ⟨229872486673108445012486621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153248324448738963341657747 229872486673108445012486621)
        ·
          refine ⟨86202182502415666879682483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229872486673108445012486621 86202182502415666879682483)
          ·
            refine ⟨129303273753623500319523725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86202182502415666879682483 129303273753623500319523725)
            ·
              refine ⟨48488727657608812619821397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129303273753623500319523725 48488727657608812619821397)
              ·
                refine ⟨142056819309400818222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48488727657608812619821397 142056819309400818222133)
                ·
                  rfl

theorem cell23_7469676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 10].length) (baseStart_7469676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469676 prefixEnd_7469676 := by exact prefixLift 7469676
  have htrace : WordTrace (prefixWord ++ tailWord_7469676) baseStart_7469676 baseEnd_7469676 := by
    simpa [prefixWord, tailWord_7469676, baseEnd_7469676] using wordTrace_append hprefix tailTrace_7469676
  have hstable : (prefixWord ++ tailWord_7469676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469676).length < 2 ^ (prefixWord ++ tailWord_7469676).sum := by decide
  have hdescent : baseEnd_7469676 < baseStart_7469676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469700 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_7469700 : Nat := 118140960795 + 7469700 * 2 ^ 59
def prefixEnd_7469700 : Nat := 4983230072969 + 3 ^ 40 * 7469700 * 2
def baseEnd_7469700 : Nat := 3835546444889529998097481

theorem tailTrace_7469700 : CollatzResearch.WordTrace tailWord_7469700 prefixEnd_7469700 3835546444889529998097481 := by
  unfold tailWord_7469700
  simp only [CollatzResearch.WordTrace]
  refine ⟨136221170519280049019799277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181628227359040065359732369 136221170519280049019799277)
  ·
    refine ⟨51082938944730018382424729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136221170519280049019799277 51082938944730018382424729)
    ·
      refine ⟨38312204208547513786818547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51082938944730018382424729 38312204208547513786818547)
      ·
        refine ⟨57468306312821270680227821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38312204208547513786818547 57468306312821270680227821)
        ·
          refine ⟨21550614867307976505085433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57468306312821270680227821 21550614867307976505085433)
          ·
            refine ⟨16162961150480982378814075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21550614867307976505085433 16162961150480982378814075)
            ·
              refine ⟨24244441725721473568221113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16162961150480982378814075 24244441725721473568221113)
              ·
                refine ⟨18183331294291105176165835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24244441725721473568221113 18183331294291105176165835)
                ·
                  refine ⟨27274996941436657764248753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18183331294291105176165835 27274996941436657764248753)
                  ·
                    refine ⟨20456247706077493323186565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27274996941436657764248753 20456247706077493323186565)
                    ·
                      refine ⟨3835546444889529998097481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20456247706077493323186565 3835546444889529998097481)
                      ·
                        rfl

theorem cell23_7469700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_7469700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469700 prefixEnd_7469700 := by exact prefixLift 7469700
  have htrace : WordTrace (prefixWord ++ tailWord_7469700) baseStart_7469700 baseEnd_7469700 := by
    simpa [prefixWord, tailWord_7469700, baseEnd_7469700] using wordTrace_append hprefix tailTrace_7469700
  have hstable : (prefixWord ++ tailWord_7469700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469700).length < 2 ^ (prefixWord ++ tailWord_7469700).sum := by decide
  have hdescent : baseEnd_7469700 < baseStart_7469700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469764 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_7469764 : Nat := 118140960795 + 7469764 * 2 ^ 59
def prefixEnd_7469764 : Nat := 4983230072969 + 3 ^ 40 * 7469764 * 2
def baseEnd_7469764 : Nat := 3835579307651417747697187

theorem tailTrace_7469764 : CollatzResearch.WordTrace tailWord_7469764 prefixEnd_7469764 3835579307651417747697187 := by
  unfold tailWord_7469764
  simp only [CollatzResearch.WordTrace]
  refine ⟨136222337655164118484964173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181629783540218824646618897 136222337655164118484964173)
  ·
    refine ⟨51083376620686544431861565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136222337655164118484964173 51083376620686544431861565)
    ·
      refine ⟨19156266232757454161948087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51083376620686544431861565 19156266232757454161948087)
      ·
        refine ⟨28734399349136181242922131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19156266232757454161948087 28734399349136181242922131)
        ·
          refine ⟨43101599023704271864383197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28734399349136181242922131 43101599023704271864383197)
          ·
            refine ⟨16163099633889101949143699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43101599023704271864383197 16163099633889101949143699)
            ·
              refine ⟨24244649450833652923715549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16163099633889101949143699 24244649450833652923715549)
              ·
                refine ⟨9091743544062619846393331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24244649450833652923715549 9091743544062619846393331)
                ·
                  refine ⟨13637615316093929769589997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9091743544062619846393331 13637615316093929769589997)
                  ·
                    refine ⟨5114105743535223663596249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13637615316093929769589997 5114105743535223663596249)
                    ·
                      refine ⟨3835579307651417747697187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114105743535223663596249 3835579307651417747697187)
                      ·
                        rfl

theorem cell23_7469764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_7469764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469764 prefixEnd_7469764 := by exact prefixLift 7469764
  have htrace : WordTrace (prefixWord ++ tailWord_7469764) baseStart_7469764 baseEnd_7469764 := by
    simpa [prefixWord, tailWord_7469764, baseEnd_7469764] using wordTrace_append hprefix tailTrace_7469764
  have hstable : (prefixWord ++ tailWord_7469764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469764).length < 2 ^ (prefixWord ++ tailWord_7469764).sum := by decide
  have hdescent : baseEnd_7469764 < baseStart_7469764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469777 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 4, 2, 2]
def baseStart_7469777 : Nat := 118140960795 + 7469777 * 2 ^ 59
def prefixEnd_7469777 : Nat := 4983230072969 + 3 ^ 40 * 7469777 * 2
def baseEnd_7469777 : Nat := 3835585982899926196834627

theorem tailTrace_7469777 : CollatzResearch.WordTrace tailWord_7469777 prefixEnd_7469777 3835585982899926196834627 := by
  unfold tailWord_7469777
  simp only [CollatzResearch.WordTrace]
  refine ⟨272445149459281140190151585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181630099639520760126767723 272445149459281140190151585)
  ·
    refine ⟨204333862094460855142613689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272445149459281140190151585 204333862094460855142613689)
    ·
      refine ⟨153250396570845641356960267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204333862094460855142613689 153250396570845641356960267)
      ·
        refine ⟨229875594856268462035440401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153250396570845641356960267 229875594856268462035440401)
        ·
          refine ⟨172406696142201346526580301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229875594856268462035440401 172406696142201346526580301)
          ·
            refine ⟨64652511053325504947467613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172406696142201346526580301 64652511053325504947467613)
            ·
              refine ⟨24244691644997064355300355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64652511053325504947467613 24244691644997064355300355)
              ·
                refine ⟨36367037467495596532950533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24244691644997064355300355 36367037467495596532950533)
                ·
                  refine ⟨6818819525155424349928225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36367037467495596532950533 6818819525155424349928225)
                  ·
                    refine ⟨5114114643866568262446169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6818819525155424349928225 5114114643866568262446169)
                    ·
                      refine ⟨3835585982899926196834627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114114643866568262446169 3835585982899926196834627)
                      ·
                        rfl

theorem cell23_7469777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_7469777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469777 prefixEnd_7469777 := by exact prefixLift 7469777
  have htrace : WordTrace (prefixWord ++ tailWord_7469777) baseStart_7469777 baseEnd_7469777 := by
    simpa [prefixWord, tailWord_7469777, baseEnd_7469777] using wordTrace_append hprefix tailTrace_7469777
  have hstable : (prefixWord ++ tailWord_7469777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469777).length < 2 ^ (prefixWord ++ tailWord_7469777).sum := by decide
  have hdescent : baseEnd_7469777 < baseStart_7469777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469783 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 7]
def baseStart_7469783 : Nat := 118140960795 + 7469783 * 2 ^ 59
def prefixEnd_7469783 : Nat := 4983230072969 + 3 ^ 40 * 7469783 * 2
def baseEnd_7469783 : Nat := 426176562642650352595511

theorem tailTrace_7469783 : CollatzResearch.WordTrace tailWord_7469783 prefixEnd_7469783 426176562642650352595511 := by
  unfold tailWord_7469783
  simp only [CollatzResearch.WordTrace]
  refine ⟨272445368297259403214870003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181630245531506268809913335 272445368297259403214870003)
  ·
    refine ⟨408668052445889104822305005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272445368297259403214870003 408668052445889104822305005)
    ·
      refine ⟨153250519667208414308364377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408668052445889104822305005 153250519667208414308364377)
      ·
        refine ⟨114937889750406310731273283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153250519667208414308364377 114937889750406310731273283)
        ·
          refine ⟨172406834625609466096909925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114937889750406310731273283 172406834625609466096909925)
          ·
            refine ⟨32326281492301774893170611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172406834625609466096909925 32326281492301774893170611)
            ·
              refine ⟨48489422238452662339755917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32326281492301774893170611 48489422238452662339755917)
              ·
                refine ⟨18183533339419748377408469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48489422238452662339755917 18183533339419748377408469)
                ·
                  refine ⟨426176562642650352595511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18183533339419748377408469 426176562642650352595511)
                  ·
                    rfl

theorem cell23_7469783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 7].length) (baseStart_7469783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469783 prefixEnd_7469783 := by exact prefixLift 7469783
  have htrace : WordTrace (prefixWord ++ tailWord_7469783) baseStart_7469783 baseEnd_7469783 := by
    simpa [prefixWord, tailWord_7469783, baseEnd_7469783] using wordTrace_append hprefix tailTrace_7469783
  have hstable : (prefixWord ++ tailWord_7469783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469783).length < 2 ^ (prefixWord ++ tailWord_7469783).sum := by decide
  have hdescent : baseEnd_7469783 < baseStart_7469783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469823 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_7469823 : Nat := 118140960795 + 7469823 * 2 ^ 59
def prefixEnd_7469823 : Nat := 4983230072969 + 3 ^ 40 * 7469823 * 2
def baseEnd_7469823 : Nat := 3835609603010033016859415

theorem tailTrace_7469823 : CollatzResearch.WordTrace tailWord_7469823 prefixEnd_7469823 3835609603010033016859415 := by
  unfold tailWord_7469823
  simp only [CollatzResearch.WordTrace]
  refine ⟨272446827217114490046326123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181631218144742993364217415 272446827217114490046326123)
  ·
    refine ⟨408670240825671735069489185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272446827217114490046326123 408670240825671735069489185)
    ·
      refine ⟨306502680619253801302116889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408670240825671735069489185 306502680619253801302116889)
      ·
        refine ⟨229877010464440350976587667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306502680619253801302116889 229877010464440350976587667)
        ·
          refine ⟨344815515696660526464881501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229877010464440350976587667 344815515696660526464881501)
          ·
            refine ⟨129305818386247697424330563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344815515696660526464881501 129305818386247697424330563)
            ·
              refine ⟨193958727579371546136495845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129305818386247697424330563 193958727579371546136495845)
              ·
                refine ⟨36367261421132164900592971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193958727579371546136495845 36367261421132164900592971)
                ·
                  refine ⟨54550892131698247350889457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36367261421132164900592971 54550892131698247350889457)
                  ·
                    refine ⟨40913169098773685513167093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54550892131698247350889457 40913169098773685513167093)
                    ·
                      refine ⟨3835609603010033016859415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40913169098773685513167093 3835609603010033016859415)
                      ·
                        rfl

theorem cell23_7469823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_7469823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469823 prefixEnd_7469823 := by exact prefixLift 7469823
  have htrace : WordTrace (prefixWord ++ tailWord_7469823) baseStart_7469823 baseEnd_7469823 := by
    simpa [prefixWord, tailWord_7469823, baseEnd_7469823] using wordTrace_append hprefix tailTrace_7469823
  have hstable : (prefixWord ++ tailWord_7469823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469823).length < 2 ^ (prefixWord ++ tailWord_7469823).sum := by decide
  have hdescent : baseEnd_7469823 < baseStart_7469823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469850 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_7469850 : Nat := 118140960795 + 7469850 * 2 ^ 59
def prefixEnd_7469850 : Nat := 4983230072969 + 3 ^ 40 * 7469850 * 2
def baseEnd_7469850 : Nat := 3835623466987704411221791

theorem tailTrace_7469850 : CollatzResearch.WordTrace tailWord_7469850 prefixEnd_7469850 3835623466987704411221791 := by
  unfold tailWord_7469850
  simp only [CollatzResearch.WordTrace]
  refine ⟨68111952997004168414389751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181631874658677782438372669 68111952997004168414389751)
  ·
    refine ⟨102167929495506252621584627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68111952997004168414389751 102167929495506252621584627)
    ·
      refine ⟨153251894243259378932376941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102167929495506252621584627 153251894243259378932376941)
      ·
        refine ⟨57469460341222267099641353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153251894243259378932376941 57469460341222267099641353)
        ·
          refine ⟨43102095255916700324731015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57469460341222267099641353 43102095255916700324731015)
          ·
            refine ⟨64653142883875050487096523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43102095255916700324731015 64653142883875050487096523)
            ·
              refine ⟨96979714325812575730644785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64653142883875050487096523 96979714325812575730644785)
              ·
                refine ⟨72734785744359431797983589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96979714325812575730644785 72734785744359431797983589)
                ·
                  refine ⟨13637772327067393462121923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72734785744359431797983589 13637772327067393462121923)
                  ·
                    refine ⟨20456658490601090193182885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13637772327067393462121923 20456658490601090193182885)
                    ·
                      refine ⟨3835623466987704411221791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20456658490601090193182885 3835623466987704411221791)
                      ·
                        rfl

theorem cell23_7469850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_7469850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469850 prefixEnd_7469850 := by exact prefixLift 7469850
  have htrace : WordTrace (prefixWord ++ tailWord_7469850) baseStart_7469850 baseEnd_7469850 := by
    simpa [prefixWord, tailWord_7469850, baseEnd_7469850] using wordTrace_append hprefix tailTrace_7469850
  have hstable : (prefixWord ++ tailWord_7469850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469850).length < 2 ^ (prefixWord ++ tailWord_7469850).sum := by decide
  have hdescent : baseEnd_7469850 < baseStart_7469850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469887 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 3]
def baseStart_7469887 : Nat := 118140960795 + 7469887 * 2 ^ 59
def prefixEnd_7469887 : Nat := 4983230072969 + 3 ^ 40 * 7469887 * 2
def baseEnd_7469887 : Nat := 3835642465771920766459121

theorem tailTrace_7469887 : CollatzResearch.WordTrace tailWord_7469887 prefixEnd_7469887 3835642465771920766459121 := by
  unfold tailWord_7469887
  simp only [CollatzResearch.WordTrace]
  refine ⟨272449161488882628976655915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181632774325921752651103943 272449161488882628976655915)
  ·
    refine ⟨408673742233323943464983873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272449161488882628976655915 408673742233323943464983873)
    ·
      refine ⟨306505306674992957598737905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408673742233323943464983873 306505306674992957598737905)
      ·
        refine ⟨229878980006244718199053429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306505306674992957598737905 229878980006244718199053429)
        ·
          refine ⟨21551154375585442331161259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229878980006244718199053429 21551154375585442331161259)
          ·
            refine ⟨32326731563378163496741889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21551154375585442331161259 32326731563378163496741889)
            ·
              refine ⟨24245048672533622622556417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32326731563378163496741889 24245048672533622622556417)
              ·
                refine ⟨18183786504400216966917313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24245048672533622622556417 18183786504400216966917313)
                ·
                  refine ⟨13637839878300162725187985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18183786504400216966917313 13637839878300162725187985)
                  ·
                    refine ⟨10228379908725122043890989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13637839878300162725187985 10228379908725122043890989)
                    ·
                      refine ⟨3835642465771920766459121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10228379908725122043890989 3835642465771920766459121)
                      ·
                        rfl

theorem cell23_7469887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_7469887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469887 prefixEnd_7469887 := by exact prefixLift 7469887
  have htrace : WordTrace (prefixWord ++ tailWord_7469887) baseStart_7469887 baseEnd_7469887 := by
    simpa [prefixWord, tailWord_7469887, baseEnd_7469887] using wordTrace_append hprefix tailTrace_7469887
  have hstable : (prefixWord ++ tailWord_7469887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469887).length < 2 ^ (prefixWord ++ tailWord_7469887).sum := by decide
  have hdescent : baseEnd_7469887 < baseStart_7469887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469901 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7469901 : Nat := 118140960795 + 7469901 * 2 ^ 59
def prefixEnd_7469901 : Nat := 4983230072969 + 3 ^ 40 * 7469901 * 2
def baseEnd_7469901 : Nat := 3835649654501083711684057

theorem tailTrace_7469901 : CollatzResearch.WordTrace tailWord_7469901 prefixEnd_7469901 3835649654501083711684057 := by
  unfold tailWord_7469901
  simp only [CollatzResearch.WordTrace]
  refine ⟨272449672110831909367665557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181633114740554606245110371 272449672110831909367665557)
  ·
    refine ⟨12771078380195245751609323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 272449672110831909367665557 12771078380195245751609323)
    ·
      refine ⟨19156617570292868627413985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12771078380195245751609323 19156617570292868627413985)
      ·
        refine ⟨14367463177719651470560489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19156617570292868627413985 14367463177719651470560489)
        ·
          refine ⟨10775597383289738602920367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14367463177719651470560489 10775597383289738602920367)
          ·
            refine ⟨16163396074934607904380551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10775597383289738602920367 16163396074934607904380551)
            ·
              refine ⟨24245094112401911856570827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16163396074934607904380551 24245094112401911856570827)
              ·
                refine ⟨36367641168602867784856241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24245094112401911856570827 36367641168602867784856241)
                ·
                  refine ⟨27275730876452150838642181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36367641168602867784856241 27275730876452150838642181)
                  ·
                    refine ⟨5114199539334778282245409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27275730876452150838642181 5114199539334778282245409)
                    ·
                      refine ⟨3835649654501083711684057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114199539334778282245409 3835649654501083711684057)
                      ·
                        rfl

theorem cell23_7469901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7469901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469901 prefixEnd_7469901 := by exact prefixLift 7469901
  have htrace : WordTrace (prefixWord ++ tailWord_7469901) baseStart_7469901 baseEnd_7469901 := by
    simpa [prefixWord, tailWord_7469901, baseEnd_7469901] using wordTrace_append hprefix tailTrace_7469901
  have hstable : (prefixWord ++ tailWord_7469901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469901).length < 2 ^ (prefixWord ++ tailWord_7469901).sum := by decide
  have hdescent : baseEnd_7469901 < baseStart_7469901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469920 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 3, 5]
def baseStart_7469920 : Nat := 118140960795 + 7469920 * 2 ^ 59
def prefixEnd_7469920 : Nat := 4983230072969 + 3 ^ 40 * 7469920 * 2
def baseEnd_7469920 : Nat := 1278553136877839712448823

theorem tailTrace_7469920 : CollatzResearch.WordTrace tailWord_7469920 prefixEnd_7469920 1278553136877839712448823 := by
  unfold tailWord_7469920
  simp only [CollatzResearch.WordTrace]
  refine ⟨136225182548881537806303607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181633576731842050408404809 136225182548881537806303607)
  ·
    refine ⟨204337773823322306709455411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136225182548881537806303607 204337773823322306709455411)
    ·
      refine ⟨306506660734983460064183117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204337773823322306709455411 306506660734983460064183117)
      ·
        refine ⟨114939997775618797524068669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306506660734983460064183117 114939997775618797524068669)
        ·
          refine ⟨43102499165857049071525751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114939997775618797524068669 43102499165857049071525751)
          ·
            refine ⟨64653748748785573607288627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43102499165857049071525751 64653748748785573607288627)
            ·
              refine ⟨96980623123178360410932941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64653748748785573607288627 96980623123178360410932941)
              ·
                refine ⟨36367733671191885154099853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96980623123178360410932941 36367733671191885154099853)
                ·
                  refine ⟨13637900126696956932787445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36367733671191885154099853 13637900126696956932787445)
                  ·
                    refine ⟨1278553136877839712448823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13637900126696956932787445 1278553136877839712448823)
                    ·
                      rfl

theorem cell23_7469920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_7469920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469920 prefixEnd_7469920 := by exact prefixLift 7469920
  have htrace : WordTrace (prefixWord ++ tailWord_7469920) baseStart_7469920 baseEnd_7469920 := by
    simpa [prefixWord, tailWord_7469920, baseEnd_7469920] using wordTrace_append hprefix tailTrace_7469920
  have hstable : (prefixWord ++ tailWord_7469920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469920).length < 2 ^ (prefixWord ++ tailWord_7469920).sum := by decide
  have hdescent : baseEnd_7469920 < baseStart_7469920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469937 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 1, 5]
def baseStart_7469937 : Nat := 118140960795 + 7469937 * 2 ^ 59
def prefixEnd_7469937 : Nat := 4983230072969 + 3 ^ 40 * 7469937 * 2
def baseEnd_7469937 : Nat := 1278556046601548523611297

theorem tailTrace_7469937 : CollatzResearch.WordTrace tailWord_7469937 prefixEnd_7469937 1278556046601548523611297 := by
  unfold tailWord_7469937
  simp only [CollatzResearch.WordTrace]
  refine ⟨272450985138701487515976065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181633990092467658343984043 272450985138701487515976065)
  ·
    refine ⟨204338238854026115636982049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272450985138701487515976065 204338238854026115636982049)
    ·
      refine ⟨153253679140519586727736537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204338238854026115636982049 153253679140519586727736537)
      ·
        refine ⟨114940259355389690045802403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153253679140519586727736537 114940259355389690045802403)
        ·
          refine ⟨172410389033084535068703605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114940259355389690045802403 172410389033084535068703605)
          ·
            refine ⟨16163473971851675162690963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172410389033084535068703605 16163473971851675162690963)
            ·
              refine ⟨24245210957777512744036445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16163473971851675162690963 24245210957777512744036445)
              ·
                refine ⟨9091954109166567279013667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24245210957777512744036445 9091954109166567279013667)
                ·
                  refine ⟨13637931163749850918520501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9091954109166567279013667 13637931163749850918520501)
                  ·
                    refine ⟨1278556046601548523611297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13637931163749850918520501 1278556046601548523611297)
                    ·
                      rfl

theorem cell23_7469937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_7469937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469937 prefixEnd_7469937 := by exact prefixLift 7469937
  have htrace : WordTrace (prefixWord ++ tailWord_7469937) baseStart_7469937 baseEnd_7469937 := by
    simpa [prefixWord, tailWord_7469937, baseEnd_7469937] using wordTrace_append hprefix tailTrace_7469937
  have hstable : (prefixWord ++ tailWord_7469937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469937).length < 2 ^ (prefixWord ++ tailWord_7469937).sum := by decide
  have hdescent : baseEnd_7469937 < baseStart_7469937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470004 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7470004 : Nat := 118140960795 + 7470004 * 2 ^ 59
def prefixEnd_7470004 : Nat := 4983230072969 + 3 ^ 40 * 7470004 * 2
def baseEnd_7470004 : Nat := 3835702543008496808696083

theorem tailTrace_7470004 : CollatzResearch.WordTrace tailWord_7470004 prefixEnd_7470004 3835702543008496808696083 := by
  unfold tailWord_7470004
  simp only [CollatzResearch.WordTrace]
  refine ⟨136226714414729378979332533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181635619219639171972443377 136226714414729378979332533)
  ·
    refine ⟨12771254476380879279312425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136226714414729378979332533 12771254476380879279312425)
    ·
      refine ⟨9578440857285659459484319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12771254476380879279312425 9578440857285659459484319)
      ·
        refine ⟨14367661285928489189226479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9578440857285659459484319 14367661285928489189226479)
        ·
          refine ⟨21551491928892733783839719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14367661285928489189226479 21551491928892733783839719)
          ·
            refine ⟨32327237893339100675759579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21551491928892733783839719 32327237893339100675759579)
            ·
              refine ⟨48490856840008651013639369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32327237893339100675759579 48490856840008651013639369)
              ·
                refine ⟨36368142630006488260229527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48490856840008651013639369 36368142630006488260229527)
                ·
                  refine ⟨54552213945009732390344291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36368142630006488260229527 54552213945009732390344291)
                  ·
                    refine ⟨81828320917514598585516437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54552213945009732390344291 81828320917514598585516437)
                    ·
                      refine ⟨3835702543008496808696083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81828320917514598585516437 3835702543008496808696083)
                      ·
                        rfl

theorem cell23_7470004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7470004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470004 prefixEnd_7470004 := by exact prefixLift 7470004
  have htrace : WordTrace (prefixWord ++ tailWord_7470004) baseStart_7470004 baseEnd_7470004 := by
    simpa [prefixWord, tailWord_7470004, baseEnd_7470004] using wordTrace_append hprefix tailTrace_7470004
  have hstable : (prefixWord ++ tailWord_7470004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470004).length < 2 ^ (prefixWord ++ tailWord_7470004).sum := by decide
  have hdescent : baseEnd_7470004 < baseStart_7470004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470010 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_7470010 : Nat := 118140960795 + 7470010 * 2 ^ 59
def prefixEnd_7470010 : Nat := 4983230072969 + 3 ^ 40 * 7470010 * 2
def baseEnd_7470010 : Nat := 1278568541297474595073685

theorem tailTrace_7470010 : CollatzResearch.WordTrace tailWord_7470010 prefixEnd_7470010 1278568541297474595073685 := by
  unfold tailWord_7470010
  simp only [CollatzResearch.WordTrace]
  refine ⟨68113411916859255245845871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181635765111624680655588989 68113411916859255245845871)
  ·
    refine ⟨102170117875288882868768807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68113411916859255245845871 102170117875288882868768807)
    ·
      refine ⟨153255176812933324303153211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102170117875288882868768807 153255176812933324303153211)
      ·
        refine ⟨229882765219399986454729817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153255176812933324303153211 229882765219399986454729817)
        ·
          refine ⟨172412073914549989841047363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229882765219399986454729817 172412073914549989841047363)
          ·
            refine ⟨258618110871824984761571045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172412073914549989841047363 258618110871824984761571045)
            ·
              refine ⟨48490895788467184642794571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258618110871824984761571045 48490895788467184642794571)
              ·
                refine ⟨72736343682700776964191857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48490895788467184642794571 72736343682700776964191857)
                ·
                  refine ⟨54552257762025582723143893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72736343682700776964191857 54552257762025582723143893)
                  ·
                    refine ⟨1278568541297474595073685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54552257762025582723143893 1278568541297474595073685)
                    ·
                      rfl

theorem cell23_7470010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_7470010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470010 prefixEnd_7470010 := by exact prefixLift 7470010
  have htrace : WordTrace (prefixWord ++ tailWord_7470010) baseStart_7470010 baseEnd_7470010 := by
    simpa [prefixWord, tailWord_7470010, baseEnd_7470010] using wordTrace_append hprefix tailTrace_7470010
  have hstable : (prefixWord ++ tailWord_7470010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470010).length < 2 ^ (prefixWord ++ tailWord_7470010).sum := by decide
  have hdescent : baseEnd_7470010 < baseStart_7470010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470022 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7470022 : Nat := 118140960795 + 7470022 * 2 ^ 59
def prefixEnd_7470022 : Nat := 4983230072969 + 3 ^ 40 * 7470022 * 2
def baseEnd_7470022 : Nat := 1278570595220092579423667

theorem tailTrace_7470022 : CollatzResearch.WordTrace tailWord_7470022 prefixEnd_7470022 1278570595220092579423667 := by
  unfold tailWord_7470022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514190166981048344775635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181636056895595698021880213 8514190166981048344775635)
  ·
    refine ⟨12771285250471572517163453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8514190166981048344775635 12771285250471572517163453)
    ·
      refine ⟨4789231968926839693936295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12771285250471572517163453 4789231968926839693936295)
      ·
        refine ⟨7183847953390259540904443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4789231968926839693936295 7183847953390259540904443)
        ·
          refine ⟨10775771930085389311356665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7183847953390259540904443 10775771930085389311356665)
          ·
            refine ⟨8081828947564041983517499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10775771930085389311356665 8081828947564041983517499)
            ·
              refine ⟨12122743421346062975276249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081828947564041983517499 12122743421346062975276249)
              ·
                refine ⟨9092057566009547231457187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12122743421346062975276249 9092057566009547231457187)
                ·
                  refine ⟨13638086349014320847185781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9092057566009547231457187 13638086349014320847185781)
                  ·
                    refine ⟨1278570595220092579423667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13638086349014320847185781 1278570595220092579423667)
                    ·
                      rfl

theorem cell23_7470022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7470022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470022 prefixEnd_7470022 := by exact prefixLift 7470022
  have htrace : WordTrace (prefixWord ++ tailWord_7470022) baseStart_7470022 baseEnd_7470022 := by
    simpa [prefixWord, tailWord_7470022, baseEnd_7470022] using wordTrace_append hprefix tailTrace_7470022
  have hstable : (prefixWord ++ tailWord_7470022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470022).length < 2 ^ (prefixWord ++ tailWord_7470022).sum := by decide
  have hdescent : baseEnd_7470022 < baseStart_7470022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470060 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_7470060 : Nat := 118140960795 + 7470060 * 2 ^ 59
def prefixEnd_7470060 : Nat := 4983230072969 + 3 ^ 40 * 7470060 * 2
def baseEnd_7470060 : Nat := 3835731297925148589595825

theorem tailTrace_7470060 : CollatzResearch.WordTrace tailWord_7470060 prefixEnd_7470060 3835731297925148589595825 := by
  unfold tailWord_7470060
  simp only [CollatzResearch.WordTrace]
  refine ⟨136227735658627939761351817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181636980878170586348469089 136227735658627939761351817)
  ·
    refine ⟨102170801743970954821013863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136227735658627939761351817 102170801743970954821013863)
    ·
      refine ⟨153256202615956432231520795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102170801743970954821013863 153256202615956432231520795)
      ·
        refine ⟨229884303923934648347281193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153256202615956432231520795 229884303923934648347281193)
        ·
          refine ⟨172413227942950986260460895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229884303923934648347281193 172413227942950986260460895)
          ·
            refine ⟨258619841914426479390691343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172413227942950986260460895 258619841914426479390691343)
            ·
              refine ⟨387929762871639719086037015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258619841914426479390691343 387929762871639719086037015)
              ·
                refine ⟨581894644307459578629055523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387929762871639719086037015 581894644307459578629055523)
                ·
                  refine ⟨872841966461189367943583285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581894644307459578629055523 872841966461189367943583285)
                  ·
                    refine ⟨81828934355736503244710933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 872841966461189367943583285 81828934355736503244710933)
                    ·
                      refine ⟨3835731297925148589595825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81828934355736503244710933 3835731297925148589595825)
                      ·
                        rfl

theorem cell23_7470060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_7470060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470060 prefixEnd_7470060 := by exact prefixLift 7470060
  have htrace : WordTrace (prefixWord ++ tailWord_7470060) baseStart_7470060 baseEnd_7470060 := by
    simpa [prefixWord, tailWord_7470060, baseEnd_7470060] using wordTrace_append hprefix tailTrace_7470060
  have hstable : (prefixWord ++ tailWord_7470060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470060).length < 2 ^ (prefixWord ++ tailWord_7470060).sum := by decide
  have hdescent : baseEnd_7470060 < baseStart_7470060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470080 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_7470080 : Nat := 118140960795 + 7470080 * 2 ^ 59
def prefixEnd_7470080 : Nat := 4983230072969 + 3 ^ 40 * 7470080 * 2
def baseEnd_7470080 : Nat := 3835741567538238511345733

theorem tailTrace_7470080 : CollatzResearch.WordTrace tailWord_7470080 prefixEnd_7470080 3835741567538238511345733 := by
  unfold tailWord_7470080
  simp only [CollatzResearch.WordTrace]
  refine ⟨136228100388591711469215847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181637467184788948625621129 136228100388591711469215847)
  ·
    refine ⟨204342150582887567203823771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136228100388591711469215847 204342150582887567203823771)
    ·
      refine ⟨306513225874331350805735657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204342150582887567203823771 306513225874331350805735657)
      ·
        refine ⟨229884919405748513104301743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306513225874331350805735657 229884919405748513104301743)
        ·
          refine ⟨344827379108622769656452615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229884919405748513104301743 344827379108622769656452615)
          ·
            refine ⟨517241068662934154484678923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344827379108622769656452615 517241068662934154484678923)
            ·
              refine ⟨775861602994401231727018385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517241068662934154484678923 775861602994401231727018385)
              ·
                refine ⟨581896202245800923795263789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775861602994401231727018385 581896202245800923795263789)
                ·
                  refine ⟨218211075842175346423223921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581896202245800923795263789 218211075842175346423223921)
                  ·
                    refine ⟨163658306881631509817417941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218211075842175346423223921 163658306881631509817417941)
                    ·
                      refine ⟨3835741567538238511345733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163658306881631509817417941 3835741567538238511345733)
                      ·
                        rfl

theorem cell23_7470080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_7470080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470080 prefixEnd_7470080 := by exact prefixLift 7470080
  have htrace : WordTrace (prefixWord ++ tailWord_7470080) baseStart_7470080 baseEnd_7470080 := by
    simpa [prefixWord, tailWord_7470080, baseEnd_7470080] using wordTrace_append hprefix tailTrace_7470080
  have hstable : (prefixWord ++ tailWord_7470080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470080).length < 2 ^ (prefixWord ++ tailWord_7470080).sum := by decide
  have hdescent : baseEnd_7470080 < baseStart_7470080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470081 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_7470081 : Nat := 118140960795 + 7470081 * 2 ^ 59
def prefixEnd_7470081 : Nat := 4983230072969 + 3 ^ 40 * 7470081 * 2
def baseEnd_7470081 : Nat := 3835742081018893007433229

theorem tailTrace_7470081 : CollatzResearch.WordTrace tailWord_7470081 prefixEnd_7470081 3835742081018893007433229 := by
  unfold tailWord_7470081
  simp only [CollatzResearch.WordTrace]
  refine ⟨272456237250179800109218097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181637491500119866739478731 272456237250179800109218097)
  ·
    refine ⟨204342177937634850081913573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272456237250179800109218097 204342177937634850081913573)
    ·
      refine ⟨38314158363306534390358795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204342177937634850081913573 38314158363306534390358795)
      ·
        refine ⟨57471237544959801585538193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38314158363306534390358795 57471237544959801585538193)
        ·
          refine ⟨43103428158719851189153645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57471237544959801585538193 43103428158719851189153645)
          ·
            refine ⟨16163785559519944195932617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43103428158719851189153645 16163785559519944195932617)
            ·
              refine ⟨12122839169639958146949463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16163785559519944195932617 12122839169639958146949463)
              ·
                refine ⟨18184258754459937220424195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12122839169639958146949463 18184258754459937220424195)
                ·
                  refine ⟨27276388131689905830636293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18184258754459937220424195 27276388131689905830636293)
                  ·
                    refine ⟨5114322774691857343244305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27276388131689905830636293 5114322774691857343244305)
                    ·
                      refine ⟨3835742081018893007433229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114322774691857343244305 3835742081018893007433229)
                      ·
                        rfl

theorem cell23_7470081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_7470081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470081 prefixEnd_7470081 := by exact prefixLift 7470081
  have htrace : WordTrace (prefixWord ++ tailWord_7470081) baseStart_7470081 baseEnd_7470081 := by
    simpa [prefixWord, tailWord_7470081, baseEnd_7470081] using wordTrace_append hprefix tailTrace_7470081
  have hstable : (prefixWord ++ tailWord_7470081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470081).length < 2 ^ (prefixWord ++ tailWord_7470081).sum := by decide
  have hdescent : baseEnd_7470081 < baseStart_7470081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470087 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 7]
def baseStart_7470087 : Nat := 118140960795 + 7470087 * 2 ^ 59
def prefixEnd_7470087 : Nat := 4983230072969 + 3 ^ 40 * 7470087 * 2
def baseEnd_7470087 : Nat := 426193906878091109328689

theorem tailTrace_7470087 : CollatzResearch.WordTrace tailWord_7470087 prefixEnd_7470087 426193906878091109328689 := by
  unfold tailWord_7470087
  simp only [CollatzResearch.WordTrace]
  refine ⟨272456456088158063133936515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181637637392105375422624343 272456456088158063133936515)
  ·
    refine ⟨408684684132237094700904773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272456456088158063133936515 408684684132237094700904773)
    ·
      refine ⟨76628378274794455256419645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408684684132237094700904773 76628378274794455256419645)
      ·
        refine ⟨28735641853047920721157367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76628378274794455256419645 28735641853047920721157367)
        ·
          refine ⟨43103462779571881081736051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28735641853047920721157367 43103462779571881081736051)
          ·
            refine ⟨64655194169357821622604077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43103462779571881081736051 64655194169357821622604077)
            ·
              refine ⟨24245697813509183108476529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64655194169357821622604077 24245697813509183108476529)
              ·
                refine ⟨18184273360131887331357397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24245697813509183108476529 18184273360131887331357397)
                ·
                  refine ⟨426193906878091109328689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18184273360131887331357397 426193906878091109328689)
                  ·
                    rfl

theorem cell23_7470087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 7].length) (baseStart_7470087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470087 prefixEnd_7470087 := by exact prefixLift 7470087
  have htrace : WordTrace (prefixWord ++ tailWord_7470087) baseStart_7470087 baseEnd_7470087 := by
    simpa [prefixWord, tailWord_7470087, baseEnd_7470087] using wordTrace_append hprefix tailTrace_7470087
  have hstable : (prefixWord ++ tailWord_7470087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470087).length < 2 ^ (prefixWord ++ tailWord_7470087).sum := by decide
  have hdescent : baseEnd_7470087 < baseStart_7470087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470104 : List Nat := [2, 1, 2, 3, 2, 2, 1, 5, 5]
def baseStart_7470104 : Nat := 118140960795 + 7470104 * 2 ^ 59
def prefixEnd_7470104 : Nat := 4983230072969 + 3 ^ 40 * 7470104 * 2
def baseEnd_7470104 : Nat := 426194876785994046382847

theorem tailTrace_7470104 : CollatzResearch.WordTrace tailWord_7470104 prefixEnd_7470104 426194876785994046382847 := by
  unfold tailWord_7470104
  simp only [CollatzResearch.WordTrace]
  refine ⟨136228538064548237518652683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181638050752730983358203577 136228538064548237518652683)
  ·
    refine ⟨204342807096822356277979025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136228538064548237518652683 204342807096822356277979025)
    ·
      refine ⟨153257105322616767208484269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204342807096822356277979025 153257105322616767208484269)
      ·
        refine ⟨57471414495981287703181601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153257105322616767208484269 57471414495981287703181601)
        ·
          refine ⟨43103560871985965777386201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57471414495981287703181601 43103560871985965777386201)
          ·
            refine ⟨32327670653989474333039651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43103560871985965777386201 32327670653989474333039651)
            ·
              refine ⟨48491505980984211499559477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32327670653989474333039651 48491505980984211499559477)
              ·
                refine ⟨4546078685717269828083701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48491505980984211499559477 4546078685717269828083701)
                ·
                  refine ⟨426194876785994046382847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4546078685717269828083701 426194876785994046382847)
                  ·
                    rfl

theorem cell23_7470104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 5].length) (baseStart_7470104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470104 prefixEnd_7470104 := by exact prefixLift 7470104
  have htrace : WordTrace (prefixWord ++ tailWord_7470104) baseStart_7470104 baseEnd_7470104 := by
    simpa [prefixWord, tailWord_7470104, baseEnd_7470104] using wordTrace_append hprefix tailTrace_7470104
  have hstable : (prefixWord ++ tailWord_7470104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470104).length < 2 ^ (prefixWord ++ tailWord_7470104).sum := by decide
  have hdescent : baseEnd_7470104 < baseStart_7470104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470114 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_7470114 : Nat := 118140960795 + 7470114 * 2 ^ 59
def prefixEnd_7470114 : Nat := 4983230072969 + 3 ^ 40 * 7470114 * 2
def baseEnd_7470114 : Nat := 3835759025880491378320577

theorem tailTrace_7470114 : CollatzResearch.WordTrace tailWord_7470114 prefixEnd_7470114 3835759025880491378320577 := by
  unfold tailWord_7470114
  simp only [CollatzResearch.WordTrace]
  refine ⟨68114360214765061686292349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181638293906040164496779597 68114360214765061686292349)
  ·
    refine ⟨25542885080536898132359631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68114360214765061686292349 25542885080536898132359631)
    ·
      refine ⟨38314327620805347198539447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25542885080536898132359631 38314327620805347198539447)
      ·
        refine ⟨57471491431208020797809171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38314327620805347198539447 57471491431208020797809171)
        ·
          refine ⟨86207237146812031196713757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57471491431208020797809171 86207237146812031196713757)
          ·
            refine ⟨32327713930054511698767659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86207237146812031196713757 32327713930054511698767659)
            ·
              refine ⟨48491570895081767548151489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32327713930054511698767659 48491570895081767548151489)
              ·
                refine ⟨36368678171311325661113617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48491570895081767548151489 36368678171311325661113617)
                ·
                  refine ⟨27276508628483494245835213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36368678171311325661113617 27276508628483494245835213)
                  ·
                    refine ⟨10228690735681310342188205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27276508628483494245835213 10228690735681310342188205)
                    ·
                      refine ⟨3835759025880491378320577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10228690735681310342188205 3835759025880491378320577)
                      ·
                        rfl

theorem cell23_7470114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_7470114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470114 prefixEnd_7470114 := by exact prefixLift 7470114
  have htrace : WordTrace (prefixWord ++ tailWord_7470114) baseStart_7470114 baseEnd_7470114 := by
    simpa [prefixWord, tailWord_7470114, baseEnd_7470114] using wordTrace_append hprefix tailTrace_7470114
  have hstable : (prefixWord ++ tailWord_7470114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470114).length < 2 ^ (prefixWord ++ tailWord_7470114).sum := by decide
  have hdescent : baseEnd_7470114 < baseStart_7470114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470117 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_7470117 : Nat := 118140960795 + 7470117 * 2 ^ 59
def prefixEnd_7470117 : Nat := 4983230072969 + 3 ^ 40 * 7470117 * 2
def baseEnd_7470117 : Nat := 1278586855440818288861021

theorem tailTrace_7470117 : CollatzResearch.WordTrace tailWord_7470117 prefixEnd_7470117 1278586855440818288861021 := by
  unfold tailWord_7470117
  simp only [CollatzResearch.WordTrace]
  refine ⟨272457550278049378257528605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181638366852032918838352403 272457550278049378257528605)
  ·
    refine ⟨102171581354268516846573227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272457550278049378257528605 102171581354268516846573227)
    ·
      refine ⟨153257372031402775269859841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102171581354268516846573227 153257372031402775269859841)
      ·
        refine ⟨114943029023552081452394881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153257372031402775269859841 114943029023552081452394881)
        ·
          refine ⟨86207271767664061089296161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114943029023552081452394881 86207271767664061089296161)
          ·
            refine ⟨64655453825748045816972121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86207271767664061089296161 64655453825748045816972121)
            ·
              refine ⟨48491590369311034362729091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64655453825748045816972121 48491590369311034362729091)
              ·
                refine ⟨72737385553966551544093637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48491590369311034362729091 72737385553966551544093637)
                ·
                  refine ⟨13638259791368728414517557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72737385553966551544093637 13638259791368728414517557)
                  ·
                    refine ⟨1278586855440818288861021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13638259791368728414517557 1278586855440818288861021)
                    ·
                      rfl

theorem cell23_7470117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_7470117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470117 prefixEnd_7470117 := by exact prefixLift 7470117
  have htrace : WordTrace (prefixWord ++ tailWord_7470117) baseStart_7470117 baseEnd_7470117 := by
    simpa [prefixWord, tailWord_7470117, baseEnd_7470117] using wordTrace_append hprefix tailTrace_7470117
  have hstable : (prefixWord ++ tailWord_7470117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470117).length < 2 ^ (prefixWord ++ tailWord_7470117).sum := by decide
  have hdescent : baseEnd_7470117 < baseStart_7470117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470132 : List Nat := [2, 5, 1, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7470132 : Nat := 118140960795 + 7470132 * 2 ^ 59
def prefixEnd_7470132 : Nat := 4983230072969 + 3 ^ 40 * 7470132 * 2
def baseEnd_7470132 : Nat := 3835768268532272307895495

theorem tailTrace_7470132 : CollatzResearch.WordTrace tailWord_7470132 prefixEnd_7470132 3835768268532272307895495 := by
  unfold tailWord_7470132
  simp only [CollatzResearch.WordTrace]
  refine ⟨136229048686497517909662325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181638731581996690546216433 136229048686497517909662325)
  ·
    refine ⟨12771473314359142304030843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136229048686497517909662325 12771473314359142304030843)
    ·
      refine ⟨19157209971538713456046265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12771473314359142304030843 19157209971538713456046265)
      ·
        refine ⟨14367907478654035092034699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19157209971538713456046265 14367907478654035092034699)
        ·
          refine ⟨21551861217981052638052049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14367907478654035092034699 21551861217981052638052049)
          ·
            refine ⟨16163895913485789478539037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21551861217981052638052049 16163895913485789478539037)
            ·
              refine ⟨6061460967557171054452139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16163895913485789478539037 6061460967557171054452139)
              ·
                refine ⟨9092191451335756581678209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061460967557171054452139 9092191451335756581678209)
                ·
                  refine ⟨6819143588501817436258657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9092191451335756581678209 6819143588501817436258657)
                  ·
                    refine ⟨5114357691376363077193993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819143588501817436258657 5114357691376363077193993)
                    ·
                      refine ⟨3835768268532272307895495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114357691376363077193993 3835768268532272307895495)
                      ·
                        rfl

theorem cell23_7470132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7470132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470132 prefixEnd_7470132 := by exact prefixLift 7470132
  have htrace : WordTrace (prefixWord ++ tailWord_7470132) baseStart_7470132 baseEnd_7470132 := by
    simpa [prefixWord, tailWord_7470132, baseEnd_7470132] using wordTrace_append hprefix tailTrace_7470132
  have hstable : (prefixWord ++ tailWord_7470132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470132).length < 2 ^ (prefixWord ++ tailWord_7470132).sum := by decide
  have hdescent : baseEnd_7470132 < baseStart_7470132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470134 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7470134 : Nat := 118140960795 + 7470134 * 2 ^ 59
def prefixEnd_7470134 : Nat := 4983230072969 + 3 ^ 40 * 7470134 * 2
def baseEnd_7470134 : Nat := 1278589765164527100023495

theorem tailTrace_7470134 : CollatzResearch.WordTrace tailWord_7470134 prefixEnd_7470134 1278589765164527100023495 := by
  unfold tailWord_7470134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17028635644936736885056091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181638780212658526773931637 17028635644936736885056091)
  ·
    refine ⟨25542953467405105327584137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17028635644936736885056091 25542953467405105327584137)
    ·
      refine ⟨19157215100553828995688103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25542953467405105327584137 19157215100553828995688103)
      ·
        refine ⟨28735822650830743493532155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19157215100553828995688103 28735822650830743493532155)
        ·
          refine ⟨43103733976246115240298233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28735822650830743493532155 43103733976246115240298233)
          ·
            refine ⟨32327800482184586430223675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43103733976246115240298233 32327800482184586430223675)
            ·
              refine ⟨48491700723276879645335513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32327800482184586430223675 48491700723276879645335513)
              ·
                refine ⟨36368775542457659734001635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48491700723276879645335513 36368775542457659734001635)
                ·
                  refine ⟨54553163313686489601002453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36368775542457659734001635 54553163313686489601002453)
                  ·
                    refine ⟨1278589765164527100023495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54553163313686489601002453 1278589765164527100023495)
                    ·
                      rfl

theorem cell23_7470134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7470134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470134 prefixEnd_7470134 := by exact prefixLift 7470134
  have htrace : WordTrace (prefixWord ++ tailWord_7470134) baseStart_7470134 baseEnd_7470134 := by
    simpa [prefixWord, tailWord_7470134, baseEnd_7470134] using wordTrace_append hprefix tailTrace_7470134
  have hstable : (prefixWord ++ tailWord_7470134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470134).length < 2 ^ (prefixWord ++ tailWord_7470134).sum := by decide
  have hdescent : baseEnd_7470134 < baseStart_7470134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470154 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_7470154 : Nat := 118140960795 + 7470154 * 2 ^ 59
def prefixEnd_7470154 : Nat := 4983230072969 + 3 ^ 40 * 7470154 * 2
def baseEnd_7470154 : Nat := 3835779565106671221820393

theorem tailTrace_7470154 : CollatzResearch.WordTrace tailWord_7470154 prefixEnd_7470154 3835779565106671221820393 := by
  unfold tailWord_7470154
  simp only [CollatzResearch.WordTrace]
  refine ⟨68114724944728833394156379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181639266519276889051083677 68114724944728833394156379)
  ·
    refine ⟨102172087417093250091234569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68114724944728833394156379 102172087417093250091234569)
    ·
      refine ⟨76629065562819937568425927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102172087417093250091234569 76629065562819937568425927)
      ·
        refine ⟨114943598344229906352638891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76629065562819937568425927 114943598344229906352638891)
        ·
          refine ⟨172415397516344859528958337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114943598344229906352638891 172415397516344859528958337)
          ·
            refine ⟨129311548137258644646718753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172415397516344859528958337 129311548137258644646718753)
            ·
              refine ⟨96983661102943983485039065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129311548137258644646718753 96983661102943983485039065)
              ·
                refine ⟨72737745827207987613779299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96983661102943983485039065 72737745827207987613779299)
                ·
                  refine ⟨109106618740811981420668949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72737745827207987613779299 109106618740811981420668949)
                  ·
                    refine ⟨5114372753475561629093857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109106618740811981420668949 5114372753475561629093857)
                    ·
                      refine ⟨3835779565106671221820393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114372753475561629093857 3835779565106671221820393)
                      ·
                        rfl

theorem cell23_7470154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_7470154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470154 prefixEnd_7470154 := by exact prefixLift 7470154
  have htrace : WordTrace (prefixWord ++ tailWord_7470154) baseStart_7470154 baseEnd_7470154 := by
    simpa [prefixWord, tailWord_7470154, baseEnd_7470154] using wordTrace_append hprefix tailTrace_7470154
  have hstable : (prefixWord ++ tailWord_7470154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470154).length < 2 ^ (prefixWord ++ tailWord_7470154).sum := by decide
  have hdescent : baseEnd_7470154 < baseStart_7470154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470164 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_7470164 : Nat := 118140960795 + 7470164 * 2 ^ 59
def prefixEnd_7470164 : Nat := 4983230072969 + 3 ^ 40 * 7470164 * 2
def baseEnd_7470164 : Nat := 1278594899971072060898449

theorem tailTrace_7470164 : CollatzResearch.WordTrace tailWord_7470164 prefixEnd_7470164 1278594899971072060898449 := by
  unfold tailWord_7470164
  simp only [CollatzResearch.WordTrace]
  refine ⟨136229632254439552642244773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181639509672586070189659697 136229632254439552642244773)
  ·
    refine ⟨25543056047707416120420895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136229632254439552642244773 25543056047707416120420895)
    ·
      refine ⟨38314584071561124180631343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25543056047707416120420895 38314584071561124180631343)
      ·
        refine ⟨57471876107341686270947015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38314584071561124180631343 57471876107341686270947015)
        ·
          refine ⟨86207814161012529406420523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57471876107341686270947015 86207814161012529406420523)
          ·
            refine ⟨129311721241518794109630785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86207814161012529406420523 129311721241518794109630785)
            ·
              refine ⟨96983790931139095582223089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129311721241518794109630785 96983790931139095582223089)
              ·
                refine ⟨72737843198354321686667317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96983790931139095582223089 72737843198354321686667317)
                ·
                  refine ⟨6819172799845717658125061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72737843198354321686667317 6819172799845717658125061)
                  ·
                    refine ⟨1278594899971072060898449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6819172799845717658125061 1278594899971072060898449)
                    ·
                      rfl

theorem cell23_7470164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_7470164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470164 prefixEnd_7470164 := by exact prefixLift 7470164
  have htrace : WordTrace (prefixWord ++ tailWord_7470164) baseStart_7470164 baseEnd_7470164 := by
    simpa [prefixWord, tailWord_7470164, baseEnd_7470164] using wordTrace_append hprefix tailTrace_7470164
  have hstable : (prefixWord ++ tailWord_7470164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470164).length < 2 ^ (prefixWord ++ tailWord_7470164).sum := by decide
  have hdescent : baseEnd_7470164 < baseStart_7470164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470177 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 8]
def baseStart_7470177 : Nat := 118140960795 + 7470177 * 2 ^ 59
def prefixEnd_7470177 : Nat := 4983230072969 + 3 ^ 40 * 7470177 * 2
def baseEnd_7470177 : Nat := 426199041684636070203643

theorem tailTrace_7470177 : CollatzResearch.WordTrace tailWord_7470177 prefixEnd_7470177 426199041684636070203643 := by
  unfold tailWord_7470177
  simp only [CollatzResearch.WordTrace]
  refine ⟨272459738657832008504712785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181639825771888005669808523 272459738657832008504712785)
  ·
    refine ⟨204344803993374006378534589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272459738657832008504712785 204344803993374006378534589)
    ·
      refine ⟨76629301497515252391950471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204344803993374006378534589 76629301497515252391950471)
      ·
        refine ⟨114943952246272878587925707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76629301497515252391950471 114943952246272878587925707)
        ·
          refine ⟨172415928369409317881888561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114943952246272878587925707 172415928369409317881888561)
          ·
            refine ⟨129311946277056988411416421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172415928369409317881888561 129311946277056988411416421)
            ·
              refine ⟨24245989926948185327140579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129311946277056988411416421 24245989926948185327140579)
              ·
                refine ⟨36368984890422277990710869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24245989926948185327140579 36368984890422277990710869)
                ·
                  refine ⟨426199041684636070203643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36368984890422277990710869 426199041684636070203643)
                  ·
                    rfl

theorem cell23_7470177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 8].length) (baseStart_7470177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470177 prefixEnd_7470177 := by exact prefixLift 7470177
  have htrace : WordTrace (prefixWord ++ tailWord_7470177) baseStart_7470177 baseEnd_7470177 := by
    simpa [prefixWord, tailWord_7470177, baseEnd_7470177] using wordTrace_append hprefix tailTrace_7470177
  have hstable : (prefixWord ++ tailWord_7470177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470177).length < 2 ^ (prefixWord ++ tailWord_7470177).sum := by decide
  have hdescent : baseEnd_7470177 < baseStart_7470177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470194 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 6]
def baseStart_7470194 : Nat := 118140960795 + 7470194 * 2 ^ 59
def prefixEnd_7470194 : Nat := 4983230072969 + 3 ^ 40 * 7470194 * 2
def baseEnd_7470194 : Nat := 426200011592539007257801

theorem tailTrace_7470194 : CollatzResearch.WordTrace tailWord_7470194 prefixEnd_7470194 426200011592539007257801 := by
  unfold tailWord_7470194
  simp only [CollatzResearch.WordTrace]
  refine ⟨68115089674692605102020409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181640239132513613605387757 68115089674692605102020409)
  ·
    refine ⟨51086317256019453826515307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68115089674692605102020409 51086317256019453826515307)
    ·
      refine ⟨76629475884029180739772961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51086317256019453826515307 76629475884029180739772961)
      ·
        refine ⟨57472106913021885554829721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76629475884029180739772961 57472106913021885554829721)
        ·
          refine ⟨43104080184766414166122291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57472106913021885554829721 43104080184766414166122291)
          ·
            refine ⟨64656120277149621249183437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43104080184766414166122291 64656120277149621249183437)
            ·
              refine ⟨24246045103931107968443789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64656120277149621249183437 24246045103931107968443789)
              ·
                refine ⟨9092266913974165488166421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24246045103931107968443789 9092266913974165488166421)
                ·
                  refine ⟨426200011592539007257801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9092266913974165488166421 426200011592539007257801)
                  ·
                    rfl

theorem cell23_7470194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_7470194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470194 prefixEnd_7470194 := by exact prefixLift 7470194
  have htrace : WordTrace (prefixWord ++ tailWord_7470194) baseStart_7470194 baseEnd_7470194 := by
    simpa [prefixWord, tailWord_7470194, baseEnd_7470194] using wordTrace_append hprefix tailTrace_7470194
  have hstable : (prefixWord ++ tailWord_7470194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470194).length < 2 ^ (prefixWord ++ tailWord_7470194).sum := by decide
  have hdescent : baseEnd_7470194 < baseStart_7470194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470295 : List Nat := [1, 1, 3, 2, 1, 2, 4, 4, 1, 2, 2]
def baseStart_7470295 : Nat := 118140960795 + 7470295 * 2 ^ 59
def prefixEnd_7470295 : Nat := 4983230072969 + 3 ^ 40 * 7470295 * 2
def baseEnd_7470295 : Nat := 3835851965878955170157245

theorem tailTrace_7470295 : CollatzResearch.WordTrace tailWord_7470295 prefixEnd_7470295 3835851965878955170157245 := by
  unfold tailWord_7470295
  simp only [CollatzResearch.WordTrace]
  refine ⟨272464042471404514657508339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181642694980936343105005559 272464042471404514657508339)
  ·
    refine ⟨408696063707106771986262509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272464042471404514657508339 408696063707106771986262509)
    ·
      refine ⟨153261023890165039494848441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408696063707106771986262509 153261023890165039494848441)
      ·
        refine ⟨114945767917623779621136331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153261023890165039494848441 114945767917623779621136331)
        ·
          refine ⟨172418651876435669431704497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114945767917623779621136331 172418651876435669431704497)
          ·
            refine ⟨129313988907326752073778373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172418651876435669431704497 129313988907326752073778373)
            ·
              refine ⟨24246372920123766013833445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129313988907326752073778373 24246372920123766013833445)
              ·
                refine ⟨4546194922523206127593771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24246372920123766013833445 4546194922523206127593771)
                ·
                  refine ⟨6819292383784809191390657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546194922523206127593771 6819292383784809191390657)
                  ·
                    refine ⟨5114469287838606893542993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819292383784809191390657 5114469287838606893542993)
                    ·
                      refine ⟨3835851965878955170157245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114469287838606893542993 3835851965878955170157245)
                      ·
                        rfl

theorem cell23_7470295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_7470295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470295 prefixEnd_7470295 := by exact prefixLift 7470295
  have htrace : WordTrace (prefixWord ++ tailWord_7470295) baseStart_7470295 baseEnd_7470295 := by
    simpa [prefixWord, tailWord_7470295, baseEnd_7470295] using wordTrace_append hprefix tailTrace_7470295
  have hstable : (prefixWord ++ tailWord_7470295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470295).length < 2 ^ (prefixWord ++ tailWord_7470295).sum := by decide
  have hdescent : baseEnd_7470295 < baseStart_7470295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470362 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3]
def baseStart_7470362 : Nat := 118140960795 + 7470362 * 2 ^ 59
def prefixEnd_7470362 : Nat := 4983230072969 + 3 ^ 40 * 7470362 * 2
def baseEnd_7470362 : Nat := 3835886369082806408019437

theorem tailTrace_7470362 : CollatzResearch.WordTrace tailWord_7470362 prefixEnd_7470362 3835886369082806408019437 := by
  unfold tailWord_7470362
  simp only [CollatzResearch.WordTrace]
  refine ⟨68116621540540446275049335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181644324108107856733464893 68116621540540446275049335)
  ·
    refine ⟨102174932310810669412574003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68116621540540446275049335 102174932310810669412574003)
    ·
      refine ⟨153262398466216004118861005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102174932310810669412574003 153262398466216004118861005)
      ·
        refine ⟨57473399424831001544572877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153262398466216004118861005 57473399424831001544572877)
        ·
          refine ⟨21552524784311625579214829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57473399424831001544572877 21552524784311625579214829)
          ·
            refine ⟨8082196794116859592205561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21552524784311625579214829 8082196794116859592205561)
            ·
              refine ⟨6061647595587644694154171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082196794116859592205561 6061647595587644694154171)
              ·
                refine ⟨9092471393381467041231257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061647595587644694154171 9092471393381467041231257)
                ·
                  refine ⟨6819353545036100280923443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9092471393381467041231257 6819353545036100280923443)
                  ·
                    refine ⟨10229030317554150421385165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6819353545036100280923443 10229030317554150421385165)
                    ·
                      refine ⟨3835886369082806408019437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10229030317554150421385165 3835886369082806408019437)
                      ·
                        rfl

theorem cell23_7470362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_7470362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470362 prefixEnd_7470362 := by exact prefixLift 7470362
  have htrace : WordTrace (prefixWord ++ tailWord_7470362) baseStart_7470362 baseEnd_7470362 := by
    simpa [prefixWord, tailWord_7470362, baseEnd_7470362] using wordTrace_append hprefix tailTrace_7470362
  have hstable : (prefixWord ++ tailWord_7470362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470362).length < 2 ^ (prefixWord ++ tailWord_7470362).sum := by decide
  have hdescent : baseEnd_7470362 < baseStart_7470362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470441 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_7470441 : Nat := 118140960795 + 7470441 * 2 ^ 59
def prefixEnd_7470441 : Nat := 4983230072969 + 3 ^ 40 * 7470441 * 2
def baseEnd_7470441 : Nat := 3835926934054511598931573

theorem tailTrace_7470441 : CollatzResearch.WordTrace tailWord_7470441 prefixEnd_7470441 3835926934054511598931573 := by
  unfold tailWord_7470441
  simp only [CollatzResearch.WordTrace]
  refine ⟨272469367528875581592323177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181646245019250387728215451 272469367528875581592323177)
  ·
    refine ⟨204352025646656686194242383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272469367528875581592323177 204352025646656686194242383)
    ·
      refine ⟨306528038469985029291363575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204352025646656686194242383 306528038469985029291363575)
      ·
        refine ⟨459792057704977543937045363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306528038469985029291363575 459792057704977543937045363)
        ·
          refine ⟨689688086557466315905568045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459792057704977543937045363 689688086557466315905568045)
          ·
            refine ⟨258633032459049868464588017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 689688086557466315905568045 258633032459049868464588017)
            ·
              refine ⟨193974774344287401348441013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258633032459049868464588017 193974774344287401348441013)
              ·
                refine ⟨18185135094776943876416345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193974774344287401348441013 18185135094776943876416345)
                ·
                  refine ⟨13638851321082707907312259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18185135094776943876416345 13638851321082707907312259)
                  ·
                    refine ⟨20458276981624061860968389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13638851321082707907312259 20458276981624061860968389)
                    ·
                      refine ⟨3835926934054511598931573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20458276981624061860968389 3835926934054511598931573)
                      ·
                        rfl

theorem cell23_7470441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_7470441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470441 prefixEnd_7470441 := by exact prefixLift 7470441
  have htrace : WordTrace (prefixWord ++ tailWord_7470441) baseStart_7470441 baseEnd_7470441 := by
    simpa [prefixWord, tailWord_7470441, baseEnd_7470441] using wordTrace_append hprefix tailTrace_7470441
  have hstable : (prefixWord ++ tailWord_7470441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470441).length < 2 ^ (prefixWord ++ tailWord_7470441).sum := by decide
  have hdescent : baseEnd_7470441 < baseStart_7470441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470468 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_7470468 : Nat := 118140960795 + 7470468 * 2 ^ 59
def prefixEnd_7470468 : Nat := 4983230072969 + 3 ^ 40 * 7470468 * 2
def baseEnd_7470468 : Nat := 1278646932677394331097983

theorem tailTrace_7470468 : CollatzResearch.WordTrace tailWord_7470468 prefixEnd_7470468 1278646932677394331097983 := by
  unfold tailWord_7470468
  simp only [CollatzResearch.WordTrace]
  refine ⟨136235176149888882601778029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181646901533185176802370705 136235176149888882601778029)
  ·
    refine ⟨51088191056208330975666761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136235176149888882601778029 51088191056208330975666761)
    ·
      refine ⟨38316143292156248231750071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51088191056208330975666761 38316143292156248231750071)
      ·
        refine ⟨57474214938234372347625107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38316143292156248231750071 57474214938234372347625107)
        ·
          refine ⟨86211322407351558521437661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57474214938234372347625107 86211322407351558521437661)
          ·
            refine ⟨32329245902756834445539123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86211322407351558521437661 32329245902756834445539123)
            ·
              refine ⟨48493868854135251668308685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32329245902756834445539123 48493868854135251668308685)
              ·
                refine ⟨18185200820300719375615757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48493868854135251668308685 18185200820300719375615757)
                ·
                  refine ⟨6819450307612769765855909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18185200820300719375615757 6819450307612769765855909)
                  ·
                    refine ⟨1278646932677394331097983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6819450307612769765855909 1278646932677394331097983)
                    ·
                      rfl

theorem cell23_7470468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_7470468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470468 prefixEnd_7470468 := by exact prefixLift 7470468
  have htrace : WordTrace (prefixWord ++ tailWord_7470468) baseStart_7470468 baseEnd_7470468 := by
    simpa [prefixWord, tailWord_7470468, baseEnd_7470468] using wordTrace_append hprefix tailTrace_7470468
  have hstable : (prefixWord ++ tailWord_7470468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470468).length < 2 ^ (prefixWord ++ tailWord_7470468).sum := by decide
  have hdescent : baseEnd_7470468 < baseStart_7470468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470508 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_7470508 : Nat := 118140960795 + 7470508 * 2 ^ 59
def prefixEnd_7470508 : Nat := 4983230072969 + 3 ^ 40 * 7470508 * 2
def baseEnd_7470508 : Nat := 3835961337258362836793765

theorem tailTrace_7470508 : CollatzResearch.WordTrace tailWord_7470508 prefixEnd_7470508 3835961337258362836793765 := by
  unfold tailWord_7470508
  simp only [CollatzResearch.WordTrace]
  refine ⟨136235905609816426017506089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181647874146421901356674785 136235905609816426017506089)
  ·
    refine ⟨102176929207362319513129567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136235905609816426017506089 102176929207362319513129567)
    ·
      refine ⟨153265393811043479269694351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102176929207362319513129567 153265393811043479269694351)
      ·
        refine ⟨229898090716565218904541527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153265393811043479269694351 229898090716565218904541527)
        ·
          refine ⟨344847136074847828356812291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229898090716565218904541527 344847136074847828356812291)
          ·
            refine ⟨517270704112271742535218437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344847136074847828356812291 517270704112271742535218437)
            ·
              refine ⟨96988257021050951725353457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517270704112271742535218437 96988257021050951725353457)
              ·
                refine ⟨72741192765788213794015093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96988257021050951725353457 72741192765788213794015093)
                ·
                  refine ⟨6819486821792645043188915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72741192765788213794015093 6819486821792645043188915)
                  ·
                    refine ⟨10229230232688967564783373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6819486821792645043188915 10229230232688967564783373)
                    ·
                      refine ⟨3835961337258362836793765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10229230232688967564783373 3835961337258362836793765)
                      ·
                        rfl

theorem cell23_7470508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_7470508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470508 prefixEnd_7470508 := by exact prefixLift 7470508
  have htrace : WordTrace (prefixWord ++ tailWord_7470508) baseStart_7470508 baseEnd_7470508 := by
    simpa [prefixWord, tailWord_7470508, baseEnd_7470508] using wordTrace_append hprefix tailTrace_7470508
  have hstable : (prefixWord ++ tailWord_7470508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470508).length < 2 ^ (prefixWord ++ tailWord_7470508).sum := by decide
  have hdescent : baseEnd_7470508 < baseStart_7470508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470532 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 6]
def baseStart_7470532 : Nat := 118140960795 + 7470532 * 2 ^ 59
def prefixEnd_7470532 : Nat := 4983230072969 + 3 ^ 40 * 7470532 * 2
def baseEnd_7470532 : Nat := 426219295643785638099295

theorem tailTrace_7470532 : CollatzResearch.WordTrace tailWord_7470532 prefixEnd_7470532 426219295643785638099295 := by
  unfold tailWord_7470532
  simp only [CollatzResearch.WordTrace]
  refine ⟨136236343285772952066942925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181648457714363936089257233 136236343285772952066942925)
  ·
    refine ⟨51088628732164857025103597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136236343285772952066942925 51088628732164857025103597)
    ·
      refine ⟨19158235774561821384413849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51088628732164857025103597 19158235774561821384413849)
      ·
        refine ⟨14368676830921366038310387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19158235774561821384413849 14368676830921366038310387)
        ·
          refine ⟨21553015246382049057465581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14368676830921366038310387 21553015246382049057465581)
          ·
            refine ⟨8082380717393268396549593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21553015246382049057465581 8082380717393268396549593)
            ·
              refine ⟨6061785538044951297412195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082380717393268396549593 6061785538044951297412195)
              ·
                refine ⟨9092678307067426946118293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061785538044951297412195 9092678307067426946118293)
                ·
                  refine ⟨426219295643785638099295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9092678307067426946118293 426219295643785638099295)
                  ·
                    rfl

theorem cell23_7470532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_7470532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470532 prefixEnd_7470532 := by exact prefixLift 7470532
  have htrace : WordTrace (prefixWord ++ tailWord_7470532) baseStart_7470532 baseEnd_7470532 := by
    simpa [prefixWord, tailWord_7470532, baseEnd_7470532] using wordTrace_append hprefix tailTrace_7470532
  have hstable : (prefixWord ++ tailWord_7470532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470532).length < 2 ^ (prefixWord ++ tailWord_7470532).sum := by decide
  have hdescent : baseEnd_7470532 < baseStart_7470532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470551 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_7470551 : Nat := 118140960795 + 7470551 * 2 ^ 59
def prefixEnd_7470551 : Nat := 4983230072969 + 3 ^ 40 * 7470551 * 2
def baseEnd_7470551 : Nat := 3835983416926506168556067

theorem tailTrace_7470551 : CollatzResearch.WordTrace tailWord_7470551 prefixEnd_7470551 3835983416926506168556067 := by
  unfold tailWord_7470551
  simp only [CollatzResearch.WordTrace]
  refine ⟨272473379558477070378827507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181648919705651380252551671 272473379558477070378827507)
  ·
    refine ⟨408710069337715605568241261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272473379558477070378827507 408710069337715605568241261)
    ·
      refine ⟨153266276001643352088090473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408710069337715605568241261 153266276001643352088090473)
      ·
        refine ⟨114949707001232514066067855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153266276001643352088090473 114949707001232514066067855)
        ·
          refine ⟨172424560501848771099101783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114949707001232514066067855 172424560501848771099101783)
          ·
            refine ⟨258636840752773156648652675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172424560501848771099101783 258636840752773156648652675)
            ·
              refine ⟨387955261129159734972979013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258636840752773156648652675 387955261129159734972979013)
              ·
                refine ⟨72741611461717450307433565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387955261129159734972979013 72741611461717450307433565)
                ·
                  refine ⟨27278104298144043865287587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72741611461717450307433565 27278104298144043865287587)
                  ·
                    refine ⟨40917156447216065797931381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27278104298144043865287587 40917156447216065797931381)
                    ·
                      refine ⟨3835983416926506168556067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40917156447216065797931381 3835983416926506168556067)
                      ·
                        rfl

theorem cell23_7470551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_7470551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470551 prefixEnd_7470551 := by exact prefixLift 7470551
  have htrace : WordTrace (prefixWord ++ tailWord_7470551) baseStart_7470551 baseEnd_7470551 := by
    simpa [prefixWord, tailWord_7470551, baseEnd_7470551] using wordTrace_append hprefix tailTrace_7470551
  have hstable : (prefixWord ++ tailWord_7470551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470551).length < 2 ^ (prefixWord ++ tailWord_7470551).sum := by decide
  have hdescent : baseEnd_7470551 < baseStart_7470551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470601 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 2, 7]
def baseStart_7470601 : Nat := 118140960795 + 7470601 * 2 ^ 59
def prefixEnd_7470601 : Nat := 4983230072969 + 3 ^ 40 * 7470601 * 2
def baseEnd_7470601 : Nat := 1278669696986410324310279

theorem tailTrace_7470601 : CollatzResearch.WordTrace tailWord_7470601 prefixEnd_7470601 1278669696986410324310279 := by
  unfold tailWord_7470601
  simp only [CollatzResearch.WordTrace]
  refine ⟨272475203208295928918147657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181650135472197285945431771 272475203208295928918147657)
  ·
    refine ⟨204356402406221946688610743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272475203208295928918147657 204356402406221946688610743)
    ·
      refine ⟨306534603609332920032916115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204356402406221946688610743 306534603609332920032916115)
      ·
        refine ⟨459801905413999380049374173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306534603609332920032916115 459801905413999380049374173)
        ·
          refine ⟨172425714530249767518515315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459801905413999380049374173 172425714530249767518515315)
          ·
            refine ⟨258638571795374651277772973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172425714530249767518515315 258638571795374651277772973)
            ·
              refine ⟨96989464423265494229164865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258638571795374651277772973 96989464423265494229164865)
              ·
                refine ⟨72742098317449120671873649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96989464423265494229164865 72742098317449120671873649)
                ·
                  refine ⟨54556573738086840503905237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72742098317449120671873649 54556573738086840503905237)
                  ·
                    refine ⟨1278669696986410324310279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54556573738086840503905237 1278669696986410324310279)
                    ·
                      rfl

theorem cell23_7470601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_7470601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470601 prefixEnd_7470601 := by exact prefixLift 7470601
  have htrace : WordTrace (prefixWord ++ tailWord_7470601) baseStart_7470601 baseEnd_7470601 := by
    simpa [prefixWord, tailWord_7470601, baseEnd_7470601] using wordTrace_append hprefix tailTrace_7470601
  have hstable : (prefixWord ++ tailWord_7470601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470601).length < 2 ^ (prefixWord ++ tailWord_7470601).sum := by decide
  have hdescent : baseEnd_7470601 < baseStart_7470601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470616 : List Nat := [2, 1, 2, 3, 4, 1, 2, 3, 1, 2, 2]
def baseStart_7470616 : Nat := 118140960795 + 7470616 * 2 ^ 59
def prefixEnd_7470616 : Nat := 4983230072969 + 3 ^ 40 * 7470616 * 2
def baseEnd_7470616 : Nat := 3836016793169048414243269

theorem tailTrace_7470616 : CollatzResearch.WordTrace tailWord_7470616 prefixEnd_7470616 3836016793169048414243269 := by
  unfold tailWord_7470616
  simp only [CollatzResearch.WordTrace]
  refine ⟨136237875151620793239971851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181650500202161057653295801 136237875151620793239971851)
  ·
    refine ⟨204356812727431189859957777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136237875151620793239971851 204356812727431189859957777)
    ·
      refine ⟨153267609545573392394968333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204356812727431189859957777 153267609545573392394968333)
      ·
        refine ⟨57475353579590022148113125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153267609545573392394968333 57475353579590022148113125)
        ·
          refine ⟨10776628796173129152771211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57475353579590022148113125 10776628796173129152771211)
          ·
            refine ⟨16164943194259693729156817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776628796173129152771211 16164943194259693729156817)
            ·
              refine ⟨12123707395694770296867613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16164943194259693729156817 12123707395694770296867613)
              ·
                refine ⟨4546390273385538861325355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12123707395694770296867613 4546390273385538861325355)
                ·
                  refine ⟨6819585410078308291988033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546390273385538861325355 6819585410078308291988033)
                  ·
                    refine ⟨5114689057558731218991025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819585410078308291988033 5114689057558731218991025)
                    ·
                      refine ⟨3836016793169048414243269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114689057558731218991025 3836016793169048414243269)
                      ·
                        rfl

theorem cell23_7470616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_7470616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470616 prefixEnd_7470616 := by exact prefixLift 7470616
  have htrace : WordTrace (prefixWord ++ tailWord_7470616) baseStart_7470616 baseEnd_7470616 := by
    simpa [prefixWord, tailWord_7470616, baseEnd_7470616] using wordTrace_append hprefix tailTrace_7470616
  have hstable : (prefixWord ++ tailWord_7470616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470616).length < 2 ^ (prefixWord ++ tailWord_7470616).sum := by decide
  have hdescent : baseEnd_7470616 < baseStart_7470616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470648 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 2, 6]
def baseStart_7470648 : Nat := 118140960795 + 7470648 * 2 ^ 59
def prefixEnd_7470648 : Nat := 4983230072969 + 3 ^ 40 * 7470648 * 2
def baseEnd_7470648 : Nat := 1278677741516664096347707

theorem tailTrace_7470648 : CollatzResearch.WordTrace tailWord_7470648 prefixEnd_7470648 1278677741516664096347707 := by
  unfold tailWord_7470648
  simp only [CollatzResearch.WordTrace]
  refine ⟨136238458719562827972554299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181651278292750437296739065 136238458719562827972554299)
  ·
    refine ⟨204357688079344241958831449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136238458719562827972554299 204357688079344241958831449)
    ·
      refine ⟨153268266059508181469123587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204357688079344241958831449 153268266059508181469123587)
      ·
        refine ⟨229902399089262272203685381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153268266059508181469123587 229902399089262272203685381)
        ·
          refine ⟨43106699829236676038191009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229902399089262272203685381 43106699829236676038191009)
          ·
            refine ⟨32330024871927507028643257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43106699829236676038191009 32330024871927507028643257)
            ·
              refine ⟨24247518653945630271482443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32330024871927507028643257 24247518653945630271482443)
              ·
                refine ⟨36371277980918445407223665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24247518653945630271482443 36371277980918445407223665)
                ·
                  refine ⟨27278458485688834055417749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36371277980918445407223665 27278458485688834055417749)
                  ·
                    refine ⟨1278677741516664096347707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27278458485688834055417749 1278677741516664096347707)
                    ·
                      rfl

theorem cell23_7470648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_7470648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470648 prefixEnd_7470648 := by exact prefixLift 7470648
  have htrace : WordTrace (prefixWord ++ tailWord_7470648) baseStart_7470648 baseEnd_7470648 := by
    simpa [prefixWord, tailWord_7470648, baseEnd_7470648] using wordTrace_append hprefix tailTrace_7470648
  have hstable : (prefixWord ++ tailWord_7470648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470648).length < 2 ^ (prefixWord ++ tailWord_7470648).sum := by decide
  have hdescent : baseEnd_7470648 < baseStart_7470648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470649 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7470649 : Nat := 118140960795 + 7470649 * 2 ^ 59
def prefixEnd_7470649 : Nat := 4983230072969 + 3 ^ 40 * 7470649 * 2
def baseEnd_7470649 : Nat := 3836033738030646785130617

theorem tailTrace_7470649 : CollatzResearch.WordTrace tailWord_7470649 prefixEnd_7470649 3836033738030646785130617 := by
  unfold tailWord_7470649
  simp only [CollatzResearch.WordTrace]
  refine ⟨272476953912122033115895001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181651302608081355410596667 272476953912122033115895001)
  ·
    refine ⟨204357715434091524836921251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272476953912122033115895001 204357715434091524836921251)
    ·
      refine ⟨306536573151137287255381877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204357715434091524836921251 306536573151137287255381877)
      ·
        refine ⟨28737803732919120680192051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306536573151137287255381877 28737803732919120680192051)
        ·
          refine ⟨43106705599378681020288077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28737803732919120680192051 43106705599378681020288077)
          ·
            refine ⟨16165014599767005382608029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43106705599378681020288077 16165014599767005382608029)
            ·
              refine ⟨6061880474912627018478011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16165014599767005382608029 6061880474912627018478011)
              ·
                refine ⟨9092820712368940527717017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061880474912627018478011 9092820712368940527717017)
                ·
                  refine ⟨6819615534276705395787763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9092820712368940527717017 6819615534276705395787763)
                  ·
                    refine ⟨10229423301415058093681645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6819615534276705395787763 10229423301415058093681645)
                    ·
                      refine ⟨3836033738030646785130617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10229423301415058093681645 3836033738030646785130617)
                      ·
                        rfl

theorem cell23_7470649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7470649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470649 prefixEnd_7470649 := by exact prefixLift 7470649
  have htrace : WordTrace (prefixWord ++ tailWord_7470649) baseStart_7470649 baseEnd_7470649 := by
    simpa [prefixWord, tailWord_7470649, baseEnd_7470649] using wordTrace_append hprefix tailTrace_7470649
  have hstable : (prefixWord ++ tailWord_7470649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470649).length < 2 ^ (prefixWord ++ tailWord_7470649).sum := by decide
  have hdescent : baseEnd_7470649 < baseStart_7470649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470695 : List Nat := [1, 1, 5, 1, 1, 1, 2, 6, 5]
def baseStart_7470695 : Nat := 118140960795 + 7470695 * 2 ^ 59
def prefixEnd_7470695 : Nat := 4983230072969 + 3 ^ 40 * 7470695 * 2
def baseEnd_7470695 : Nat := 426228595348972622795045

theorem tailTrace_7470695 : CollatzResearch.WordTrace tailWord_7470695 prefixEnd_7470695 426228595348972622795045 := by
  unfold tailWord_7470695
  simp only [CollatzResearch.WordTrace]
  refine ⟨272478631669955382972069539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181652421113303588648046359 272478631669955382972069539)
  ·
    refine ⟨408717947504933074458104309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272478631669955382972069539 408717947504933074458104309)
    ·
      refine ⟨38317307578587475730447279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408717947504933074458104309 38317307578587475730447279)
      ·
        refine ⟨57475961367881213595670919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38317307578587475730447279 57475961367881213595670919)
        ·
          refine ⟨86213942051821820393506379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57475961367881213595670919 86213942051821820393506379)
          ·
            refine ⟨129320913077732730590259569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86213942051821820393506379 129320913077732730590259569)
            ·
              refine ⟨96990684808299547942694677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129320913077732730590259569 96990684808299547942694677)
              ·
                refine ⟨4546438350389041309813813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96990684808299547942694677 4546438350389041309813813)
                ·
                  refine ⟨426228595348972622795045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4546438350389041309813813 426228595348972622795045)
                  ·
                    rfl

theorem cell23_7470695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 5].length) (baseStart_7470695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470695 prefixEnd_7470695 := by exact prefixLift 7470695
  have htrace : WordTrace (prefixWord ++ tailWord_7470695) baseStart_7470695 baseEnd_7470695 := by
    simpa [prefixWord, tailWord_7470695, baseEnd_7470695] using wordTrace_append hprefix tailTrace_7470695
  have hstable : (prefixWord ++ tailWord_7470695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470695).length < 2 ^ (prefixWord ++ tailWord_7470695).sum := by decide
  have hdescent : baseEnd_7470695 < baseStart_7470695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470706 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_7470706 : Nat := 118140960795 + 7470706 * 2 ^ 59
def prefixEnd_7470706 : Nat := 4983230072969 + 3 ^ 40 * 7470706 * 2
def baseEnd_7470706 : Nat := 3836063006427953062117855

theorem tailTrace_7470706 : CollatzResearch.WordTrace tailWord_7470706 prefixEnd_7470706 3836063006427953062117855 := by
  unfold tailWord_7470706
  simp only [CollatzResearch.WordTrace]
  refine ⟨68119758218228882962679993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181652688581943687900479981 68119758218228882962679993)
  ·
    refine ⟨51089818663671662222009995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68119758218228882962679993 51089818663671662222009995)
    ·
      refine ⟨76634727995507493333014993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51089818663671662222009995 76634727995507493333014993)
      ·
        refine ⟨57476045996630619999761245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76634727995507493333014993 57476045996630619999761245)
        ·
          refine ⟨21553517248736482499910467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57476045996630619999761245 21553517248736482499910467)
          ·
            refine ⟨32330275873104723749865701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21553517248736482499910467 32330275873104723749865701)
            ·
              refine ⟨6061926726207135703099819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32330275873104723749865701 6061926726207135703099819)
              ·
                refine ⟨9092890089310703554649729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6061926726207135703099819 9092890089310703554649729)
                ·
                  refine ⟨6819667566983027665987297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9092890089310703554649729 6819667566983027665987297)
                  ·
                    refine ⟨5114750675237270749490473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819667566983027665987297 5114750675237270749490473)
                    ·
                      refine ⟨3836063006427953062117855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114750675237270749490473 3836063006427953062117855)
                      ·
                        rfl

theorem cell23_7470706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_7470706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470706 prefixEnd_7470706 := by exact prefixLift 7470706
  have htrace : WordTrace (prefixWord ++ tailWord_7470706) baseStart_7470706 baseEnd_7470706 := by
    simpa [prefixWord, tailWord_7470706, baseEnd_7470706] using wordTrace_append hprefix tailTrace_7470706
  have hstable : (prefixWord ++ tailWord_7470706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470706).length < 2 ^ (prefixWord ++ tailWord_7470706).sum := by decide
  have hdescent : baseEnd_7470706 < baseStart_7470706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470725 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_7470725 : Nat := 118140960795 + 7470725 * 2 ^ 59
def prefixEnd_7470725 : Nat := 4983230072969 + 3 ^ 40 * 7470725 * 2
def baseEnd_7470725 : Nat := 1278690920853462829260089

theorem tailTrace_7470725 : CollatzResearch.WordTrace tailWord_7470725 prefixEnd_7470725 1278690920853462829260089 := by
  unfold tailWord_7470725
  simp only [CollatzResearch.WordTrace]
  refine ⟨272479725859846698095661629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181653150573231132063774419 272479725859846698095661629)
  ·
    refine ⟨102179897197442511785873111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272479725859846698095661629 102179897197442511785873111)
    ·
      refine ⟨153269845796163767678809667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102179897197442511785873111 153269845796163767678809667)
      ·
        refine ⟨229904768694245651518214501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153269845796163767678809667 229904768694245651518214501)
        ·
          refine ⟨43107144130171059659665219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229904768694245651518214501 43107144130171059659665219)
          ·
            refine ⟨64660716195256589489497829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43107144130171059659665219 64660716195256589489497829)
            ·
              refine ⟨12123884286610610529280843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64660716195256589489497829 12123884286610610529280843)
              ·
                refine ⟨18185826429915915793921265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12123884286610610529280843 18185826429915915793921265)
                ·
                  refine ⟨13639369822436936845440949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18185826429915915793921265 13639369822436936845440949)
                  ·
                    refine ⟨1278690920853462829260089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13639369822436936845440949 1278690920853462829260089)
                    ·
                      rfl

theorem cell23_7470725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_7470725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470725 prefixEnd_7470725 := by exact prefixLift 7470725
  have htrace : WordTrace (prefixWord ++ tailWord_7470725) baseStart_7470725 baseEnd_7470725 := by
    simpa [prefixWord, tailWord_7470725, baseEnd_7470725] using wordTrace_append hprefix tailTrace_7470725
  have hstable : (prefixWord ++ tailWord_7470725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470725).length < 2 ^ (prefixWord ++ tailWord_7470725).sum := by decide
  have hdescent : baseEnd_7470725 < baseStart_7470725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470755 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 3, 4]
def baseStart_7470755 : Nat := 118140960795 + 7470755 * 2 ^ 59
def prefixEnd_7470755 : Nat := 4983230072969 + 3 ^ 40 * 7470755 * 2
def baseEnd_7470755 : Nat := 1278696055660007790135043

theorem tailTrace_7470755 : CollatzResearch.WordTrace tailWord_7470755 prefixEnd_7470755 1278696055660007790135043 := by
  unfold tailWord_7470755
  simp only [CollatzResearch.WordTrace]
  refine ⟨272480820049738013219253719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181653880033158675479502479 272480820049738013219253719)
  ·
    refine ⟨408721230074607019828880579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272480820049738013219253719 408721230074607019828880579)
    ·
      refine ⟨613081845111910529743320869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408721230074607019828880579 613081845111910529743320869)
      ·
        refine ⟨114952845958483224326872663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 613081845111910529743320869 114952845958483224326872663)
        ·
          refine ⟨172429268937724836490308995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114952845958483224326872663 172429268937724836490308995)
          ·
            refine ⟨258643903406587254735463493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172429268937724836490308995 258643903406587254735463493)
            ·
              refine ⟨48495731888735110262899405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258643903406587254735463493 48495731888735110262899405)
              ·
                refine ⟨18185899458275666348587277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48495731888735110262899405 18185899458275666348587277)
                ·
                  refine ⟨6819712296853374880720229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18185899458275666348587277 6819712296853374880720229)
                  ·
                    refine ⟨1278696055660007790135043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6819712296853374880720229 1278696055660007790135043)
                    ·
                      rfl

theorem cell23_7470755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 4].length) (baseStart_7470755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470755 prefixEnd_7470755 := by exact prefixLift 7470755
  have htrace : WordTrace (prefixWord ++ tailWord_7470755) baseStart_7470755 baseEnd_7470755 := by
    simpa [prefixWord, tailWord_7470755, baseEnd_7470755] using wordTrace_append hprefix tailTrace_7470755
  have hstable : (prefixWord ++ tailWord_7470755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470755).length < 2 ^ (prefixWord ++ tailWord_7470755).sum := by decide
  have hdescent : baseEnd_7470755 < baseStart_7470755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470782 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_7470782 : Nat := 118140960795 + 7470782 * 2 ^ 59
def prefixEnd_7470782 : Nat := 4983230072969 + 3 ^ 40 * 7470782 * 2
def baseEnd_7470782 : Nat := 3836102030957694764767505

theorem tailTrace_7470782 : CollatzResearch.WordTrace tailWord_7470782 prefixEnd_7470782 3836102030957694764767505 := by
  unfold tailWord_7470782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34060225602580024603810825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181654536547093464553657733 34060225602580024603810825)
  ·
    refine ⟨25545169201935018452858119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34060225602580024603810825 25545169201935018452858119)
    ·
      refine ⟨38317753802902527679287179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25545169201935018452858119 38317753802902527679287179)
      ·
        refine ⟨57476630704353791518930769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38317753802902527679287179 57476630704353791518930769)
        ·
          refine ⟨43107473028265343639198077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57476630704353791518930769 43107473028265343639198077)
          ·
            refine ⟨16165302385599503864699279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43107473028265343639198077 16165302385599503864699279)
            ·
              refine ⟨24247953578399255797048919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16165302385599503864699279 24247953578399255797048919)
              ·
                refine ⟨36371930367598883695573379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24247953578399255797048919 36371930367598883695573379)
                ·
                  refine ⟨54557895551398325543360069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36371930367598883695573379 54557895551398325543360069)
                  ·
                    refine ⟨10229605415887186039380013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54557895551398325543360069 10229605415887186039380013)
                    ·
                      refine ⟨3836102030957694764767505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10229605415887186039380013 3836102030957694764767505)
                      ·
                        rfl

theorem cell23_7470782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_7470782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470782 prefixEnd_7470782 := by exact prefixLift 7470782
  have htrace : WordTrace (prefixWord ++ tailWord_7470782) baseStart_7470782 baseEnd_7470782 := by
    simpa [prefixWord, tailWord_7470782, baseEnd_7470782] using wordTrace_append hprefix tailTrace_7470782
  have hstable : (prefixWord ++ tailWord_7470782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470782).length < 2 ^ (prefixWord ++ tailWord_7470782).sum := by decide
  have hdescent : baseEnd_7470782 < baseStart_7470782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470802 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 6]
def baseStart_7470802 : Nat := 118140960795 + 7470802 * 2 ^ 59
def prefixEnd_7470802 : Nat := 4983230072969 + 3 ^ 40 * 7470802 * 2
def baseEnd_7470802 : Nat := 426234700063420520724157

theorem tailTrace_7470802 : CollatzResearch.WordTrace tailWord_7470802 prefixEnd_7470802 426234700063420520724157 := by
  unfold tailWord_7470802
  simp only [CollatzResearch.WordTrace]
  refine ⟨68120633570141935061553665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181655022853711826830809773 68120633570141935061553665)
  ·
    refine ⟨51090475177606451296165249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68120633570141935061553665 51090475177606451296165249)
    ·
      refine ⟨38317856383204838472123937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51090475177606451296165249 38317856383204838472123937)
      ·
        refine ⟨28738392287403628854092953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38317856383204838472123937 28738392287403628854092953)
        ·
          refine ⟨21553794215552721640569715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28738392287403628854092953 21553794215552721640569715)
          ·
            refine ⟨32330691323329082460854573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21553794215552721640569715 32330691323329082460854573)
            ·
              refine ⟨12124009246248405922820465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32330691323329082460854573 12124009246248405922820465)
              ·
                refine ⟨9093006934686304442115349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12124009246248405922820465 9093006934686304442115349)
                ·
                  refine ⟨426234700063420520724157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9093006934686304442115349 426234700063420520724157)
                  ·
                    rfl

theorem cell23_7470802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_7470802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470802 prefixEnd_7470802 := by exact prefixLift 7470802
  have htrace : WordTrace (prefixWord ++ tailWord_7470802) baseStart_7470802 baseEnd_7470802 := by
    simpa [prefixWord, tailWord_7470802, baseEnd_7470802] using wordTrace_append hprefix tailTrace_7470802
  have hstable : (prefixWord ++ tailWord_7470802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470802).length < 2 ^ (prefixWord ++ tailWord_7470802).sum := by decide
  have hdescent : baseEnd_7470802 < baseStart_7470802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470819 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 6]
def baseStart_7470819 : Nat := 118140960795 + 7470819 * 2 ^ 59
def prefixEnd_7470819 : Nat := 4983230072969 + 3 ^ 40 * 7470819 * 2
def baseEnd_7470819 : Nat := 426235669971323457778315

theorem tailTrace_7470819 : CollatzResearch.WordTrace tailWord_7470819 prefixEnd_7470819 426235669971323457778315 := by
  unfold tailWord_7470819
  simp only [CollatzResearch.WordTrace]
  refine ⟨272483154321506152149583511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181655436214337434766389007 272483154321506152149583511)
  ·
    refine ⟨408724731482259228224375267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272483154321506152149583511 408724731482259228224375267)
    ·
      refine ⟨613087097223388842336562901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408724731482259228224375267 613087097223388842336562901)
      ·
        refine ⟨14369228841173175992263193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 613087097223388842336562901 14369228841173175992263193)
        ·
          refine ⟨10776921630879881994197395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14369228841173175992263193 10776921630879881994197395)
          ·
            refine ⟨16165382446319822991296093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776921630879881994197395 16165382446319822991296093)
            ·
              refine ⟨6062018417369933621736035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16165382446319822991296093 6062018417369933621736035)
              ·
                refine ⟨9093027626054900432604053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062018417369933621736035 9093027626054900432604053)
                ·
                  refine ⟨426235669971323457778315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9093027626054900432604053 426235669971323457778315)
                  ·
                    rfl

theorem cell23_7470819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 6].length) (baseStart_7470819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470819 prefixEnd_7470819 := by exact prefixLift 7470819
  have htrace : WordTrace (prefixWord ++ tailWord_7470819) baseStart_7470819 baseEnd_7470819 := by
    simpa [prefixWord, tailWord_7470819, baseEnd_7470819] using wordTrace_append hprefix tailTrace_7470819
  have hstable : (prefixWord ++ tailWord_7470819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470819).length < 2 ^ (prefixWord ++ tailWord_7470819).sum := by decide
  have hdescent : baseEnd_7470819 < baseStart_7470819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470829 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7470829 : Nat := 118140960795 + 7470829 * 2 ^ 59
def prefixEnd_7470829 : Nat := 4983230072969 + 3 ^ 40 * 7470829 * 2
def baseEnd_7470829 : Nat := 3836126164548456080879789

theorem tailTrace_7470829 : CollatzResearch.WordTrace tailWord_7470829 prefixEnd_7470829 3836126164548456080879789 := by
  unfold tailWord_7470829
  simp only [CollatzResearch.WordTrace]
  refine ⟨272483519051469923857447541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181655679367646615904965027 272483519051469923857447541)
  ·
    refine ⟨25545329911075305361635707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272483519051469923857447541 25545329911075305361635707)
    ·
      refine ⟨38317994866612958042453561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25545329911075305361635707 38317994866612958042453561)
      ·
        refine ⟨28738496149959718531840171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38317994866612958042453561 28738496149959718531840171)
        ·
          refine ⟨43107744224939577797760257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28738496149959718531840171 43107744224939577797760257)
          ·
            refine ⟨32330808168704683348320193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43107744224939577797760257 32330808168704683348320193)
            ·
              refine ⟨24248106126528512511240145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32330808168704683348320193 24248106126528512511240145)
              ·
                refine ⟨18186079594896384383430109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24248106126528512511240145 18186079594896384383430109)
                ·
                  refine ⟨6819779848086144143786291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18186079594896384383430109 6819779848086144143786291)
                  ·
                    refine ⟨10229669772129216215679437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6819779848086144143786291 10229669772129216215679437)
                    ·
                      refine ⟨3836126164548456080879789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10229669772129216215679437 3836126164548456080879789)
                      ·
                        rfl

theorem cell23_7470829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7470829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470829 prefixEnd_7470829 := by exact prefixLift 7470829
  have htrace : WordTrace (prefixWord ++ tailWord_7470829) baseStart_7470829 baseEnd_7470829 := by
    simpa [prefixWord, tailWord_7470829, baseEnd_7470829] using wordTrace_append hprefix tailTrace_7470829
  have hstable : (prefixWord ++ tailWord_7470829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470829).length < 2 ^ (prefixWord ++ tailWord_7470829).sum := by decide
  have hdescent : baseEnd_7470829 < baseStart_7470829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470835 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 4]
def baseStart_7470835 : Nat := 118140960795 + 7470835 * 2 ^ 59
def prefixEnd_7470835 : Nat := 4983230072969 + 3 ^ 40 * 7470835 * 2
def baseEnd_7470835 : Nat := 3836129245432383057404761

theorem tailTrace_7470835 : CollatzResearch.WordTrace tailWord_7470835 prefixEnd_7470835 3836129245432383057404761 := by
  unfold tailWord_7470835
  simp only [CollatzResearch.WordTrace]
  refine ⟨272483737889448186882165959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181655825259632124588110639 272483737889448186882165959)
  ·
    refine ⟨408725606834172280323248939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272483737889448186882165959 408725606834172280323248939)
    ·
      refine ⟨613088410251258420484873409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408725606834172280323248939 613088410251258420484873409)
      ·
        refine ⟨459816307688443815363655057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613088410251258420484873409 459816307688443815363655057)
        ·
          refine ⟨344862230766332861522741293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459816307688443815363655057 344862230766332861522741293)
          ·
            refine ⟨129323336537374823071027985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344862230766332861522741293 129323336537374823071027985)
            ·
              refine ⟨96992502403031117303270989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129323336537374823071027985 96992502403031117303270989)
              ·
                refine ⟨36372188401136668988726621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96992502403031117303270989 36372188401136668988726621)
                ·
                  refine ⟨13639570650426250870772483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36372188401136668988726621 13639570650426250870772483)
                  ·
                    refine ⟨20459355975639376306158725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13639570650426250870772483 20459355975639376306158725)
                    ·
                      refine ⟨3836129245432383057404761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20459355975639376306158725 3836129245432383057404761)
                      ·
                        rfl

theorem cell23_7470835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_7470835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470835 prefixEnd_7470835 := by exact prefixLift 7470835
  have htrace : WordTrace (prefixWord ++ tailWord_7470835) baseStart_7470835 baseEnd_7470835 := by
    simpa [prefixWord, tailWord_7470835, baseEnd_7470835] using wordTrace_append hprefix tailTrace_7470835
  have hstable : (prefixWord ++ tailWord_7470835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470835).length < 2 ^ (prefixWord ++ tailWord_7470835).sum := by decide
  have hdescent : baseEnd_7470835 < baseStart_7470835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470862 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_7470862 : Nat := 118140960795 + 7470862 * 2 ^ 59
def prefixEnd_7470862 : Nat := 4983230072969 + 3 ^ 40 * 7470862 * 2
def baseEnd_7470862 : Nat := 1278714369803351483922379

theorem tailTrace_7470862 : CollatzResearch.WordTrace tailWord_7470862 prefixEnd_7470862 1278714369803351483922379 := by
  unfold tailWord_7470862
  simp only [CollatzResearch.WordTrace]
  refine ⟨34060590332543796311674855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181656481773566913662265893 34060590332543796311674855)
  ·
    refine ⟨51090885498815694467512283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34060590332543796311674855 51090885498815694467512283)
    ·
      refine ⟨76636328248223541701268425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51090885498815694467512283 76636328248223541701268425)
      ·
        refine ⟨57477246186167656275951319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76636328248223541701268425 57477246186167656275951319)
        ·
          refine ⟨86215869279251484413926979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57477246186167656275951319 86215869279251484413926979)
          ·
            refine ⟨129323803918877226620890469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86215869279251484413926979 129323803918877226620890469)
            ·
              refine ⟨24248213234789479991416963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129323803918877226620890469 24248213234789479991416963)
              ·
                refine ⟨36372319852184219987125445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24248213234789479991416963 36372319852184219987125445)
                ·
                  refine ⟨6819809972284541247586021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36372319852184219987125445 6819809972284541247586021)
                  ·
                    refine ⟨1278714369803351483922379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6819809972284541247586021 1278714369803351483922379)
                    ·
                      rfl

theorem cell23_7470862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_7470862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470862 prefixEnd_7470862 := by exact prefixLift 7470862
  have htrace : WordTrace (prefixWord ++ tailWord_7470862) baseStart_7470862 baseEnd_7470862 := by
    simpa [prefixWord, tailWord_7470862, baseEnd_7470862] using wordTrace_append hprefix tailTrace_7470862
  have hstable : (prefixWord ++ tailWord_7470862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470862).length < 2 ^ (prefixWord ++ tailWord_7470862).sum := by decide
  have hdescent : baseEnd_7470862 < baseStart_7470862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470882 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_7470882 : Nat := 118140960795 + 7470882 * 2 ^ 59
def prefixEnd_7470882 : Nat := 4983230072969 + 3 ^ 40 * 7470882 * 2
def baseEnd_7470882 : Nat := 3836153379023144373517045

theorem tailTrace_7470882 : CollatzResearch.WordTrace tailWord_7470882 prefixEnd_7470882 3836153379023144373517045 := by
  unfold tailWord_7470882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68121363030069478477281725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181656968080185275939417933 68121363030069478477281725)
  ·
    refine ⟨25545511136276054428980647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68121363030069478477281725 25545511136276054428980647)
    ·
      refine ⟨38318266704414081643470971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25545511136276054428980647 38318266704414081643470971)
      ·
        refine ⟨57477400056621122465206457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38318266704414081643470971 57477400056621122465206457)
        ·
          refine ⟨43108050042465841848904843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57477400056621122465206457 43108050042465841848904843)
          ·
            refine ⟨64662075063698762773357265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43108050042465841848904843 64662075063698762773357265)
            ·
              refine ⟨48496556297774072080017949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64662075063698762773357265 48496556297774072080017949)
              ·
                refine ⟨18186208611665277030006731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48496556297774072080017949 18186208611665277030006731)
                ·
                  refine ⟨27279312917497915545010097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18186208611665277030006731 27279312917497915545010097)
                  ·
                    refine ⟨20459484688123436658757573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27279312917497915545010097 20459484688123436658757573)
                    ·
                      refine ⟨3836153379023144373517045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20459484688123436658757573 3836153379023144373517045)
                      ·
                        rfl

theorem cell23_7470882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_7470882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470882 prefixEnd_7470882 := by exact prefixLift 7470882
  have htrace : WordTrace (prefixWord ++ tailWord_7470882) baseStart_7470882 baseEnd_7470882 := by
    simpa [prefixWord, tailWord_7470882, baseEnd_7470882] using wordTrace_append hprefix tailTrace_7470882
  have hstable : (prefixWord ++ tailWord_7470882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470882).length < 2 ^ (prefixWord ++ tailWord_7470882).sum := by decide
  have hdescent : baseEnd_7470882 < baseStart_7470882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470906 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3]
def baseStart_7470906 : Nat := 118140960795 + 7470906 * 2 ^ 59
def prefixEnd_7470906 : Nat := 4983230072969 + 3 ^ 40 * 7470906 * 2
def baseEnd_7470906 : Nat := 3836165702558852279616935

theorem tailTrace_7470906 : CollatzResearch.WordTrace tailWord_7470906 prefixEnd_7470906 3836165702558852279616935 := by
  unfold tailWord_7470906
  simp only [CollatzResearch.WordTrace]
  refine ⟨68121581868047741502000143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181657551648127310672000381 68121581868047741502000143)
  ·
    refine ⟨102182372802071612253000215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68121581868047741502000143 102182372802071612253000215)
    ·
      refine ⟨153273559203107418379500323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102182372802071612253000215 153273559203107418379500323)
      ·
        refine ⟨229910338804661127569250485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153273559203107418379500323 229910338804661127569250485)
        ·
          refine ⟨21554094262936980709617233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229910338804661127569250485 21554094262936980709617233)
          ·
            refine ⟨16165570697202735532212925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21554094262936980709617233 16165570697202735532212925)
            ·
              refine ⟨6062089011451025824579847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16165570697202735532212925 6062089011451025824579847)
              ·
                refine ⟨9093133517176538736869771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062089011451025824579847 9093133517176538736869771)
                ·
                  refine ⟨13639700275764808105304657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9093133517176538736869771 13639700275764808105304657)
                  ·
                    refine ⟨10229775206823606078978493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13639700275764808105304657 10229775206823606078978493)
                    ·
                      refine ⟨3836165702558852279616935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10229775206823606078978493 3836165702558852279616935)
                      ·
                        rfl

theorem cell23_7470906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_7470906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470906 prefixEnd_7470906 := by exact prefixLift 7470906
  have htrace : WordTrace (prefixWord ++ tailWord_7470906) baseStart_7470906 baseEnd_7470906 := by
    simpa [prefixWord, tailWord_7470906, baseEnd_7470906] using wordTrace_append hprefix tailTrace_7470906
  have hstable : (prefixWord ++ tailWord_7470906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470906).length < 2 ^ (prefixWord ++ tailWord_7470906).sum := by decide
  have hdescent : baseEnd_7470906 < baseStart_7470906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470919 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_7470919 : Nat := 118140960795 + 7470919 * 2 ^ 59
def prefixEnd_7470919 : Nat := 4983230072969 + 3 ^ 40 * 7470919 * 2
def baseEnd_7470919 : Nat := 3836172377807360728754375

theorem tailTrace_7470919 : CollatzResearch.WordTrace tailWord_7470919 prefixEnd_7470919 3836172377807360728754375 := by
  unfold tailWord_7470919
  simp only [CollatzResearch.WordTrace]
  refine ⟨272486801621143869228223811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181657867747429246152149207 272486801621143869228223811)
  ·
    refine ⟨408730202431715803842335717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272486801621143869228223811 408730202431715803842335717)
    ·
      refine ⟨76636912955946713220437947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408730202431715803842335717 76636912955946713220437947)
      ·
        refine ⟨114955369433920069830656921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76636912955946713220437947 114955369433920069830656921)
        ·
          refine ⟨86216527075440052372992691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114955369433920069830656921 86216527075440052372992691)
          ·
            refine ⟨129324790613160078559489037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86216527075440052372992691 129324790613160078559489037)
            ·
              refine ⟨48496796479935029459808389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129324790613160078559489037 48496796479935029459808389)
              ·
                refine ⟨9093149339987818023714073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48496796479935029459808389 9093149339987818023714073)
                ·
                  refine ⟨6819862004990863517785555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9093149339987818023714073 6819862004990863517785555)
                  ·
                    refine ⟨10229793007486295276678333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6819862004990863517785555 10229793007486295276678333)
                    ·
                      refine ⟨3836172377807360728754375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10229793007486295276678333 3836172377807360728754375)
                      ·
                        rfl

theorem cell23_7470919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_7470919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470919 prefixEnd_7470919 := by exact prefixLift 7470919
  have htrace : WordTrace (prefixWord ++ tailWord_7470919) baseStart_7470919 baseEnd_7470919 := by
    simpa [prefixWord, tailWord_7470919, baseEnd_7470919] using wordTrace_append hprefix tailTrace_7470919
  have hstable : (prefixWord ++ tailWord_7470919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470919).length < 2 ^ (prefixWord ++ tailWord_7470919).sum := by decide
  have hdescent : baseEnd_7470919 < baseStart_7470919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470920 : List Nat := [2, 1, 3, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_7470920 : Nat := 118140960795 + 7470920 * 2 ^ 59
def prefixEnd_7470920 : Nat := 4983230072969 + 3 ^ 40 * 7470920 * 2
def baseEnd_7470920 : Nat := 3836172891288015224841871

theorem tailTrace_7470920 : CollatzResearch.WordTrace tailWord_7470920 prefixEnd_7470920 3836172891288015224841871 := by
  unfold tailWord_7470920
  simp only [CollatzResearch.WordTrace]
  refine ⟨136243419047070123199505107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181657892062760164266006809 136243419047070123199505107)
  ·
    refine ⟨204365128570605184799257661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136243419047070123199505107 204365128570605184799257661)
    ·
      refine ⟨76636923213976944299721623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204365128570605184799257661 76636923213976944299721623)
      ·
        refine ⟨114955384820965416449582435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76636923213976944299721623 114955384820965416449582435)
        ·
          refine ⟨172433077231448124674373653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114955384820965416449582435 172433077231448124674373653)
          ·
            refine ⟨8082800495224130844111265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172433077231448124674373653 8082800495224130844111265)
            ·
              refine ⟨6062100371418098133083449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8082800495224130844111265 6062100371418098133083449)
              ·
                refine ⟨4546575278563573599812587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6062100371418098133083449 4546575278563573599812587)
                ·
                  refine ⟨6819862917845360399718881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546575278563573599812587 6819862917845360399718881)
                  ·
                    refine ⟨5114897188384020299789161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6819862917845360399718881 5114897188384020299789161)
                    ·
                      refine ⟨3836172891288015224841871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114897188384020299789161 3836172891288015224841871)
                      ·
                        rfl

theorem cell23_7470920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_7470920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470920 prefixEnd_7470920 := by exact prefixLift 7470920
  have htrace : WordTrace (prefixWord ++ tailWord_7470920) baseStart_7470920 baseEnd_7470920 := by
    simpa [prefixWord, tailWord_7470920, baseEnd_7470920] using wordTrace_append hprefix tailTrace_7470920
  have hstable : (prefixWord ++ tailWord_7470920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470920).length < 2 ^ (prefixWord ++ tailWord_7470920).sum := by decide
  have hdescent : baseEnd_7470920 < baseStart_7470920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470929 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 3, 3, 2]
def baseStart_7470929 : Nat := 118140960795 + 7470929 * 2 ^ 59
def prefixEnd_7470929 : Nat := 4983230072969 + 3 ^ 40 * 7470929 * 2
def baseEnd_7470929 : Nat := 3836177512613905689629329

theorem tailTrace_7470929 : CollatzResearch.WordTrace tailWord_7470929 prefixEnd_7470929 3836177512613905689629329 := by
  unfold tailWord_7470929
  simp only [CollatzResearch.WordTrace]
  refine ⟨272487166351107640936087841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181658110900738427290725227 272487166351107640936087841)
  ·
    refine ⟨204365374763330730702065881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272487166351107640936087841 204365374763330730702065881)
    ·
      refine ⟨153274031072498048026549411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204365374763330730702065881 153274031072498048026549411)
      ·
        refine ⟨229911046608747072039824117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153274031072498048026549411 229911046608747072039824117)
        ·
          refine ⟨21554160619570038003733511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229911046608747072039824117 21554160619570038003733511)
          ·
            refine ⟨32331240929355057005600267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21554160619570038003733511 32331240929355057005600267)
            ·
              refine ⟨48496861394032585508400401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32331240929355057005600267 48496861394032585508400401)
              ·
                refine ⟨36372646045524439131300301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48496861394032585508400401 36372646045524439131300301)
                ·
                  refine ⟨13639742267071664674237613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36372646045524439131300301 13639742267071664674237613)
                  ·
                    refine ⟨5114903350151874252839105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13639742267071664674237613 5114903350151874252839105)
                    ·
                      refine ⟨3836177512613905689629329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114903350151874252839105 3836177512613905689629329)
                      ·
                        rfl

theorem cell23_7470929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_7470929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470929 prefixEnd_7470929 := by exact prefixLift 7470929
  have htrace : WordTrace (prefixWord ++ tailWord_7470929) baseStart_7470929 baseEnd_7470929 := by
    simpa [prefixWord, tailWord_7470929, baseEnd_7470929] using wordTrace_append hprefix tailTrace_7470929
  have hstable : (prefixWord ++ tailWord_7470929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470929).length < 2 ^ (prefixWord ++ tailWord_7470929).sum := by decide
  have hdescent : baseEnd_7470929 < baseStart_7470929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470946 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_7470946 : Nat := 118140960795 + 7470946 * 2 ^ 59
def prefixEnd_7470946 : Nat := 4983230072969 + 3 ^ 40 * 7470946 * 2
def baseEnd_7470946 : Nat := 3836186241785032123116751

theorem tailTrace_7470946 : CollatzResearch.WordTrace tailWord_7470946 prefixEnd_7470946 3836186241785032123116751 := by
  unfold tailWord_7470946
  simp only [CollatzResearch.WordTrace]
  refine ⟨68121946598011513209864173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181658524261364035226304461 68121946598011513209864173)
  ·
    refine ⟨25545729974254317453699065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68121946598011513209864173 25545729974254317453699065)
    ·
      refine ⟨19159297480690738090274299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25545729974254317453699065 19159297480690738090274299)
      ·
        refine ⟨28738946221036107135411449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19159297480690738090274299 28738946221036107135411449)
        ·
          refine ⟨21554209665777080351558587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28738946221036107135411449 21554209665777080351558587)
          ·
            refine ⟨32331314498665620527337881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21554209665777080351558587 32331314498665620527337881)
            ·
              refine ⟨24248485873999215395503411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32331314498665620527337881 24248485873999215395503411)
              ·
                refine ⟨36372728810998823093255117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24248485873999215395503411 36372728810998823093255117)
                ·
                  refine ⟨13639773304124558659970669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36372728810998823093255117 13639773304124558659970669)
                  ·
                    refine ⟨5114914989046709497489001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13639773304124558659970669 5114914989046709497489001)
                    ·
                      refine ⟨3836186241785032123116751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5114914989046709497489001 3836186241785032123116751)
                      ·
                        rfl

theorem cell23_7470946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_7470946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470946 prefixEnd_7470946 := by exact prefixLift 7470946
  have htrace : WordTrace (prefixWord ++ tailWord_7470946) baseStart_7470946 baseEnd_7470946 := by
    simpa [prefixWord, tailWord_7470946, baseEnd_7470946] using wordTrace_append hprefix tailTrace_7470946
  have hstable : (prefixWord ++ tailWord_7470946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470946).length < 2 ^ (prefixWord ++ tailWord_7470946).sum := by decide
  have hdescent : baseEnd_7470946 < baseStart_7470946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7470955 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4]
def baseStart_7470955 : Nat := 118140960795 + 7470955 * 2 ^ 59
def prefixEnd_7470955 : Nat := 4983230072969 + 3 ^ 40 * 7470955 * 2
def baseEnd_7470955 : Nat := 3836190863110922587904209

theorem tailTrace_7470955 : CollatzResearch.WordTrace tailWord_7470955 prefixEnd_7470955 3836190863110922587904209 := by
  unfold tailWord_7470955
  simp only [CollatzResearch.WordTrace]
  refine ⟨272488114649013447376534319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181658743099342298251022879 272488114649013447376534319)
  ·
    refine ⟨408732171973520171064801479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272488114649013447376534319 408732171973520171064801479)
    ·
      refine ⟨613098257960280256597202219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408732171973520171064801479 613098257960280256597202219)
      ·
        refine ⟨919647386940420384895803329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613098257960280256597202219 919647386940420384895803329)
        ·
          refine ⟨689735540205315288671852497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919647386940420384895803329 689735540205315288671852497)
          ·
            refine ⟨517301655153986466503889373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689735540205315288671852497 517301655153986466503889373)
            ·
              refine ⟨193988120682744924938958515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517301655153986466503889373 193988120682744924938958515)
              ·
                refine ⟨290982181024117387408437773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193988120682744924938958515 290982181024117387408437773)
                ·
                  refine ⟨109118317884044020278164165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290982181024117387408437773 109118317884044020278164165)
                  ·
                    refine ⟨20459684603258253802155781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109118317884044020278164165 20459684603258253802155781)
                    ·
                      refine ⟨3836190863110922587904209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20459684603258253802155781 3836190863110922587904209)
                      ·
                        rfl

theorem cell23_7470955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_7470955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7470955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7470955 prefixEnd_7470955 := by exact prefixLift 7470955
  have htrace : WordTrace (prefixWord ++ tailWord_7470955) baseStart_7470955 baseEnd_7470955 := by
    simpa [prefixWord, tailWord_7470955, baseEnd_7470955] using wordTrace_append hprefix tailTrace_7470955
  have hstable : (prefixWord ++ tailWord_7470955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7470955).length < 2 ^ (prefixWord ++ tailWord_7470955).sum := by decide
  have hdescent : baseEnd_7470955 < baseStart_7470955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7470955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471012 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_7471012 : Nat := 118140960795 + 7471012 * 2 ^ 59
def prefixEnd_7471012 : Nat := 4983230072969 + 3 ^ 40 * 7471012 * 2
def baseEnd_7471012 : Nat := 1278740043836076288297149

theorem tailTrace_7471012 : CollatzResearch.WordTrace tailWord_7471012 prefixEnd_7471012 1278740043836076288297149 := by
  unfold tailWord_7471012
  simp only [CollatzResearch.WordTrace]
  refine ⟨136245096804903473055679645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181660129073204630740906193 136245096804903473055679645)
  ·
    refine ⟨51091911301838802395879867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136245096804903473055679645 51091911301838802395879867)
    ·
      refine ⟨76637866952758203593819801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51091911301838802395879867 76637866952758203593819801)
      ·
        refine ⟨57478400214568652695364851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76637866952758203593819801 57478400214568652695364851)
        ·
          refine ⟨86217600321852979043047277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57478400214568652695364851 86217600321852979043047277)
          ·
            refine ⟨32331600120694867141142729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86217600321852979043047277 32331600120694867141142729)
            ·
              refine ⟨24248700090521150355857047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32331600120694867141142729 24248700090521150355857047)
              ·
                refine ⟨36373050135781725533785571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24248700090521150355857047 36373050135781725533785571)
                ·
                  refine ⟨54559575203672588300678357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36373050135781725533785571 54559575203672588300678357)
                  ·
                    refine ⟨1278740043836076288297149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54559575203672588300678357 1278740043836076288297149)
                    ·
                      rfl

theorem cell23_7471012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_7471012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471012 prefixEnd_7471012 := by exact prefixLift 7471012
  have htrace : WordTrace (prefixWord ++ tailWord_7471012) baseStart_7471012 baseEnd_7471012 := by
    simpa [prefixWord, tailWord_7471012, baseEnd_7471012] using wordTrace_append hprefix tailTrace_7471012
  have hstable : (prefixWord ++ tailWord_7471012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471012).length < 2 ^ (prefixWord ++ tailWord_7471012).sum := by decide
  have hdescent : baseEnd_7471012 < baseStart_7471012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471029 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7471029 : Nat := 118140960795 + 7471029 * 2 ^ 59
def prefixEnd_7471029 : Nat := 4983230072969 + 3 ^ 40 * 7471029 * 2
def baseEnd_7471029 : Nat := 1278742953559785099459623

theorem tailTrace_7471029 : CollatzResearch.WordTrace tailWord_7471029 prefixEnd_7471029 1278742953559785099459623 := by
  unfold tailWord_7471029
  simp only [CollatzResearch.WordTrace]
  refine ⟨272490813650745358014728141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181660542433830238676485427 272490813650745358014728141)
  ·
    refine ⟨102184055119029509255523053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272490813650745358014728141 102184055119029509255523053)
    ·
      refine ⟨38319020669636065970821145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102184055119029509255523053 38319020669636065970821145)
      ·
        refine ⟨28739265502227049478115859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38319020669636065970821145 28739265502227049478115859)
        ·
          refine ⟨43108898253340574217173789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28739265502227049478115859 43108898253340574217173789)
          ·
            refine ⟨16165836845002715331440171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43108898253340574217173789 16165836845002715331440171)
            ·
              refine ⟨24248755267504072997160257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16165836845002715331440171 24248755267504072997160257)
              ·
                refine ⟨18186566450628054747870193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24248755267504072997160257 18186566450628054747870193)
                ·
                  refine ⟨13639924837971041060902645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18186566450628054747870193 13639924837971041060902645)
                  ·
                    refine ⟨1278742953559785099459623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13639924837971041060902645 1278742953559785099459623)
                    ·
                      rfl

theorem cell23_7471029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7471029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471029 prefixEnd_7471029 := by exact prefixLift 7471029
  have htrace : WordTrace (prefixWord ++ tailWord_7471029) baseStart_7471029 baseEnd_7471029 := by
    simpa [prefixWord, tailWord_7471029, baseEnd_7471029] using wordTrace_append hprefix tailTrace_7471029
  have hstable : (prefixWord ++ tailWord_7471029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471029).length < 2 ^ (prefixWord ++ tailWord_7471029).sum := by decide
  have hdescent : baseEnd_7471029 < baseStart_7471029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471066 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_7471066 : Nat := 118140960795 + 7471066 * 2 ^ 59
def prefixEnd_7471066 : Nat := 4983230072969 + 3 ^ 40 * 7471066 * 2
def baseEnd_7471066 : Nat := 3836247859463571653616199

theorem tailTrace_7471066 : CollatzResearch.WordTrace tailWord_7471066 prefixEnd_7471066 3836247859463571653616199 := by
  unfold tailWord_7471066
  simp only [CollatzResearch.WordTrace]
  refine ⟨68123040787902828333456263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181661442101074208889216701 68123040787902828333456263)
  ·
    refine ⟨102184561181854242500184395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68123040787902828333456263 102184561181854242500184395)
    ·
      refine ⟨153276841772781363750276593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102184561181854242500184395 153276841772781363750276593)
      ·
        refine ⟨114957631329586022812707445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153276841772781363750276593 114957631329586022812707445)
        ·
          refine ⟨10777277937148689638691323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114957631329586022812707445 10777277937148689638691323)
          ·
            refine ⟨16165916905723034458036985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10777277937148689638691323 16165916905723034458036985)
            ·
              refine ⟨12124437679292275843527739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16165916905723034458036985 12124437679292275843527739)
              ·
                refine ⟨18186656518938413765291609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12124437679292275843527739 18186656518938413765291609)
                ·
                  refine ⟨13639992389203810323968707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18186656518938413765291609 13639992389203810323968707)
                  ·
                    refine ⟨20459988583805715485953061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13639992389203810323968707 20459988583805715485953061)
                    ·
                      refine ⟨3836247859463571653616199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20459988583805715485953061 3836247859463571653616199)
                      ·
                        rfl

theorem cell23_7471066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_7471066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471066 prefixEnd_7471066 := by exact prefixLift 7471066
  have htrace : WordTrace (prefixWord ++ tailWord_7471066) baseStart_7471066 baseEnd_7471066 := by
    simpa [prefixWord, tailWord_7471066, baseEnd_7471066] using wordTrace_append hprefix tailTrace_7471066
  have hstable : (prefixWord ++ tailWord_7471066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471066).length < 2 ^ (prefixWord ++ tailWord_7471066).sum := by decide
  have hdescent : baseEnd_7471066 < baseStart_7471066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471076 : List Nat := [2, 3, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_7471076 : Nat := 118140960795 + 7471076 * 2 ^ 59
def prefixEnd_7471076 : Nat := 4983230072969 + 3 ^ 40 * 7471076 * 2
def baseEnd_7471076 : Nat := 1278750998090038871497051

theorem tailTrace_7471076 : CollatzResearch.WordTrace tailWord_7471076 prefixEnd_7471076 1278750998090038871497051 := by
  unfold tailWord_7471076
  simp only [CollatzResearch.WordTrace]
  refine ⟨136246263940787542520844541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181661685254383390027792721 136246263940787542520844541)
  ·
    refine ⟨51092348977795328445316703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136246263940787542520844541 51092348977795328445316703)
    ·
      refine ⟨76638523466692992667975055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51092348977795328445316703 76638523466692992667975055)
      ·
        refine ⟨114957785200039489001962583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76638523466692992667975055 114957785200039489001962583)
        ·
          refine ⟨172436677800059233502943875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114957785200039489001962583 172436677800059233502943875)
          ·
            refine ⟨258655016700088850254415813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172436677800059233502943875 258655016700088850254415813)
            ·
              refine ⟨48497815631266659422702965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258655016700088850254415813 48497815631266659422702965)
              ·
                refine ⟨4546670215431249320878403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48497815631266659422702965 4546670215431249320878403)
                ·
                  refine ⟨6820005323146873981317605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546670215431249320878403 6820005323146873981317605)
                  ·
                    refine ⟨1278750998090038871497051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6820005323146873981317605 1278750998090038871497051)
                    ·
                      rfl

theorem cell23_7471076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_7471076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471076 prefixEnd_7471076 := by exact prefixLift 7471076
  have htrace : WordTrace (prefixWord ++ tailWord_7471076) baseStart_7471076 baseEnd_7471076 := by
    simpa [prefixWord, tailWord_7471076, baseEnd_7471076] using wordTrace_append hprefix tailTrace_7471076
  have hstable : (prefixWord ++ tailWord_7471076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471076).length < 2 ^ (prefixWord ++ tailWord_7471076).sum := by decide
  have hdescent : baseEnd_7471076 < baseStart_7471076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471086 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_7471086 : Nat := 118140960795 + 7471086 * 2 ^ 59
def prefixEnd_7471086 : Nat := 4983230072969 + 3 ^ 40 * 7471086 * 2
def baseEnd_7471086 : Nat := 3836258129076661575366107

theorem tailTrace_7471086 : CollatzResearch.WordTrace tailWord_7471086 prefixEnd_7471086 3836258129076661575366107 := by
  unfold tailWord_7471086
  simp only [CollatzResearch.WordTrace]
  refine ⟨34061611576442357093694139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181661928407692571166368741 34061611576442357093694139)
  ·
    refine ⟨51092417364663535640541209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34061611576442357093694139 51092417364663535640541209)
    ·
      refine ⟨38319313023497651730405907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51092417364663535640541209 38319313023497651730405907)
      ·
        refine ⟨57478969535246477595608861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38319313023497651730405907 57478969535246477595608861)
        ·
          refine ⟨21554613575717429098353323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57478969535246477595608861 21554613575717429098353323)
          ·
            refine ⟨32331920363576143647529985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21554613575717429098353323 32331920363576143647529985)
            ·
              refine ⟨24248940272682107735647489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32331920363576143647529985 24248940272682107735647489)
              ·
                refine ⟨18186705204511580801735617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24248940272682107735647489 18186705204511580801735617)
                ·
                  refine ⟨13640028903383685601301713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18186705204511580801735617 13640028903383685601301713)
                  ·
                    refine ⟨10230021677537764200976285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13640028903383685601301713 10230021677537764200976285)
                    ·
                      refine ⟨3836258129076661575366107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10230021677537764200976285 3836258129076661575366107)
                      ·
                        rfl

theorem cell23_7471086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_7471086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471086 prefixEnd_7471086 := by exact prefixLift 7471086
  have htrace : WordTrace (prefixWord ++ tailWord_7471086) baseStart_7471086 baseEnd_7471086 := by
    simpa [prefixWord, tailWord_7471086, baseEnd_7471086] using wordTrace_append hprefix tailTrace_7471086
  have hstable : (prefixWord ++ tailWord_7471086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471086).length < 2 ^ (prefixWord ++ tailWord_7471086).sum := by decide
  have hdescent : baseEnd_7471086 < baseStart_7471086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471112 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_7471112 : Nat := 118140960795 + 7471112 * 2 ^ 59
def prefixEnd_7471112 : Nat := 4983230072969 + 3 ^ 40 * 7471112 * 2
def baseEnd_7471112 : Nat := 3836271479573678473640987

theorem tailTrace_7471112 : CollatzResearch.WordTrace tailWord_7471112 prefixEnd_7471112 3836271479573678473640987 := by
  unfold tailWord_7471112
  simp only [CollatzResearch.WordTrace]
  refine ⟨136246920454722331594999795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181662560606296442126666393 136246920454722331594999795)
  ·
    refine ⟨204370380682083497392499693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136246920454722331594999795 204370380682083497392499693)
    ·
      refine ⟨76638892755781311522187385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204370380682083497392499693 76638892755781311522187385)
      ·
        refine ⟨57479169566835983641640539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76638892755781311522187385 57479169566835983641640539)
        ·
          refine ⟨86218754350253975462460809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57479169566835983641640539 86218754350253975462460809)
          ·
            refine ⟨64664065762690481596845607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86218754350253975462460809 64664065762690481596845607)
            ·
              refine ⟨96996098644035722395268411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64664065762690481596845607 96996098644035722395268411)
              ·
                refine ⟨145494147966053583592902617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96996098644035722395268411 145494147966053583592902617)
                ·
                  refine ⟨109120610974540187694676963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145494147966053583592902617 109120610974540187694676963)
                  ·
                    refine ⟨163680916461810281542015445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109120610974540187694676963 163680916461810281542015445)
                    ·
                      refine ⟨3836271479573678473640987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163680916461810281542015445 3836271479573678473640987)
                      ·
                        rfl

theorem cell23_7471112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_7471112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471112 prefixEnd_7471112 := by exact prefixLift 7471112
  have htrace : WordTrace (prefixWord ++ tailWord_7471112) baseStart_7471112 baseEnd_7471112 := by
    simpa [prefixWord, tailWord_7471112, baseEnd_7471112] using wordTrace_append hprefix tailTrace_7471112
  have hstable : (prefixWord ++ tailWord_7471112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471112).length < 2 ^ (prefixWord ++ tailWord_7471112).sum := by decide
  have hdescent : baseEnd_7471112 < baseStart_7471112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471116 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_7471116 : Nat := 118140960795 + 7471116 * 2 ^ 59
def prefixEnd_7471116 : Nat := 4983230072969 + 3 ^ 40 * 7471116 * 2
def baseEnd_7471116 : Nat := 3836273533496296457990969

theorem tailTrace_7471116 : CollatzResearch.WordTrace tailWord_7471116 prefixEnd_7471116 3836273533496296457990969 := by
  unfold tailWord_7471116
  simp only [CollatzResearch.WordTrace]
  refine ⟨136246993400715085936572601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181662657867620114582096801 136246993400715085936572601)
  ·
    refine ⟨102185245050536314452429451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136246993400715085936572601 102185245050536314452429451)
    ·
      refine ⟨153277867575804471678644177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102185245050536314452429451 153277867575804471678644177)
      ·
        refine ⟨114958400681853353758983133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153277867575804471678644177 114958400681853353758983133)
        ·
          refine ⟨43109400255695007659618675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114958400681853353758983133 43109400255695007659618675)
          ·
            refine ⟨64664100383542511489428013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43109400255695007659618675 64664100383542511489428013)
            ·
              refine ⟨24249037643828441808535505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64664100383542511489428013 24249037643828441808535505)
              ·
                refine ⟨18186778232871331356401629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24249037643828441808535505 18186778232871331356401629)
                ·
                  refine ⟨6820041837326749258650611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18186778232871331356401629 6820041837326749258650611)
                  ·
                    refine ⟨10230062755990123887975917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6820041837326749258650611 10230062755990123887975917)
                    ·
                      refine ⟨3836273533496296457990969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10230062755990123887975917 3836273533496296457990969)
                      ·
                        rfl

theorem cell23_7471116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_7471116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471116 prefixEnd_7471116 := by exact prefixLift 7471116
  have htrace : WordTrace (prefixWord ++ tailWord_7471116) baseStart_7471116 baseEnd_7471116 := by
    simpa [prefixWord, tailWord_7471116, baseEnd_7471116] using wordTrace_append hprefix tailTrace_7471116
  have hstable : (prefixWord ++ tailWord_7471116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471116).length < 2 ^ (prefixWord ++ tailWord_7471116).sum := by decide
  have hdescent : baseEnd_7471116 < baseStart_7471116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471117 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7471117 : Nat := 118140960795 + 7471117 * 2 ^ 59
def prefixEnd_7471117 : Nat := 4983230072969 + 3 ^ 40 * 7471117 * 2
def baseEnd_7471117 : Nat := 3836274046976950954078465

theorem tailTrace_7471117 : CollatzResearch.WordTrace tailWord_7471117 prefixEnd_7471117 3836274046976950954078465 := by
  unfold tailWord_7471117
  simp only [CollatzResearch.WordTrace]
  refine ⟨272494023274426549043931605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181662682182951032695954403 272494023274426549043931605)
  ·
    refine ⟨6386578670494372243217147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 272494023274426549043931605 6386578670494372243217147)
    ·
      refine ⟨9579868005741558364825721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386578670494372243217147 9579868005741558364825721)
      ·
        refine ⟨7184901004306168773619291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9579868005741558364825721 7184901004306168773619291)
        ·
          refine ⟨10777351506459253160428937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7184901004306168773619291 10777351506459253160428937)
          ·
            refine ⟨8083013629844439870321703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10777351506459253160428937 8083013629844439870321703)
            ·
              refine ⟨12124520444766659805482555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8083013629844439870321703 12124520444766659805482555)
              ·
                refine ⟨18186780667149989708223833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12124520444766659805482555 18186780667149989708223833)
                ·
                  refine ⟨13640085500362492281167875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18186780667149989708223833 13640085500362492281167875)
                  ·
                    refine ⟨20460128250543738421751813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13640085500362492281167875 20460128250543738421751813)
                    ·
                      refine ⟨3836274046976950954078465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20460128250543738421751813 3836274046976950954078465)
                      ·
                        rfl

theorem cell23_7471117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7471117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471117 prefixEnd_7471117 := by exact prefixLift 7471117
  have htrace : WordTrace (prefixWord ++ tailWord_7471117) baseStart_7471117 baseEnd_7471117 := by
    simpa [prefixWord, tailWord_7471117, baseEnd_7471117] using wordTrace_append hprefix tailTrace_7471117
  have hstable : (prefixWord ++ tailWord_7471117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471117).length < 2 ^ (prefixWord ++ tailWord_7471117).sum := by decide
  have hdescent : baseEnd_7471117 < baseStart_7471117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471150 : List Nat := [4, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_7471150 : Nat := 118140960795 + 7471150 * 2 ^ 59
def prefixEnd_7471150 : Nat := 4983230072969 + 3 ^ 40 * 7471150 * 2
def baseEnd_7471150 : Nat := 3836290991838549324965813

theorem tailTrace_7471150 : CollatzResearch.WordTrace tailWord_7471150 prefixEnd_7471150 3836290991838549324965813 := by
  unfold tailWord_7471150
  simp only [CollatzResearch.WordTrace]
  refine ⟨34061903360413374459985363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181663484588871330453255269 34061903360413374459985363)
  ·
    refine ⟨51092855040620061689978045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34061903360413374459985363 51092855040620061689978045)
    ·
      refine ⟨19159820640232523133741767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51092855040620061689978045 19159820640232523133741767)
      ·
        refine ⟨28739730960348784700612651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19159820640232523133741767 28739730960348784700612651)
        ·
          refine ⟨43109596440523177050918977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28739730960348784700612651 43109596440523177050918977)
          ·
            refine ⟨32332197330392382788189233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43109596440523177050918977 32332197330392382788189233)
            ·
              refine ⟨24249147997794287091141925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32332197330392382788189233 24249147997794287091141925)
              ·
                refine ⟨4546715249586428829589111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24249147997794287091141925 4546715249586428829589111)
                ·
                  refine ⟨6820072874379643244383667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546715249586428829589111 6820072874379643244383667)
                  ·
                    refine ⟨10230109311569464866575501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6820072874379643244383667 10230109311569464866575501)
                    ·
                      refine ⟨3836290991838549324965813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10230109311569464866575501 3836290991838549324965813)
                      ·
                        rfl

theorem cell23_7471150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_7471150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471150 prefixEnd_7471150 := by exact prefixLift 7471150
  have htrace : WordTrace (prefixWord ++ tailWord_7471150) baseStart_7471150 baseEnd_7471150 := by
    simpa [prefixWord, tailWord_7471150, baseEnd_7471150] using wordTrace_append hprefix tailTrace_7471150
  have hstable : (prefixWord ++ tailWord_7471150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471150).length < 2 ^ (prefixWord ++ tailWord_7471150).sum := by decide
  have hdescent : baseEnd_7471150 < baseStart_7471150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471159 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_7471159 : Nat := 118140960795 + 7471159 * 2 ^ 59
def prefixEnd_7471159 : Nat := 4983230072969 + 3 ^ 40 * 7471159 * 2
def baseEnd_7471159 : Nat := 3836295613164439789753271

theorem tailTrace_7471159 : CollatzResearch.WordTrace tailWord_7471159 prefixEnd_7471159 3836295613164439789753271 := by
  unfold tailWord_7471159
  simp only [CollatzResearch.WordTrace]
  refine ⟨272495555140274390216960531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181663703426849593477973687 272495555140274390216960531)
  ·
    refine ⟨408743332710411585325440797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272495555140274390216960531 408743332710411585325440797)
    ·
      refine ⟨153278749766404344497040299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408743332710411585325440797 153278749766404344497040299)
      ·
        refine ⟨229918124649606516745560449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153278749766404344497040299 229918124649606516745560449)
        ·
          refine ⟨172438593487204887559170337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229918124649606516745560449 172438593487204887559170337)
          ·
            refine ⟨129328945115403665669377753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172438593487204887559170337 129328945115403665669377753)
            ·
              refine ⟨96996708836552749252033315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129328945115403665669377753 96996708836552749252033315)
              ·
                refine ⟨145495063254829123878049973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96996708836552749252033315 145495063254829123878049973)
                ·
                  refine ⟨13640162180140230363567185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145495063254829123878049973 13640162180140230363567185)
                  ·
                    refine ⟨10230121635105172772675389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13640162180140230363567185 10230121635105172772675389)
                    ·
                      refine ⟨3836295613164439789753271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10230121635105172772675389 3836295613164439789753271)
                      ·
                        rfl

theorem cell23_7471159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_7471159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471159 prefixEnd_7471159 := by exact prefixLift 7471159
  have htrace : WordTrace (prefixWord ++ tailWord_7471159) baseStart_7471159 baseEnd_7471159 := by
    simpa [prefixWord, tailWord_7471159, baseEnd_7471159] using wordTrace_append hprefix tailTrace_7471159
  have hstable : (prefixWord ++ tailWord_7471159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471159).length < 2 ^ (prefixWord ++ tailWord_7471159).sum := by decide
  have hdescent : baseEnd_7471159 < baseStart_7471159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471162 : List Nat := [3, 1, 1, 1, 3, 1, 1, 12]
def baseStart_7471162 : Nat := 118140960795 + 7471162 * 2 ^ 59
def prefixEnd_7471162 : Nat := 4983230072969 + 3 ^ 40 * 7471162 * 2
def baseEnd_7471162 : Nat := 142085079763200121407991

theorem tailTrace_7471162 : CollatzResearch.WordTrace tailWord_7471162 prefixEnd_7471162 142085079763200121407991 := by
  unfold tailWord_7471162
  simp only [CollatzResearch.WordTrace]
  refine ⟨68123916139815880432329935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181663776372842347819546493 68123916139815880432329935)
  ·
    refine ⟨102185874209723820648494903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68123916139815880432329935 102185874209723820648494903)
    ·
      refine ⟨153278811314585730972742355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102185874209723820648494903 153278811314585730972742355)
      ·
        refine ⟨229918216971878596459113533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153278811314585730972742355 229918216971878596459113533)
        ·
          refine ⟨86219331364454473672167575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229918216971878596459113533 86219331364454473672167575)
          ·
            refine ⟨129328997046681710508251363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86219331364454473672167575 129328997046681710508251363)
            ·
              refine ⟨193993495570022565762377045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129328997046681710508251363 193993495570022565762377045)
              ·
                refine ⟨142085079763200121407991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 193993495570022565762377045 142085079763200121407991)
                ·
                  rfl

theorem cell23_7471162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_7471162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471162 prefixEnd_7471162 := by exact prefixLift 7471162
  have htrace : WordTrace (prefixWord ++ tailWord_7471162) baseStart_7471162 baseEnd_7471162 := by
    simpa [prefixWord, tailWord_7471162, baseEnd_7471162] using wordTrace_append hprefix tailTrace_7471162
  have hstable : (prefixWord ++ tailWord_7471162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471162).length < 2 ^ (prefixWord ++ tailWord_7471162).sum := by decide
  have hdescent : baseEnd_7471162 < baseStart_7471162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471190 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7471190 : Nat := 118140960795 + 7471190 * 2 ^ 59
def prefixEnd_7471190 : Nat := 4983230072969 + 3 ^ 40 * 7471190 * 2
def baseEnd_7471190 : Nat := 3836311531064729168465629

theorem tailTrace_7471190 : CollatzResearch.WordTrace tailWord_7471190 prefixEnd_7471190 3836311531064729168465629 := by
  unfold tailWord_7471190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17031042862697630156958689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181664457202108055007559349 17031042862697630156958689)
  ·
    refine ⟨12773282147023222617719017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17031042862697630156958689 12773282147023222617719017)
    ·
      refine ⟨9579961610267416963289263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12773282147023222617719017 9579961610267416963289263)
      ·
        refine ⟨14369942415401125444933895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579961610267416963289263 14369942415401125444933895)
        ·
          refine ⟨21554913623101688167400843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14369942415401125444933895 21554913623101688167400843)
          ·
            refine ⟨32332370434652532251101265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21554913623101688167400843 32332370434652532251101265)
            ·
              refine ⟨24249277825989399188325949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32332370434652532251101265 24249277825989399188325949)
              ·
                refine ⟨9093479184746024695622231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24249277825989399188325949 9093479184746024695622231)
                ·
                  refine ⟨13640218777119037043433347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9093479184746024695622231 13640218777119037043433347)
                  ·
                    refine ⟨20460328165678555565150021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13640218777119037043433347 20460328165678555565150021)
                    ·
                      refine ⟨3836311531064729168465629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20460328165678555565150021 3836311531064729168465629)
                      ·
                        rfl

theorem cell23_7471190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7471190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471190 prefixEnd_7471190 := by exact prefixLift 7471190
  have htrace : WordTrace (prefixWord ++ tailWord_7471190) baseStart_7471190 baseEnd_7471190 := by
    simpa [prefixWord, tailWord_7471190, baseEnd_7471190] using wordTrace_append hprefix tailTrace_7471190
  have hstable : (prefixWord ++ tailWord_7471190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471190).length < 2 ^ (prefixWord ++ tailWord_7471190).sum := by decide
  have hdescent : baseEnd_7471190 < baseStart_7471190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471207 : List Nat := [1, 1, 5, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_7471207 : Nat := 118140960795 + 7471207 * 2 ^ 59
def prefixEnd_7471207 : Nat := 4983230072969 + 3 ^ 40 * 7471207 * 2
def baseEnd_7471207 : Nat := 3836320260235855601953051

theorem tailTrace_7471207 : CollatzResearch.WordTrace tailWord_7471207 prefixEnd_7471207 3836320260235855601953051 := by
  unfold tailWord_7471207
  simp only [CollatzResearch.WordTrace]
  refine ⟨272497305844100494414707875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181664870562733662943138583 272497305844100494414707875)
  ·
    refine ⟨408745958766150741622061813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272497305844100494414707875 408745958766150741622061813)
    ·
      refine ⟨38319933634326632027068295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408745958766150741622061813 38319933634326632027068295)
      ·
        refine ⟨57479900451489948040602443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38319933634326632027068295 57479900451489948040602443)
        ·
          refine ⟨86219850677234922060903665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57479900451489948040602443 86219850677234922060903665)
          ·
            refine ⟨64664888007926191545677749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86219850677234922060903665 64664888007926191545677749)
            ·
              refine ⟨6062333250743080457407289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64664888007926191545677749 6062333250743080457407289)
              ·
                refine ⟨4546749938057310343055467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6062333250743080457407289 4546749938057310343055467)
                ·
                  refine ⟨6820124907085965514583201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546749938057310343055467 6820124907085965514583201)
                  ·
                    refine ⟨5115093680314474135937401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6820124907085965514583201 5115093680314474135937401)
                    ·
                      refine ⟨3836320260235855601953051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5115093680314474135937401 3836320260235855601953051)
                      ·
                        rfl

theorem cell23_7471207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_7471207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471207 prefixEnd_7471207 := by exact prefixLift 7471207
  have htrace : WordTrace (prefixWord ++ tailWord_7471207) baseStart_7471207 baseEnd_7471207 := by
    simpa [prefixWord, tailWord_7471207, baseEnd_7471207] using wordTrace_append hprefix tailTrace_7471207
  have hstable : (prefixWord ++ tailWord_7471207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471207).length < 2 ^ (prefixWord ++ tailWord_7471207).sum := by decide
  have hdescent : baseEnd_7471207 < baseStart_7471207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471223 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_7471223 : Nat := 118140960795 + 7471223 * 2 ^ 59
def prefixEnd_7471223 : Nat := 4983230072969 + 3 ^ 40 * 7471223 * 2
def baseEnd_7471223 : Nat := 3836328475926327539352977

theorem tailTrace_7471223 : CollatzResearch.WordTrace tailWord_7471223 prefixEnd_7471223 3836328475926327539352977 := by
  unfold tailWord_7471223
  simp only [CollatzResearch.WordTrace]
  refine ⟨272497889412042529147290323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181665259608028352764860215 272497889412042529147290323)
  ·
    refine ⟨408746834118063793720935485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272497889412042529147290323 408746834118063793720935485)
    ·
      refine ⟨153280062794273922645350807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408746834118063793720935485 153280062794273922645350807)
      ·
        refine ⟨229920094191410883968026211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153280062794273922645350807 229920094191410883968026211)
        ·
          refine ⟨344880141287116325952039317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229920094191410883968026211 344880141287116325952039317)
          ·
            refine ⟨16166256622833577779001843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 344880141287116325952039317 16166256622833577779001843)
            ·
              refine ⟨24249384934250366668502765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16166256622833577779001843 24249384934250366668502765)
              ·
                refine ⟨9093519350343887500688537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24249384934250366668502765 9093519350343887500688537)
                ·
                  refine ⟨6820139512757915625516403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9093519350343887500688537 6820139512757915625516403)
                  ·
                    refine ⟨10230209269136873438274605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6820139512757915625516403 10230209269136873438274605)
                    ·
                      refine ⟨3836328475926327539352977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10230209269136873438274605 3836328475926327539352977)
                      ·
                        rfl

theorem cell23_7471223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_7471223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471223 prefixEnd_7471223 := by exact prefixLift 7471223
  have htrace : WordTrace (prefixWord ++ tailWord_7471223) baseStart_7471223 baseEnd_7471223 := by
    simpa [prefixWord, tailWord_7471223, baseEnd_7471223] using wordTrace_append hprefix tailTrace_7471223
  have hstable : (prefixWord ++ tailWord_7471223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471223).length < 2 ^ (prefixWord ++ tailWord_7471223).sum := by decide
  have hdescent : baseEnd_7471223 < baseStart_7471223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471249 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_7471249 : Nat := 118140960795 + 7471249 * 2 ^ 59
def prefixEnd_7471249 : Nat := 4983230072969 + 3 ^ 40 * 7471249 * 2
def baseEnd_7471249 : Nat := 3836341826423344437627857

theorem tailTrace_7471249 : CollatzResearch.WordTrace tailWord_7471249 prefixEnd_7471249 3836341826423344437627857 := by
  unfold tailWord_7471249
  simp only [CollatzResearch.WordTrace]
  refine ⟨272498837709948335587736801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181665891806632223725157867 272498837709948335587736801)
  ·
    refine ⟨204374128282461251690802601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272498837709948335587736801 204374128282461251690802601)
    ·
      refine ⟨153280596211845938768101951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204374128282461251690802601 153280596211845938768101951)
      ·
        refine ⟨229920894317768908152152927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153280596211845938768101951 229920894317768908152152927)
        ·
          refine ⟨344881341476653362228229391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229920894317768908152152927 344881341476653362228229391)
          ·
            refine ⟨517322012214980043342344087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344881341476653362228229391 517322012214980043342344087)
            ·
              refine ⟨775983018322470065013516131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517322012214980043342344087 775983018322470065013516131)
              ·
                refine ⟨1163974527483705097520274197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775983018322470065013516131 1163974527483705097520274197)
                ·
                  refine ⟨54561305975798676446262853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1163974527483705097520274197 54561305975798676446262853)
                  ·
                    refine ⟨10230244870462251833674285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54561305975798676446262853 10230244870462251833674285)
                    ·
                      refine ⟨3836341826423344437627857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10230244870462251833674285 3836341826423344437627857)
                      ·
                        rfl

theorem cell23_7471249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_7471249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471249 prefixEnd_7471249 := by exact prefixLift 7471249
  have htrace : WordTrace (prefixWord ++ tailWord_7471249) baseStart_7471249 baseEnd_7471249 := by
    simpa [prefixWord, tailWord_7471249, baseEnd_7471249] using wordTrace_append hprefix tailTrace_7471249
  have hstable : (prefixWord ++ tailWord_7471249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471249).length < 2 ^ (prefixWord ++ tailWord_7471249).sum := by decide
  have hdescent : baseEnd_7471249 < baseStart_7471249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471269 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 7]
def baseStart_7471269 : Nat := 118140960795 + 7471269 * 2 ^ 59
def prefixEnd_7471269 : Nat := 4983230072969 + 3 ^ 40 * 7471269 * 2
def baseEnd_7471269 : Nat := 426261344004048262153085

theorem tailTrace_7471269 : CollatzResearch.WordTrace tailWord_7471269 prefixEnd_7471269 426261344004048262153085 := by
  unfold tailWord_7471269
  simp only [CollatzResearch.WordTrace]
  refine ⟨272499567169875879003464861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181666378113250586002309907 272499567169875879003464861)
  ·
    refine ⟨102187337688703454626299323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272499567169875879003464861 102187337688703454626299323)
    ·
      refine ⟨153281006533055181939448985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102187337688703454626299323 153281006533055181939448985)
      ·
        refine ⟨114960754899791386454586739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153281006533055181939448985 114960754899791386454586739)
        ·
          refine ⟨172441132349687079681880109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114960754899791386454586739 172441132349687079681880109)
          ·
            refine ⟨64665424631132654880705041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172441132349687079681880109 64665424631132654880705041)
            ·
              refine ⟨48499068473349491160528781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64665424631132654880705041 48499068473349491160528781)
              ·
                refine ⟨18187150677506059185198293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48499068473349491160528781 18187150677506059185198293)
                ·
                  refine ⟨426261344004048262153085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18187150677506059185198293 426261344004048262153085)
                  ·
                    rfl

theorem cell23_7471269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_7471269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471269 prefixEnd_7471269 := by exact prefixLift 7471269
  have htrace : WordTrace (prefixWord ++ tailWord_7471269) baseStart_7471269 baseEnd_7471269 := by
    simpa [prefixWord, tailWord_7471269, baseEnd_7471269] using wordTrace_append hprefix tailTrace_7471269
  have hstable : (prefixWord ++ tailWord_7471269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471269).length < 2 ^ (prefixWord ++ tailWord_7471269).sum := by decide
  have hdescent : baseEnd_7471269 < baseStart_7471269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471336 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7471336 : Nat := 118140960795 + 7471336 * 2 ^ 59
def prefixEnd_7471336 : Nat := 4983230072969 + 3 ^ 40 * 7471336 * 2
def baseEnd_7471336 : Nat := 3836386499240285597239957

theorem tailTrace_7471336 : CollatzResearch.WordTrace tailWord_7471336 prefixEnd_7471336 3836386499240285597239957 := by
  unfold tailWord_7471336
  simp only [CollatzResearch.WordTrace]
  refine ⟨136251005430316574723076931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181668007240422099630769241 136251005430316574723076931)
  ·
    refine ⟨204376508145474862084615397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136251005430316574723076931 204376508145474862084615397)
    ·
      refine ⟨38320595277276536640865387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204376508145474862084615397 38320595277276536640865387)
      ·
        refine ⟨57480892915914804961298081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38320595277276536640865387 57480892915914804961298081)
        ·
          refine ⟨43110669686936103720973561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57480892915914804961298081 43110669686936103720973561)
          ·
            refine ⟨32333002265202077790730171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43110669686936103720973561 32333002265202077790730171)
            ·
              refine ⟨48499503397803116686095257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32333002265202077790730171 48499503397803116686095257)
              ·
                refine ⟨36374627548352337514571443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48499503397803116686095257 36374627548352337514571443)
                ·
                  refine ⟨54561941322528506271857165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36374627548352337514571443 54561941322528506271857165)
                  ·
                    refine ⟨20460727995948189851946437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54561941322528506271857165 20460727995948189851946437)
                    ·
                      refine ⟨3836386499240285597239957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20460727995948189851946437 3836386499240285597239957)
                      ·
                        rfl

theorem cell23_7471336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7471336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471336 prefixEnd_7471336 := by exact prefixLift 7471336
  have htrace : WordTrace (prefixWord ++ tailWord_7471336) baseStart_7471336 baseEnd_7471336 := by
    simpa [prefixWord, tailWord_7471336, baseEnd_7471336] using wordTrace_append hprefix tailTrace_7471336
  have hstable : (prefixWord ++ tailWord_7471336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471336).length < 2 ^ (prefixWord ++ tailWord_7471336).sum := by decide
  have hdescent : baseEnd_7471336 < baseStart_7471336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471359 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 10]
def baseStart_7471359 : Nat := 118140960795 + 7471359 * 2 ^ 59
def prefixEnd_7471359 : Nat := 4983230072969 + 3 ^ 40 * 7471359 * 2
def baseEnd_7471359 : Nat := 426266478810593223028039

theorem tailTrace_7471359 : CollatzResearch.WordTrace tailWord_7471359 prefixEnd_7471359 426266478810593223028039 := by
  unfold tailWord_7471359
  simp only [CollatzResearch.WordTrace]
  refine ⟨272502849739549824374241131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181668566493033216249494087 272502849739549824374241131)
  ·
    refine ⟨408754274609324736561361697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272502849739549824374241131 408754274609324736561361697)
    ·
      refine ⟨306565705956993552421021273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408754274609324736561361697 306565705956993552421021273)
      ·
        refine ⟨229924279467745164315765955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306565705956993552421021273 229924279467745164315765955)
        ·
          refine ⟨344886419201617746473648933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229924279467745164315765955 344886419201617746473648933)
          ·
            refine ⟨64666203600303327463809175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344886419201617746473648933 64666203600303327463809175)
            ·
              refine ⟨96999305400454991195713763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64666203600303327463809175 96999305400454991195713763)
              ·
                refine ⟨145498958100682486793570645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96999305400454991195713763 145498958100682486793570645)
                ·
                  refine ⟨426266478810593223028039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 145498958100682486793570645 426266478810593223028039)
                  ·
                    rfl

theorem cell23_7471359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 10].length) (baseStart_7471359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471359 prefixEnd_7471359 := by exact prefixLift 7471359
  have htrace : WordTrace (prefixWord ++ tailWord_7471359) baseStart_7471359 baseEnd_7471359 := by
    simpa [prefixWord, tailWord_7471359, baseEnd_7471359] using wordTrace_append hprefix tailTrace_7471359
  have hstable : (prefixWord ++ tailWord_7471359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471359).length < 2 ^ (prefixWord ++ tailWord_7471359).sum := by decide
  have hdescent : baseEnd_7471359 < baseStart_7471359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471379 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8]
def baseStart_7471379 : Nat := 118140960795 + 7471379 * 2 ^ 59
def prefixEnd_7471379 : Nat := 4983230072969 + 3 ^ 40 * 7471379 * 2
def baseEnd_7471379 : Nat := 3836408578908428929002259

theorem tailTrace_7471379 : CollatzResearch.WordTrace tailWord_7471379 prefixEnd_7471379 3836408578908428929002259 := by
  unfold tailWord_7471379
  simp only [CollatzResearch.WordTrace]
  refine ⟨272503579199477367789969191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181669052799651578526646127 272503579199477367789969191)
  ·
    refine ⟨408755368799216051684953787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272503579199477367789969191 408755368799216051684953787)
    ·
      refine ⟨613133053198824077527430681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408755368799216051684953787 613133053198824077527430681)
      ·
        refine ⟨459849789899118058145573011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613133053198824077527430681 459849789899118058145573011)
        ·
          refine ⟨689774684848677087218359517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459849789899118058145573011 689774684848677087218359517)
          ·
            refine ⟨258665506818253907706884819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 689774684848677087218359517 258665506818253907706884819)
            ·
              refine ⟨387998260227380861560327229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258665506818253907706884819 387998260227380861560327229)
              ·
                refine ⟨145499347585267823085122711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387998260227380861560327229 145499347585267823085122711)
                ·
                  refine ⟨218249021377901734627684067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145499347585267823085122711 218249021377901734627684067)
                  ·
                    refine ⟨327373532066852601941526101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218249021377901734627684067 327373532066852601941526101)
                    ·
                      refine ⟨3836408578908428929002259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 327373532066852601941526101 3836408578908428929002259)
                      ·
                        rfl

theorem cell23_7471379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_7471379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471379 prefixEnd_7471379 := by exact prefixLift 7471379
  have htrace : WordTrace (prefixWord ++ tailWord_7471379) baseStart_7471379 baseEnd_7471379 := by
    simpa [prefixWord, tailWord_7471379, baseEnd_7471379] using wordTrace_append hprefix tailTrace_7471379
  have hstable : (prefixWord ++ tailWord_7471379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471379).length < 2 ^ (prefixWord ++ tailWord_7471379).sum := by decide
  have hdescent : baseEnd_7471379 < baseStart_7471379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471393 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 6]
def baseStart_7471393 : Nat := 118140960795 + 7471393 * 2 ^ 59
def prefixEnd_7471393 : Nat := 4983230072969 + 3 ^ 40 * 7471393 * 2
def baseEnd_7471393 : Nat := 426268418626399097136355

theorem tailTrace_7471393 : CollatzResearch.WordTrace tailWord_7471393 prefixEnd_7471393 426268418626399097136355 := by
  unfold tailWord_7471393
  simp only [CollatzResearch.WordTrace]
  refine ⟨272504089821426648180978833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181669393214284432120652555 272504089821426648180978833)
  ·
    refine ⟨204378067366069986135734125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272504089821426648180978833 204378067366069986135734125)
    ·
      refine ⟨76641775262276244800900297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204378067366069986135734125 76641775262276244800900297)
      ·
        refine ⟨57481331446707183600675223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76641775262276244800900297 57481331446707183600675223)
        ·
          refine ⟨86221997170060775401012835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57481331446707183600675223 86221997170060775401012835)
          ·
            refine ⟨129332995755091163101519253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86221997170060775401012835 129332995755091163101519253)
            ·
              refine ⟨6062484176019898270383715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129332995755091163101519253 6062484176019898270383715)
              ·
                refine ⟨9093726264029847405575573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062484176019898270383715 9093726264029847405575573)
                ·
                  refine ⟨426268418626399097136355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9093726264029847405575573 426268418626399097136355)
                  ·
                    rfl

theorem cell23_7471393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 6].length) (baseStart_7471393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471393 prefixEnd_7471393 := by exact prefixLift 7471393
  have htrace : WordTrace (prefixWord ++ tailWord_7471393) baseStart_7471393 baseEnd_7471393 := by
    simpa [prefixWord, tailWord_7471393, baseEnd_7471393] using wordTrace_append hprefix tailTrace_7471393
  have hstable : (prefixWord ++ tailWord_7471393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471393).length < 2 ^ (prefixWord ++ tailWord_7471393).sum := by decide
  have hdescent : baseEnd_7471393 < baseStart_7471393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471436 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_7471436 : Nat := 118140960795 + 7471436 * 2 ^ 59
def prefixEnd_7471436 : Nat := 4983230072969 + 3 ^ 40 * 7471436 * 2
def baseEnd_7471436 : Nat := 1278812615768578401996499

theorem tailTrace_7471436 : CollatzResearch.WordTrace tailWord_7471436 prefixEnd_7471436 1278812615768578401996499 := by
  unfold tailWord_7471436
  simp only [CollatzResearch.WordTrace]
  refine ⟨136252829080135433262397081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181670438773513911016529441 136252829080135433262397081)
  ·
    refine ⟨102189621810101574946797811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136252829080135433262397081 102189621810101574946797811)
    ·
      refine ⟨153284432715152362420196717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102189621810101574946797811 153284432715152362420196717)
      ·
        refine ⟨57481662268182135907573769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153284432715152362420196717 57481662268182135907573769)
        ·
          refine ⟨43111246701136601930680327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57481662268182135907573769 43111246701136601930680327)
          ·
            refine ⟨64666870051704902896020491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43111246701136601930680327 64666870051704902896020491)
            ·
              refine ⟨97000305077557354344030737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64666870051704902896020491 97000305077557354344030737)
              ·
                refine ⟨72750228808168015758023053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97000305077557354344030737 72750228808168015758023053)
                ·
                  refine ⟨27281335803063005909258645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72750228808168015758023053 27281335803063005909258645)
                  ·
                    refine ⟨1278812615768578401996499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27281335803063005909258645 1278812615768578401996499)
                    ·
                      rfl

theorem cell23_7471436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_7471436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471436 prefixEnd_7471436 := by exact prefixLift 7471436
  have htrace : WordTrace (prefixWord ++ tailWord_7471436) baseStart_7471436 baseEnd_7471436 := by
    simpa [prefixWord, tailWord_7471436, baseEnd_7471436] using wordTrace_append hprefix tailTrace_7471436
  have hstable : (prefixWord ++ tailWord_7471436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471436).length < 2 ^ (prefixWord ++ tailWord_7471436).sum := by decide
  have hdescent : baseEnd_7471436 < baseStart_7471436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471477 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7471477 : Nat := 118140960795 + 7471477 * 2 ^ 59
def prefixEnd_7471477 : Nat := 4983230072969 + 3 ^ 40 * 7471477 * 2
def baseEnd_7471477 : Nat := 3836458900012569545576809

theorem tailTrace_7471477 : CollatzResearch.WordTrace tailWord_7471477 prefixEnd_7471477 3836458900012569545576809 := by
  unfold tailWord_7471477
  simp only [CollatzResearch.WordTrace]
  refine ⟨272507153553122330527036685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181671435702081553684691123 272507153553122330527036685)
  ·
    refine ⟨102190182582420873947638757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272507153553122330527036685 102190182582420873947638757)
    ·
      refine ⟨19160659234203913865182267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102190182582420873947638757 19160659234203913865182267)
      ·
        refine ⟨28740988851305870797773401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19160659234203913865182267 28740988851305870797773401)
        ·
          refine ⟨21555741638479403098330051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28740988851305870797773401 21555741638479403098330051)
          ·
            refine ⟨32333612457719104647495077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21555741638479403098330051 32333612457719104647495077)
            ·
              refine ⟨6062552335822332121405327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32333612457719104647495077 6062552335822332121405327)
              ·
                refine ⟨9093828503733498182107991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062552335822332121405327 9093828503733498182107991)
                ·
                  refine ⟨13640742755600247273161987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9093828503733498182107991 13640742755600247273161987)
                  ·
                    refine ⟨20461114133400370909742981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13640742755600247273161987 20461114133400370909742981)
                    ·
                      refine ⟨3836458900012569545576809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20461114133400370909742981 3836458900012569545576809)
                      ·
                        rfl

theorem cell23_7471477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7471477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471477 prefixEnd_7471477 := by exact prefixLift 7471477
  have htrace : WordTrace (prefixWord ++ tailWord_7471477) baseStart_7471477 baseEnd_7471477 := by
    simpa [prefixWord, tailWord_7471477, baseEnd_7471477] using wordTrace_append hprefix tailTrace_7471477
  have hstable : (prefixWord ++ tailWord_7471477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471477).length < 2 ^ (prefixWord ++ tailWord_7471477).sum := by decide
  have hdescent : baseEnd_7471477 < baseStart_7471477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471517 : List Nat := [1, 4, 2, 1, 5, 1, 2, 7]
def baseStart_7471517 : Nat := 118140960795 + 7471517 * 2 ^ 59
def prefixEnd_7471517 : Nat := 4983230072969 + 3 ^ 40 * 7471517 * 2
def baseEnd_7471517 : Nat := 142091831082916644039875

theorem tailTrace_7471517 : CollatzResearch.WordTrace tailWord_7471517 prefixEnd_7471517 142091831082916644039875 := by
  unfold tailWord_7471517
  simp only [CollatzResearch.WordTrace]
  refine ⟨272508612472977417358492805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181672408315318278238995203 272508612472977417358492805)
  ·
    refine ⟨51095364838683265754717401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272508612472977417358492805 51095364838683265754717401)
    ·
      refine ⟨38321523629012449316038051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51095364838683265754717401 38321523629012449316038051)
      ·
        refine ⟨57482285443518673974057077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38321523629012449316038051 57482285443518673974057077)
        ·
          refine ⟨5388964260329875685067851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57482285443518673974057077 5388964260329875685067851)
          ·
            refine ⟨8083446390494813527601777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5388964260329875685067851 8083446390494813527601777)
            ·
              refine ⟨6062584792871110145701333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8083446390494813527601777 6062584792871110145701333)
              ·
                refine ⟨142091831082916644039875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6062584792871110145701333 142091831082916644039875)
                ·
                  rfl

theorem cell23_7471517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 7].length) (baseStart_7471517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471517 prefixEnd_7471517 := by exact prefixLift 7471517
  have htrace : WordTrace (prefixWord ++ tailWord_7471517) baseStart_7471517 baseEnd_7471517 := by
    simpa [prefixWord, tailWord_7471517, baseEnd_7471517] using wordTrace_append hprefix tailTrace_7471517
  have hstable : (prefixWord ++ tailWord_7471517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471517).length < 2 ^ (prefixWord ++ tailWord_7471517).sum := by decide
  have hdescent : baseEnd_7471517 < baseStart_7471517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471528 : List Nat := [2, 1, 6, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7471528 : Nat := 118140960795 + 7471528 * 2 ^ 59
def prefixEnd_7471528 : Nat := 4983230072969 + 3 ^ 40 * 7471528 * 2
def baseEnd_7471528 : Nat := 3836485087525948846039075

theorem tailTrace_7471528 : CollatzResearch.WordTrace tailWord_7471528 prefixEnd_7471528 3836485087525948846039075 := by
  unfold tailWord_7471528
  simp only [CollatzResearch.WordTrace]
  refine ⟨136254506837968783118571619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181672675783958377491428825 136254506837968783118571619)
  ·
    refine ⟨204381760256953174677857429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136254506837968783118571619 204381760256953174677857429)
    ·
      refine ⟨9580395012044680063024567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 204381760256953174677857429 9580395012044680063024567)
      ·
        refine ⟨14370592518067020094536851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9580395012044680063024567 14370592518067020094536851)
        ·
          refine ⟨21555888777100530141805277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14370592518067020094536851 21555888777100530141805277)
          ·
            refine ⟨8083458291412698803176979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21555888777100530141805277 8083458291412698803176979)
            ·
              refine ⟨12125187437119048204765469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8083458291412698803176979 12125187437119048204765469)
              ·
                refine ⟨4546945288919643076787051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12125187437119048204765469 4546945288919643076787051)
                ·
                  refine ⟨6820417933379464615180577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4546945288919643076787051 6820417933379464615180577)
                  ·
                    refine ⟨5115313450034598461385433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6820417933379464615180577 5115313450034598461385433)
                    ·
                      refine ⟨3836485087525948846039075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5115313450034598461385433 3836485087525948846039075)
                      ·
                        rfl

theorem cell23_7471528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7471528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471528 prefixEnd_7471528 := by exact prefixLift 7471528
  have htrace : WordTrace (prefixWord ++ tailWord_7471528) baseStart_7471528 baseEnd_7471528 := by
    simpa [prefixWord, tailWord_7471528, baseEnd_7471528] using wordTrace_append hprefix tailTrace_7471528
  have hstable : (prefixWord ++ tailWord_7471528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471528).length < 2 ^ (prefixWord ++ tailWord_7471528).sum := by decide
  have hdescent : baseEnd_7471528 < baseStart_7471528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471537 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 1, 3, 2]
def baseStart_7471537 : Nat := 118140960795 + 7471537 * 2 ^ 59
def prefixEnd_7471537 : Nat := 4983230072969 + 3 ^ 40 * 7471537 * 2
def baseEnd_7471537 : Nat := 3836489708851839310826533

theorem tailTrace_7471537 : CollatzResearch.WordTrace tailWord_7471537 prefixEnd_7471537 3836489708851839310826533 := by
  unfold tailWord_7471537
  simp only [CollatzResearch.WordTrace]
  refine ⟨272509341932904960774220865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181672894621936640516147243 272509341932904960774220865)
  ·
    refine ⟨204382006449678720580665649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272509341932904960774220865 204382006449678720580665649)
    ·
      refine ⟨153286504837259040435499237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204382006449678720580665649 153286504837259040435499237)
      ·
        refine ⟨28741219656986070081656107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153286504837259040435499237 28741219656986070081656107)
        ·
          refine ⟨43111829485479105122484161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28741219656986070081656107 43111829485479105122484161)
          ·
            refine ⟨32333872114109328841863121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43111829485479105122484161 32333872114109328841863121)
            ·
              refine ⟨24250404085581996631397341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32333872114109328841863121 24250404085581996631397341)
              ·
                refine ⟨9093901532093248736774003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24250404085581996631397341 9093901532093248736774003)
                ·
                  refine ⟨13640852298139873105161005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9093901532093248736774003 13640852298139873105161005)
                  ·
                    refine ⟨5115319611802452414435377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13640852298139873105161005 5115319611802452414435377)
                    ·
                      refine ⟨3836489708851839310826533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5115319611802452414435377 3836489708851839310826533)
                      ·
                        rfl

theorem cell23_7471537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_7471537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471537 prefixEnd_7471537 := by exact prefixLift 7471537
  have htrace : WordTrace (prefixWord ++ tailWord_7471537) baseStart_7471537 baseEnd_7471537 := by
    simpa [prefixWord, tailWord_7471537, baseEnd_7471537] using wordTrace_append hprefix tailTrace_7471537
  have hstable : (prefixWord ++ tailWord_7471537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471537).length < 2 ^ (prefixWord ++ tailWord_7471537).sum := by decide
  have hdescent : baseEnd_7471537 < baseStart_7471537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471603 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 2, 5]
def baseStart_7471603 : Nat := 118140960795 + 7471603 * 2 ^ 59
def prefixEnd_7471603 : Nat := 4983230072969 + 3 ^ 40 * 7471603 * 2
def baseEnd_7471603 : Nat := 1278841199525012017533743

theorem tailTrace_7471603 : CollatzResearch.WordTrace tailWord_7471603 prefixEnd_7471603 1278841199525012017533743 := by
  unfold tailWord_7471603
  simp only [CollatzResearch.WordTrace]
  refine ⟨272511749150665854046123463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181674499433777236030748975 272511749150665854046123463)
  ·
    refine ⟨408767623725998781069185195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272511749150665854046123463 408767623725998781069185195)
    ·
      refine ⟨613151435588998171603777793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408767623725998781069185195 613151435588998171603777793)
      ·
        refine ⟨459863576691748628702833345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613151435588998171603777793 459863576691748628702833345)
        ·
          refine ⟨344897682518811471527125009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459863576691748628702833345 344897682518811471527125009)
          ·
            refine ⟨258673261889108603645343757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344897682518811471527125009 258673261889108603645343757)
            ·
              refine ⟨97002473208415726367003909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258673261889108603645343757 97002473208415726367003909)
              ·
                refine ⟨18187963726577948693813233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97002473208415726367003909 18187963726577948693813233)
                ·
                  refine ⟨13640972794933461520359925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18187963726577948693813233 13640972794933461520359925)
                  ·
                    refine ⟨1278841199525012017533743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13640972794933461520359925 1278841199525012017533743)
                    ·
                      rfl

theorem cell23_7471603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 5].length) (baseStart_7471603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471603 prefixEnd_7471603 := by exact prefixLift 7471603
  have htrace : WordTrace (prefixWord ++ tailWord_7471603) baseStart_7471603 baseEnd_7471603 := by
    simpa [prefixWord, tailWord_7471603, baseEnd_7471603] using wordTrace_append hprefix tailTrace_7471603
  have hstable : (prefixWord ++ tailWord_7471603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471603).length < 2 ^ (prefixWord ++ tailWord_7471603).sum := by decide
  have hdescent : baseEnd_7471603 < baseStart_7471603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471613 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_7471613 : Nat := 118140960795 + 7471613 * 2 ^ 59
def prefixEnd_7471613 : Nat := 4983230072969 + 3 ^ 40 * 7471613 * 2
def baseEnd_7471613 : Nat := 3836528733381581013476183

theorem tailTrace_7471613 : CollatzResearch.WordTrace tailWord_7471613 prefixEnd_7471613 3836528733381581013476183 := by
  unfold tailWord_7471613
  simp only [CollatzResearch.WordTrace]
  refine ⟨272512113880629625753987493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181674742587086417169324995 272512113880629625753987493)
  ·
    refine ⟨51096021352618054828872655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272512113880629625753987493 51096021352618054828872655)
    ·
      refine ⟨76644032028927082243308983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51096021352618054828872655 76644032028927082243308983)
      ·
        refine ⟨114966048043390623364963475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76644032028927082243308983 114966048043390623364963475)
        ·
          refine ⟨172449072065085935047445213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114966048043390623364963475 172449072065085935047445213)
          ·
            refine ⟨64668402024407225642791955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172449072065085935047445213 64668402024407225642791955)
            ·
              refine ⟨97002603036610838464187933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64668402024407225642791955 97002603036610838464187933)
              ·
                refine ⟨36375976138729064424070475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97002603036610838464187933 36375976138729064424070475)
                ·
                  refine ⟨54563964208093596636105713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36375976138729064424070475 54563964208093596636105713)
                  ·
                    refine ⟨40922973156070197477079285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54563964208093596636105713 40922973156070197477079285)
                    ·
                      refine ⟨3836528733381581013476183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40922973156070197477079285 3836528733381581013476183)
                      ·
                        rfl

theorem cell23_7471613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_7471613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471613 prefixEnd_7471613 := by exact prefixLift 7471613
  have htrace : WordTrace (prefixWord ++ tailWord_7471613) baseStart_7471613 baseEnd_7471613 := by
    simpa [prefixWord, tailWord_7471613, baseEnd_7471613] using wordTrace_append hprefix tailTrace_7471613
  have hstable : (prefixWord ++ tailWord_7471613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471613).length < 2 ^ (prefixWord ++ tailWord_7471613).sum := by decide
  have hdescent : baseEnd_7471613 < baseStart_7471613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471640 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_7471640 : Nat := 118140960795 + 7471640 * 2 ^ 59
def prefixEnd_7471640 : Nat := 4983230072969 + 3 ^ 40 * 7471640 * 2
def baseEnd_7471640 : Nat := 3836542597359252407838559

theorem tailTrace_7471640 : CollatzResearch.WordTrace tailWord_7471640 prefixEnd_7471640 3836542597359252407838559 := by
  unfold tailWord_7471640
  simp only [CollatzResearch.WordTrace]
  refine ⟨136256549325765904682610187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181675399101021206243480249 136256549325765904682610187)
  ·
    refine ⟨204384823988648857023915281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136256549325765904682610187 204384823988648857023915281)
    ·
      refine ⟨153288617991486642767936461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204384823988648857023915281 153288617991486642767936461)
      ·
        refine ⟨57483231746807491037976173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153288617991486642767936461 57483231746807491037976173)
        ·
          refine ⟨21556211905052809139241065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57483231746807491037976173 21556211905052809139241065)
          ·
            refine ⟨16167158928789606854430799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21556211905052809139241065 16167158928789606854430799)
            ·
              refine ⟨24250738393184410281646199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16167158928789606854430799 24250738393184410281646199)
              ·
                refine ⟨36376107589776615422469299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24250738393184410281646199 36376107589776615422469299)
                ·
                  refine ⟨54564161384664923133703949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36376107589776615422469299 54564161384664923133703949)
                  ·
                    refine ⟨20461560519249346175138981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54564161384664923133703949 20461560519249346175138981)
                    ·
                      refine ⟨3836542597359252407838559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20461560519249346175138981 3836542597359252407838559)
                      ·
                        rfl

theorem cell23_7471640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_7471640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471640 prefixEnd_7471640 := by exact prefixLift 7471640
  have htrace : WordTrace (prefixWord ++ tailWord_7471640) baseStart_7471640 baseEnd_7471640 := by
    simpa [prefixWord, tailWord_7471640, baseEnd_7471640] using wordTrace_append hprefix tailTrace_7471640
  have hstable : (prefixWord ++ tailWord_7471640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471640).length < 2 ^ (prefixWord ++ tailWord_7471640).sum := by decide
  have hdescent : baseEnd_7471640 < baseStart_7471640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471650 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_7471650 : Nat := 118140960795 + 7471650 * 2 ^ 59
def prefixEnd_7471650 : Nat := 4983230072969 + 3 ^ 40 * 7471650 * 2
def baseEnd_7471650 : Nat := 1278849244055265789571171

theorem tailTrace_7471650 : CollatzResearch.WordTrace tailWord_7471650 prefixEnd_7471650 1278849244055265789571171 := by
  unfold tailWord_7471650
  simp only [CollatzResearch.WordTrace]
  refine ⟨68128365845373895268271101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181675642254330387382056269 68128365845373895268271101)
  ·
    refine ⟨25548137192015210725601663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68128365845373895268271101 25548137192015210725601663)
    ·
      refine ⟨38322205788022816088402495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25548137192015210725601663 38322205788022816088402495)
      ·
        refine ⟨57483308682034224132603743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38322205788022816088402495 57483308682034224132603743)
        ·
          refine ⟨86224963023051336198905615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57483308682034224132603743 86224963023051336198905615)
          ·
            refine ⟨129337444534577004298358423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86224963023051336198905615 129337444534577004298358423)
            ·
              refine ⟨194006166801865506447537635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129337444534577004298358423 194006166801865506447537635)
              ·
                refine ⟨291009250202798259671306453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194006166801865506447537635 291009250202798259671306453)
                ·
                  refine ⟨6820529301628084211046245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 291009250202798259671306453 6820529301628084211046245)
                  ·
                    refine ⟨1278849244055265789571171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6820529301628084211046245 1278849244055265789571171)
                    ·
                      rfl

theorem cell23_7471650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_7471650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471650 prefixEnd_7471650 := by exact prefixLift 7471650
  have htrace : WordTrace (prefixWord ++ tailWord_7471650) baseStart_7471650 baseEnd_7471650 := by
    simpa [prefixWord, tailWord_7471650, baseEnd_7471650] using wordTrace_append hprefix tailTrace_7471650
  have hstable : (prefixWord ++ tailWord_7471650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471650).length < 2 ^ (prefixWord ++ tailWord_7471650).sum := by decide
  have hdescent : baseEnd_7471650 < baseStart_7471650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471653 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_7471653 : Nat := 118140960795 + 7471653 * 2 ^ 59
def prefixEnd_7471653 : Nat := 4983230072969 + 3 ^ 40 * 7471653 * 2
def baseEnd_7471653 : Nat := 3836549272607760856975999

theorem tailTrace_7471653 : CollatzResearch.WordTrace tailWord_7471653 prefixEnd_7471653 3836549272607760856975999 := by
  unfold tailWord_7471653
  simp only [CollatzResearch.WordTrace]
  refine ⟨272513572800484712585443613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181675715200323141723629075 272513572800484712585443613)
  ·
    refine ⟨102192589800181767219541355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272513572800484712585443613 102192589800181767219541355)
    ·
      refine ⟨153288884700272650829312033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102192589800181767219541355 153288884700272650829312033)
      ·
        refine ⟨114966663525204488121984025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153288884700272650829312033 114966663525204488121984025)
        ·
          refine ⟨86224997643903366091488019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114966663525204488121984025 86224997643903366091488019)
          ·
            refine ⟨129337496465855049137232029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86224997643903366091488019 129337496465855049137232029)
            ·
              refine ⟨48501561174695643426462011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129337496465855049137232029 48501561174695643426462011)
              ·
                refine ⟨72752341762043465139693017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48501561174695643426462011 72752341762043465139693017)
                ·
                  refine ⟨54564256321532598854769763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72752341762043465139693017 54564256321532598854769763)
                  ·
                    refine ⟨81846384482298898282154645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54564256321532598854769763 81846384482298898282154645)
                    ·
                      refine ⟨3836549272607760856975999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81846384482298898282154645 3836549272607760856975999)
                      ·
                        rfl

theorem cell23_7471653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_7471653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471653 prefixEnd_7471653 := by exact prefixLift 7471653
  have htrace : WordTrace (prefixWord ++ tailWord_7471653) baseStart_7471653 baseEnd_7471653 := by
    simpa [prefixWord, tailWord_7471653, baseEnd_7471653] using wordTrace_append hprefix tailTrace_7471653
  have hstable : (prefixWord ++ tailWord_7471653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471653).length < 2 ^ (prefixWord ++ tailWord_7471653).sum := by decide
  have hdescent : baseEnd_7471653 < baseStart_7471653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471660 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_7471660 : Nat := 118140960795 + 7471660 * 2 ^ 59
def prefixEnd_7471660 : Nat := 4983230072969 + 3 ^ 40 * 7471660 * 2
def baseEnd_7471660 : Nat := 3836552866972342329588467

theorem tailTrace_7471660 : CollatzResearch.WordTrace tailWord_7471660 prefixEnd_7471660 3836552866972342329588467 := by
  unfold tailWord_7471660
  simp only [CollatzResearch.WordTrace]
  refine ⟨136256914055729676390474217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181675885407639568520632289 136256914055729676390474217)
  ·
    refine ⟨102192685541797257292855663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136256914055729676390474217 102192685541797257292855663)
    ·
      refine ⟨153289028312695885939283495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102192685541797257292855663 153289028312695885939283495)
      ·
        refine ⟨229933542469043828908925243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153289028312695885939283495 229933542469043828908925243)
        ·
          refine ⟨344900313703565743363387865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229933542469043828908925243 344900313703565743363387865)
          ·
            refine ⟨258675235277674307522540899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344900313703565743363387865 258675235277674307522540899)
            ·
              refine ⟨388012852916511461283811349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258675235277674307522540899 388012852916511461283811349)
              ·
                refine ⟨18188102480461474747678657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388012852916511461283811349 18188102480461474747678657)
                ·
                  refine ⟨13641076860346106060758993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18188102480461474747678657 13641076860346106060758993)
                  ·
                    refine ⟨10230807645259579545569245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13641076860346106060758993 10230807645259579545569245)
                    ·
                      refine ⟨3836552866972342329588467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10230807645259579545569245 3836552866972342329588467)
                      ·
                        rfl

theorem cell23_7471660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_7471660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471660 prefixEnd_7471660 := by exact prefixLift 7471660
  have htrace : WordTrace (prefixWord ++ tailWord_7471660) baseStart_7471660 baseEnd_7471660 := by
    simpa [prefixWord, tailWord_7471660, baseEnd_7471660] using wordTrace_append hprefix tailTrace_7471660
  have hstable : (prefixWord ++ tailWord_7471660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471660).length < 2 ^ (prefixWord ++ tailWord_7471660).sum := by decide
  have hdescent : baseEnd_7471660 < baseStart_7471660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471667 : List Nat := [1, 1, 1, 2, 4, 2, 1, 6, 1, 4]
def baseStart_7471667 : Nat := 118140960795 + 7471667 * 2 ^ 59
def prefixEnd_7471667 : Nat := 4983230072969 + 3 ^ 40 * 7471667 * 2
def baseEnd_7471667 : Nat := 1278852153778974600733645

theorem tailTrace_7471667 : CollatzResearch.WordTrace tailWord_7471667 prefixEnd_7471667 1278852153778974600733645 := by
  unfold tailWord_7471667
  simp only [CollatzResearch.WordTrace]
  refine ⟨272514083422433992976453255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181676055614955995317635503 272514083422433992976453255)
  ·
    refine ⟨408771125133650989464679883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272514083422433992976453255 408771125133650989464679883)
    ·
      refine ⟨613156687700476484197019825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408771125133650989464679883 613156687700476484197019825)
      ·
        refine ⟨459867515775357363147764869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613156687700476484197019825 459867515775357363147764869)
        ·
          refine ⟨86225159207879505590205913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459867515775357363147764869 86225159207879505590205913)
          ·
            refine ⟨64668869405909629192654435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86225159207879505590205913 64668869405909629192654435)
            ·
              refine ⟨97003304108864443788981653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64668869405909629192654435 97003304108864443788981653)
              ·
                refine ⟨4547029880103020802608515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97003304108864443788981653 4547029880103020802608515)
                ·
                  refine ⟨6820544820154531203912773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547029880103020802608515 6820544820154531203912773)
                  ·
                    refine ⟨1278852153778974600733645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6820544820154531203912773 1278852153778974600733645)
                    ·
                      rfl

theorem cell23_7471667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 4].length) (baseStart_7471667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471667 prefixEnd_7471667 := by exact prefixLift 7471667
  have htrace : WordTrace (prefixWord ++ tailWord_7471667) baseStart_7471667 baseEnd_7471667 := by
    simpa [prefixWord, tailWord_7471667, baseEnd_7471667] using wordTrace_append hprefix tailTrace_7471667
  have hstable : (prefixWord ++ tailWord_7471667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471667).length < 2 ^ (prefixWord ++ tailWord_7471667).sum := by decide
  have hdescent : baseEnd_7471667 < baseStart_7471667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471723 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 5, 6]
def baseStart_7471723 : Nat := 118140960795 + 7471723 * 2 ^ 59
def prefixEnd_7471723 : Nat := 4983230072969 + 3 ^ 40 * 7471723 * 2
def baseEnd_7471723 : Nat := 1278861738751191861033559

theorem tailTrace_7471723 : CollatzResearch.WordTrace tailWord_7471723 prefixEnd_7471723 1278861738751191861033559 := by
  unfold tailWord_7471723
  simp only [CollatzResearch.WordTrace]
  refine ⟨272516125910231114540491823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181677417273487409693661215 272516125910231114540491823)
  ·
    refine ⟨408774188865346671810737735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272516125910231114540491823 408774188865346671810737735)
    ·
      refine ⟨613161283298020007716106603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408774188865346671810737735 613161283298020007716106603)
      ·
        refine ⟨919741924947030011574159905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613161283298020007716106603 919741924947030011574159905)
        ·
          refine ⟨689806443710272508680619929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919741924947030011574159905 689806443710272508680619929)
          ·
            refine ⟨517354832782704381510464947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689806443710272508680619929 517354832782704381510464947)
            ·
              refine ⟨776032249174056572265697421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517354832782704381510464947 776032249174056572265697421)
              ·
                refine ⟨291012093440271214599636533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 776032249174056572265697421 291012093440271214599636533)
                ·
                  refine ⟨27282383760025426368715925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291012093440271214599636533 27282383760025426368715925)
                  ·
                    refine ⟨1278861738751191861033559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27282383760025426368715925 1278861738751191861033559)
                    ·
                      rfl

theorem cell23_7471723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 6].length) (baseStart_7471723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471723 prefixEnd_7471723 := by exact prefixLift 7471723
  have htrace : WordTrace (prefixWord ++ tailWord_7471723) baseStart_7471723 baseEnd_7471723 := by
    simpa [prefixWord, tailWord_7471723, baseEnd_7471723] using wordTrace_append hprefix tailTrace_7471723
  have hstable : (prefixWord ++ tailWord_7471723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471723).length < 2 ^ (prefixWord ++ tailWord_7471723).sum := by decide
  have hdescent : baseEnd_7471723 < baseStart_7471723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471724 : List Nat := [2, 2, 1, 1, 3, 1, 2, 6, 1, 1, 3]
def baseStart_7471724 : Nat := 118140960795 + 7471724 * 2 ^ 59
def prefixEnd_7471724 : Nat := 4983230072969 + 3 ^ 40 * 7471724 * 2
def baseEnd_7471724 : Nat := 3836585729734230079188173

theorem tailTrace_7471724 : CollatzResearch.WordTrace tailWord_7471724 prefixEnd_7471724 3836585729734230079188173 := by
  unfold tailWord_7471724
  simp only [CollatzResearch.WordTrace]
  refine ⟨136258081191613745855639113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181677441588818327807518817 136258081191613745855639113)
  ·
    refine ⟨102193560893710309391729335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136258081191613745855639113 102193560893710309391729335)
    ·
      refine ⟨153290341340565464087594003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102193560893710309391729335 153290341340565464087594003)
      ·
        refine ⟨229935512010848196131391005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153290341340565464087594003 229935512010848196131391005)
        ·
          refine ⟨86225817004068073549271627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229935512010848196131391005 86225817004068073549271627)
          ·
            refine ⟨129338725506102110323907441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86225817004068073549271627 129338725506102110323907441)
            ·
              refine ⟨97004044129576582742930581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129338725506102110323907441 97004044129576582742930581)
              ·
                refine ⟨4547064568573902316074871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97004044129576582742930581 4547064568573902316074871)
                ·
                  refine ⟨6820596852860853474112307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547064568573902316074871 6820596852860853474112307)
                  ·
                    refine ⟨10230895279291280211168461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6820596852860853474112307 10230895279291280211168461)
                    ·
                      refine ⟨3836585729734230079188173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10230895279291280211168461 3836585729734230079188173)
                      ·
                        rfl

theorem cell23_7471724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_7471724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471724 prefixEnd_7471724 := by exact prefixLift 7471724
  have htrace : WordTrace (prefixWord ++ tailWord_7471724) baseStart_7471724 baseEnd_7471724 := by
    simpa [prefixWord, tailWord_7471724, baseEnd_7471724] using wordTrace_append hprefix tailTrace_7471724
  have hstable : (prefixWord ++ tailWord_7471724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471724).length < 2 ^ (prefixWord ++ tailWord_7471724).sum := by decide
  have hdescent : baseEnd_7471724 < baseStart_7471724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471747 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 4]
def baseStart_7471747 : Nat := 118140960795 + 7471747 * 2 ^ 59
def prefixEnd_7471747 : Nat := 4983230072969 + 3 ^ 40 * 7471747 * 2
def baseEnd_7471747 : Nat := 3836597539789283489200567

theorem tailTrace_7471747 : CollatzResearch.WordTrace tailWord_7471747 prefixEnd_7471747 3836597539789283489200567 := by
  unfold tailWord_7471747
  simp only [CollatzResearch.WordTrace]
  refine ⟨272517001262144166639365495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181678000841429444426243663 272517001262144166639365495)
  ·
    refine ⟨408775501893216249959048243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272517001262144166639365495 408775501893216249959048243)
    ·
      refine ⟨613163252839824374938572365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408775501893216249959048243 613163252839824374938572365)
      ·
        refine ⟨229936219814934140601964637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613163252839824374938572365 229936219814934140601964637)
        ·
          refine ⟨86226082430600302725736739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229936219814934140601964637 86226082430600302725736739)
          ·
            refine ⟨129339123645900454088605109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86226082430600302725736739 129339123645900454088605109)
            ·
              refine ⟨12125542841803167570806729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129339123645900454088605109 12125542841803167570806729)
              ·
                refine ⟨9094157131352375678105047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12125542841803167570806729 9094157131352375678105047)
                ·
                  refine ⟨13641235697028563517157571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9094157131352375678105047 13641235697028563517157571)
                  ·
                    refine ⟨20461853545542845275736357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13641235697028563517157571 20461853545542845275736357)
                    ·
                      refine ⟨3836597539789283489200567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20461853545542845275736357 3836597539789283489200567)
                      ·
                        rfl

theorem cell23_7471747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_7471747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471747 prefixEnd_7471747 := by exact prefixLift 7471747
  have htrace : WordTrace (prefixWord ++ tailWord_7471747) baseStart_7471747 baseEnd_7471747 := by
    simpa [prefixWord, tailWord_7471747, baseEnd_7471747] using wordTrace_append hprefix tailTrace_7471747
  have hstable : (prefixWord ++ tailWord_7471747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471747).length < 2 ^ (prefixWord ++ tailWord_7471747).sum := by decide
  have hdescent : baseEnd_7471747 < baseStart_7471747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471770 : List Nat := [3, 1, 1, 6, 12]
def baseStart_7471770 : Nat := 118140960795 + 7471770 * 2 ^ 59
def prefixEnd_7471770 : Nat := 4983230072969 + 3 ^ 40 * 7471770 * 2
def baseEnd_7471770 : Nat := 5262838614326936761609

theorem tailTrace_7471770 : CollatzResearch.WordTrace tailWord_7471770 prefixEnd_7471770 5262838614326936761609 := by
  unfold tailWord_7471770
  simp only [CollatzResearch.WordTrace]
  refine ⟨68129460035265210391863191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181678560094040561044968509 68129460035265210391863191)
  ·
    refine ⟨102194190052897815587794787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68129460035265210391863191 102194190052897815587794787)
    ·
      refine ⟨153291285079346723381692181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102194190052897815587794787 153291285079346723381692181)
      ·
        refine ⟨7185528988094377658516821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153291285079346723381692181 7185528988094377658516821)
        ·
          refine ⟨5262838614326936761609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7185528988094377658516821 5262838614326936761609)
          ·
            rfl

theorem cell23_7471770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 12].length) (baseStart_7471770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471770 prefixEnd_7471770 := by exact prefixLift 7471770
  have htrace : WordTrace (prefixWord ++ tailWord_7471770) baseStart_7471770 baseEnd_7471770 := by
    simpa [prefixWord, tailWord_7471770, baseEnd_7471770] using wordTrace_append hprefix tailTrace_7471770
  have hstable : (prefixWord ++ tailWord_7471770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471770).length < 2 ^ (prefixWord ++ tailWord_7471770).sum := by decide
  have hdescent : baseEnd_7471770 < baseStart_7471770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471831 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_7471831 : Nat := 118140960795 + 7471831 * 2 ^ 59
def prefixEnd_7471831 : Nat := 4983230072969 + 3 ^ 40 * 7471831 * 2
def baseEnd_7471831 : Nat := 3836640672164261160550181

theorem tailTrace_7471831 : CollatzResearch.WordTrace tailWord_7471831 prefixEnd_7471831 3836640672164261160550181 := by
  unfold tailWord_7471831
  simp only [CollatzResearch.WordTrace]
  refine ⟨272520064993839848985423347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181680043329226565990282231 272520064993839848985423347)
  ·
    refine ⟨408780097490759773478135021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272520064993839848985423347 408780097490759773478135021)
    ·
      refine ⟨153292536559034915054300633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408780097490759773478135021 153292536559034915054300633)
      ·
        refine ⟨114969402419276186290725475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153292536559034915054300633 114969402419276186290725475)
        ·
          refine ⟨172454103628914279436088213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114969402419276186290725475 172454103628914279436088213)
          ·
            refine ⟨8083786107605356848566635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172454103628914279436088213 8083786107605356848566635)
            ·
              refine ⟨12125679161408035272849953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8083786107605356848566635 12125679161408035272849953)
              ·
                refine ⟨9094259371056026454637465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12125679161408035272849953 9094259371056026454637465)
                ·
                  refine ⟨6820694528292019840978099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9094259371056026454637465 6820694528292019840978099)
                  ·
                    refine ⟨10231041792438029761467149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6820694528292019840978099 10231041792438029761467149)
                    ·
                      refine ⟨3836640672164261160550181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10231041792438029761467149 3836640672164261160550181)
                      ·
                        rfl

theorem cell23_7471831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_7471831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471831 prefixEnd_7471831 := by exact prefixLift 7471831
  have htrace : WordTrace (prefixWord ++ tailWord_7471831) baseStart_7471831 baseEnd_7471831 := by
    simpa [prefixWord, tailWord_7471831, baseEnd_7471831] using wordTrace_append hprefix tailTrace_7471831
  have hstable : (prefixWord ++ tailWord_7471831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471831).length < 2 ^ (prefixWord ++ tailWord_7471831).sum := by decide
  have hdescent : baseEnd_7471831 < baseStart_7471831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471840 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_7471840 : Nat := 118140960795 + 7471840 * 2 ^ 59
def prefixEnd_7471840 : Nat := 4983230072969 + 3 ^ 40 * 7471840 * 2
def baseEnd_7471840 : Nat := 3836645293490151625337639

theorem tailTrace_7471840 : CollatzResearch.WordTrace tailWord_7471840 prefixEnd_7471840 3836645293490151625337639 := by
  unfold tailWord_7471840
  simp only [CollatzResearch.WordTrace]
  refine ⟨136260196625403621761250487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181680262167204829015000649 136260196625403621761250487)
  ·
    refine ⟨204390294938105432641875731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136260196625403621761250487 204390294938105432641875731)
    ·
      refine ⟨306585442407158148962813597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204390294938105432641875731 306585442407158148962813597)
      ·
        refine ⟨114969540902684305861055099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306585442407158148962813597 114969540902684305861055099)
        ·
          refine ⟨172454311354026458791582649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114969540902684305861055099 172454311354026458791582649)
          ·
            refine ⟨129340733515519844093686987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172454311354026458791582649 129340733515519844093686987)
            ·
              refine ⟨194011100273279766140530481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129340733515519844093686987 194011100273279766140530481)
              ·
                refine ⟨145508325204959824605397861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194011100273279766140530481 145508325204959824605397861)
                ·
                  refine ⟨27282810975929967113512099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145508325204959824605397861 27282810975929967113512099)
                  ·
                    refine ⟨40924216463894950670268149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27282810975929967113512099 40924216463894950670268149)
                    ·
                      refine ⟨3836645293490151625337639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40924216463894950670268149 3836645293490151625337639)
                      ·
                        rfl

theorem cell23_7471840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_7471840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471840 prefixEnd_7471840 := by exact prefixLift 7471840
  have htrace : WordTrace (prefixWord ++ tailWord_7471840) baseStart_7471840 baseEnd_7471840 := by
    simpa [prefixWord, tailWord_7471840, baseEnd_7471840] using wordTrace_append hprefix tailTrace_7471840
  have hstable : (prefixWord ++ tailWord_7471840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471840).length < 2 ^ (prefixWord ++ tailWord_7471840).sum := by decide
  have hdescent : baseEnd_7471840 < baseStart_7471840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471848 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_7471848 : Nat := 118140960795 + 7471848 * 2 ^ 59
def prefixEnd_7471848 : Nat := 4983230072969 + 3 ^ 40 * 7471848 * 2
def baseEnd_7471848 : Nat := 3836649401335387594037603

theorem tailTrace_7471848 : CollatzResearch.WordTrace tailWord_7471848 prefixEnd_7471848 3836649401335387594037603 := by
  unfold tailWord_7471848
  simp only [CollatzResearch.WordTrace]
  refine ⟨136260342517389130444396099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181680456689852173925861465 136260342517389130444396099)
  ·
    refine ⟨204390513776083695666594149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136260342517389130444396099 204390513776083695666594149)
    ·
      refine ⟨38323221333015692937486403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204390513776083695666594149 38323221333015692937486403)
      ·
        refine ⟨57484831999523539406229605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38323221333015692937486403 57484831999523539406229605)
        ·
          refine ⟨10778405999910663638668051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57484831999523539406229605 10778405999910663638668051)
          ·
            refine ⟨16167608999865995458002077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10778405999910663638668051 16167608999865995458002077)
            ·
              refine ⟨6062853374949748296750779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16167608999865995458002077 6062853374949748296750779)
              ·
                refine ⟨9094280062424622445126169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062853374949748296750779 9094280062424622445126169)
                ·
                  refine ⟨6820710046818466833844627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9094280062424622445126169 6820710046818466833844627)
                  ·
                    refine ⟨10231065070227700250766941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6820710046818466833844627 10231065070227700250766941)
                    ·
                      refine ⟨3836649401335387594037603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10231065070227700250766941 3836649401335387594037603)
                      ·
                        rfl

theorem cell23_7471848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_7471848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471848 prefixEnd_7471848 := by exact prefixLift 7471848
  have htrace : WordTrace (prefixWord ++ tailWord_7471848) baseStart_7471848 baseEnd_7471848 := by
    simpa [prefixWord, tailWord_7471848, baseEnd_7471848] using wordTrace_append hprefix tailTrace_7471848
  have hstable : (prefixWord ++ tailWord_7471848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471848).length < 2 ^ (prefixWord ++ tailWord_7471848).sum := by decide
  have hdescent : baseEnd_7471848 < baseStart_7471848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471874 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7471874 : Nat := 118140960795 + 7471874 * 2 ^ 59
def prefixEnd_7471874 : Nat := 4983230072969 + 3 ^ 40 * 7471874 * 2
def baseEnd_7471874 : Nat := 3836662751832404492312483

theorem tailTrace_7471874 : CollatzResearch.WordTrace tailWord_7471874 prefixEnd_7471874 3836662751832404492312483 := by
  unfold tailWord_7471874
  simp only [CollatzResearch.WordTrace]
  refine ⟨68130408333171016832309669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181681088888456044886159117 68130408333171016832309669)
  ·
    refine ⟨12774451562469565656058063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68130408333171016832309669 12774451562469565656058063)
    ·
      refine ⟨19161677343704348484087095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12774451562469565656058063 19161677343704348484087095)
      ·
        refine ⟨28742516015556522726130643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19161677343704348484087095 28742516015556522726130643)
        ·
          refine ⟨43113774023334784089195965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28742516015556522726130643 43113774023334784089195965)
          ·
            refine ⟨16167665258750544033448487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43113774023334784089195965 16167665258750544033448487)
            ·
              refine ⟨24251497888125816050172731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16167665258750544033448487 24251497888125816050172731)
              ·
                refine ⟨36377246832188724075259097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24251497888125816050172731 36377246832188724075259097)
                ·
                  refine ⟨27282935124141543056444323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36377246832188724075259097 27282935124141543056444323)
                  ·
                    refine ⟨40924402686212314584666485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27282935124141543056444323 40924402686212314584666485)
                    ·
                      refine ⟨3836662751832404492312483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40924402686212314584666485 3836662751832404492312483)
                      ·
                        rfl

theorem cell23_7471874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7471874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471874 prefixEnd_7471874 := by exact prefixLift 7471874
  have htrace : WordTrace (prefixWord ++ tailWord_7471874) baseStart_7471874 baseEnd_7471874 := by
    simpa [prefixWord, tailWord_7471874, baseEnd_7471874] using wordTrace_append hprefix tailTrace_7471874
  have hstable : (prefixWord ++ tailWord_7471874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471874).length < 2 ^ (prefixWord ++ tailWord_7471874).sum := by decide
  have hdescent : baseEnd_7471874 < baseStart_7471874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471920 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 2, 8]
def baseStart_7471920 : Nat := 118140960795 + 7471920 * 2 ^ 59
def prefixEnd_7471920 : Nat := 4983230072969 + 3 ^ 40 * 7471920 * 2
def baseEnd_7471920 : Nat := 1278895457314170437445757

theorem tailTrace_7471920 : CollatzResearch.WordTrace tailWord_7471920 prefixEnd_7471920 1278895457314170437445757 := by
  unfold tailWord_7471920
  simp only [CollatzResearch.WordTrace]
  refine ⟨136261655545258708592706607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181682207393678278123608809 136261655545258708592706607)
  ·
    refine ⟨204392483317888062889059911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136261655545258708592706607 204392483317888062889059911)
    ·
      refine ⟨306588724976832094333589867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204392483317888062889059911 306588724976832094333589867)
      ·
        refine ⟨459883087465248141500384801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306588724976832094333589867 459883087465248141500384801)
        ·
          refine ⟨344912315598936106125288601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459883087465248141500384801 344912315598936106125288601)
          ·
            refine ⟨258684236699202079593966451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344912315598936106125288601 258684236699202079593966451)
            ·
              refine ⟨388026355048803119390949677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258684236699202079593966451 388026355048803119390949677)
              ·
                refine ⟨145509883143301169771606129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388026355048803119390949677 145509883143301169771606129)
                ·
                  refine ⟨109132412357475877328704597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145509883143301169771606129 109132412357475877328704597)
                  ·
                    refine ⟨1278895457314170437445757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109132412357475877328704597 1278895457314170437445757)
                    ·
                      rfl

theorem cell23_7471920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_7471920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471920 prefixEnd_7471920 := by exact prefixLift 7471920
  have htrace : WordTrace (prefixWord ++ tailWord_7471920) baseStart_7471920 baseEnd_7471920 := by
    simpa [prefixWord, tailWord_7471920, baseEnd_7471920] using wordTrace_append hprefix tailTrace_7471920
  have hstable : (prefixWord ++ tailWord_7471920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471920).length < 2 ^ (prefixWord ++ tailWord_7471920).sum := by decide
  have hdescent : baseEnd_7471920 < baseStart_7471920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471944 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_7471944 : Nat := 118140960795 + 7471944 * 2 ^ 59
def prefixEnd_7471944 : Nat := 4983230072969 + 3 ^ 40 * 7471944 * 2
def baseEnd_7471944 : Nat := 3836698695478219218437161

theorem tailTrace_7471944 : CollatzResearch.WordTrace tailWord_7471944 prefixEnd_7471944 3836698695478219218437161 := by
  unfold tailWord_7471944
  simp only [CollatzResearch.WordTrace]
  refine ⟨136262093221215234642143443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181682790961620312856191257 136262093221215234642143443)
  ·
    refine ⟨204393139831822851963215165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136262093221215234642143443 204393139831822851963215165)
    ·
      refine ⟨76647427436933569486205687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204393139831822851963215165 76647427436933569486205687)
      ·
        refine ⟨114971141155400354229308531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76647427436933569486205687 114971141155400354229308531)
        ·
          refine ⟨172456711733100531343962797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114971141155400354229308531 172456711733100531343962797)
          ·
            refine ⟨64671266899912699253986049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172456711733100531343962797 64671266899912699253986049)
            ·
              refine ⟨48503450174934524440489537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64671266899912699253986049 48503450174934524440489537)
              ·
                refine ⟨36377587631200893330367153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48503450174934524440489537 36377587631200893330367153)
                ·
                  refine ⟨27283190723400669997775365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36377587631200893330367153 27283190723400669997775365)
                  ·
                    refine ⟨5115598260637625624582881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27283190723400669997775365 5115598260637625624582881)
                    ·
                      refine ⟨3836698695478219218437161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5115598260637625624582881 3836698695478219218437161)
                      ·
                        rfl

theorem cell23_7471944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_7471944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471944 prefixEnd_7471944 := by exact prefixLift 7471944
  have htrace : WordTrace (prefixWord ++ tailWord_7471944) baseStart_7471944 baseEnd_7471944 := by
    simpa [prefixWord, tailWord_7471944, baseEnd_7471944] using wordTrace_append hprefix tailTrace_7471944
  have hstable : (prefixWord ++ tailWord_7471944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471944).length < 2 ^ (prefixWord ++ tailWord_7471944).sum := by decide
  have hdescent : baseEnd_7471944 < baseStart_7471944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471954 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_7471954 : Nat := 118140960795 + 7471954 * 2 ^ 59
def prefixEnd_7471954 : Nat := 4983230072969 + 3 ^ 40 * 7471954 * 2
def baseEnd_7471954 : Nat := 1278901276761588059770705

theorem tailTrace_7471954 : CollatzResearch.WordTrace tailWord_7471954 prefixEnd_7471954 1278901276761588059770705 := by
  unfold tailWord_7471954
  simp only [CollatzResearch.WordTrace]
  refine ⟨68131137793098560248037729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181683034114929493994767277 68131137793098560248037729)
  ·
    refine ⟨51098353344823920186028297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68131137793098560248037729 51098353344823920186028297)
    ·
      refine ⟨38323765008617940139521223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51098353344823920186028297 38323765008617940139521223)
      ·
        refine ⟨57485647512926910209281835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38323765008617940139521223 57485647512926910209281835)
        ·
          refine ⟨86228471269390365313922753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57485647512926910209281835 86228471269390365313922753)
          ·
            refine ⟨64671353452042773985442065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86228471269390365313922753 64671353452042773985442065)
            ·
              refine ⟨48503515089032080489081549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64671353452042773985442065 48503515089032080489081549)
              ·
                refine ⟨18188818158387030183405581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48503515089032080489081549 18188818158387030183405581)
                ·
                  refine ⟨6820806809395136318777093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18188818158387030183405581 6820806809395136318777093)
                  ·
                    refine ⟨1278901276761588059770705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6820806809395136318777093 1278901276761588059770705)
                    ·
                      rfl

theorem cell23_7471954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_7471954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471954 prefixEnd_7471954 := by exact prefixLift 7471954
  have htrace : WordTrace (prefixWord ++ tailWord_7471954) baseStart_7471954 baseEnd_7471954 := by
    simpa [prefixWord, tailWord_7471954, baseEnd_7471954] using wordTrace_append hprefix tailTrace_7471954
  have hstable : (prefixWord ++ tailWord_7471954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471954).length < 2 ^ (prefixWord ++ tailWord_7471954).sum := by decide
  have hdescent : baseEnd_7471954 < baseStart_7471954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471967 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 6]
def baseStart_7471967 : Nat := 118140960795 + 7471967 * 2 ^ 59
def prefixEnd_7471967 : Nat := 4983230072969 + 3 ^ 40 * 7471967 * 2
def baseEnd_7471967 : Nat := 426301167281474736494395

theorem tailTrace_7471967 : CollatzResearch.WordTrace tailWord_7471967 prefixEnd_7471967 426301167281474736494395 := by
  unfold tailWord_7471967
  simp only [CollatzResearch.WordTrace]
  refine ⟨272525025321347144212374155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181683350214231429474916103 272525025321347144212374155)
  ·
    refine ⟨408787537982020716318561233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272525025321347144212374155 408787537982020716318561233)
    ·
      refine ⟨306590653486515537238920925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408787537982020716318561233 306590653486515537238920925)
      ·
        refine ⟨114971495057443326464595347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306590653486515537238920925 114971495057443326464595347)
        ·
          refine ⟨172457242586164989696893021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114971495057443326464595347 172457242586164989696893021)
          ·
            refine ⟨64671465969811871136334883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172457242586164989696893021 64671465969811871136334883)
            ·
              refine ⟨97007198954717806704502325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64671465969811871136334883 97007198954717806704502325)
              ·
                refine ⟨9094424902004794378547093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97007198954717806704502325 9094424902004794378547093)
                ·
                  refine ⟨426301167281474736494395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9094424902004794378547093 426301167281474736494395)
                  ·
                    rfl

theorem cell23_7471967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 6].length) (baseStart_7471967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471967 prefixEnd_7471967 := by exact prefixLift 7471967
  have htrace : WordTrace (prefixWord ++ tailWord_7471967) baseStart_7471967 baseEnd_7471967 := by
    simpa [prefixWord, tailWord_7471967, baseEnd_7471967] using wordTrace_append hprefix tailTrace_7471967
  have hstable : (prefixWord ++ tailWord_7471967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471967).length < 2 ^ (prefixWord ++ tailWord_7471967).sum := by decide
  have hdescent : baseEnd_7471967 < baseStart_7471967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7471994 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_7471994 : Nat := 118140960795 + 7471994 * 2 ^ 59
def prefixEnd_7471994 : Nat := 4983230072969 + 3 ^ 40 * 7471994 * 2
def baseEnd_7471994 : Nat := 3836724369510944022811931

theorem tailTrace_7471994 : CollatzResearch.WordTrace tailWord_7471994 prefixEnd_7471994 3836724369510944022811931 := by
  unfold tailWord_7471994
  simp only [CollatzResearch.WordTrace]
  refine ⟨68131502523062331955901759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181684006728166218549071357 68131502523062331955901759)
  ·
    refine ⟨102197253784593497933852639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68131502523062331955901759 102197253784593497933852639)
    ·
      refine ⟨153295880676890246900778959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102197253784593497933852639 153295880676890246900778959)
      ·
        refine ⟨229943821015335370351168439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153295880676890246900778959 229943821015335370351168439)
        ·
          refine ⟨344915731523003055526752659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229943821015335370351168439 344915731523003055526752659)
          ·
            refine ⟨517373597284504583290128989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344915731523003055526752659 517373597284504583290128989)
            ·
              refine ⟨194015098981689218733798371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517373597284504583290128989 194015098981689218733798371)
              ·
                refine ⟨291022648472533828100697557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194015098981689218733798371 291022648472533828100697557)
                ·
                  refine ⟨6820843323575011596110099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 291022648472533828100697557 6820843323575011596110099)
                  ·
                    refine ⟨10231264985362517394165149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6820843323575011596110099 10231264985362517394165149)
                    ·
                      refine ⟨3836724369510944022811931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10231264985362517394165149 3836724369510944022811931)
                      ·
                        rfl

theorem cell23_7471994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_7471994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7471994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7471994 prefixEnd_7471994 := by exact prefixLift 7471994
  have htrace : WordTrace (prefixWord ++ tailWord_7471994) baseStart_7471994 baseEnd_7471994 := by
    simpa [prefixWord, tailWord_7471994, baseEnd_7471994] using wordTrace_append hprefix tailTrace_7471994
  have hstable : (prefixWord ++ tailWord_7471994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7471994).length < 2 ^ (prefixWord ++ tailWord_7471994).sum := by decide
  have hdescent : baseEnd_7471994 < baseStart_7471994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7471994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472018 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 6]
def baseStart_7472018 : Nat := 118140960795 + 7472018 * 2 ^ 59
def prefixEnd_7472018 : Nat := 4983230072969 + 3 ^ 40 * 7472018 * 2
def baseEnd_7472018 : Nat := 426304077005183547656869

theorem tailTrace_7472018 : CollatzResearch.WordTrace tailWord_7472018 prefixEnd_7472018 426304077005183547656869 := by
  unfold tailWord_7472018
  simp only [CollatzResearch.WordTrace]
  refine ⟨68131721361040594980620177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181684590296108253281653805 68131721361040594980620177)
  ·
    refine ⟨51098791020780446235465133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68131721361040594980620177 51098791020780446235465133)
    ·
      refine ⟨19162046632792667338299425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51098791020780446235465133 19162046632792667338299425)
      ·
        refine ⟨14371534974594500503724569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19162046632792667338299425 14371534974594500503724569)
        ·
          refine ⟨10778651230945875377793427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14371534974594500503724569 10778651230945875377793427)
          ·
            refine ⟨16167976846418813066690141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10778651230945875377793427 16167976846418813066690141)
            ·
              refine ⟨6062991317407054900008803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16167976846418813066690141 6062991317407054900008803)
              ·
                refine ⟨9094486976110582350013205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6062991317407054900008803 9094486976110582350013205)
                ·
                  refine ⟨426304077005183547656869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9094486976110582350013205 426304077005183547656869)
                  ·
                    rfl

theorem cell23_7472018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_7472018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472018 prefixEnd_7472018 := by exact prefixLift 7472018
  have htrace : WordTrace (prefixWord ++ tailWord_7472018) baseStart_7472018 baseEnd_7472018 := by
    simpa [prefixWord, tailWord_7472018, baseEnd_7472018] using wordTrace_append hprefix tailTrace_7472018
  have hstable : (prefixWord ++ tailWord_7472018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472018).length < 2 ^ (prefixWord ++ tailWord_7472018).sum := by decide
  have hdescent : baseEnd_7472018 < baseStart_7472018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472031 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 1, 5]
def baseStart_7472031 : Nat := 118140960795 + 7472031 * 2 ^ 59
def prefixEnd_7472031 : Nat := 4983230072969 + 3 ^ 40 * 7472031 * 2
def baseEnd_7472031 : Nat := 1278914456098386792683087

theorem tailTrace_7472031 : CollatzResearch.WordTrace tailWord_7472031 prefixEnd_7472031 1278914456098386792683087 := by
  unfold tailWord_7472031
  simp only [CollatzResearch.WordTrace]
  refine ⟨272527359593115283142703947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181684906395410188761802631 272527359593115283142703947)
  ·
    refine ⟨408791039389672924714055921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272527359593115283142703947 408791039389672924714055921)
    ·
      refine ⟨306593279542254693535541941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408791039389672924714055921 306593279542254693535541941)
      ·
        refine ⟨28743119957086377518957057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306593279542254693535541941 28743119957086377518957057)
        ·
          refine ⟨21557339967814783139217793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28743119957086377518957057 21557339967814783139217793)
          ·
            refine ⟨16168004975861087354413345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21557339967814783139217793 16168004975861087354413345)
            ·
              refine ⟨12126003731895815515810009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16168004975861087354413345 12126003731895815515810009)
              ·
                refine ⟨9094502798921861636857507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12126003731895815515810009 9094502798921861636857507)
                ·
                  refine ⟨13641754198382792455286261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9094502798921861636857507 13641754198382792455286261)
                  ·
                    refine ⟨1278914456098386792683087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13641754198382792455286261 1278914456098386792683087)
                    ·
                      rfl

theorem cell23_7472031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_7472031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472031 prefixEnd_7472031 := by exact prefixLift 7472031
  have htrace : WordTrace (prefixWord ++ tailWord_7472031) baseStart_7472031 baseEnd_7472031 := by
    simpa [prefixWord, tailWord_7472031, baseEnd_7472031] using wordTrace_append hprefix tailTrace_7472031
  have hstable : (prefixWord ++ tailWord_7472031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472031).length < 2 ^ (prefixWord ++ tailWord_7472031).sum := by decide
  have hdescent : baseEnd_7472031 < baseStart_7472031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472057 : List Nat := [1, 2, 1, 4, 2, 2, 11]
def baseStart_7472057 : Nat := 118140960795 + 7472057 * 2 ^ 59
def prefixEnd_7472057 : Nat := 4983230072969 + 3 ^ 40 * 7472057 * 2
def baseEnd_7472057 : Nat := 47367366898668855263261

theorem tailTrace_7472057 : CollatzResearch.WordTrace tailWord_7472057 prefixEnd_7472057 47367366898668855263261 := by
  unfold tailWord_7472057
  simp only [CollatzResearch.WordTrace]
  refine ⟨272528307891021089583150425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181685538594014059722100283 272528307891021089583150425)
  ·
    refine ⟨204396230918265817187362819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272528307891021089583150425 204396230918265817187362819)
    ·
      refine ⟨306594346377398725781044229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204396230918265817187362819 306594346377398725781044229)
      ·
        refine ⟨57486439945762261083945793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306594346377398725781044229 57486439945762261083945793)
        ·
          refine ⟨43114829959321695812959345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57486439945762261083945793 43114829959321695812959345)
          ·
            refine ⟨32336122469491271859719509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43114829959321695812959345 32336122469491271859719509)
            ·
              refine ⟨47367366898668855263261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32336122469491271859719509 47367366898668855263261)
              ·
                rfl

theorem cell23_7472057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 11].length) (baseStart_7472057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472057 prefixEnd_7472057 := by exact prefixLift 7472057
  have htrace : WordTrace (prefixWord ++ tailWord_7472057) baseStart_7472057 baseEnd_7472057 := by
    simpa [prefixWord, tailWord_7472057, baseEnd_7472057] using wordTrace_append hprefix tailTrace_7472057
  have hstable : (prefixWord ++ tailWord_7472057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472057).length < 2 ^ (prefixWord ++ tailWord_7472057).sum := by decide
  have hdescent : baseEnd_7472057 < baseStart_7472057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472078 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_7472078 : Nat := 118140960795 + 7472078 * 2 ^ 59
def prefixEnd_7472078 : Nat := 4983230072969 + 3 ^ 40 * 7472078 * 2
def baseEnd_7472078 : Nat := 1278922500628640564720515

theorem tailTrace_7472078 : CollatzResearch.WordTrace tailWord_7472078 prefixEnd_7472078 1278922500628640564720515 := by
  unfold tailWord_7472078
  simp only [CollatzResearch.WordTrace]
  refine ⟨34066134227993126271208111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181686049215963340113109925 34066134227993126271208111)
  ·
    refine ⟨51099201341989689406812167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34066134227993126271208111 51099201341989689406812167)
    ·
      refine ⟨76648802012984534110218251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51099201341989689406812167 76648802012984534110218251)
      ·
        refine ⟨114973203019476801165327377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76648802012984534110218251 114973203019476801165327377)
        ·
          refine ⟨86229902264607600873995533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114973203019476801165327377 86229902264607600873995533)
          ·
            refine ⟨32336213349227850327748325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86229902264607600873995533 32336213349227850327748325)
            ·
              refine ⟨6063040002980221936452811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32336213349227850327748325 6063040002980221936452811)
              ·
                refine ⟨9094560004470332904679217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063040002980221936452811 9094560004470332904679217)
                ·
                  refine ⟨6820920003352749678509413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9094560004470332904679217 6820920003352749678509413)
                  ·
                    refine ⟨1278922500628640564720515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6820920003352749678509413 1278922500628640564720515)
                    ·
                      rfl

theorem cell23_7472078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_7472078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472078 prefixEnd_7472078 := by exact prefixLift 7472078
  have htrace : WordTrace (prefixWord ++ tailWord_7472078) baseStart_7472078 baseEnd_7472078 := by
    simpa [prefixWord, tailWord_7472078, baseEnd_7472078] using wordTrace_append hprefix tailTrace_7472078
  have hstable : (prefixWord ++ tailWord_7472078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472078).length < 2 ^ (prefixWord ++ tailWord_7472078).sum := by decide
  have hdescent : baseEnd_7472078 < baseStart_7472078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472085 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_7472085 : Nat := 118140960795 + 7472085 * 2 ^ 59
def prefixEnd_7472085 : Nat := 4983230072969 + 3 ^ 40 * 7472085 * 2
def baseEnd_7472085 : Nat := 3836771096250503166774013

theorem tailTrace_7472085 : CollatzResearch.WordTrace tailWord_7472085 prefixEnd_7472085 3836771096250503166774013 := by
  unfold tailWord_7472085
  simp only [CollatzResearch.WordTrace]
  refine ⟨272529329134919650365169709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181686219423279766910113139 272529329134919650365169709)
  ·
    refine ⟨102198498425594868886938641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272529329134919650365169709 102198498425594868886938641)
    ·
      refine ⟨76648873819196151665203981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102198498425594868886938641 76648873819196151665203981)
      ·
        refine ⟨28743327682198556874451493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76648873819196151665203981 28743327682198556874451493)
        ·
          refine ⟨5389373940412229413959655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28743327682198556874451493 5389373940412229413959655)
          ·
            refine ⟨8084060910618344120939483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389373940412229413959655 8084060910618344120939483)
            ·
              refine ⟨12126091365927516181409225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084060910618344120939483 12126091365927516181409225)
              ·
                refine ⟨9094568524445637136056919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12126091365927516181409225 9094568524445637136056919)
                ·
                  refine ⟨13641852786668455704085379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9094568524445637136056919 13641852786668455704085379)
                  ·
                    refine ⟨20462779180002683556128069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13641852786668455704085379 20462779180002683556128069)
                    ·
                      refine ⟨3836771096250503166774013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20462779180002683556128069 3836771096250503166774013)
                      ·
                        rfl

theorem cell23_7472085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_7472085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472085 prefixEnd_7472085 := by exact prefixLift 7472085
  have htrace : WordTrace (prefixWord ++ tailWord_7472085) baseStart_7472085 baseEnd_7472085 := by
    simpa [prefixWord, tailWord_7472085, baseEnd_7472085] using wordTrace_append hprefix tailTrace_7472085
  have hstable : (prefixWord ++ tailWord_7472085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472085).length < 2 ^ (prefixWord ++ tailWord_7472085).sum := by decide
  have hdescent : baseEnd_7472085 < baseStart_7472085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472087 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 4, 7]
def baseStart_7472087 : Nat := 118140960795 + 7472087 * 2 ^ 59
def prefixEnd_7472087 : Nat := 4983230072969 + 3 ^ 40 * 7472087 * 2
def baseEnd_7472087 : Nat := 1278924041070604052983001

theorem tailTrace_7472087 : CollatzResearch.WordTrace tailWord_7472087 prefixEnd_7472087 1278924041070604052983001 := by
  unfold tailWord_7472087
  simp only [CollatzResearch.WordTrace]
  refine ⟨272529402080912404706742515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181686268053941603137828343 272529402080912404706742515)
  ·
    refine ⟨408794103121368607060113773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272529402080912404706742515 408794103121368607060113773)
    ·
      refine ⟨153297788670513227647542665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408794103121368607060113773 153297788670513227647542665)
      ·
        refine ⟨114973341502884920735656999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153297788670513227647542665 114973341502884920735656999)
        ·
          refine ⟨172460012254327381103485499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114973341502884920735656999 172460012254327381103485499)
          ·
            refine ⟨258690018381491071655228249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172460012254327381103485499 258690018381491071655228249)
            ·
              refine ⟨194017513786118303741421187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258690018381491071655228249 194017513786118303741421187)
              ·
                refine ⟨291026270679177455612131781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194017513786118303741421187 291026270679177455612131781)
                ·
                  refine ⟨54567425752345772927274709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291026270679177455612131781 54567425752345772927274709)
                  ·
                    refine ⟨1278924041070604052983001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54567425752345772927274709 1278924041070604052983001)
                    ·
                      rfl

theorem cell23_7472087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_7472087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472087 prefixEnd_7472087 := by exact prefixLift 7472087
  have htrace : WordTrace (prefixWord ++ tailWord_7472087) baseStart_7472087 baseEnd_7472087 := by
    simpa [prefixWord, tailWord_7472087, baseEnd_7472087] using wordTrace_append hprefix tailTrace_7472087
  have hstable : (prefixWord ++ tailWord_7472087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472087).length < 2 ^ (prefixWord ++ tailWord_7472087).sum := by decide
  have hdescent : baseEnd_7472087 < baseStart_7472087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472088 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_7472088 : Nat := 118140960795 + 7472088 * 2 ^ 59
def prefixEnd_7472088 : Nat := 4983230072969 + 3 ^ 40 * 7472088 * 2
def baseEnd_7472088 : Nat := 3836772636692466655036499

theorem tailTrace_7472088 : CollatzResearch.WordTrace tailWord_7472088 prefixEnd_7472088 3836772636692466655036499 := by
  unfold tailWord_7472088
  simp only [CollatzResearch.WordTrace]
  refine ⟨136264719276954390938764459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181686292369272521251685945 136264719276954390938764459)
  ·
    refine ⟨204397078915431586408146689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136264719276954390938764459 204397078915431586408146689)
    ·
      refine ⟨153297809186573689806110017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204397078915431586408146689 153297809186573689806110017)
      ·
        refine ⟨114973356889930267354582513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153297809186573689806110017 114973356889930267354582513)
        ·
          refine ⟨86230017667447700515936885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114973356889930267354582513 86230017667447700515936885)
          ·
            refine ⟨8084064156323221923369083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86230017667447700515936885 8084064156323221923369083)
            ·
              refine ⟨12126096234484832885053625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084064156323221923369083 12126096234484832885053625)
              ·
                refine ⟨9094572175863624663790219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12126096234484832885053625 9094572175863624663790219)
                ·
                  refine ⟨13641858263795436995685329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9094572175863624663790219 13641858263795436995685329)
                  ·
                    refine ⟨10231393697846577746763997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13641858263795436995685329 10231393697846577746763997)
                    ·
                      refine ⟨3836772636692466655036499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10231393697846577746763997 3836772636692466655036499)
                      ·
                        rfl

theorem cell23_7472088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_7472088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472088 prefixEnd_7472088 := by exact prefixLift 7472088
  have htrace : WordTrace (prefixWord ++ tailWord_7472088) baseStart_7472088 baseEnd_7472088 := by
    simpa [prefixWord, tailWord_7472088, baseEnd_7472088] using wordTrace_append hprefix tailTrace_7472088
  have hstable : (prefixWord ++ tailWord_7472088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472088).length < 2 ^ (prefixWord ++ tailWord_7472088).sum := by decide
  have hdescent : baseEnd_7472088 < baseStart_7472088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472098 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7472098 : Nat := 118140960795 + 7472098 * 2 ^ 59
def prefixEnd_7472098 : Nat := 4983230072969 + 3 ^ 40 * 7472098 * 2
def baseEnd_7472098 : Nat := 3836777771499011615911453

theorem tailTrace_7472098 : CollatzResearch.WordTrace tailWord_7472098 prefixEnd_7472098 3836777771499011615911453 := by
  unfold tailWord_7472098
  simp only [CollatzResearch.WordTrace]
  refine ⟨68132450820968138396348237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181686535522581702390261965 68132450820968138396348237)
  ·
    refine ⟨25549669057863051898630589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68132450820968138396348237 25549669057863051898630589)
    ·
      refine ⟨9581125896698644461986471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25549669057863051898630589 9581125896698644461986471)
      ·
        refine ⟨14371688845047966692979707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9581125896698644461986471 14371688845047966692979707)
        ·
          refine ⟨21557533267571950039469561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371688845047966692979707 21557533267571950039469561)
          ·
            refine ⟨16168149950678962529602171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21557533267571950039469561 16168149950678962529602171)
            ·
              refine ⟨24252224926018443794403257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16168149950678962529602171 24252224926018443794403257)
              ·
                refine ⟨18189168694513832845802443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24252224926018443794403257 18189168694513832845802443)
                ·
                  refine ⟨27283753041770749268703665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18189168694513832845802443 27283753041770749268703665)
                  ·
                    refine ⟨20462814781328061951527749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27283753041770749268703665 20462814781328061951527749)
                    ·
                      refine ⟨3836777771499011615911453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20462814781328061951527749 3836777771499011615911453)
                      ·
                        rfl

theorem cell23_7472098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7472098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472098 prefixEnd_7472098 := by exact prefixLift 7472098
  have htrace : WordTrace (prefixWord ++ tailWord_7472098) baseStart_7472098 baseEnd_7472098 := by
    simpa [prefixWord, tailWord_7472098, baseEnd_7472098] using wordTrace_append hprefix tailTrace_7472098
  have hstable : (prefixWord ++ tailWord_7472098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472098).length < 2 ^ (prefixWord ++ tailWord_7472098).sum := by decide
  have hdescent : baseEnd_7472098 < baseStart_7472098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472124 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_7472124 : Nat := 118140960795 + 7472124 * 2 ^ 59
def prefixEnd_7472124 : Nat := 4983230072969 + 3 ^ 40 * 7472124 * 2
def baseEnd_7472124 : Nat := 3836791121996028514186333

theorem tailTrace_7472124 : CollatzResearch.WordTrace tailWord_7472124 prefixEnd_7472124 3836791121996028514186333 := by
  unfold tailWord_7472124
  simp only [CollatzResearch.WordTrace]
  refine ⟨136265375790889180012919713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181687167721185573350559617 136265375790889180012919713)
  ·
    refine ⟨102199031843166885009689785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136265375790889180012919713 102199031843166885009689785)
    ·
      refine ⟨76649273882375163757267339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102199031843166885009689785 76649273882375163757267339)
      ·
        refine ⟨114973910823562745635901009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76649273882375163757267339 114973910823562745635901009)
        ·
          refine ⟨86230433117672059226925757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114973910823562745635901009 86230433117672059226925757)
          ·
            refine ⟨32336412419127022210097159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86230433117672059226925757 32336412419127022210097159)
            ·
              refine ⟨48504618628690533315145739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32336412419127022210097159 48504618628690533315145739)
              ·
                refine ⟨72756927943035799972718609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48504618628690533315145739 72756927943035799972718609)
                ·
                  refine ⟨54567695957276849979538957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72756927943035799972718609 54567695957276849979538957)
                  ·
                    refine ⟨20462885983978818742327109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54567695957276849979538957 20462885983978818742327109)
                    ·
                      refine ⟨3836791121996028514186333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20462885983978818742327109 3836791121996028514186333)
                      ·
                        rfl

theorem cell23_7472124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_7472124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472124 prefixEnd_7472124 := by exact prefixLift 7472124
  have htrace : WordTrace (prefixWord ++ tailWord_7472124) baseStart_7472124 baseEnd_7472124 := by
    simpa [prefixWord, tailWord_7472124, baseEnd_7472124] using wordTrace_append hprefix tailTrace_7472124
  have hstable : (prefixWord ++ tailWord_7472124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472124).length < 2 ^ (prefixWord ++ tailWord_7472124).sum := by decide
  have hdescent : baseEnd_7472124 < baseStart_7472124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472154 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_7472154 : Nat := 118140960795 + 7472154 * 2 ^ 59
def prefixEnd_7472154 : Nat := 4983230072969 + 3 ^ 40 * 7472154 * 2
def baseEnd_7472154 : Nat := 3836806526415663396811195

theorem tailTrace_7472154 : CollatzResearch.WordTrace tailWord_7472154 prefixEnd_7472154 3836806526415663396811195 := by
  unfold tailWord_7472154
  simp only [CollatzResearch.WordTrace]
  refine ⟨68132961442917418787357879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181687897181113116766287677 68132961442917418787357879)
  ·
    refine ⟨102199442164376128181036819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68132961442917418787357879 102199442164376128181036819)
    ·
      refine ⟨153299163246564192271555229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102199442164376128181036819 153299163246564192271555229)
      ·
        refine ⟨57487186217461572101833211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153299163246564192271555229 57487186217461572101833211)
        ·
          refine ⟨86230779326192358152749817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57487186217461572101833211 86230779326192358152749817)
          ·
            refine ⟨64673084494644268614562363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86230779326192358152749817 64673084494644268614562363)
            ·
              refine ⟨97009626741966402921843545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64673084494644268614562363 97009626741966402921843545)
              ·
                refine ⟨72757220056474802191382659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97009626741966402921843545 72757220056474802191382659)
                ·
                  refine ⟨109135830084712203287073989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72757220056474802191382659 109135830084712203287073989)
                  ·
                    refine ⟨20462968140883538116326373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109135830084712203287073989 20462968140883538116326373)
                    ·
                      refine ⟨3836806526415663396811195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20462968140883538116326373 3836806526415663396811195)
                      ·
                        rfl

theorem cell23_7472154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_7472154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472154 prefixEnd_7472154 := by exact prefixLift 7472154
  have htrace : WordTrace (prefixWord ++ tailWord_7472154) baseStart_7472154 baseEnd_7472154 := by
    simpa [prefixWord, tailWord_7472154, baseEnd_7472154] using wordTrace_append hprefix tailTrace_7472154
  have hstable : (prefixWord ++ tailWord_7472154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472154).length < 2 ^ (prefixWord ++ tailWord_7472154).sum := by decide
  have hdescent : baseEnd_7472154 < baseStart_7472154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472162 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_7472162 : Nat := 118140960795 + 7472162 * 2 ^ 59
def prefixEnd_7472162 : Nat := 4983230072969 + 3 ^ 40 * 7472162 * 2
def baseEnd_7472162 : Nat := 3836810634260899365511159

theorem tailTrace_7472162 : CollatzResearch.WordTrace tailWord_7472162 prefixEnd_7472162 3836810634260899365511159 := by
  unfold tailWord_7472162
  simp only [CollatzResearch.WordTrace]
  refine ⟨68133034388910173128930685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181688091703760461677148493 68133034388910173128930685)
  ·
    refine ⟨25549887895841314923349007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68133034388910173128930685 25549887895841314923349007)
    ·
      refine ⟨38324831843761972385023511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25549887895841314923349007 38324831843761972385023511)
      ·
        refine ⟨57487247765642958577535267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38324831843761972385023511 57487247765642958577535267)
        ·
          refine ⟨86230871648464437866302901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57487247765642958577535267 86230871648464437866302901)
          ·
            refine ⟨8084144217043541049965897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86230871648464437866302901 8084144217043541049965897)
            ·
              refine ⟨6063108162782655787474423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8084144217043541049965897 6063108162782655787474423)
              ·
                refine ⟨9094662244173983681211635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063108162782655787474423 9094662244173983681211635)
                ·
                  refine ⟨13641993366260975521817453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9094662244173983681211635 13641993366260975521817453)
                  ·
                    refine ⟨5115747512347865820681545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13641993366260975521817453 5115747512347865820681545)
                    ·
                      refine ⟨3836810634260899365511159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5115747512347865820681545 3836810634260899365511159)
                      ·
                        rfl

theorem cell23_7472162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_7472162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472162 prefixEnd_7472162 := by exact prefixLift 7472162
  have htrace : WordTrace (prefixWord ++ tailWord_7472162) baseStart_7472162 baseEnd_7472162 := by
    simpa [prefixWord, tailWord_7472162, baseEnd_7472162] using wordTrace_append hprefix tailTrace_7472162
  have hstable : (prefixWord ++ tailWord_7472162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472162).length < 2 ^ (prefixWord ++ tailWord_7472162).sum := by decide
  have hdescent : baseEnd_7472162 < baseStart_7472162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472198 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_7472198 : Nat := 118140960795 + 7472198 * 2 ^ 59
def prefixEnd_7472198 : Nat := 4983230072969 + 3 ^ 40 * 7472198 * 2
def baseEnd_7472198 : Nat := 426314346618273469406777

theorem tailTrace_7472198 : CollatzResearch.WordTrace tailWord_7472198 prefixEnd_7472198 426314346618273469406777 := by
  unfold tailWord_7472198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8516670330734695958251039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181688967055673513776022165 8516670330734695958251039)
  ·
    refine ⟨12775005496102043937376559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8516670330734695958251039 12775005496102043937376559)
    ·
      refine ⟨19162508244153065906064839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12775005496102043937376559 19162508244153065906064839)
      ·
        refine ⟨28743762366229598859097259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19162508244153065906064839 28743762366229598859097259)
        ·
          refine ⟨43115643549344398288645889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28743762366229598859097259 43115643549344398288645889)
          ·
            refine ⟨32336732662008298716484417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43115643549344398288645889 32336732662008298716484417)
            ·
              refine ⟨24252549496506224037363313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32336732662008298716484417 24252549496506224037363313)
              ·
                refine ⟨18189412122379668028022485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24252549496506224037363313 18189412122379668028022485)
                ·
                  refine ⟨426314346618273469406777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18189412122379668028022485 426314346618273469406777)
                  ·
                    rfl

theorem cell23_7472198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_7472198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472198 prefixEnd_7472198 := by exact prefixLift 7472198
  have htrace : WordTrace (prefixWord ++ tailWord_7472198) baseStart_7472198 baseEnd_7472198 := by
    simpa [prefixWord, tailWord_7472198, baseEnd_7472198] using wordTrace_append hprefix tailTrace_7472198
  have hstable : (prefixWord ++ tailWord_7472198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472198).length < 2 ^ (prefixWord ++ tailWord_7472198).sum := by decide
  have hdescent : baseEnd_7472198 < baseStart_7472198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472204 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7472204 : Nat := 118140960795 + 7472204 * 2 ^ 59
def prefixEnd_7472204 : Nat := 4983230072969 + 3 ^ 40 * 7472204 * 2
def baseEnd_7472204 : Nat := 3836832200448388201185965

theorem tailTrace_7472204 : CollatzResearch.WordTrace tailWord_7472204 prefixEnd_7472204 3836832200448388201185965 := by
  unfold tailWord_7472204
  simp only [CollatzResearch.WordTrace]
  refine ⟨136266834710744266844375833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181689112947659022459167777 136266834710744266844375833)
  ·
    refine ⟨102200126033058200133281875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136266834710744266844375833 102200126033058200133281875)
    ·
      refine ⟨153300189049587300199922813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102200126033058200133281875 153300189049587300199922813)
      ·
        refine ⟨57487570893595237574971055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153300189049587300199922813 57487570893595237574971055)
        ·
          refine ⟨86231356340392856362456583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57487570893595237574971055 86231356340392856362456583)
          ·
            refine ⟨129347034510589284543684875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86231356340392856362456583 129347034510589284543684875)
            ·
              refine ⟨194020551765883926815527313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129347034510589284543684875 194020551765883926815527313)
              ·
                refine ⟨145515413824412945111645485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194020551765883926815527313 145515413824412945111645485)
                ·
                  refine ⟨54568280184154854416867057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145515413824412945111645485 54568280184154854416867057)
                  ·
                    refine ⟨40926210138116140812650293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54568280184154854416867057 40926210138116140812650293)
                    ·
                      refine ⟨3836832200448388201185965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40926210138116140812650293 3836832200448388201185965)
                      ·
                        rfl

theorem cell23_7472204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7472204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472204 prefixEnd_7472204 := by exact prefixLift 7472204
  have htrace : WordTrace (prefixWord ++ tailWord_7472204) baseStart_7472204 baseEnd_7472204 := by
    simpa [prefixWord, tailWord_7472204, baseEnd_7472204] using wordTrace_append hprefix tailTrace_7472204
  have hstable : (prefixWord ++ tailWord_7472204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472204).length < 2 ^ (prefixWord ++ tailWord_7472204).sum := by decide
  have hdescent : baseEnd_7472204 < baseStart_7472204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472231 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_7472231 : Nat := 118140960795 + 7472231 * 2 ^ 59
def prefixEnd_7472231 : Nat := 4983230072969 + 3 ^ 40 * 7472231 * 2
def baseEnd_7472231 : Nat := 3836846064426059595548341

theorem tailTrace_7472231 : CollatzResearch.WordTrace tailWord_7472231 prefixEnd_7472231 3836846064426059595548341 := by
  unfold tailWord_7472231
  simp only [CollatzResearch.WordTrace]
  refine ⟨272534654192390717299984547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181689769461593811533323031 272534654192390717299984547)
  ·
    refine ⟨408801981288586075949976821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272534654192390717299984547 408801981288586075949976821)
    ·
      refine ⟨38325185745804944620310327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408801981288586075949976821 38325185745804944620310327)
      ·
        refine ⟨57487778618707416930465491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38325185745804944620310327 57487778618707416930465491)
        ·
          refine ⟨86231667928061125395698237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57487778618707416930465491 86231667928061125395698237)
          ·
            refine ⟨32336875473022922023386839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86231667928061125395698237 32336875473022922023386839)
            ·
              refine ⟨48505313209534383035080259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32336875473022922023386839 48505313209534383035080259)
              ·
                refine ⟨72757969814301574552620389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48505313209534383035080259 72757969814301574552620389)
                ·
                  refine ⟨13642119340181545228616323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72757969814301574552620389 13642119340181545228616323)
                  ·
                    refine ⟨20463179010272317842924485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13642119340181545228616323 20463179010272317842924485)
                    ·
                      refine ⟨3836846064426059595548341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20463179010272317842924485 3836846064426059595548341)
                      ·
                        rfl

theorem cell23_7472231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_7472231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472231 prefixEnd_7472231 := by exact prefixLift 7472231
  have htrace : WordTrace (prefixWord ++ tailWord_7472231) baseStart_7472231 baseEnd_7472231 := by
    simpa [prefixWord, tailWord_7472231, baseEnd_7472231] using wordTrace_append hprefix tailTrace_7472231
  have hstable : (prefixWord ++ tailWord_7472231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472231).length < 2 ^ (prefixWord ++ tailWord_7472231).sum := by decide
  have hdescent : baseEnd_7472231 < baseStart_7472231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472232 : List Nat := [2, 1, 4, 4, 1, 1, 3, 2, 5]
def baseStart_7472232 : Nat := 118140960795 + 7472232 * 2 ^ 59
def prefixEnd_7472232 : Nat := 4983230072969 + 3 ^ 40 * 7472232 * 2
def baseEnd_7472232 : Nat := 426316286434079343515093

theorem tailTrace_7472232 : CollatzResearch.WordTrace tailWord_7472232 prefixEnd_7472232 426316286434079343515093 := by
  unfold tailWord_7472232
  simp only [CollatzResearch.WordTrace]
  refine ⟨136267345332693547235385475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181689793776924729647180633 136267345332693547235385475)
  ·
    refine ⟨204401017999040320853078213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136267345332693547235385475 204401017999040320853078213)
    ·
      refine ⟨38325190874820060159952165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204401017999040320853078213 38325190874820060159952165)
      ·
        refine ⟨7185973289028761279991031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38325190874820060159952165 7185973289028761279991031)
        ·
          refine ⟨10778959933543141919986547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185973289028761279991031 10778959933543141919986547)
          ·
            refine ⟨16168439900314712879979821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10778959933543141919986547 16168439900314712879979821)
            ·
              refine ⟨6063164962618017329992433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16168439900314712879979821 6063164962618017329992433)
              ·
                refine ⟨4547373721963512997494325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6063164962618017329992433 4547373721963512997494325)
                ·
                  refine ⟨426316286434079343515093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4547373721963512997494325 426316286434079343515093)
                  ·
                    rfl

theorem cell23_7472232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 5].length) (baseStart_7472232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472232 prefixEnd_7472232 := by exact prefixLift 7472232
  have htrace : WordTrace (prefixWord ++ tailWord_7472232) baseStart_7472232 baseEnd_7472232 := by
    simpa [prefixWord, tailWord_7472232, baseEnd_7472232] using wordTrace_append hprefix tailTrace_7472232
  have hstable : (prefixWord ++ tailWord_7472232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472232).length < 2 ^ (prefixWord ++ tailWord_7472232).sum := by decide
  have hdescent : baseEnd_7472232 < baseStart_7472232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472241 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 3, 4]
def baseStart_7472241 : Nat := 118140960795 + 7472241 * 2 ^ 59
def prefixEnd_7472241 : Nat := 4983230072969 + 3 ^ 40 * 7472241 * 2
def baseEnd_7472241 : Nat := 1278950399744201518807765

theorem tailTrace_7472241 : CollatzResearch.WordTrace tailWord_7472241 prefixEnd_7472241 1278950399744201518807765 := by
  unfold tailWord_7472241
  simp only [CollatzResearch.WordTrace]
  refine ⟨272535018922354489007848577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181690012614902992671899051 272535018922354489007848577)
  ·
    refine ⟨204401264191765866755886433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272535018922354489007848577 204401264191765866755886433)
    ·
      refine ⟨153300948143824400066914825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204401264191765866755886433 153300948143824400066914825)
      ·
        refine ⟨114975711107868300050186119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153300948143824400066914825 114975711107868300050186119)
        ·
          refine ⟨172463566661802450075279179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114975711107868300050186119 172463566661802450075279179)
          ·
            refine ⟨258695349992703675112918769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172463566661802450075279179 258695349992703675112918769)
            ·
              refine ⟨194021512494527756334689077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258695349992703675112918769 194021512494527756334689077)
              ·
                refine ⟨18189516796361977156377101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194021512494527756334689077 18189516796361977156377101)
                ·
                  refine ⟨6821068798635741433641413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18189516796361977156377101 6821068798635741433641413)
                  ·
                    refine ⟨1278950399744201518807765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821068798635741433641413 1278950399744201518807765)
                    ·
                      rfl

theorem cell23_7472241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_7472241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472241 prefixEnd_7472241 := by exact prefixLift 7472241
  have htrace : WordTrace (prefixWord ++ tailWord_7472241) baseStart_7472241 baseEnd_7472241 := by
    simpa [prefixWord, tailWord_7472241, baseEnd_7472241] using wordTrace_append hprefix tailTrace_7472241
  have hstable : (prefixWord ++ tailWord_7472241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472241).length < 2 ^ (prefixWord ++ tailWord_7472241).sum := by decide
  have hdescent : baseEnd_7472241 < baseStart_7472241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472292 : List Nat := [2, 3, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_7472292 : Nat := 118140960795 + 7472292 * 2 ^ 59
def prefixEnd_7472292 : Nat := 4983230072969 + 3 ^ 40 * 7472292 * 2
def baseEnd_7472292 : Nat := 1278959128915327952295187

theorem tailTrace_7472292 : CollatzResearch.WordTrace tailWord_7472292 prefixEnd_7472292 1278959128915327952295187 := by
  unfold tailWord_7472292
  simp only [CollatzResearch.WordTrace]
  refine ⟨136268439522584862358977565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181691252696779816478636753 136268439522584862358977565)
  ·
    refine ⟨51100664820969323384616587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136268439522584862358977565 51100664820969323384616587)
    ·
      refine ⟨76650997231453985076924881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51100664820969323384616587 76650997231453985076924881)
      ·
        refine ⟨57488247923590488807693661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76650997231453985076924881 57488247923590488807693661)
        ·
          refine ⟨21558092971346433302885123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57488247923590488807693661 21558092971346433302885123)
          ·
            refine ⟨32337139457019649954327685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21558092971346433302885123 32337139457019649954327685)
            ·
              refine ⟨6063213648191184366436441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32337139457019649954327685 6063213648191184366436441)
              ·
                refine ⟨4547410236143388274827331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6063213648191184366436441 4547410236143388274827331)
                ·
                  refine ⟨6821115354215082412240997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547410236143388274827331 6821115354215082412240997)
                  ·
                    refine ⟨1278959128915327952295187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821115354215082412240997 1278959128915327952295187)
                    ·
                      rfl

theorem cell23_7472292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_7472292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472292 prefixEnd_7472292 := by exact prefixLift 7472292
  have htrace : WordTrace (prefixWord ++ tailWord_7472292) baseStart_7472292 baseEnd_7472292 := by
    simpa [prefixWord, tailWord_7472292, baseEnd_7472292] using wordTrace_append hprefix tailTrace_7472292
  have hstable : (prefixWord ++ tailWord_7472292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472292).length < 2 ^ (prefixWord ++ tailWord_7472292).sum := by decide
  have hdescent : baseEnd_7472292 < baseStart_7472292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472318 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_7472318 : Nat := 118140960795 + 7472318 * 2 ^ 59
def prefixEnd_7472318 : Nat := 4983230072969 + 3 ^ 40 * 7472318 * 2
def baseEnd_7472318 : Nat := 1278963579081000251720147

theorem tailTrace_7472318 : CollatzResearch.WordTrace tailWord_7472318 prefixEnd_7472318 1278963579081000251720147 := by
  unfold tailWord_7472318
  simp only [CollatzResearch.WordTrace]
  refine ⟨34067228417884441394800201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181691884895383687438934405 34067228417884441394800201)
  ·
    refine ⟨25550421313413331046100151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34067228417884441394800201 25550421313413331046100151)
    ·
      refine ⟨38325631970119996569150227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25550421313413331046100151 38325631970119996569150227)
      ·
        refine ⟨57488447955179994853725341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38325631970119996569150227 57488447955179994853725341)
        ·
          refine ⟨21558167983192498070147003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57488447955179994853725341 21558167983192498070147003)
          ·
            refine ⟨32337251974788747105220505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21558167983192498070147003 32337251974788747105220505)
            ·
              refine ⟨24252938981091560328915379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32337251974788747105220505 24252938981091560328915379)
              ·
                refine ⟨36379408471637340493373069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24252938981091560328915379 36379408471637340493373069)
                ·
                  refine ⟨13642278176864002685014901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36379408471637340493373069 13642278176864002685014901)
                  ·
                    refine ⟨1278963579081000251720147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13642278176864002685014901 1278963579081000251720147)
                    ·
                      rfl

theorem cell23_7472318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_7472318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472318 prefixEnd_7472318 := by exact prefixLift 7472318
  have htrace : WordTrace (prefixWord ++ tailWord_7472318) baseStart_7472318 baseEnd_7472318 := by
    simpa [prefixWord, tailWord_7472318, baseEnd_7472318] using wordTrace_append hprefix tailTrace_7472318
  have hstable : (prefixWord ++ tailWord_7472318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472318).length < 2 ^ (prefixWord ++ tailWord_7472318).sum := by decide
  have hdescent : baseEnd_7472318 < baseStart_7472318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472351 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_7472351 : Nat := 118140960795 + 7472351 * 2 ^ 59
def prefixEnd_7472351 : Nat := 4983230072969 + 3 ^ 40 * 7472351 * 2
def baseEnd_7472351 : Nat := 3836907682104599126047789

theorem tailTrace_7472351 : CollatzResearch.WordTrace tailWord_7472351 prefixEnd_7472351 3836907682104599126047789 := by
  unfold tailWord_7472351
  simp only [CollatzResearch.WordTrace]
  refine ⟨272539030951955977794352907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181692687301303985196235271 272539030951955977794352907)
  ·
    refine ⟨408808546427933966691529361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272539030951955977794352907 408808546427933966691529361)
    ·
      refine ⟨306606409820950475018647021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408808546427933966691529361 306606409820950475018647021)
      ·
        refine ⟨114977403682856428131992633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306606409820950475018647021 114977403682856428131992633)
        ·
          refine ⟨86233052762142321098994475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114977403682856428131992633 86233052762142321098994475)
          ·
            refine ⟨129349579143213481648491713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86233052762142321098994475 129349579143213481648491713)
            ·
              refine ⟨97012184357410111236368785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129349579143213481648491713 97012184357410111236368785)
              ·
                refine ⟨72759138268057583427276589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97012184357410111236368785 72759138268057583427276589)
                ·
                  refine ⟨27284676850521593785228721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72759138268057583427276589 27284676850521593785228721)
                  ·
                    refine ⟨20463507637891195338921541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27284676850521593785228721 20463507637891195338921541)
                    ·
                      refine ⟨3836907682104599126047789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20463507637891195338921541 3836907682104599126047789)
                      ·
                        rfl

theorem cell23_7472351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_7472351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472351 prefixEnd_7472351 := by exact prefixLift 7472351
  have htrace : WordTrace (prefixWord ++ tailWord_7472351) baseStart_7472351 baseEnd_7472351 := by
    simpa [prefixWord, tailWord_7472351, baseEnd_7472351] using wordTrace_append hprefix tailTrace_7472351
  have hstable : (prefixWord ++ tailWord_7472351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472351).length < 2 ^ (prefixWord ++ tailWord_7472351).sum := by decide
  have hdescent : baseEnd_7472351 < baseStart_7472351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472365 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_7472365 : Nat := 118140960795 + 7472365 * 2 ^ 59
def prefixEnd_7472365 : Nat := 4983230072969 + 3 ^ 40 * 7472365 * 2
def baseEnd_7472365 : Nat := 1278971623611254023757575

theorem tailTrace_7472365 : CollatzResearch.WordTrace tailWord_7472365 prefixEnd_7472365 1278971623611254023757575 := by
  unfold tailWord_7472365
  simp only [CollatzResearch.WordTrace]
  refine ⟨272539541573905258185362549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181693027715936838790241699 272539541573905258185362549)
  ·
    refine ⟨25550582022553617954877739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272539541573905258185362549 25550582022553617954877739)
    ·
      refine ⟨38325873033830426932316609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25550582022553617954877739 38325873033830426932316609)
      ·
        refine ⟨28744404775372820199237457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38325873033830426932316609 28744404775372820199237457)
        ·
          refine ⟨21558303581529615149428093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28744404775372820199237457 21558303581529615149428093)
          ·
            refine ⟨8084363843073605681035535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21558303581529615149428093 8084363843073605681035535)
            ·
              refine ⟨12126545764610408521553303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084363843073605681035535 12126545764610408521553303)
              ·
                refine ⟨18189818646915612782329955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12126545764610408521553303 18189818646915612782329955)
                ·
                  refine ⟨27284727970373419173494933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18189818646915612782329955 27284727970373419173494933)
                  ·
                    refine ⟨1278971623611254023757575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27284727970373419173494933 1278971623611254023757575)
                    ·
                      rfl

theorem cell23_7472365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_7472365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472365 prefixEnd_7472365 := by exact prefixLift 7472365
  have htrace : WordTrace (prefixWord ++ tailWord_7472365) baseStart_7472365 baseEnd_7472365 := by
    simpa [prefixWord, tailWord_7472365, baseEnd_7472365] using wordTrace_append hprefix tailTrace_7472365
  have hstable : (prefixWord ++ tailWord_7472365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472365).length < 2 ^ (prefixWord ++ tailWord_7472365).sum := by decide
  have hdescent : baseEnd_7472365 < baseStart_7472365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472401 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_7472401 : Nat := 118140960795 + 7472401 * 2 ^ 59
def prefixEnd_7472401 : Nat := 4983230072969 + 3 ^ 40 * 7472401 * 2
def baseEnd_7472401 : Nat := 3836933356137323930422559

theorem tailTrace_7472401 : CollatzResearch.WordTrace tailWord_7472401 prefixEnd_7472401 3836933356137323930422559 := by
  unfold tailWord_7472401
  simp only [CollatzResearch.WordTrace]
  refine ⟨272540854601774836333673057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181693903067849890889115371 272540854601774836333673057)
  ·
    refine ⟨204405640951331127250254793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272540854601774836333673057 204405640951331127250254793)
    ·
      refine ⟨153304230713498345437691095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204405640951331127250254793 153304230713498345437691095)
      ·
        refine ⟨229956346070247518156536643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153304230713498345437691095 229956346070247518156536643)
        ·
          refine ⟨344934519105371277234804965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229956346070247518156536643 344934519105371277234804965)
          ·
            refine ⟨64675222332257114481525931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344934519105371277234804965 64675222332257114481525931)
            ·
              refine ⟨97012833498385671722288897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64675222332257114481525931 97012833498385671722288897)
              ·
                refine ⟨72759625123789253791716673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97012833498385671722288897 72759625123789253791716673)
                ·
                  refine ⟨54569718842841940343787505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72759625123789253791716673 54569718842841940343787505)
                  ·
                    refine ⟨40927289132131455257840629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54569718842841940343787505 40927289132131455257840629)
                    ·
                      refine ⟨3836933356137323930422559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40927289132131455257840629 3836933356137323930422559)
                      ·
                        rfl

theorem cell23_7472401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_7472401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472401 prefixEnd_7472401 := by exact prefixLift 7472401
  have htrace : WordTrace (prefixWord ++ tailWord_7472401) baseStart_7472401 baseEnd_7472401 := by
    simpa [prefixWord, tailWord_7472401, baseEnd_7472401] using wordTrace_append hprefix tailTrace_7472401
  have hstable : (prefixWord ++ tailWord_7472401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472401).length < 2 ^ (prefixWord ++ tailWord_7472401).sum := by decide
  have hdescent : baseEnd_7472401 < baseStart_7472401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472405 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_7472405 : Nat := 118140960795 + 7472405 * 2 ^ 59
def prefixEnd_7472405 : Nat := 4983230072969 + 3 ^ 40 * 7472405 * 2
def baseEnd_7472405 : Nat := 3836935410059941914772541

theorem tailTrace_7472405 : CollatzResearch.WordTrace tailWord_7472405 prefixEnd_7472405 3836935410059941914772541 := by
  unfold tailWord_7472405
  simp only [CollatzResearch.WordTrace]
  refine ⟨272541000493760345016818669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181694000329173563344545779 272541000493760345016818669)
  ·
    refine ⟨102202875185160129381307001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272541000493760345016818669 102202875185160129381307001)
    ·
      refine ⟨76652156388870097035980251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102202875185160129381307001 76652156388870097035980251)
      ·
        refine ⟨114978234583305145553970377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76652156388870097035980251 114978234583305145553970377)
        ·
          refine ⟨86233675937478859165477783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114978234583305145553970377 86233675937478859165477783)
          ·
            refine ⟨129350513906218288748216675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86233675937478859165477783 129350513906218288748216675)
            ·
              refine ⟨194025770859327433122325013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129350513906218288748216675 194025770859327433122325013)
              ·
                refine ⟨9094958009030973427608985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194025770859327433122325013 9094958009030973427608985)
                ·
                  refine ⟨6821218506773230070706739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9094958009030973427608985 6821218506773230070706739)
                  ·
                    refine ⟨10231827760159845106060109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6821218506773230070706739 10231827760159845106060109)
                    ·
                      refine ⟨3836935410059941914772541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10231827760159845106060109 3836935410059941914772541)
                      ·
                        rfl

theorem cell23_7472405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_7472405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472405 prefixEnd_7472405 := by exact prefixLift 7472405
  have htrace : WordTrace (prefixWord ++ tailWord_7472405) baseStart_7472405 baseEnd_7472405 := by
    simpa [prefixWord, tailWord_7472405, baseEnd_7472405] using wordTrace_append hprefix tailTrace_7472405
  have hstable : (prefixWord ++ tailWord_7472405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472405).length < 2 ^ (prefixWord ++ tailWord_7472405).sum := by decide
  have hdescent : baseEnd_7472405 < baseStart_7472405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472411 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4]
def baseStart_7472411 : Nat := 118140960795 + 7472411 * 2 ^ 59
def prefixEnd_7472411 : Nat := 4983230072969 + 3 ^ 40 * 7472411 * 2
def baseEnd_7472411 : Nat := 3836938490943868891297513

theorem tailTrace_7472411 : CollatzResearch.WordTrace tailWord_7472411 prefixEnd_7472411 3836938490943868891297513 := by
  unfold tailWord_7472411
  simp only [CollatzResearch.WordTrace]
  refine ⟨272541219331738608041537087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181694146221159072027691391 272541219331738608041537087)
  ·
    refine ⟨408811828997607912062305631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272541219331738608041537087 408811828997607912062305631)
    ·
      refine ⟨613217743496411868093458447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408811828997607912062305631 613217743496411868093458447)
      ·
        refine ⟨919826615244617802140187671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613217743496411868093458447 919826615244617802140187671)
        ·
          refine ⟨1379739922866926703210281507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919826615244617802140187671 1379739922866926703210281507)
          ·
            refine ⟨2069609884300390054815422261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379739922866926703210281507 2069609884300390054815422261)
            ·
              refine ⟨194025926653161567638945837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2069609884300390054815422261 194025926653161567638945837)
              ·
                refine ⟨72759722494935587864604689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194025926653161567638945837 72759722494935587864604689)
                ·
                  refine ⟨54569791871201690898453517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72759722494935587864604689 54569791871201690898453517)
                  ·
                    refine ⟨20463671951700634086920069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54569791871201690898453517 20463671951700634086920069)
                    ·
                      refine ⟨3836938490943868891297513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20463671951700634086920069 3836938490943868891297513)
                      ·
                        rfl

theorem cell23_7472411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_7472411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472411 prefixEnd_7472411 := by exact prefixLift 7472411
  have htrace : WordTrace (prefixWord ++ tailWord_7472411) baseStart_7472411 baseEnd_7472411 := by
    simpa [prefixWord, tailWord_7472411, baseEnd_7472411] using wordTrace_append hprefix tailTrace_7472411
  have hstable : (prefixWord ++ tailWord_7472411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472411).length < 2 ^ (prefixWord ++ tailWord_7472411).sum := by decide
  have hdescent : baseEnd_7472411 < baseStart_7472411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472468 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 7]
def baseStart_7472468 : Nat := 118140960795 + 7472468 * 2 ^ 59
def prefixEnd_7472468 : Nat := 4983230072969 + 3 ^ 40 * 7472468 * 2
def baseEnd_7472468 : Nat := 426329751037908352031639

theorem tailTrace_7472468 : CollatzResearch.WordTrace tailWord_7472468 prefixEnd_7472468 426329751037908352031639 := by
  unfold tailWord_7472468
  simp only [CollatzResearch.WordTrace]
  refine ⟨136271649146266053388181029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181695532195021404517574705 136271649146266053388181029)
  ·
    refine ⟨25550934214924885010283943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136271649146266053388181029 25550934214924885010283943)
    ·
      refine ⟨38326401322387327515425915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25550934214924885010283943 38326401322387327515425915)
      ·
        refine ⟨57489601983580991273138873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38326401322387327515425915 57489601983580991273138873)
        ·
          refine ⟨43117201487685743454854155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57489601983580991273138873 43117201487685743454854155)
          ·
            refine ⟨64675802231528615182281233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43117201487685743454854155 64675802231528615182281233)
            ·
              refine ⟨48506851673646461386710925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64675802231528615182281233 48506851673646461386710925)
              ·
                refine ⟨18190069377617423020016597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48506851673646461386710925 18190069377617423020016597)
                ·
                  refine ⟨426329751037908352031639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18190069377617423020016597 426329751037908352031639)
                  ·
                    rfl

theorem cell23_7472468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_7472468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472468 prefixEnd_7472468 := by exact prefixLift 7472468
  have htrace : WordTrace (prefixWord ++ tailWord_7472468) baseStart_7472468 baseEnd_7472468 := by
    simpa [prefixWord, tailWord_7472468, baseEnd_7472468] using wordTrace_append hprefix tailTrace_7472468
  have hstable : (prefixWord ++ tailWord_7472468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472468).length < 2 ^ (prefixWord ++ tailWord_7472468).sum := by decide
  have hdescent : baseEnd_7472468 < baseStart_7472468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472498 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_7472498 : Nat := 118140960795 + 7472498 * 2 ^ 59
def prefixEnd_7472498 : Nat := 4983230072969 + 3 ^ 40 * 7472498 * 2
def baseEnd_7472498 : Nat := 1278994387920270016969871

theorem tailTrace_7472498 : CollatzResearch.WordTrace tailWord_7472498 prefixEnd_7472498 1278994387920270016969871 := by
  unfold tailWord_7472498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68136098120605855474988537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181696261654948947933302765 68136098120605855474988537)
  ·
    refine ⟨51102073590454391606241403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68136098120605855474988537 51102073590454391606241403)
    ·
      refine ⟨76653110385681587409362105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51102073590454391606241403 76653110385681587409362105)
      ·
        refine ⟨57489832789261190557021579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76653110385681587409362105 57489832789261190557021579)
        ·
          refine ⟨86234749183891785835532369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57489832789261190557021579 86234749183891785835532369)
          ·
            refine ⟨64676061887918839376649277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86234749183891785835532369 64676061887918839376649277)
            ·
              refine ⟨24253523207969564766243479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64676061887918839376649277 24253523207969564766243479)
              ·
                refine ⟨36380284811954347149365219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24253523207969564766243479 36380284811954347149365219)
                ·
                  refine ⟨54570427217931520724047829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36380284811954347149365219 54570427217931520724047829)
                  ·
                    refine ⟨1278994387920270016969871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54570427217931520724047829 1278994387920270016969871)
                    ·
                      rfl

theorem cell23_7472498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_7472498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472498 prefixEnd_7472498 := by exact prefixLift 7472498
  have htrace : WordTrace (prefixWord ++ tailWord_7472498) baseStart_7472498 baseEnd_7472498 := by
    simpa [prefixWord, tailWord_7472498, baseEnd_7472498] using wordTrace_append hprefix tailTrace_7472498
  have hstable : (prefixWord ++ tailWord_7472498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472498).length < 2 ^ (prefixWord ++ tailWord_7472498).sum := by decide
  have hdescent : baseEnd_7472498 < baseStart_7472498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472513 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_7472513 : Nat := 118140960795 + 7472513 * 2 ^ 59
def prefixEnd_7472513 : Nat := 4983230072969 + 3 ^ 40 * 7472513 * 2
def baseEnd_7472513 : Nat := 3836990865970627492222045

theorem tailTrace_7472513 : CollatzResearch.WordTrace tailWord_7472513 prefixEnd_7472513 3836990865970627492222045 := by
  unfold tailWord_7472513
  simp only [CollatzResearch.WordTrace]
  refine ⟨272544939577369079461750193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181696626384912719641166795 272544939577369079461750193)
  ·
    refine ⟨204408704683026809596312645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272544939577369079461750193 204408704683026809596312645)
    ·
      refine ⟨38326632128067526799308621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204408704683026809596312645 38326632128067526799308621)
      ·
        refine ⟨14372487048025322549740733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38326632128067526799308621 14372487048025322549740733)
        ·
          refine ⟨5389682643009495956152775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14372487048025322549740733 5389682643009495956152775)
          ·
            refine ⟨8084523964514243934229163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389682643009495956152775 8084523964514243934229163)
            ·
              refine ⟨12126785946771365901343745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084523964514243934229163 12126785946771365901343745)
              ·
                refine ⟨9095089460078524426007809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12126785946771365901343745 9095089460078524426007809)
                ·
                  refine ⟨6821317095058893319505857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9095089460078524426007809 6821317095058893319505857)
                  ·
                    refine ⟨5115987821294169989629393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6821317095058893319505857 5115987821294169989629393)
                    ·
                      refine ⟨3836990865970627492222045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5115987821294169989629393 3836990865970627492222045)
                      ·
                        rfl

theorem cell23_7472513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_7472513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472513 prefixEnd_7472513 := by exact prefixLift 7472513
  have htrace : WordTrace (prefixWord ++ tailWord_7472513) baseStart_7472513 baseEnd_7472513 := by
    simpa [prefixWord, tailWord_7472513, baseEnd_7472513] using wordTrace_append hprefix tailTrace_7472513
  have hstable : (prefixWord ++ tailWord_7472513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472513).length < 2 ^ (prefixWord ++ tailWord_7472513).sum := by decide
  have hdescent : baseEnd_7472513 < baseStart_7472513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472548 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_7472548 : Nat := 118140960795 + 7472548 * 2 ^ 59
def prefixEnd_7472548 : Nat := 4983230072969 + 3 ^ 40 * 7472548 * 2
def baseEnd_7472548 : Nat := 3837008837793534855284383

theorem tailTrace_7472548 : CollatzResearch.WordTrace tailWord_7472548 prefixEnd_7472548 3837008837793534855284383 := by
  unfold tailWord_7472548
  simp only [CollatzResearch.WordTrace]
  refine ⟨136273108066121140219637149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181697477421494853626182865 136273108066121140219637149)
  ·
    refine ⟨51102415524795427582363931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136273108066121140219637149 51102415524795427582363931)
    ·
      refine ⟨76653623287193141373545897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51102415524795427582363931 76653623287193141373545897)
      ·
        refine ⟨57490217465394856030159423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76653623287193141373545897 57490217465394856030159423)
        ·
          refine ⟨86235326198092284045239135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57490217465394856030159423 86235326198092284045239135)
          ·
            refine ⟨129352989297138426067858703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86235326198092284045239135 129352989297138426067858703)
            ·
              refine ⟨194029483945707639101788055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129352989297138426067858703 194029483945707639101788055)
              ·
                refine ⟨291044225918561458652682083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194029483945707639101788055 291044225918561458652682083)
                ·
                  refine ⟨436566338877842187979023125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291044225918561458652682083 436566338877842187979023125)
                  ·
                    refine ⟨20464047134898852561516709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 436566338877842187979023125 20464047134898852561516709)
                    ·
                      refine ⟨3837008837793534855284383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20464047134898852561516709 3837008837793534855284383)
                      ·
                        rfl

theorem cell23_7472548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_7472548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472548 prefixEnd_7472548 := by exact prefixLift 7472548
  have htrace : WordTrace (prefixWord ++ tailWord_7472548) baseStart_7472548 baseEnd_7472548 := by
    simpa [prefixWord, tailWord_7472548, baseEnd_7472548] using wordTrace_append hprefix tailTrace_7472548
  have hstable : (prefixWord ++ tailWord_7472548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472548).length < 2 ^ (prefixWord ++ tailWord_7472548).sum := by decide
  have hdescent : baseEnd_7472548 < baseStart_7472548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472562 : List Nat := [3, 2, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_7472562 : Nat := 118140960795 + 7472562 * 2 ^ 59
def prefixEnd_7472562 : Nat := 4983230072969 + 3 ^ 40 * 7472562 * 2
def baseEnd_7472562 : Nat := 1279005342174232600169773

theorem tailTrace_7472562 : CollatzResearch.WordTrace tailWord_7472562 prefixEnd_7472562 1279005342174232600169773 := by
  unfold tailWord_7472562
  simp only [CollatzResearch.WordTrace]
  refine ⟨68136681688547890207570985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181697817836127707220189293 68136681688547890207570985)
  ·
    refine ⟨51102511266410917655678239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68136681688547890207570985 51102511266410917655678239)
    ·
      refine ⟨76653766899616376483517359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51102511266410917655678239 76653766899616376483517359)
      ·
        refine ⟨114980650349424564725276039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76653766899616376483517359 114980650349424564725276039)
        ·
          refine ⟨172470975524136847087914059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114980650349424564725276039 172470975524136847087914059)
          ·
            refine ⟨258706463286205270631871089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172470975524136847087914059 258706463286205270631871089)
            ·
              refine ⟨194029847464653952973903317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258706463286205270631871089 194029847464653952973903317)
              ·
                refine ⟨4547574549952827022825859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194029847464653952973903317 4547574549952827022825859)
                ·
                  refine ⟨6821361824929240534238789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547574549952827022825859 6821361824929240534238789)
                  ·
                    refine ⟨1279005342174232600169773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821361824929240534238789 1279005342174232600169773)
                    ·
                      rfl

theorem cell23_7472562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_7472562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472562 prefixEnd_7472562 := by exact prefixLift 7472562
  have htrace : WordTrace (prefixWord ++ tailWord_7472562) baseStart_7472562 baseEnd_7472562 := by
    simpa [prefixWord, tailWord_7472562, baseEnd_7472562] using wordTrace_append hprefix tailTrace_7472562
  have hstable : (prefixWord ++ tailWord_7472562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472562).length < 2 ^ (prefixWord ++ tailWord_7472562).sum := by decide
  have hdescent : baseEnd_7472562 < baseStart_7472562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472636 : List Nat := [2, 2, 2, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_7472636 : Nat := 118140960795 + 7472636 * 2 ^ 59
def prefixEnd_7472636 : Nat := 4983230072969 + 3 ^ 40 * 7472636 * 2
def baseEnd_7472636 : Nat := 3837054024091130510983979

theorem tailTrace_7472636 : CollatzResearch.WordTrace tailWord_7472636 prefixEnd_7472636 3837054024091130510983979 := by
  unfold tailWord_7472636
  simp only [CollatzResearch.WordTrace]
  refine ⟨136274712877961735734238881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181699617170615647645651841 136274712877961735734238881)
  ·
    refine ⟨102206034658471301800679161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136274712877961735734238881 102206034658471301800679161)
    ·
      refine ⟨76654525993853476350509371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102206034658471301800679161 76654525993853476350509371)
      ·
        refine ⟨114981788990780214525764057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76654525993853476350509371 114981788990780214525764057)
        ·
          refine ⟨86236341743085160894323043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114981788990780214525764057 86236341743085160894323043)
          ·
            refine ⟨129354512614627741341484565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86236341743085160894323043 129354512614627741341484565)
            ·
              refine ⟨6063492778810675375382089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129354512614627741341484565 6063492778810675375382089)
              ·
                refine ⟨4547619584108006531536567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6063492778810675375382089 4547619584108006531536567)
                ·
                  refine ⟨6821429376162009797304851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547619584108006531536567 6821429376162009797304851)
                  ·
                    refine ⟨10232144064243014695957277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6821429376162009797304851 10232144064243014695957277)
                    ·
                      refine ⟨3837054024091130510983979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10232144064243014695957277 3837054024091130510983979)
                      ·
                        rfl

theorem cell23_7472636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_7472636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472636 prefixEnd_7472636 := by exact prefixLift 7472636
  have htrace : WordTrace (prefixWord ++ tailWord_7472636) baseStart_7472636 baseEnd_7472636 := by
    simpa [prefixWord, tailWord_7472636, baseEnd_7472636] using wordTrace_append hprefix tailTrace_7472636
  have hstable : (prefixWord ++ tailWord_7472636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472636).length < 2 ^ (prefixWord ++ tailWord_7472636).sum := by decide
  have hdescent : baseEnd_7472636 < baseStart_7472636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472652 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_7472652 : Nat := 118140960795 + 7472652 * 2 ^ 59
def prefixEnd_7472652 : Nat := 4983230072969 + 3 ^ 40 * 7472652 * 2
def baseEnd_7472652 : Nat := 1279020746593867482794635

theorem tailTrace_7472652 : CollatzResearch.WordTrace tailWord_7472652 prefixEnd_7472652 1279020746593867482794635 := by
  unfold tailWord_7472652
  simp only [CollatzResearch.WordTrace]
  refine ⟨136275004661932753100530105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181700006215910337467373473 136275004661932753100530105)
  ·
    refine ⟨102206253496449564825397579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136275004661932753100530105 102206253496449564825397579)
    ·
      refine ⟨153309380244674347238096369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102206253496449564825397579 153309380244674347238096369)
      ·
        refine ⟨114982035183505760428572277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153309380244674347238096369 114982035183505760428572277)
        ·
          refine ⟨10779565798453665040178651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114982035183505760428572277 10779565798453665040178651)
          ·
            refine ⟨16169348697680497560267977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779565798453665040178651 16169348697680497560267977)
            ·
              refine ⟨12127011523260373170200983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16169348697680497560267977 12127011523260373170200983)
              ·
                refine ⟨18190517284890559755301475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12127011523260373170200983 18190517284890559755301475)
                ·
                  refine ⟨27285775927335839632952213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18190517284890559755301475 27285775927335839632952213)
                  ·
                    refine ⟨1279020746593867482794635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27285775927335839632952213 1279020746593867482794635)
                    ·
                      rfl

theorem cell23_7472652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_7472652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472652 prefixEnd_7472652 := by exact prefixLift 7472652
  have htrace : WordTrace (prefixWord ++ tailWord_7472652) baseStart_7472652 baseEnd_7472652 := by
    simpa [prefixWord, tailWord_7472652, baseEnd_7472652] using wordTrace_append hprefix tailTrace_7472652
  have hstable : (prefixWord ++ tailWord_7472652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472652).length < 2 ^ (prefixWord ++ tailWord_7472652).sum := by decide
  have hdescent : baseEnd_7472652 < baseStart_7472652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472653 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7472653 : Nat := 118140960795 + 7472653 * 2 ^ 59
def prefixEnd_7472653 : Nat := 4983230072969 + 3 ^ 40 * 7472653 * 2
def baseEnd_7472653 : Nat := 3837062753262256944471401

theorem tailTrace_7472653 : CollatzResearch.WordTrace tailWord_7472653 prefixEnd_7472653 3837062753262256944471401 := by
  unfold tailWord_7472653
  simp only [CollatzResearch.WordTrace]
  refine ⟨272550045796861883371846613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181700030531241255581231075 272550045796861883371846613)
  ·
    refine ⟨6387891698363950391527655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 272550045796861883371846613 6387891698363950391527655)
    ·
      refine ⟨9581837547545925587291483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6387891698363950391527655 9581837547545925587291483)
      ·
        refine ⟨14372756321318888380937225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9581837547545925587291483 14372756321318888380937225)
        ·
          refine ⟨10779567240989166285702919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14372756321318888380937225 10779567240989166285702919)
          ·
            refine ⟨16169350861483749428554379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779567240989166285702919 16169350861483749428554379)
            ·
              refine ⟨24254026292225624142831569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16169350861483749428554379 24254026292225624142831569)
              ·
                refine ⟨18190519719169218107123677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24254026292225624142831569 18190519719169218107123677)
                ·
                  refine ⟨6821444894688456790171379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18190519719169218107123677 6821444894688456790171379)
                  ·
                    refine ⟨10232167342032685185257069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6821444894688456790171379 10232167342032685185257069)
                    ·
                      refine ⟨3837062753262256944471401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10232167342032685185257069 3837062753262256944471401)
                      ·
                        rfl

theorem cell23_7472653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7472653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472653 prefixEnd_7472653 := by exact prefixLift 7472653
  have htrace : WordTrace (prefixWord ++ tailWord_7472653) baseStart_7472653 baseEnd_7472653 := by
    simpa [prefixWord, tailWord_7472653, baseEnd_7472653] using wordTrace_append hprefix tailTrace_7472653
  have hstable : (prefixWord ++ tailWord_7472653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472653).length < 2 ^ (prefixWord ++ tailWord_7472653).sum := by decide
  have hdescent : baseEnd_7472653 < baseStart_7472653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472659 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 3, 2, 2]
def baseStart_7472659 : Nat := 118140960795 + 7472659 * 2 ^ 59
def prefixEnd_7472659 : Nat := 4983230072969 + 3 ^ 40 * 7472659 * 2
def baseEnd_7472659 : Nat := 3837065834146183920996373

theorem tailTrace_7472659 : CollatzResearch.WordTrace tailWord_7472659 prefixEnd_7472659 3837065834146183920996373 := by
  unfold tailWord_7472659
  simp only [CollatzResearch.WordTrace]
  refine ⟨272550264634840146396565031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181700176423226764264376687 272550264634840146396565031)
  ·
    refine ⟨408825396952260219594847547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272550264634840146396565031 408825396952260219594847547)
    ·
      refine ⟨613238095428390329392271321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408825396952260219594847547 613238095428390329392271321)
      ·
        refine ⟨459928571571292747044203491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613238095428390329392271321 459928571571292747044203491)
        ·
          refine ⟨689892857356939120566305237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459928571571292747044203491 689892857356939120566305237)
          ·
            refine ⟨16169363844303260638272779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 689892857356939120566305237 16169363844303260638272779)
            ·
              refine ⟨24254045766454890957409169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16169363844303260638272779 24254045766454890957409169)
              ·
                refine ⟨18190534324841168218056877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24254045766454890957409169 18190534324841168218056877)
                ·
                  refine ⟨6821450371815438081771329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18190534324841168218056877 6821450371815438081771329)
                  ·
                    refine ⟨5116087778861578561328497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6821450371815438081771329 5116087778861578561328497)
                    ·
                      refine ⟨3837065834146183920996373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116087778861578561328497 3837065834146183920996373)
                      ·
                        rfl

theorem cell23_7472659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 2, 2].length) (baseStart_7472659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472659 prefixEnd_7472659 := by exact prefixLift 7472659
  have htrace : WordTrace (prefixWord ++ tailWord_7472659) baseStart_7472659 baseEnd_7472659 := by
    simpa [prefixWord, tailWord_7472659, baseEnd_7472659] using wordTrace_append hprefix tailTrace_7472659
  have hstable : (prefixWord ++ tailWord_7472659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472659).length < 2 ^ (prefixWord ++ tailWord_7472659).sum := by decide
  have hdescent : baseEnd_7472659 < baseStart_7472659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472672 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7472672 : Nat := 118140960795 + 7472672 * 2 ^ 59
def prefixEnd_7472672 : Nat := 4983230072969 + 3 ^ 40 * 7472672 * 2
def baseEnd_7472672 : Nat := 3837072509394692370133813

theorem tailTrace_7472672 : CollatzResearch.WordTrace tailWord_7472672 prefixEnd_7472672 3837072509394692370133813 := by
  unfold tailWord_7472672
  simp only [CollatzResearch.WordTrace]
  refine ⟨136275369391896524808394135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181700492522528699744525513 136275369391896524808394135)
  ·
    refine ⟨204413054087844787212591203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136275369391896524808394135 204413054087844787212591203)
    ·
      refine ⟨306619581131767180818886805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204413054087844787212591203 306619581131767180818886805)
      ·
        refine ⟨14372792865551586600885319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 306619581131767180818886805 14372792865551586600885319)
        ·
          refine ⟨21559189298327379901327979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372792865551586600885319 21559189298327379901327979)
          ·
            refine ⟨32338783947491069851991969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21559189298327379901327979 32338783947491069851991969)
            ·
              refine ⟨24254087960618302388993977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32338783947491069851991969 24254087960618302388993977)
              ·
                refine ⟨18190565970463726791745483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24254087960618302388993977 18190565970463726791745483)
                ·
                  refine ⟨27285848955695590187618225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18190565970463726791745483 27285848955695590187618225)
                  ·
                    refine ⟨20464386716771692640713669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27285848955695590187618225 20464386716771692640713669)
                    ·
                      refine ⟨3837072509394692370133813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20464386716771692640713669 3837072509394692370133813)
                      ·
                        rfl

theorem cell23_7472672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7472672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472672 prefixEnd_7472672 := by exact prefixLift 7472672
  have htrace : WordTrace (prefixWord ++ tailWord_7472672) baseStart_7472672 baseEnd_7472672 := by
    simpa [prefixWord, tailWord_7472672, baseEnd_7472672] using wordTrace_append hprefix tailTrace_7472672
  have hstable : (prefixWord ++ tailWord_7472672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472672).length < 2 ^ (prefixWord ++ tailWord_7472672).sum := by decide
  have hdescent : baseEnd_7472672 < baseStart_7472672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472686 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7472686 : Nat := 118140960795 + 7472686 * 2 ^ 59
def prefixEnd_7472686 : Nat := 4983230072969 + 3 ^ 40 * 7472686 * 2
def baseEnd_7472686 : Nat := 1279026566041285105119583

theorem tailTrace_7472686 : CollatzResearch.WordTrace tailWord_7472686 prefixEnd_7472686 1279026566041285105119583 := by
  unfold tailWord_7472686
  simp only [CollatzResearch.WordTrace]
  refine ⟨34068906175717791250974739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181700832937161553338531941 34068906175717791250974739)
  ·
    refine ⟨51103359263576686876462109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34068906175717791250974739 51103359263576686876462109)
    ·
      refine ⟨19163759723841257578673291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51103359263576686876462109 19163759723841257578673291)
      ·
        refine ⟨28745639585761886368009937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19163759723841257578673291 28745639585761886368009937)
        ·
          refine ⟨21559229689321414776007453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28745639585761886368009937 21559229689321414776007453)
          ·
            refine ⟨8084711133495530541002795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21559229689321414776007453 8084711133495530541002795)
            ·
              refine ⟨12127066700243295811504193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084711133495530541002795 12127066700243295811504193)
              ·
                refine ⟨9095300025182471858628145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12127066700243295811504193 9095300025182471858628145)
                ·
                  refine ⟨6821475018886853893971109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9095300025182471858628145 6821475018886853893971109)
                  ·
                    refine ⟨1279026566041285105119583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821475018886853893971109 1279026566041285105119583)
                    ·
                      rfl

theorem cell23_7472686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7472686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472686 prefixEnd_7472686 := by exact prefixLift 7472686
  have htrace : WordTrace (prefixWord ++ tailWord_7472686) baseStart_7472686 baseEnd_7472686 := by
    simpa [prefixWord, tailWord_7472686, baseEnd_7472686] using wordTrace_append hprefix tailTrace_7472686
  have hstable : (prefixWord ++ tailWord_7472686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472686).length < 2 ^ (prefixWord ++ tailWord_7472686).sum := by decide
  have hdescent : baseEnd_7472686 < baseStart_7472686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472735 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 3]
def baseStart_7472735 : Nat := 118140960795 + 7472735 * 2 ^ 59
def prefixEnd_7472735 : Nat := 4983230072969 + 3 ^ 40 * 7472735 * 2
def baseEnd_7472735 : Nat := 3837104858675925623646023

theorem tailTrace_7472735 : CollatzResearch.WordTrace tailWord_7472735 prefixEnd_7472735 3837104858675925623646023 := by
  unfold tailWord_7472735
  simp only [CollatzResearch.WordTrace]
  refine ⟨272553036582564811376331659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181702024388376540917554439 272553036582564811376331659)
  ·
    refine ⟨408829554873847217064497489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272553036582564811376331659 408829554873847217064497489)
    ·
      refine ⟨306622166155385412798373117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408829554873847217064497489 306622166155385412798373117)
      ·
        refine ⟨114983312308269529799389919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306622166155385412798373117 114983312308269529799389919)
        ·
          refine ⟨172474968462404294699084879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114983312308269529799389919 172474968462404294699084879)
          ·
            refine ⟨258712452693606442048627319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172474968462404294699084879 258712452693606442048627319)
            ·
              refine ⟨388068679040409663072940979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258712452693606442048627319 388068679040409663072940979)
              ·
                refine ⟨582103018560614494609411469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388068679040409663072940979 582103018560614494609411469)
                ·
                  refine ⟨218288631960230435478529301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582103018560614494609411469 218288631960230435478529301)
                  ·
                    refine ⟨10232279623135801663056061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218288631960230435478529301 10232279623135801663056061)
                    ·
                      refine ⟨3837104858675925623646023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10232279623135801663056061 3837104858675925623646023)
                      ·
                        rfl

theorem cell23_7472735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_7472735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472735 prefixEnd_7472735 := by exact prefixLift 7472735
  have htrace : WordTrace (prefixWord ++ tailWord_7472735) baseStart_7472735 baseEnd_7472735 := by
    simpa [prefixWord, tailWord_7472735, baseEnd_7472735] using wordTrace_append hprefix tailTrace_7472735
  have hstable : (prefixWord ++ tailWord_7472735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472735).length < 2 ^ (prefixWord ++ tailWord_7472735).sum := by decide
  have hdescent : baseEnd_7472735 < baseStart_7472735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472745 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_7472745 : Nat := 118140960795 + 7472745 * 2 ^ 59
def prefixEnd_7472745 : Nat := 4983230072969 + 3 ^ 40 * 7472745 * 2
def baseEnd_7472745 : Nat := 3837109993482470584520977

theorem tailTrace_7472745 : CollatzResearch.WordTrace tailWord_7472745 prefixEnd_7472745 3837109993482470584520977 := by
  unfold tailWord_7472745
  simp only [CollatzResearch.WordTrace]
  refine ⟨272553401312528583084195689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181702267541685722056130459 272553401312528583084195689)
  ·
    refine ⟨204415050984396437313146767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272553401312528583084195689 204415050984396437313146767)
    ·
      refine ⟨306622576476594655969720151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204415050984396437313146767 306622576476594655969720151)
      ·
        refine ⟨459933864714891983954580227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306622576476594655969720151 459933864714891983954580227)
        ·
          refine ⟨689900797072337975931870341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459933864714891983954580227 689900797072337975931870341)
          ·
            refine ⟨129356399451063370487225689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 689900797072337975931870341 129356399451063370487225689)
            ·
              refine ⟨97017299588297527865419267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129356399451063370487225689 97017299588297527865419267)
              ·
                refine ⟨145525949382446291798128901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97017299588297527865419267 145525949382446291798128901)
                ·
                  refine ⟨27286115509208679712149169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145525949382446291798128901 27286115509208679712149169)
                  ·
                    refine ⟨20464586631906509784111877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27286115509208679712149169 20464586631906509784111877)
                    ·
                      refine ⟨3837109993482470584520977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20464586631906509784111877 3837109993482470584520977)
                      ·
                        rfl

theorem cell23_7472745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_7472745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472745 prefixEnd_7472745 := by exact prefixLift 7472745
  have htrace : WordTrace (prefixWord ++ tailWord_7472745) baseStart_7472745 baseEnd_7472745 := by
    simpa [prefixWord, tailWord_7472745, baseEnd_7472745] using wordTrace_append hprefix tailTrace_7472745
  have hstable : (prefixWord ++ tailWord_7472745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472745).length < 2 ^ (prefixWord ++ tailWord_7472745).sum := by decide
  have hdescent : baseEnd_7472745 < baseStart_7472745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472835 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6]
def baseStart_7472835 : Nat := 118140960795 + 7472835 * 2 ^ 59
def prefixEnd_7472835 : Nat := 4983230072969 + 3 ^ 40 * 7472835 * 2
def baseEnd_7472835 : Nat := 3837156206741375232395563

theorem tailTrace_7472835 : CollatzResearch.WordTrace tailWord_7472835 prefixEnd_7472835 3837156206741375232395563 := by
  unfold tailWord_7472835
  simp only [CollatzResearch.WordTrace]
  refine ⟨272556683882202528454971959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181704455921468352303314639 272556683882202528454971959)
  ·
    refine ⟨408835025823303792682457939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272556683882202528454971959 408835025823303792682457939)
    ·
      refine ⟨613252538734955689023686909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408835025823303792682457939 613252538734955689023686909)
      ·
        refine ⟨229969702025608383383882591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613252538734955689023686909 229969702025608383383882591)
        ·
          refine ⟨344954553038412575075823887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229969702025608383383882591 344954553038412575075823887)
          ·
            refine ⟨517431829557618862613735831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344954553038412575075823887 517431829557618862613735831)
            ·
              refine ⟨776147744336428293920603747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517431829557618862613735831 776147744336428293920603747)
              ·
                refine ⟨1164221616504642440880905621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776147744336428293920603747 1164221616504642440880905621)
                ·
                  refine ⟨54572888273655114416292451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1164221616504642440880905621 54572888273655114416292451)
                  ·
                    refine ⟨81859332410482671624438677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54572888273655114416292451 81859332410482671624438677)
                    ·
                      refine ⟨3837156206741375232395563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81859332410482671624438677 3837156206741375232395563)
                      ·
                        rfl

theorem cell23_7472835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_7472835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472835 prefixEnd_7472835 := by exact prefixLift 7472835
  have htrace : WordTrace (prefixWord ++ tailWord_7472835) baseStart_7472835 baseEnd_7472835 := by
    simpa [prefixWord, tailWord_7472835, baseEnd_7472835] using wordTrace_append hprefix tailTrace_7472835
  have hstable : (prefixWord ++ tailWord_7472835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472835).length < 2 ^ (prefixWord ++ tailWord_7472835).sum := by decide
  have hdescent : baseEnd_7472835 < baseStart_7472835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472879 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 6]
def baseStart_7472879 : Nat := 118140960795 + 7472879 * 2 ^ 59
def prefixEnd_7472879 : Nat := 4983230072969 + 3 ^ 40 * 7472879 * 2
def baseEnd_7472879 : Nat := 426353199987797006693929

theorem tailTrace_7472879 : CollatzResearch.WordTrace tailWord_7472879 prefixEnd_7472879 426353199987797006693929 := by
  unfold tailWord_7472879
  simp only [CollatzResearch.WordTrace]
  refine ⟨272558288694043123969573691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181705525796028749313049127 272558288694043123969573691)
  ·
    refine ⟨408837433041064685954360537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272558288694043123969573691 408837433041064685954360537)
    ·
      refine ⟨306628074780798514465770403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408837433041064685954360537 306628074780798514465770403)
      ·
        refine ⟨459942112171197771698655605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306628074780798514465770403 459942112171197771698655605)
        ·
          refine ⟨43119573016049791096748963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 459942112171197771698655605 43119573016049791096748963)
          ·
            refine ⟨64679359524074686645123445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43119573016049791096748963 64679359524074686645123445)
            ·
              refine ⟨6063689955382001872980323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64679359524074686645123445 6063689955382001872980323)
              ·
                refine ⟨9095534933073002809470485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063689955382001872980323 9095534933073002809470485)
                ·
                  refine ⟨426353199987797006693929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9095534933073002809470485 426353199987797006693929)
                  ·
                    rfl

theorem cell23_7472879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 6].length) (baseStart_7472879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472879 prefixEnd_7472879 := by exact prefixLift 7472879
  have htrace : WordTrace (prefixWord ++ tailWord_7472879) baseStart_7472879 baseEnd_7472879 := by
    simpa [prefixWord, tailWord_7472879, baseEnd_7472879] using wordTrace_append hprefix tailTrace_7472879
  have hstable : (prefixWord ++ tailWord_7472879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472879).length < 2 ^ (prefixWord ++ tailWord_7472879).sum := by decide
  have hdescent : baseEnd_7472879 < baseStart_7472879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472882 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7472882 : Nat := 118140960795 + 7472882 * 2 ^ 59
def prefixEnd_7472882 : Nat := 4983230072969 + 3 ^ 40 * 7472882 * 2
def baseEnd_7472882 : Nat := 3837180340332136548507847

theorem tailTrace_7472882 : CollatzResearch.WordTrace tailWord_7472882 prefixEnd_7472882 3837180340332136548507847 := by
  unfold tailWord_7472882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68139599528258063870483225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181705598742021503654621933 68139599528258063870483225)
  ·
    refine ⟨51104699646193547902862419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68139599528258063870483225 51104699646193547902862419)
    ·
      refine ⟨76657049469290321854293629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51104699646193547902862419 76657049469290321854293629)
      ·
        refine ⟨28746393550983870695360111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76657049469290321854293629 28746393550983870695360111)
        ·
          refine ⟨43119590326475806043040167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28746393550983870695360111 43119590326475806043040167)
          ·
            refine ⟨64679385489713709064560251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43119590326475806043040167 64679385489713709064560251)
            ·
              refine ⟨97019078234570563596840377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64679385489713709064560251 97019078234570563596840377)
              ·
                refine ⟨72764308675927922697630283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97019078234570563596840377 72764308675927922697630283)
                ·
                  refine ⟨109146463013891884046445425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72764308675927922697630283 109146463013891884046445425)
                  ·
                    refine ⟨81859847260418913034834069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109146463013891884046445425 81859847260418913034834069)
                    ·
                      refine ⟨3837180340332136548507847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81859847260418913034834069 3837180340332136548507847)
                      ·
                        rfl

theorem cell23_7472882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7472882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472882 prefixEnd_7472882 := by exact prefixLift 7472882
  have htrace : WordTrace (prefixWord ++ tailWord_7472882) baseStart_7472882 baseEnd_7472882 := by
    simpa [prefixWord, tailWord_7472882, baseEnd_7472882] using wordTrace_append hprefix tailTrace_7472882
  have hstable : (prefixWord ++ tailWord_7472882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472882).length < 2 ^ (prefixWord ++ tailWord_7472882).sum := by decide
  have hdescent : baseEnd_7472882 < baseStart_7472882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472899 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 1, 5, 2]
def baseStart_7472899 : Nat := 118140960795 + 7472899 * 2 ^ 59
def prefixEnd_7472899 : Nat := 4983230072969 + 3 ^ 40 * 7472899 * 2
def baseEnd_7472899 : Nat := 3837189069503262981995269

theorem tailTrace_7472899 : CollatzResearch.WordTrace tailWord_7472899 prefixEnd_7472899 3837189069503262981995269 := by
  unfold tailWord_7472899
  simp only [CollatzResearch.WordTrace]
  refine ⟨272559018153970667385301751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181706012102647111590201167 272559018153970667385301751)
  ·
    refine ⟨408838527230956001077952627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272559018153970667385301751 408838527230956001077952627)
    ·
      refine ⟨613257790846434001616928941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408838527230956001077952627 613257790846434001616928941)
      ·
        refine ⟨229971671567412750606348353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613257790846434001616928941 229971671567412750606348353)
        ·
          refine ⟨172478753675559562954761265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229971671567412750606348353 172478753675559562954761265)
          ·
            refine ⟨129359065256669672216070949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172478753675559562954761265 129359065256669672216070949)
            ·
              refine ⟨24254824735625563540513303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129359065256669672216070949 24254824735625563540513303)
              ·
                refine ⟨36382237103438345310769955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24254824735625563540513303 36382237103438345310769955)
                ·
                  refine ⟨54573355655157517966154933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36382237103438345310769955 54573355655157517966154933)
                  ·
                    refine ⟨5116252092671017309327025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54573355655157517966154933 5116252092671017309327025)
                    ·
                      refine ⟨3837189069503262981995269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116252092671017309327025 3837189069503262981995269)
                      ·
                        rfl

theorem cell23_7472899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_7472899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472899 prefixEnd_7472899 := by exact prefixLift 7472899
  have htrace : WordTrace (prefixWord ++ tailWord_7472899) baseStart_7472899 baseEnd_7472899 := by
    simpa [prefixWord, tailWord_7472899, baseEnd_7472899] using wordTrace_append hprefix tailTrace_7472899
  have hstable : (prefixWord ++ tailWord_7472899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472899).length < 2 ^ (prefixWord ++ tailWord_7472899).sum := by decide
  have hdescent : baseEnd_7472899 < baseStart_7472899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472946 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_7472946 : Nat := 118140960795 + 7472946 * 2 ^ 59
def prefixEnd_7472946 : Nat := 4983230072969 + 3 ^ 40 * 7472946 * 2
def baseEnd_7472946 : Nat := 3837213203094024298107553

theorem tailTrace_7472946 : CollatzResearch.WordTrace tailWord_7472946 prefixEnd_7472946 3837213203094024298107553 := by
  unfold tailWord_7472946
  simp only [CollatzResearch.WordTrace]
  refine ⟨68140183096200098603065673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181707154923200262941508461 68140183096200098603065673)
  ·
    refine ⟨51105137322150073952299255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68140183096200098603065673 51105137322150073952299255)
    ·
      refine ⟨76657705983225110928448883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51105137322150073952299255 76657705983225110928448883)
      ·
        refine ⟨114986558974837666392673325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76657705983225110928448883 114986558974837666392673325)
        ·
          refine ⟨43119959615564124897252497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114986558974837666392673325 43119959615564124897252497)
          ·
            refine ⟨32339969711673093672939373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43119959615564124897252497 32339969711673093672939373)
            ·
              refine ⟨12127488641877410127352265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32339969711673093672939373 12127488641877410127352265)
              ·
                refine ⟨9095616481408057595514199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12127488641877410127352265 9095616481408057595514199)
                ·
                  refine ⟨13643424722112086393271299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9095616481408057595514199 13643424722112086393271299)
                  ·
                    refine ⟨20465137083168129589906949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13643424722112086393271299 20465137083168129589906949)
                    ·
                      refine ⟨3837213203094024298107553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20465137083168129589906949 3837213203094024298107553)
                      ·
                        rfl

theorem cell23_7472946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_7472946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472946 prefixEnd_7472946 := by exact prefixLift 7472946
  have htrace : WordTrace (prefixWord ++ tailWord_7472946) baseStart_7472946 baseEnd_7472946 := by
    simpa [prefixWord, tailWord_7472946, baseEnd_7472946] using wordTrace_append hprefix tailTrace_7472946
  have hstable : (prefixWord ++ tailWord_7472946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472946).length < 2 ^ (prefixWord ++ tailWord_7472946).sum := by decide
  have hdescent : baseEnd_7472946 < baseStart_7472946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472950 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7472950 : Nat := 118140960795 + 7472950 * 2 ^ 59
def prefixEnd_7472950 : Nat := 4983230072969 + 3 ^ 40 * 7472950 * 2
def baseEnd_7472950 : Nat := 3837215257016642282457535

theorem tailTrace_7472950 : CollatzResearch.WordTrace tailWord_7472950 prefixEnd_7472950 3837215257016642282457535 := by
  unfold tailWord_7472950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17035054892299118943463019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181707252184523935396938869 17035054892299118943463019)
  ·
    refine ⟨25552582338448678415194529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17035054892299118943463019 25552582338448678415194529)
    ·
      refine ⟨19164436753836508811395897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25552582338448678415194529 19164436753836508811395897)
      ·
        refine ⟨14373327565377381608546923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19164436753836508811395897 14373327565377381608546923)
        ·
          refine ⟨21559991348066072412820385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14373327565377381608546923 21559991348066072412820385)
          ·
            refine ⟨16169993511049554309615289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21559991348066072412820385 16169993511049554309615289)
            ·
              refine ⟨12127495133287165732211467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16169993511049554309615289 12127495133287165732211467)
              ·
                refine ⟨18191242699930748598317201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12127495133287165732211467 18191242699930748598317201)
                ·
                  refine ⟨13643432024948061448737901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18191242699930748598317201 13643432024948061448737901)
                  ·
                    refine ⟨5116287009355523043276713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13643432024948061448737901 5116287009355523043276713)
                    ·
                      refine ⟨3837215257016642282457535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116287009355523043276713 3837215257016642282457535)
                      ·
                        rfl

theorem cell23_7472950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7472950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472950 prefixEnd_7472950 := by exact prefixLift 7472950
  have htrace : WordTrace (prefixWord ++ tailWord_7472950) baseStart_7472950 baseEnd_7472950 := by
    simpa [prefixWord, tailWord_7472950, baseEnd_7472950] using wordTrace_append hprefix tailTrace_7472950
  have hstable : (prefixWord ++ tailWord_7472950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472950).length < 2 ^ (prefixWord ++ tailWord_7472950).sum := by decide
  have hdescent : baseEnd_7472950 < baseStart_7472950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472952 : List Nat := [2, 1, 2, 1, 3, 3, 2, 9]
def baseStart_7472952 : Nat := 118140960795 + 7472952 * 2 ^ 59
def prefixEnd_7472952 : Nat := 4983230072969 + 3 ^ 40 * 7472952 * 2
def baseEnd_7472952 : Nat := 142119121628813010171575

theorem tailTrace_7472952 : CollatzResearch.WordTrace tailWord_7472952 prefixEnd_7472952 142119121628813010171575 := by
  unfold tailWord_7472952
  simp only [CollatzResearch.WordTrace]
  refine ⟨136280475611389328718490555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181707300815185771624654073 136280475611389328718490555)
  ·
    refine ⟨204420713417083993077735833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136280475611389328718490555 204420713417083993077735833)
    ·
      refine ⟨153315535062812994808301875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204420713417083993077735833 153315535062812994808301875)
      ·
        refine ⟨229973302594219492212452813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153315535062812994808301875 229973302594219492212452813)
        ·
          refine ⟨86239988472832309579669805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229973302594219492212452813 86239988472832309579669805)
          ·
            refine ⟨32339995677312116092376177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86239988472832309579669805 32339995677312116092376177)
            ·
              refine ⟨24254996757984087069282133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32339995677312116092376177 24254996757984087069282133)
              ·
                refine ⟨142119121628813010171575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24254996757984087069282133 142119121628813010171575)
                ·
                  rfl

theorem cell23_7472952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 9].length) (baseStart_7472952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472952 prefixEnd_7472952 := by exact prefixLift 7472952
  have htrace : WordTrace (prefixWord ++ tailWord_7472952) baseStart_7472952 baseEnd_7472952 := by
    simpa [prefixWord, tailWord_7472952, baseEnd_7472952] using wordTrace_append hprefix tailTrace_7472952
  have hstable : (prefixWord ++ tailWord_7472952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472952).length < 2 ^ (prefixWord ++ tailWord_7472952).sum := by decide
  have hdescent : baseEnd_7472952 < baseStart_7472952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7472973 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_7472973 : Nat := 118140960795 + 7472973 * 2 ^ 59
def prefixEnd_7472973 : Nat := 4983230072969 + 3 ^ 40 * 7472973 * 2
def baseEnd_7472973 : Nat := 1279075689023898564156643

theorem tailTrace_7472973 : CollatzResearch.WordTrace tailWord_7472973 prefixEnd_7472973 1279075689023898564156643 := by
  unfold tailWord_7472973
  simp only [CollatzResearch.WordTrace]
  refine ⟨272561717155702578023495573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181707811437135052015663715 272561717155702578023495573)
  ·
    refine ⟨12776330491673558344851355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 272561717155702578023495573 12776330491673558344851355)
    ·
      refine ⟨19164495737510337517277033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12776330491673558344851355 19164495737510337517277033)
      ·
        refine ⟨14373371803132753137957775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19164495737510337517277033 14373371803132753137957775)
        ·
          refine ⟨21560057704699129706936663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14373371803132753137957775 21560057704699129706936663)
          ·
            refine ⟨32340086557048694560404995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21560057704699129706936663 32340086557048694560404995)
            ·
              refine ⟨48510129835573041840607493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32340086557048694560404995 48510129835573041840607493)
              ·
                refine ⟨9095649344169945345113905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48510129835573041840607493 9095649344169945345113905)
                ·
                  refine ⟨6821737008127459008835429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9095649344169945345113905 6821737008127459008835429)
                  ·
                    refine ⟨1279075689023898564156643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821737008127459008835429 1279075689023898564156643)
                    ·
                      rfl

theorem cell23_7472973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_7472973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7472973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7472973 prefixEnd_7472973 := by exact prefixLift 7472973
  have htrace : WordTrace (prefixWord ++ tailWord_7472973) baseStart_7472973 baseEnd_7472973 := by
    simpa [prefixWord, tailWord_7472973, baseEnd_7472973] using wordTrace_append hprefix tailTrace_7472973
  have hstable : (prefixWord ++ tailWord_7472973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7472973).length < 2 ^ (prefixWord ++ tailWord_7472973).sum := by decide
  have hdescent : baseEnd_7472973 < baseStart_7472973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7472973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473014 : List Nat := [5, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7473014 : Nat := 118140960795 + 7473014 * 2 ^ 59
def prefixEnd_7473014 : Nat := 4983230072969 + 3 ^ 40 * 7473014 * 2
def baseEnd_7473014 : Nat := 3837248119778530032057241

theorem tailTrace_7473014 : CollatzResearch.WordTrace tailWord_7473014 prefixEnd_7473014 3837248119778530032057241 := by
  unfold tailWord_7473014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17035200784284627626608631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181708808365702694683825397 17035200784284627626608631)
  ·
    refine ⟨25552801176426941439912947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17035200784284627626608631 25552801176426941439912947)
    ·
      refine ⟨38329201764640412159869421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25552801176426941439912947 38329201764640412159869421)
      ·
        refine ⟨14373450661740154559951033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38329201764640412159869421 14373450661740154559951033)
        ·
          refine ⟨10780087996305115919963275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14373450661740154559951033 10780087996305115919963275)
          ·
            refine ⟨16170131994457673879944913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780087996305115919963275 16170131994457673879944913)
            ·
              refine ⟨12127598995843255409958685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16170131994457673879944913 12127598995843255409958685)
              ·
                refine ⟨4547849623441220778734507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12127598995843255409958685 4547849623441220778734507)
                ·
                  refine ⟨6821774435161831168101761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547849623441220778734507 6821774435161831168101761)
                  ·
                    refine ⟨5116330826371373376076321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6821774435161831168101761 5116330826371373376076321)
                    ·
                      refine ⟨3837248119778530032057241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116330826371373376076321 3837248119778530032057241)
                      ·
                        rfl

theorem cell23_7473014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7473014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473014 prefixEnd_7473014 := by exact prefixLift 7473014
  have htrace : WordTrace (prefixWord ++ tailWord_7473014) baseStart_7473014 baseEnd_7473014 := by
    simpa [prefixWord, tailWord_7473014, baseEnd_7473014] using wordTrace_append hprefix tailTrace_7473014
  have hstable : (prefixWord ++ tailWord_7473014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473014).length < 2 ^ (prefixWord ++ tailWord_7473014).sum := by decide
  have hdescent : baseEnd_7473014 < baseStart_7473014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473049 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_7473049 : Nat := 118140960795 + 7473049 * 2 ^ 59
def prefixEnd_7473049 : Nat := 4983230072969 + 3 ^ 40 * 7473049 * 2
def baseEnd_7473049 : Nat := 3837266091601437395119579

theorem tailTrace_7473049 : CollatzResearch.WordTrace tailWord_7473049 prefixEnd_7473049 3837266091601437395119579 := by
  unfold tailWord_7473049
  simp only [CollatzResearch.WordTrace]
  refine ⟨272564489103427243003262201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181709659402284828668841467 272564489103427243003262201)
  ·
    refine ⟨204423366827570432252446651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272564489103427243003262201 204423366827570432252446651)
    ·
      refine ⟨306635050241355648378669977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204423366827570432252446651 306635050241355648378669977)
      ·
        refine ⟨229976287681016736284002483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306635050241355648378669977 229976287681016736284002483)
        ·
          refine ⟨344964431521525104426003725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229976287681016736284002483 344964431521525104426003725)
          ·
            refine ⟨129361661820571914159751397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344964431521525104426003725 129361661820571914159751397)
            ·
              refine ⟨24255311591357233904953387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129361661820571914159751397 24255311591357233904953387)
              ·
                refine ⟨36382967387035850857430081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24255311591357233904953387 36382967387035850857430081)
                ·
                  refine ⟨27287225540276888143072561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36382967387035850857430081 27287225540276888143072561)
                  ·
                    refine ⟨20465419155207666107304421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27287225540276888143072561 20465419155207666107304421)
                    ·
                      refine ⟨3837266091601437395119579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20465419155207666107304421 3837266091601437395119579)
                      ·
                        rfl

theorem cell23_7473049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_7473049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473049 prefixEnd_7473049 := by exact prefixLift 7473049
  have htrace : WordTrace (prefixWord ++ tailWord_7473049) baseStart_7473049 baseEnd_7473049 := by
    simpa [prefixWord, tailWord_7473049, baseEnd_7473049] using wordTrace_append hprefix tailTrace_7473049
  have hstable : (prefixWord ++ tailWord_7473049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473049).length < 2 ^ (prefixWord ++ tailWord_7473049).sum := by decide
  have hdescent : baseEnd_7473049 < baseStart_7473049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473053 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_7473053 : Nat := 118140960795 + 7473053 * 2 ^ 59
def prefixEnd_7473053 : Nat := 4983230072969 + 3 ^ 40 * 7473053 * 2
def baseEnd_7473053 : Nat := 3837268145524055379469561

theorem tailTrace_7473053 : CollatzResearch.WordTrace tailWord_7473053 prefixEnd_7473053 3837268145524055379469561 := by
  unfold tailWord_7473053
  simp only [CollatzResearch.WordTrace]
  refine ⟨272564634995412751686407813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181709756663608501124271875 272564634995412751686407813)
  ·
    refine ⟨51105869061639890941201465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272564634995412751686407813 51105869061639890941201465)
    ·
      refine ⟨38329401796229918205901099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51105869061639890941201465 38329401796229918205901099)
      ·
        refine ⟨57494102694344877308851649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38329401796229918205901099 57494102694344877308851649)
        ·
          refine ⟨43120577020758657981638737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57494102694344877308851649 43120577020758657981638737)
          ·
            refine ⟨32340432765568993486229053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43120577020758657981638737 32340432765568993486229053)
            ·
              refine ⟨12127662287088372557335895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32340432765568993486229053 12127662287088372557335895)
              ·
                refine ⟨18191493430632558836003843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12127662287088372557335895 18191493430632558836003843)
                ·
                  refine ⟨27287240145948838254005765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18191493430632558836003843 27287240145948838254005765)
                  ·
                    refine ⟨5116357527365407172626081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27287240145948838254005765 5116357527365407172626081)
                    ·
                      refine ⟨3837268145524055379469561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116357527365407172626081 3837268145524055379469561)
                      ·
                        rfl

theorem cell23_7473053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_7473053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473053 prefixEnd_7473053 := by exact prefixLift 7473053
  have htrace : WordTrace (prefixWord ++ tailWord_7473053) baseStart_7473053 baseEnd_7473053 := by
    simpa [prefixWord, tailWord_7473053, baseEnd_7473053] using wordTrace_append hprefix tailTrace_7473053
  have hstable : (prefixWord ++ tailWord_7473053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473053).length < 2 ^ (prefixWord ++ tailWord_7473053).sum := by decide
  have hdescent : baseEnd_7473053 < baseStart_7473053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473099 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5]
def baseStart_7473099 : Nat := 118140960795 + 7473099 * 2 ^ 59
def prefixEnd_7473099 : Nat := 4983230072969 + 3 ^ 40 * 7473099 * 2
def baseEnd_7473099 : Nat := 3837291765634162199494349

theorem tailTrace_7473099 : CollatzResearch.WordTrace tailWord_7473099 prefixEnd_7473099 3837291765634162199494349 := by
  unfold tailWord_7473099
  simp only [CollatzResearch.WordTrace]
  refine ⟨272566312753246101542582351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181710875168830734361721567 272566312753246101542582351)
  ·
    refine ⟨408849469129869152313873527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272566312753246101542582351 408849469129869152313873527)
    ·
      refine ⟨613274203694803728470810291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408849469129869152313873527 613274203694803728470810291)
      ·
        refine ⟨919911305542205592706215437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613274203694803728470810291 919911305542205592706215437)
        ·
          refine ⟨344966739578327097264830789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 919911305542205592706215437 344966739578327097264830789)
          ·
            refine ⟨64681263670936330737155773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344966739578327097264830789 64681263670936330737155773)
            ·
              refine ⟨24255473876601124026433415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64681263670936330737155773 24255473876601124026433415)
              ·
                refine ⟨36383210814901686039650123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24255473876601124026433415 36383210814901686039650123)
                ·
                  refine ⟨54574816222352529059475185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36383210814901686039650123 54574816222352529059475185)
                  ·
                    refine ⟨40931112166764396794606389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54574816222352529059475185 40931112166764396794606389)
                    ·
                      refine ⟨3837291765634162199494349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40931112166764396794606389 3837291765634162199494349)
                      ·
                        rfl

theorem cell23_7473099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_7473099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473099 prefixEnd_7473099 := by exact prefixLift 7473099
  have htrace : WordTrace (prefixWord ++ tailWord_7473099) baseStart_7473099 baseEnd_7473099 := by
    simpa [prefixWord, tailWord_7473099, baseEnd_7473099] using wordTrace_append hprefix tailTrace_7473099
  have hstable : (prefixWord ++ tailWord_7473099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473099).length < 2 ^ (prefixWord ++ tailWord_7473099).sum := by decide
  have hdescent : baseEnd_7473099 < baseStart_7473099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473149 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 8]
def baseStart_7473149 : Nat := 118140960795 + 7473149 * 2 ^ 59
def prefixEnd_7473149 : Nat := 4983230072969 + 3 ^ 40 * 7473149 * 2
def baseEnd_7473149 : Nat := 426368604407431889318791

theorem tailTrace_7473149 : CollatzResearch.WordTrace tailWord_7473149 prefixEnd_7473149 426368604407431889318791 := by
  unfold tailWord_7473149
  simp only [CollatzResearch.WordTrace]
  refine ⟨272568136403064960081902501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181712090935376640054601667 272568136403064960081902501)
  ·
    refine ⟨51106525575574680015356719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272568136403064960081902501 51106525575574680015356719)
    ·
      refine ⟨76659788363362020023035079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51106525575574680015356719 76659788363362020023035079)
      ·
        refine ⟨114989682545043030034552619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76659788363362020023035079 114989682545043030034552619)
        ·
          refine ⟨172484523817564545051828929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114989682545043030034552619 172484523817564545051828929)
          ·
            refine ⟨129363392863173408788871697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172484523817564545051828929 129363392863173408788871697)
            ·
              refine ⟨97022544647380056591653773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129363392863173408788871697 97022544647380056591653773)
              ·
                refine ⟨36383454242767521221870165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97022544647380056591653773 36383454242767521221870165)
                ·
                  refine ⟨426368604407431889318791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36383454242767521221870165 426368604407431889318791)
                  ·
                    rfl

theorem cell23_7473149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_7473149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473149 prefixEnd_7473149 := by exact prefixLift 7473149
  have htrace : WordTrace (prefixWord ++ tailWord_7473149) baseStart_7473149 baseEnd_7473149 := by
    simpa [prefixWord, tailWord_7473149, baseEnd_7473149] using wordTrace_append hprefix tailTrace_7473149
  have hstable : (prefixWord ++ tailWord_7473149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473149).length < 2 ^ (prefixWord ++ tailWord_7473149).sum := by decide
  have hdescent : baseEnd_7473149 < baseStart_7473149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473166 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_7473166 : Nat := 118140960795 + 7473166 * 2 ^ 59
def prefixEnd_7473166 : Nat := 4983230072969 + 3 ^ 40 * 7473166 * 2
def baseEnd_7473166 : Nat := 426369574315334826372949

theorem tailTrace_7473166 : CollatzResearch.WordTrace tailWord_7473166 prefixEnd_7473166 426369574315334826372949 := by
  unfold tailWord_7473166
  simp only [CollatzResearch.WordTrace]
  refine ⟨34071094555500421498158919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181712504296002247990180901 34071094555500421498158919)
  ·
    refine ⟨51106641833250632247238379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34071094555500421498158919 51106641833250632247238379)
    ·
      refine ⟨76659962749875948370857569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51106641833250632247238379 76659962749875948370857569)
      ·
        refine ⟨57494972062406961278143177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76659962749875948370857569 57494972062406961278143177)
        ·
          refine ⟨43121229046805220958607383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57494972062406961278143177 43121229046805220958607383)
          ·
            refine ⟨64681843570207831437911075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43121229046805220958607383 64681843570207831437911075)
            ·
              refine ⟨97022765355311747156866613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64681843570207831437911075 97022765355311747156866613)
              ·
                refine ⟨9095884252060476295956245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97022765355311747156866613 9095884252060476295956245)
                ·
                  refine ⟨426369574315334826372949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9095884252060476295956245 426369574315334826372949)
                  ·
                    rfl

theorem cell23_7473166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_7473166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473166 prefixEnd_7473166 := by exact prefixLift 7473166
  have htrace : WordTrace (prefixWord ++ tailWord_7473166) baseStart_7473166 baseEnd_7473166 := by
    simpa [prefixWord, tailWord_7473166, baseEnd_7473166] using wordTrace_append hprefix tailTrace_7473166
  have hstable : (prefixWord ++ tailWord_7473166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473166).length < 2 ^ (prefixWord ++ tailWord_7473166).sum := by decide
  have hdescent : baseEnd_7473166 < baseStart_7473166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473180 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_7473180 : Nat := 118140960795 + 7473180 * 2 ^ 59
def prefixEnd_7473180 : Nat := 4983230072969 + 3 ^ 40 * 7473180 * 2
def baseEnd_7473180 : Nat := 3837333357567176382581477

theorem tailTrace_7473180 : CollatzResearch.WordTrace tailWord_7473180 prefixEnd_7473180 3837333357567176382581477 := by
  unfold tailWord_7473180
  simp only [CollatzResearch.WordTrace]
  refine ⟨136284633532976326188140497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181712844710635101584187329 136284633532976326188140497)
  ·
    refine ⟨102213475149732244641105373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136284633532976326188140497 102213475149732244641105373)
    ·
      refine ⟨38330053181149591740414515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102213475149732244641105373 38330053181149591740414515)
      ·
        refine ⟨57495079771724387610621773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38330053181149591740414515 57495079771724387610621773)
        ·
          refine ⟨21560654914396645353983165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57495079771724387610621773 21560654914396645353983165)
          ·
            refine ⟨8085245592898742007743687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21560654914396645353983165 8085245592898742007743687)
            ·
              refine ⟨12127868389348113011615531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085245592898742007743687 12127868389348113011615531)
              ·
                refine ⟨18191802584022169517423297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12127868389348113011615531 18191802584022169517423297)
                ·
                  refine ⟨13643851938016627138067473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18191802584022169517423297 13643851938016627138067473)
                  ·
                    refine ⟨10232888953512470353550605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13643851938016627138067473 10232888953512470353550605)
                    ·
                      refine ⟨3837333357567176382581477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10232888953512470353550605 3837333357567176382581477)
                      ·
                        rfl

theorem cell23_7473180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_7473180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473180 prefixEnd_7473180 := by exact prefixLift 7473180
  have htrace : WordTrace (prefixWord ++ tailWord_7473180) baseStart_7473180 baseEnd_7473180 := by
    simpa [prefixWord, tailWord_7473180, baseEnd_7473180] using wordTrace_append hprefix tailTrace_7473180
  have hstable : (prefixWord ++ tailWord_7473180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473180).length < 2 ^ (prefixWord ++ tailWord_7473180).sum := by decide
  have hdescent : baseEnd_7473180 < baseStart_7473180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473203 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 2, 3, 2]
def baseStart_7473203 : Nat := 118140960795 + 7473203 * 2 ^ 59
def prefixEnd_7473203 : Nat := 4983230072969 + 3 ^ 40 * 7473203 * 2
def baseEnd_7473203 : Nat := 3837345167622229792593871

theorem tailTrace_7473203 : CollatzResearch.WordTrace tailWord_7473203 prefixEnd_7473203 3837345167622229792593871 := by
  unfold tailWord_7473203
  simp only [CollatzResearch.WordTrace]
  refine ⟨272570105944869327304368263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181713403963246218202912175 272570105944869327304368263)
  ·
    refine ⟨408855158917303990956552395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272570105944869327304368263 408855158917303990956552395)
    ·
      refine ⟨613282738375955986434828593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408855158917303990956552395 613282738375955986434828593)
      ·
        refine ⟨459962053781966989826121445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613282738375955986434828593 459962053781966989826121445)
        ·
          refine ⟨86242885084118810592397771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459962053781966989826121445 86242885084118810592397771)
          ·
            refine ⟨129364327626178215888596657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86242885084118810592397771 129364327626178215888596657)
            ·
              refine ⟨97023245719633661916447493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129364327626178215888596657 97023245719633661916447493)
              ·
                refine ⟨18191858572431311609333905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97023245719633661916447493 18191858572431311609333905)
                ·
                  refine ⟨13643893929323483707000429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18191858572431311609333905 13643893929323483707000429)
                  ·
                    refine ⟨5116460223496306390125161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13643893929323483707000429 5116460223496306390125161)
                    ·
                      refine ⟨3837345167622229792593871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116460223496306390125161 3837345167622229792593871)
                      ·
                        rfl

theorem cell23_7473203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 3, 2].length) (baseStart_7473203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473203 prefixEnd_7473203 := by exact prefixLift 7473203
  have htrace : WordTrace (prefixWord ++ tailWord_7473203) baseStart_7473203 baseEnd_7473203 := by
    simpa [prefixWord, tailWord_7473203, baseEnd_7473203] using wordTrace_append hprefix tailTrace_7473203
  have hstable : (prefixWord ++ tailWord_7473203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473203).length < 2 ^ (prefixWord ++ tailWord_7473203).sum := by decide
  have hdescent : baseEnd_7473203 < baseStart_7473203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473236 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_7473236 : Nat := 118140960795 + 7473236 * 2 ^ 59
def prefixEnd_7473236 : Nat := 4983230072969 + 3 ^ 40 * 7473236 * 2
def baseEnd_7473236 : Nat := 3837362112483828163481219

theorem tailTrace_7473236 : CollatzResearch.WordTrace tailWord_7473236 prefixEnd_7473236 3837362112483828163481219 := by
  unfold tailWord_7473236
  simp only [CollatzResearch.WordTrace]
  refine ⟨136285654776874886970159781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181714206369166515960213041 136285654776874886970159781)
  ·
    refine ⟨25553560270664041306904959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136285654776874886970159781 25553560270664041306904959)
    ·
      refine ⟨38330340405996061960357439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25553560270664041306904959 38330340405996061960357439)
      ·
        refine ⟨57495510608994092940536159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38330340405996061960357439 57495510608994092940536159)
        ·
          refine ⟨86243265913491139410804239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57495510608994092940536159 86243265913491139410804239)
          ·
            refine ⟨129364898870236709116206359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86243265913491139410804239 129364898870236709116206359)
            ·
              refine ⟨194047348305355063674309539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129364898870236709116206359 194047348305355063674309539)
              ·
                refine ⟨291071022458032595511464309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194047348305355063674309539 291071022458032595511464309)
                ·
                  refine ⟨27287908355440555829199779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291071022458032595511464309 27287908355440555829199779)
                  ·
                    refine ⟨40931862533160833743799669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27287908355440555829199779 40931862533160833743799669)
                    ·
                      refine ⟨3837362112483828163481219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40931862533160833743799669 3837362112483828163481219)
                      ·
                        rfl

theorem cell23_7473236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_7473236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473236 prefixEnd_7473236 := by exact prefixLift 7473236
  have htrace : WordTrace (prefixWord ++ tailWord_7473236) baseStart_7473236 baseEnd_7473236 := by
    simpa [prefixWord, tailWord_7473236, baseEnd_7473236] using wordTrace_append hprefix tailTrace_7473236
  have hstable : (prefixWord ++ tailWord_7473236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473236).length < 2 ^ (prefixWord ++ tailWord_7473236).sum := by decide
  have hdescent : baseEnd_7473236 < baseStart_7473236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473244 : List Nat := [2, 2, 4, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_7473244 : Nat := 118140960795 + 7473244 * 2 ^ 59
def prefixEnd_7473244 : Nat := 4983230072969 + 3 ^ 40 * 7473244 * 2
def baseEnd_7473244 : Nat := 3837366220329064132181183

theorem tailTrace_7473244 : CollatzResearch.WordTrace tailWord_7473244 prefixEnd_7473244 3837366220329064132181183 := by
  unfold tailWord_7473244
  simp only [CollatzResearch.WordTrace]
  refine ⟨136285800668860395653305393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181714400891813860871073857 136285800668860395653305393)
  ·
    refine ⟨102214350501645296739979045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136285800668860395653305393 102214350501645296739979045)
    ·
      refine ⟨19165190719058493138746071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102214350501645296739979045 19165190719058493138746071)
      ·
        refine ⟨28747786078587739708119107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19165190719058493138746071 28747786078587739708119107)
        ·
          refine ⟨43121679117881609562178661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28747786078587739708119107 43121679117881609562178661)
          ·
            refine ⟨8085314834602801792908499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43121679117881609562178661 8085314834602801792908499)
            ·
              refine ⟨12127972251904202689362749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085314834602801792908499 12127972251904202689362749)
              ·
                refine ⟨4547989594464076008511031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12127972251904202689362749 4547989594464076008511031)
                ·
                  refine ⟨6821984391696114012766547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547989594464076008511031 6821984391696114012766547)
                  ·
                    refine ⟨10232976587544171019149821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6821984391696114012766547 10232976587544171019149821)
                    ·
                      refine ⟨3837366220329064132181183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10232976587544171019149821 3837366220329064132181183)
                      ·
                        rfl

theorem cell23_7473244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_7473244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473244 prefixEnd_7473244 := by exact prefixLift 7473244
  have htrace : WordTrace (prefixWord ++ tailWord_7473244) baseStart_7473244 baseEnd_7473244 := by
    simpa [prefixWord, tailWord_7473244, baseEnd_7473244] using wordTrace_append hprefix tailTrace_7473244
  have hstable : (prefixWord ++ tailWord_7473244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473244).length < 2 ^ (prefixWord ++ tailWord_7473244).sum := by decide
  have hdescent : baseEnd_7473244 < baseStart_7473244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473253 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_7473253 : Nat := 118140960795 + 7473253 * 2 ^ 59
def prefixEnd_7473253 : Nat := 4983230072969 + 3 ^ 40 * 7473253 * 2
def baseEnd_7473253 : Nat := 3837370841654954596968641

theorem tailTrace_7473253 : CollatzResearch.WordTrace tailWord_7473253 prefixEnd_7473253 3837370841654954596968641 := by
  unfold tailWord_7473253
  simp only [CollatzResearch.WordTrace]
  refine ⟨272571929594688185843688413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181714619729792123895792275 272571929594688185843688413)
  ·
    refine ⟨102214473598008069691383155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272571929594688185843688413 102214473598008069691383155)
    ·
      refine ⟨153321710397012104537074733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102214473598008069691383155 153321710397012104537074733)
      ·
        refine ⟨57495641398879539201403025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153321710397012104537074733 57495641398879539201403025)
        ·
          refine ⟨43121731049159654401052269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57495641398879539201403025 43121731049159654401052269)
          ·
            refine ⟨16170649143434870400394601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43121731049159654401052269 16170649143434870400394601)
            ·
              refine ⟨12127986857576152800295951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16170649143434870400394601 12127986857576152800295951)
              ·
                refine ⟨18191980286364229200443927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12127986857576152800295951 18191980286364229200443927)
                ·
                  refine ⟨27287970429546343800665891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18191980286364229200443927 27287970429546343800665891)
                  ·
                    refine ⟨40931955644319515700998837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27287970429546343800665891 40931955644319515700998837)
                    ·
                      refine ⟨3837370841654954596968641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40931955644319515700998837 3837370841654954596968641)
                      ·
                        rfl

theorem cell23_7473253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_7473253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473253 prefixEnd_7473253 := by exact prefixLift 7473253
  have htrace : WordTrace (prefixWord ++ tailWord_7473253) baseStart_7473253 baseEnd_7473253 := by
    simpa [prefixWord, tailWord_7473253, baseEnd_7473253] using wordTrace_append hprefix tailTrace_7473253
  have hstable : (prefixWord ++ tailWord_7473253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473253).length < 2 ^ (prefixWord ++ tailWord_7473253).sum := by decide
  have hdescent : baseEnd_7473253 < baseStart_7473253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473277 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_7473277 : Nat := 118140960795 + 7473277 * 2 ^ 59
def prefixEnd_7473277 : Nat := 4983230072969 + 3 ^ 40 * 7473277 * 2
def baseEnd_7473277 : Nat := 1279127721730220834356177

theorem tailTrace_7473277 : CollatzResearch.WordTrace tailWord_7473277 prefixEnd_7473277 1279127721730220834356177 := by
  unfold tailWord_7473277
  simp only [CollatzResearch.WordTrace]
  refine ⟨272572804946601237942562085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181715203297734158628374723 272572804946601237942562085)
  ·
    refine ⟨51107400927487732114230391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272572804946601237942562085 51107400927487732114230391)
    ·
      refine ⟨76661101391231598171345587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51107400927487732114230391 76661101391231598171345587)
      ·
        refine ⟨114991652086847397257018381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76661101391231598171345587 114991652086847397257018381)
        ·
          refine ⟨43121869532567773971381893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114991652086847397257018381 43121869532567773971381893)
          ·
            refine ⟨8085350537356457619634105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43121869532567773971381893 8085350537356457619634105)
            ·
              refine ⟨6064012903017343214725579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8085350537356457619634105 6064012903017343214725579)
              ·
                refine ⟨9096019354526014822088369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064012903017343214725579 9096019354526014822088369)
                ·
                  refine ⟨6822014515894511116566277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9096019354526014822088369 6822014515894511116566277)
                  ·
                    refine ⟨1279127721730220834356177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6822014515894511116566277 1279127721730220834356177)
                    ·
                      rfl

theorem cell23_7473277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_7473277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473277 prefixEnd_7473277 := by exact prefixLift 7473277
  have htrace : WordTrace (prefixWord ++ tailWord_7473277) baseStart_7473277 baseEnd_7473277 := by
    simpa [prefixWord, tailWord_7473277, baseEnd_7473277] using wordTrace_append hprefix tailTrace_7473277
  have hstable : (prefixWord ++ tailWord_7473277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473277).length < 2 ^ (prefixWord ++ tailWord_7473277).sum := by decide
  have hdescent : baseEnd_7473277 < baseStart_7473277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473410 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_7473410 : Nat := 118140960795 + 7473410 * 2 ^ 59
def prefixEnd_7473410 : Nat := 4983230072969 + 3 ^ 40 * 7473410 * 2
def baseEnd_7473410 : Nat := 1279150486039236827568473

theorem tailTrace_7473410 : CollatzResearch.WordTrace tailWord_7473410 prefixEnd_7473410 1279150486039236827568473 := by
  unfold tailWord_7473410
  simp only [CollatzResearch.WordTrace]
  refine ⟨68144413963779850414288421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181718437236746267771435789 68144413963779850414288421)
  ·
    refine ⟨12777077618208721952679079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68144413963779850414288421 12777077618208721952679079)
    ·
      refine ⟨19165616427313082929018619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12777077618208721952679079 19165616427313082929018619)
      ·
        refine ⟨28748424640969624393527929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19165616427313082929018619 28748424640969624393527929)
        ·
          refine ⟨21561318480727218295145947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28748424640969624393527929 21561318480727218295145947)
          ·
            refine ⟨32341977721090827442718921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21561318480727218295145947 32341977721090827442718921)
            ·
              refine ⟨24256483290818120582039191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32341977721090827442718921 24256483290818120582039191)
              ·
                refine ⟨36384724936227180873058787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24256483290818120582039191 36384724936227180873058787)
                ·
                  refine ⟨54577087404340771309588181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36384724936227180873058787 54577087404340771309588181)
                  ·
                    refine ⟨1279150486039236827568473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54577087404340771309588181 1279150486039236827568473)
                    ·
                      rfl

theorem cell23_7473410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_7473410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473410 prefixEnd_7473410 := by exact prefixLift 7473410
  have htrace : WordTrace (prefixWord ++ tailWord_7473410) baseStart_7473410 baseEnd_7473410 := by
    simpa [prefixWord, tailWord_7473410, baseEnd_7473410] using wordTrace_append hprefix tailTrace_7473410
  have hstable : (prefixWord ++ tailWord_7473410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473410).length < 2 ^ (prefixWord ++ tailWord_7473410).sum := by decide
  have hdescent : baseEnd_7473410 < baseStart_7473410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473423 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 5, 4]
def baseStart_7473423 : Nat := 118140960795 + 7473423 * 2 ^ 59
def prefixEnd_7473423 : Nat := 4983230072969 + 3 ^ 40 * 7473423 * 2
def baseEnd_7473423 : Nat := 1279152711122072977280953

theorem tailTrace_7473423 : CollatzResearch.WordTrace tailWord_7473423 prefixEnd_7473423 1279152711122072977280953 := by
  unfold tailWord_7473423
  simp only [CollatzResearch.WordTrace]
  refine ⟨272578130004072304877376923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181718753336048203251584615 272578130004072304877376923)
  ·
    refine ⟨408867195006108457316065385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272578130004072304877376923 408867195006108457316065385)
    ·
      refine ⟨306650396254581342987049039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408867195006108457316065385 306650396254581342987049039)
      ·
        refine ⟨459975594381872014480573559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306650396254581342987049039 459975594381872014480573559)
        ·
          refine ⟨689963391572808021720860339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459975594381872014480573559 689963391572808021720860339)
          ·
            refine ⟨1034945087359212032581290509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689963391572808021720860339 1034945087359212032581290509)
            ·
              refine ⟨388104407759704512217983941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1034945087359212032581290509 388104407759704512217983941)
              ·
                refine ⟨72769576454944596040871989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388104407759704512217983941 72769576454944596040871989)
                ·
                  refine ⟨6822147792651055878831749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72769576454944596040871989 6822147792651055878831749)
                  ·
                    refine ⟨1279152711122072977280953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6822147792651055878831749 1279152711122072977280953)
                    ·
                      rfl

theorem cell23_7473423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_7473423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473423 prefixEnd_7473423 := by exact prefixLift 7473423
  have htrace : WordTrace (prefixWord ++ tailWord_7473423) baseStart_7473423 baseEnd_7473423 := by
    simpa [prefixWord, tailWord_7473423, baseEnd_7473423] using wordTrace_append hprefix tailTrace_7473423
  have hstable : (prefixWord ++ tailWord_7473423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473423).length < 2 ^ (prefixWord ++ tailWord_7473423).sum := by decide
  have hdescent : baseEnd_7473423 < baseStart_7473423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473463 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_7473463 : Nat := 118140960795 + 7473463 * 2 ^ 59
def prefixEnd_7473463 : Nat := 4983230072969 + 3 ^ 40 * 7473463 * 2
def baseEnd_7473463 : Nat := 3837478672592398775342675

theorem tailTrace_7473463 : CollatzResearch.WordTrace tailWord_7473463 prefixEnd_7473463 3837478672592398775342675 := by
  unfold tailWord_7473463
  simp only [CollatzResearch.WordTrace]
  refine ⟨272579588923927391708833043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181719725949284927805888695 272579588923927391708833043)
  ·
    refine ⟨408869383385891087563249565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272579588923927391708833043 408869383385891087563249565)
    ·
      refine ⟨153326018769709157836218587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408869383385891087563249565 153326018769709157836218587)
      ·
        refine ⟨229989028154563736754327881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153326018769709157836218587 229989028154563736754327881)
        ·
          refine ⟨172491771115922802565745911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229989028154563736754327881 172491771115922802565745911)
          ·
            refine ⟨258737656673884203848618867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172491771115922802565745911 258737656673884203848618867)
            ·
              refine ⟨388106485010826305772928301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258737656673884203848618867 388106485010826305772928301)
              ·
                refine ⟨145539931879059864664848113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388106485010826305772928301 145539931879059864664848113)
                ·
                  refine ⟨109154948909294898498636085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145539931879059864664848113 109154948909294898498636085)
                  ·
                    refine ⟨10233276460246396734247133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109154948909294898498636085 10233276460246396734247133)
                    ·
                      refine ⟨3837478672592398775342675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10233276460246396734247133 3837478672592398775342675)
                      ·
                        rfl

theorem cell23_7473463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_7473463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473463 prefixEnd_7473463 := by exact prefixLift 7473463
  have htrace : WordTrace (prefixWord ++ tailWord_7473463) baseStart_7473463 baseEnd_7473463 := by
    simpa [prefixWord, tailWord_7473463, baseEnd_7473463] using wordTrace_append hprefix tailTrace_7473463
  have hstable : (prefixWord ++ tailWord_7473463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473463).length < 2 ^ (prefixWord ++ tailWord_7473463).sum := by decide
  have hdescent : baseEnd_7473463 < baseStart_7473463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473514 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_7473514 : Nat := 118140960795 + 7473514 * 2 ^ 59
def prefixEnd_7473514 : Nat := 4983230072969 + 3 ^ 40 * 7473514 * 2
def baseEnd_7473514 : Nat := 3837504860105778075804941

theorem tailTrace_7473514 : CollatzResearch.WordTrace tailWord_7473514 prefixEnd_7473514 3837504860105778075804941 := by
  unfold tailWord_7473514
  simp only [CollatzResearch.WordTrace]
  refine ⟨68145362261685656854734899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181720966031161751612626397 68145362261685656854734899)
  ·
    refine ⟨102218043392528485282102349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68145362261685656854734899 102218043392528485282102349)
    ·
      refine ⟨38331766272198181980788381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102218043392528485282102349 38331766272198181980788381)
      ·
        refine ⟨14374412352074318242795643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38331766272198181980788381 14374412352074318242795643)
        ·
          refine ⟨21561618528111477364193465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14374412352074318242795643 21561618528111477364193465)
          ·
            refine ⟨16171213896083608023145099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21561618528111477364193465 16171213896083608023145099)
            ·
              refine ⟨24256820844125412034717649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16171213896083608023145099 24256820844125412034717649)
              ·
                refine ⟨18192615633094059026038237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24256820844125412034717649 18192615633094059026038237)
                ·
                  refine ⟨6822230862410272134764339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18192615633094059026038237 6822230862410272134764339)
                  ·
                    refine ⟨10233346293615408202146509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6822230862410272134764339 10233346293615408202146509)
                    ·
                      refine ⟨3837504860105778075804941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10233346293615408202146509 3837504860105778075804941)
                      ·
                        rfl

theorem cell23_7473514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_7473514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473514 prefixEnd_7473514 := by exact prefixLift 7473514
  have htrace : WordTrace (prefixWord ++ tailWord_7473514) baseStart_7473514 baseEnd_7473514 := by
    simpa [prefixWord, tailWord_7473514, baseEnd_7473514] using wordTrace_append hprefix tailTrace_7473514
  have hstable : (prefixWord ++ tailWord_7473514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473514).length < 2 ^ (prefixWord ++ tailWord_7473514).sum := by decide
  have hdescent : baseEnd_7473514 < baseStart_7473514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473520 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_7473520 : Nat := 118140960795 + 7473520 * 2 ^ 59
def prefixEnd_7473520 : Nat := 4983230072969 + 3 ^ 40 * 7473520 * 2
def baseEnd_7473520 : Nat := 3837507940989705052329913

theorem tailTrace_7473520 : CollatzResearch.WordTrace tailWord_7473520 prefixEnd_7473520 3837507940989705052329913 := by
  unfold tailWord_7473520
  simp only [CollatzResearch.WordTrace]
  refine ⟨136290833942360445221829007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181721111923147260295772009 136290833942360445221829007)
  ·
    refine ⟨204436250913540667832743511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136290833942360445221829007 204436250913540667832743511)
    ·
      refine ⟨306654376370311001749115267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204436250913540667832743511 306654376370311001749115267)
      ·
        refine ⟨459981564555466502623672901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306654376370311001749115267 459981564555466502623672901)
        ·
          refine ⟨86246543354149969241938669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459981564555466502623672901 86246543354149969241938669)
          ·
            refine ⟨32342453757806238465727001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86246543354149969241938669 32342453757806238465727001)
            ·
              refine ⟨24256840318354678849295251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32342453757806238465727001 24256840318354678849295251)
              ·
                refine ⟨36385260477532018273942877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24256840318354678849295251 36385260477532018273942877)
                ·
                  refine ⟨13644472679074506852728579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36385260477532018273942877 13644472679074506852728579)
                  ·
                    refine ⟨20466709018611760279092869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13644472679074506852728579 20466709018611760279092869)
                    ·
                      refine ⟨3837507940989705052329913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20466709018611760279092869 3837507940989705052329913)
                      ·
                        rfl

theorem cell23_7473520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_7473520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473520 prefixEnd_7473520 := by exact prefixLift 7473520
  have htrace : WordTrace (prefixWord ++ tailWord_7473520) baseStart_7473520 baseEnd_7473520 := by
    simpa [prefixWord, tailWord_7473520, baseEnd_7473520] using wordTrace_append hprefix tailTrace_7473520
  have hstable : (prefixWord ++ tailWord_7473520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473520).length < 2 ^ (prefixWord ++ tailWord_7473520).sum := by decide
  have hdescent : baseEnd_7473520 < baseStart_7473520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473523 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5]
def baseStart_7473523 : Nat := 118140960795 + 7473523 * 2 ^ 59
def prefixEnd_7473523 : Nat := 4983230072969 + 3 ^ 40 * 7473523 * 2
def baseEnd_7473523 : Nat := 3837509481431668540592399

theorem tailTrace_7473523 : CollatzResearch.WordTrace tailWord_7473523 prefixEnd_7473523 3837509481431668540592399 := by
  unfold tailWord_7473523
  simp only [CollatzResearch.WordTrace]
  refine ⟨272581777303710021956017223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181721184869140014637344815 272581777303710021956017223)
  ·
    refine ⟨408872665955565032934025835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272581777303710021956017223 408872665955565032934025835)
    ·
      refine ⟨613308998933347549401038753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408872665955565032934025835 613308998933347549401038753)
      ·
        refine ⟨459981749200010662050779065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613308998933347549401038753 459981749200010662050779065)
        ·
          refine ⟨344986311900007996538084299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459981749200010662050779065 344986311900007996538084299)
          ·
            refine ⟨517479467850011994807126449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344986311900007996538084299 517479467850011994807126449)
            ·
              refine ⟨388109600887508996105344837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517479467850011994807126449 388109600887508996105344837)
              ·
                refine ⟨72770550166407936769752157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388109600887508996105344837 72770550166407936769752157)
                ·
                  refine ⟨27288956312402976288657059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72770550166407936769752157 27288956312402976288657059)
                  ·
                    refine ⟨40933434468604464432985589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27288956312402976288657059 40933434468604464432985589)
                    ·
                      refine ⟨3837509481431668540592399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40933434468604464432985589 3837509481431668540592399)
                      ·
                        rfl

theorem cell23_7473523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_7473523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473523 prefixEnd_7473523 := by exact prefixLift 7473523
  have htrace : WordTrace (prefixWord ++ tailWord_7473523) baseStart_7473523 baseEnd_7473523 := by
    simpa [prefixWord, tailWord_7473523, baseEnd_7473523] using wordTrace_append hprefix tailTrace_7473523
  have hstable : (prefixWord ++ tailWord_7473523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473523).length < 2 ^ (prefixWord ++ tailWord_7473523).sum := by decide
  have hdescent : baseEnd_7473523 < baseStart_7473523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473540 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_7473540 : Nat := 118140960795 + 7473540 * 2 ^ 59
def prefixEnd_7473540 : Nat := 4983230072969 + 3 ^ 40 * 7473540 * 2
def baseEnd_7473540 : Nat := 3837518210602794974079821

theorem tailTrace_7473540 : CollatzResearch.WordTrace tailWord_7473540 prefixEnd_7473540 3837518210602794974079821 := by
  unfold tailWord_7473540
  simp only [CollatzResearch.WordTrace]
  refine ⟨136291198672324216929693037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181721598229765622572924049 136291198672324216929693037)
  ·
    refine ⟨51109199502121581348634889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136291198672324216929693037 51109199502121581348634889)
    ·
      refine ⟨38331899626591186011476167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51109199502121581348634889 38331899626591186011476167)
      ·
        refine ⟨57497849439886779017214251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38331899626591186011476167 57497849439886779017214251)
        ·
          refine ⟨86246774159830168525821377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57497849439886779017214251 86246774159830168525821377)
          ·
            refine ⟨64685080619872626394366033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86246774159830168525821377 64685080619872626394366033)
            ·
              refine ⟨48513810464904469795774525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64685080619872626394366033 48513810464904469795774525)
              ·
                refine ⟨18192678924339176173415447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48513810464904469795774525 18192678924339176173415447)
                ·
                  refine ⟨27289018386508764260123171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18192678924339176173415447 27289018386508764260123171)
                  ·
                    refine ⟨40933527579763146390184757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27289018386508764260123171 40933527579763146390184757)
                    ·
                      refine ⟨3837518210602794974079821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40933527579763146390184757 3837518210602794974079821)
                      ·
                        rfl

theorem cell23_7473540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_7473540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473540 prefixEnd_7473540 := by exact prefixLift 7473540
  have htrace : WordTrace (prefixWord ++ tailWord_7473540) baseStart_7473540 baseEnd_7473540 := by
    simpa [prefixWord, tailWord_7473540, baseEnd_7473540] using wordTrace_append hprefix tailTrace_7473540
  have hstable : (prefixWord ++ tailWord_7473540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473540).length < 2 ^ (prefixWord ++ tailWord_7473540).sum := by decide
  have hdescent : baseEnd_7473540 < baseStart_7473540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473543 : List Nat := [1, 1, 4, 2, 2, 1, 12]
def baseStart_7473543 : Nat := 118140960795 + 7473543 * 2 ^ 59
def prefixEnd_7473543 : Nat := 4983230072969 + 3 ^ 40 * 7473543 * 2
def baseEnd_7473543 : Nat := 47376787049935289658547

theorem tailTrace_7473543 : CollatzResearch.WordTrace tailWord_7473543 prefixEnd_7473543 47376787049935289658547 := by
  unfold tailWord_7473543
  simp only [CollatzResearch.WordTrace]
  refine ⟨272582506763637565371745283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181721671175758376914496855 272582506763637565371745283)
  ·
    refine ⟨408873760145456348057617925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272582506763637565371745283 408873760145456348057617925)
    ·
      refine ⟨76663830027273065260803361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408873760145456348057617925 76663830027273065260803361)
      ·
        refine ⟨57497872520454798945602521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76663830027273065260803361 57497872520454798945602521)
        ·
          refine ⟨43123404390341099209201891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57497872520454798945602521 43123404390341099209201891)
          ·
            refine ⟨64685106585511648813802837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43123404390341099209201891 64685106585511648813802837)
            ·
              refine ⟨47376787049935289658547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 64685106585511648813802837 47376787049935289658547)
              ·
                rfl

theorem cell23_7473543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 12].length) (baseStart_7473543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473543 prefixEnd_7473543 := by exact prefixLift 7473543
  have htrace : WordTrace (prefixWord ++ tailWord_7473543) baseStart_7473543 baseEnd_7473543 := by
    simpa [prefixWord, tailWord_7473543, baseEnd_7473543] using wordTrace_append hprefix tailTrace_7473543
  have hstable : (prefixWord ++ tailWord_7473543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473543).length < 2 ^ (prefixWord ++ tailWord_7473543).sum := by decide
  have hdescent : baseEnd_7473543 < baseStart_7473543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473547 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 2, 4]
def baseStart_7473547 : Nat := 118140960795 + 7473547 * 2 ^ 59
def prefixEnd_7473547 : Nat := 4983230072969 + 3 ^ 40 * 7473547 * 2
def baseEnd_7473547 : Nat := 1279173934989125482230763

theorem tailTrace_7473547 : CollatzResearch.WordTrace tailWord_7473547 prefixEnd_7473547 1279173934989125482230763 := by
  unfold tailWord_7473547
  simp only [CollatzResearch.WordTrace]
  refine ⟨272582652655623074054890895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181721768437082049369927263 272582652655623074054890895)
  ·
    refine ⟨408873978983434611082336343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272582652655623074054890895 408873978983434611082336343)
    ·
      refine ⟨613310968475151916623504515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408873978983434611082336343 613310968475151916623504515)
      ·
        refine ⟨919966452712727874935256773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613310968475151916623504515 919966452712727874935256773)
        ·
          refine ⟨172493709883636476550360645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 919966452712727874935256773 172493709883636476550360645)
          ·
            refine ⟨32342570603181839353192621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172493709883636476550360645 32342570603181839353192621)
            ·
              refine ⟨12128463976193189757447233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32342570603181839353192621 12128463976193189757447233)
              ·
                refine ⟨9096347982144892318085425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12128463976193189757447233 9096347982144892318085425)
                ·
                  refine ⟨6822260986608669238564069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9096347982144892318085425 6822260986608669238564069)
                  ·
                    refine ⟨1279173934989125482230763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6822260986608669238564069 1279173934989125482230763)
                    ·
                      rfl

theorem cell23_7473547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 4].length) (baseStart_7473547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473547 prefixEnd_7473547 := by exact prefixLift 7473547
  have htrace : WordTrace (prefixWord ++ tailWord_7473547) baseStart_7473547 baseEnd_7473547 := by
    simpa [prefixWord, tailWord_7473547, baseEnd_7473547] using wordTrace_append hprefix tailTrace_7473547
  have hstable : (prefixWord ++ tailWord_7473547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473547).length < 2 ^ (prefixWord ++ tailWord_7473547).sum := by decide
  have hdescent : baseEnd_7473547 < baseStart_7473547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473610 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_7473610 : Nat := 118140960795 + 7473610 * 2 ^ 59
def prefixEnd_7473610 : Nat := 4983230072969 + 3 ^ 40 * 7473610 * 2
def baseEnd_7473610 : Nat := 3837554154248609700204499

theorem tailTrace_7473610 : CollatzResearch.WordTrace tailWord_7473610 prefixEnd_7473610 3837554154248609700204499 := by
  unfold tailWord_7473610
  simp only [CollatzResearch.WordTrace]
  refine ⟨68146237613598708953608571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181723300302929890542956189 68146237613598708953608571)
  ·
    refine ⟨102219356420398063430412857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68146237613598708953608571 102219356420398063430412857)
    ·
      refine ⟨76664517315298547572809643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102219356420398063430412857 76664517315298547572809643)
      ·
        refine ⟨114996775972947821359214465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76664517315298547572809643 114996775972947821359214465)
        ·
          refine ⟨86247581979710866019410849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114996775972947821359214465 86247581979710866019410849)
          ·
            refine ⟨64685686484783149514558137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86247581979710866019410849 64685686484783149514558137)
            ·
              refine ⟨48514264863587362135918603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64685686484783149514558137 48514264863587362135918603)
              ·
                refine ⟨72771397295381043203877905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48514264863587362135918603 72771397295381043203877905)
                ·
                  refine ⟨54578547971535782402908429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72771397295381043203877905 54578547971535782402908429)
                  ·
                    refine ⟨20466955489325918401090661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54578547971535782402908429 20466955489325918401090661)
                    ·
                      refine ⟨3837554154248609700204499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20466955489325918401090661 3837554154248609700204499)
                      ·
                        rfl

theorem cell23_7473610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_7473610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473610 prefixEnd_7473610 := by exact prefixLift 7473610
  have htrace : WordTrace (prefixWord ++ tailWord_7473610) baseStart_7473610 baseEnd_7473610 := by
    simpa [prefixWord, tailWord_7473610, baseEnd_7473610] using wordTrace_append hprefix tailTrace_7473610
  have hstable : (prefixWord ++ tailWord_7473610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473610).length < 2 ^ (prefixWord ++ tailWord_7473610).sum := by decide
  have hdescent : baseEnd_7473610 < baseStart_7473610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473621 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_7473621 : Nat := 118140960795 + 7473621 * 2 ^ 59
def prefixEnd_7473621 : Nat := 4983230072969 + 3 ^ 40 * 7473621 * 2
def baseEnd_7473621 : Nat := 3837559802535809157166949

theorem tailTrace_7473621 : CollatzResearch.WordTrace tailWord_7473621 prefixEnd_7473621 3837559802535809157166949 := by
  unfold tailWord_7473621
  simp only [CollatzResearch.WordTrace]
  refine ⟨272585351657354984693084717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181723567771569989795389811 272585351657354984693084717)
  ·
    refine ⟨102219506871508119259906769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272585351657354984693084717 102219506871508119259906769)
    ·
      refine ⟨76664630153631089444930077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102219506871508119259906769 76664630153631089444930077)
      ·
        refine ⟨28749236307611658541848779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76664630153631089444930077 28749236307611658541848779)
        ·
          refine ⟨43123854461417487812773169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28749236307611658541848779 43123854461417487812773169)
          ·
            refine ⟨32342890846063115859579877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43123854461417487812773169 32342890846063115859579877)
            ·
              refine ⟨6064292033636834223671227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32342890846063115859579877 6064292033636834223671227)
              ·
                refine ⟨9096438050455251335506841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064292033636834223671227 9096438050455251335506841)
                ·
                  refine ⟨6822328537841438501630131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9096438050455251335506841 6822328537841438501630131)
                  ·
                    refine ⟨10233492806762157752445197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6822328537841438501630131 10233492806762157752445197)
                    ·
                      refine ⟨3837559802535809157166949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10233492806762157752445197 3837559802535809157166949)
                      ·
                        rfl

theorem cell23_7473621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_7473621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473621 prefixEnd_7473621 := by exact prefixLift 7473621
  have htrace : WordTrace (prefixWord ++ tailWord_7473621) baseStart_7473621 baseEnd_7473621 := by
    simpa [prefixWord, tailWord_7473621, baseEnd_7473621] using wordTrace_append hprefix tailTrace_7473621
  have hstable : (prefixWord ++ tailWord_7473621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473621).length < 2 ^ (prefixWord ++ tailWord_7473621).sum := by decide
  have hdescent : baseEnd_7473621 < baseStart_7473621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473631 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 1, 3, 2]
def baseStart_7473631 : Nat := 118140960795 + 7473631 * 2 ^ 59
def prefixEnd_7473631 : Nat := 4983230072969 + 3 ^ 40 * 7473631 * 2
def baseEnd_7473631 : Nat := 3837564937342354118041903

theorem tailTrace_7473631 : CollatzResearch.WordTrace tailWord_7473631 prefixEnd_7473631 3837564937342354118041903 := by
  unfold tailWord_7473631
  simp only [CollatzResearch.WordTrace]
  refine ⟨272585716387318756400948747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181723810924879170933965831 272585716387318756400948747)
  ·
    refine ⟨408878574580978134601423121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272585716387318756400948747 408878574580978134601423121)
    ·
      refine ⟨306658930935733600951067341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408878574580978134601423121 306658930935733600951067341)
      ·
        refine ⟨114997099100900100356650253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306658930935733600951067341 114997099100900100356650253)
        ·
          refine ⟨43123912162837537633743845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114997099100900100356650253 43123912162837537633743845)
          ·
            refine ⟨8085733530532038306326971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43123912162837537633743845 8085733530532038306326971)
            ·
              refine ⟨12128600295798057459490457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085733530532038306326971 12128600295798057459490457)
              ·
                refine ⟨9096450221848543094617843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12128600295798057459490457 9096450221848543094617843)
                ·
                  refine ⟨13644675332772814641926765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9096450221848543094617843 13644675332772814641926765)
                  ·
                    refine ⟨5116753249789805490722537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13644675332772814641926765 5116753249789805490722537)
                    ·
                      refine ⟨3837564937342354118041903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116753249789805490722537 3837564937342354118041903)
                      ·
                        rfl

theorem cell23_7473631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_7473631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473631 prefixEnd_7473631 := by exact prefixLift 7473631
  have htrace : WordTrace (prefixWord ++ tailWord_7473631) baseStart_7473631 baseEnd_7473631 := by
    simpa [prefixWord, tailWord_7473631, baseEnd_7473631] using wordTrace_append hprefix tailTrace_7473631
  have hstable : (prefixWord ++ tailWord_7473631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473631).length < 2 ^ (prefixWord ++ tailWord_7473631).sum := by decide
  have hdescent : baseEnd_7473631 < baseStart_7473631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473661 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_7473661 : Nat := 118140960795 + 7473661 * 2 ^ 59
def prefixEnd_7473661 : Nat := 4983230072969 + 3 ^ 40 * 7473661 * 2
def baseEnd_7473661 : Nat := 3837580341761989000666765

theorem tailTrace_7473661 : CollatzResearch.WordTrace tailWord_7473661 prefixEnd_7473661 3837580341761989000666765 := by
  unfold tailWord_7473661
  simp only [CollatzResearch.WordTrace]
  refine ⟨272586810577210071524540837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181724540384806714349693891 272586810577210071524540837)
  ·
    refine ⟨51110026983226888410851407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272586810577210071524540837 51110026983226888410851407)
    ·
      refine ⟨76665040474840332616277111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51110026983226888410851407 76665040474840332616277111)
      ·
        refine ⟨114997560712260498924415667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76665040474840332616277111 114997560712260498924415667)
        ·
          refine ⟨172496341068390748386623501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114997560712260498924415667 172496341068390748386623501)
          ·
            refine ⟨64686127900646530644983813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172496341068390748386623501 64686127900646530644983813)
            ·
              refine ⟨12128648981371224495934465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64686127900646530644983813 12128648981371224495934465)
              ·
                refine ⟨9096486736028418371950849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12128648981371224495934465 9096486736028418371950849)
                ·
                  refine ⟨6822365052021313778963137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9096486736028418371950849 6822365052021313778963137)
                  ·
                    refine ⟨5116773789015985334222353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6822365052021313778963137 5116773789015985334222353)
                    ·
                      refine ⟨3837580341761989000666765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116773789015985334222353 3837580341761989000666765)
                      ·
                        rfl

theorem cell23_7473661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_7473661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473661 prefixEnd_7473661 := by exact prefixLift 7473661
  have htrace : WordTrace (prefixWord ++ tailWord_7473661) baseStart_7473661 baseEnd_7473661 := by
    simpa [prefixWord, tailWord_7473661, baseEnd_7473661] using wordTrace_append hprefix tailTrace_7473661
  have hstable : (prefixWord ++ tailWord_7473661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473661).length < 2 ^ (prefixWord ++ tailWord_7473661).sum := by decide
  have hdescent : baseEnd_7473661 < baseStart_7473661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473667 : List Nat := [1, 1, 1, 3, 2, 1, 5, 4, 5]
def baseStart_7473667 : Nat := 118140960795 + 7473667 * 2 ^ 59
def prefixEnd_7473667 : Nat := 4983230072969 + 3 ^ 40 * 7473667 * 2
def baseEnd_7473667 : Nat := 426398158071768441910193

theorem tailTrace_7473667 : CollatzResearch.WordTrace tailWord_7473667 prefixEnd_7473667 426398158071768441910193 := by
  unfold tailWord_7473667
  simp only [CollatzResearch.WordTrace]
  refine ⟨272587029415188334549259255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181724686276792223032839503 272587029415188334549259255)
  ·
    refine ⟨408880544122782501823888883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272587029415188334549259255 408880544122782501823888883)
    ·
      refine ⟨613320816184173752735833325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408880544122782501823888883 613320816184173752735833325)
      ·
        refine ⟨229995306069065157275937497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613320816184173752735833325 229995306069065157275937497)
        ·
          refine ⟨172496479551798867956953123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229995306069065157275937497 172496479551798867956953123)
          ·
            refine ⟨258744719327698301935429685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172496479551798867956953123 258744719327698301935429685)
            ·
              refine ⟨24257317436971715806446533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258744719327698301935429685 24257317436971715806446533)
              ·
                refine ⟨4548247019432196713708725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24257317436971715806446533 4548247019432196713708725)
                ·
                  refine ⟨426398158071768441910193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4548247019432196713708725 426398158071768441910193)
                  ·
                    rfl

theorem cell23_7473667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 5].length) (baseStart_7473667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473667 prefixEnd_7473667 := by exact prefixLift 7473667
  have htrace : WordTrace (prefixWord ++ tailWord_7473667) baseStart_7473667 baseEnd_7473667 := by
    simpa [prefixWord, tailWord_7473667, baseEnd_7473667] using wordTrace_append hprefix tailTrace_7473667
  have hstable : (prefixWord ++ tailWord_7473667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473667).length < 2 ^ (prefixWord ++ tailWord_7473667).sum := by decide
  have hdescent : baseEnd_7473667 < baseStart_7473667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473684 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 7]
def baseStart_7473684 : Nat := 118140960795 + 7473684 * 2 ^ 59
def prefixEnd_7473684 : Nat := 4983230072969 + 3 ^ 40 * 7473684 * 2
def baseEnd_7473684 : Nat := 426399127979671378964351

theorem tailTrace_7473684 : CollatzResearch.WordTrace tailWord_7473684 prefixEnd_7473684 426399127979671378964351 := by
  unfold tailWord_7473684
  simp only [CollatzResearch.WordTrace]
  refine ⟨136293824728063373226314053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181725099637417830968418737 136293824728063373226314053)
  ·
    refine ⟨25555092136511882479933885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136293824728063373226314053 25555092136511882479933885)
    ·
      refine ⟨9583159551191955929975207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25555092136511882479933885 9583159551191955929975207)
      ·
        refine ⟨14374739326787933894962811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9583159551191955929975207 14374739326787933894962811)
        ·
          refine ⟨21562108990181900842444217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14374739326787933894962811 21562108990181900842444217)
          ·
            refine ⟨16171581742636425631833163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21562108990181900842444217 16171581742636425631833163)
            ·
              refine ⟨24257372613954638447749745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16171581742636425631833163 24257372613954638447749745)
              ·
                refine ⟨18193029460465978835812309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24257372613954638447749745 18193029460465978835812309)
                ·
                  refine ⟨426399127979671378964351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18193029460465978835812309 426399127979671378964351)
                  ·
                    rfl

theorem cell23_7473684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_7473684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473684 prefixEnd_7473684 := by exact prefixLift 7473684
  have htrace : WordTrace (prefixWord ++ tailWord_7473684) baseStart_7473684 baseEnd_7473684 := by
    simpa [prefixWord, tailWord_7473684, baseEnd_7473684] using wordTrace_append hprefix tailTrace_7473684
  have hstable : (prefixWord ++ tailWord_7473684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473684).length < 2 ^ (prefixWord ++ tailWord_7473684).sum := by decide
  have hdescent : baseEnd_7473684 < baseStart_7473684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473690 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_7473690 : Nat := 118140960795 + 7473690 * 2 ^ 59
def prefixEnd_7473690 : Nat := 4983230072969 + 3 ^ 40 * 7473690 * 2
def baseEnd_7473690 : Nat := 3837595232700969387204131

theorem tailTrace_7473690 : CollatzResearch.WordTrace tailWord_7473690 prefixEnd_7473690 3837595232700969387204131 := by
  unfold tailWord_7473690
  simp only [CollatzResearch.WordTrace]
  refine ⟨68146967073526252369336631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181725245529403339651564349 68146967073526252369336631)
  ·
    refine ⟨102220450610289378554004947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68146967073526252369336631 102220450610289378554004947)
    ·
      refine ⟨153330675915434067831007421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102220450610289378554004947 153330675915434067831007421)
      ·
        refine ⟨57499003468287775436627783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153330675915434067831007421 57499003468287775436627783)
        ·
          refine ⟨86248505202431663154941675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57499003468287775436627783 86248505202431663154941675)
          ·
            refine ⟨129372757803647494732412513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86248505202431663154941675 129372757803647494732412513)
            ·
              refine ⟨97029568352735621049309385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129372757803647494732412513 97029568352735621049309385)
              ·
                refine ⟨72772176264551715786982039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97029568352735621049309385 72772176264551715786982039)
                ·
                  refine ⟨109158264396827573680473059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72772176264551715786982039 109158264396827573680473059)
                  ·
                    refine ⟨163737396595241360520709589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109158264396827573680473059 163737396595241360520709589)
                    ·
                      refine ⟨3837595232700969387204131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163737396595241360520709589 3837595232700969387204131)
                      ·
                        rfl

theorem cell23_7473690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_7473690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473690 prefixEnd_7473690 := by exact prefixLift 7473690
  have htrace : WordTrace (prefixWord ++ tailWord_7473690) baseStart_7473690 baseEnd_7473690 := by
    simpa [prefixWord, tailWord_7473690, baseEnd_7473690] using wordTrace_append hprefix tailTrace_7473690
  have hstable : (prefixWord ++ tailWord_7473690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473690).length < 2 ^ (prefixWord ++ tailWord_7473690).sum := by decide
  have hdescent : baseEnd_7473690 < baseStart_7473690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473717 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7473717 : Nat := 118140960795 + 7473717 * 2 ^ 59
def prefixEnd_7473717 : Nat := 4983230072969 + 3 ^ 40 * 7473717 * 2
def baseEnd_7473717 : Nat := 3837609096678640781566507

theorem tailTrace_7473717 : CollatzResearch.WordTrace tailWord_7473717 prefixEnd_7473717 3837609096678640781566507 := by
  unfold tailWord_7473717
  simp only [CollatzResearch.WordTrace]
  refine ⟨272588853065007193088579405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181725902043338128725719603 272588853065007193088579405)
  ·
    refine ⟨102220819899377697408217277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272588853065007193088579405 102220819899377697408217277)
    ·
      refine ⟨38332807462266636528081479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102220819899377697408217277 38332807462266636528081479)
      ·
        refine ⟨57499211193399954792122219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38332807462266636528081479 57499211193399954792122219)
        ·
          refine ⟨86248816790099932188183329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57499211193399954792122219 86248816790099932188183329)
          ·
            refine ⟨64686612592574949141137497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86248816790099932188183329 64686612592574949141137497)
            ·
              refine ⟨48514959444431211855853123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64686612592574949141137497 48514959444431211855853123)
              ·
                refine ⟨72772439166646817783779685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48514959444431211855853123 72772439166646817783779685)
                ·
                  refine ⟨13644832343746278334458691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72772439166646817783779685 13644832343746278334458691)
                  ·
                    refine ⟨20467248515619417501688037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13644832343746278334458691 20467248515619417501688037)
                    ·
                      refine ⟨3837609096678640781566507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20467248515619417501688037 3837609096678640781566507)
                      ·
                        rfl

theorem cell23_7473717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7473717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473717 prefixEnd_7473717 := by exact prefixLift 7473717
  have htrace : WordTrace (prefixWord ++ tailWord_7473717) baseStart_7473717 baseEnd_7473717 := by
    simpa [prefixWord, tailWord_7473717, baseEnd_7473717] using wordTrace_append hprefix tailTrace_7473717
  have hstable : (prefixWord ++ tailWord_7473717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473717).length < 2 ^ (prefixWord ++ tailWord_7473717).sum := by decide
  have hdescent : baseEnd_7473717 < baseStart_7473717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473761 : List Nat := [1, 2, 3, 1, 1, 4, 3, 3, 1, 4]
def baseStart_7473761 : Nat := 118140960795 + 7473761 * 2 ^ 59
def prefixEnd_7473761 : Nat := 4983230072969 + 3 ^ 40 * 7473761 * 2
def baseEnd_7473761 : Nat := 1279210563275812869805435

theorem tailTrace_7473761 : CollatzResearch.WordTrace tailWord_7473761 prefixEnd_7473761 1279210563275812869805435 := by
  unfold tailWord_7473761
  simp only [CollatzResearch.WordTrace]
  refine ⟨272590457876847788603181137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181726971917898525735454091 272590457876847788603181137)
  ·
    refine ⟨204442843407635841452385853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272590457876847788603181137 204442843407635841452385853)
    ·
      refine ⟨76666066277863440544644695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204442843407635841452385853 76666066277863440544644695)
      ·
        refine ⟨114999099416795160816967043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76666066277863440544644695 114999099416795160816967043)
        ·
          refine ⟨172498649125192741225450565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114999099416795160816967043 172498649125192741225450565)
          ·
            refine ⟨32343496710973638979771981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172498649125192741225450565 32343496710973638979771981)
            ·
              refine ⟨12128811266615114617414493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32343496710973638979771981 12128811266615114617414493)
              ·
                refine ⟨4548304224980667981530435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12128811266615114617414493 4548304224980667981530435)
                ·
                  refine ⟨6822456337471001972295653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4548304224980667981530435 6822456337471001972295653)
                  ·
                    refine ⟨1279210563275812869805435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6822456337471001972295653 1279210563275812869805435)
                    ·
                      rfl

theorem cell23_7473761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_7473761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473761 prefixEnd_7473761 := by exact prefixLift 7473761
  have htrace : WordTrace (prefixWord ++ tailWord_7473761) baseStart_7473761 baseEnd_7473761 := by
    simpa [prefixWord, tailWord_7473761, baseEnd_7473761] using wordTrace_append hprefix tailTrace_7473761
  have hstable : (prefixWord ++ tailWord_7473761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473761).length < 2 ^ (prefixWord ++ tailWord_7473761).sum := by decide
  have hdescent : baseEnd_7473761 < baseStart_7473761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473778 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_7473778 : Nat := 118140960795 + 7473778 * 2 ^ 59
def prefixEnd_7473778 : Nat := 4983230072969 + 3 ^ 40 * 7473778 * 2
def baseEnd_7473778 : Nat := 1279213472999521680967909

theorem tailTrace_7473778 : CollatzResearch.WordTrace tailWord_7473778 prefixEnd_7473778 1279213472999521680967909 := by
  unfold tailWord_7473778
  simp only [CollatzResearch.WordTrace]
  refine ⟨68147769479446550126637497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181727385278524133671033325 68147769479446550126637497)
  ·
    refine ⟨51110827109584912594978123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68147769479446550126637497 51110827109584912594978123)
    ·
      refine ⟨76666240664377368892467185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51110827109584912594978123 76666240664377368892467185)
      ·
        refine ⟨57499680498283026669350389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76666240664377368892467185 57499680498283026669350389)
        ·
          refine ⟨5390595046714033750251599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57499680498283026669350389 5390595046714033750251599)
          ·
            refine ⟨8085892570071050625377399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390595046714033750251599 8085892570071050625377399)
            ·
              refine ⟨12128838855106575938066099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085892570071050625377399 12128838855106575938066099)
              ·
                refine ⟨18193258282659863907099149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12128838855106575938066099 18193258282659863907099149)
                ·
                  refine ⟨6822471855997448965162181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18193258282659863907099149 6822471855997448965162181)
                  ·
                    refine ⟨1279213472999521680967909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6822471855997448965162181 1279213472999521680967909)
                    ·
                      rfl

theorem cell23_7473778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_7473778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473778 prefixEnd_7473778 := by exact prefixLift 7473778
  have htrace : WordTrace (prefixWord ++ tailWord_7473778) baseStart_7473778 baseEnd_7473778 := by
    simpa [prefixWord, tailWord_7473778, baseEnd_7473778] using wordTrace_append hprefix tailTrace_7473778
  have hstable : (prefixWord ++ tailWord_7473778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473778).length < 2 ^ (prefixWord ++ tailWord_7473778).sum := by decide
  have hdescent : baseEnd_7473778 < baseStart_7473778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473807 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_7473807 : Nat := 118140960795 + 7473807 * 2 ^ 59
def prefixEnd_7473807 : Nat := 4983230072969 + 3 ^ 40 * 7473807 * 2
def baseEnd_7473807 : Nat := 3837655309937545429441093

theorem tailTrace_7473807 : CollatzResearch.WordTrace tailWord_7473807 prefixEnd_7473807 3837655309937545429441093 := by
  unfold tailWord_7473807
  simp only [CollatzResearch.WordTrace]
  refine ⟨272592135634681138459355675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181728090423120758972903783 272592135634681138459355675)
  ·
    refine ⟨408888203452021707689033513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272592135634681138459355675 408888203452021707689033513)
    ·
      refine ⟨306666152589016280766775135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408888203452021707689033513 306666152589016280766775135)
      ·
        refine ⟨459999228883524421150162703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306666152589016280766775135 459999228883524421150162703)
        ·
          refine ⟨689998843325286631725244055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459999228883524421150162703 689998843325286631725244055)
          ·
            refine ⟨1034998264987929947587866083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689998843325286631725244055 1034998264987929947587866083)
            ·
              refine ⟨1552497397481894921381799125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034998264987929947587866083 1552497397481894921381799125)
              ·
                refine ⟨36386657753481912219885917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1552497397481894921381799125 36386657753481912219885917)
                ·
                  refine ⟨13644996657555717082457219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36386657753481912219885917 13644996657555717082457219)
                  ·
                    refine ⟨20467494986333575623685829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13644996657555717082457219 20467494986333575623685829)
                    ·
                      refine ⟨3837655309937545429441093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20467494986333575623685829 3837655309937545429441093)
                      ·
                        rfl

theorem cell23_7473807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_7473807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473807 prefixEnd_7473807 := by exact prefixLift 7473807
  have htrace : WordTrace (prefixWord ++ tailWord_7473807) baseStart_7473807 baseEnd_7473807 := by
    simpa [prefixWord, tailWord_7473807, baseEnd_7473807] using wordTrace_append hprefix tailTrace_7473807
  have hstable : (prefixWord ++ tailWord_7473807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473807).length < 2 ^ (prefixWord ++ tailWord_7473807).sum := by decide
  have hdescent : baseEnd_7473807 < baseStart_7473807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473817 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 1, 6]
def baseStart_7473817 : Nat := 118140960795 + 7473817 * 2 ^ 59
def prefixEnd_7473817 : Nat := 4983230072969 + 3 ^ 40 * 7473817 * 2
def baseEnd_7473817 : Nat := 1279220148248030130105349

theorem tailTrace_7473817 : CollatzResearch.WordTrace tailWord_7473817 prefixEnd_7473817 1279220148248030130105349 := by
  unfold tailWord_7473817
  simp only [CollatzResearch.WordTrace]
  refine ⟨272592500364644910167219705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181728333576429940111479803 272592500364644910167219705)
  ·
    refine ⟨204444375273483682625414779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272592500364644910167219705 204444375273483682625414779)
    ·
      refine ⟨306666562910225523938122169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204444375273483682625414779 306666562910225523938122169)
      ·
        refine ⟨229999922182669142953591627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306666562910225523938122169 229999922182669142953591627)
        ·
          refine ⟨344999883274003714430387441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229999922182669142953591627 344999883274003714430387441)
          ·
            refine ⟨258749912455502785822790581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344999883274003714430387441 258749912455502785822790581)
            ·
              refine ⟨24257804292703386170886617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258749912455502785822790581 24257804292703386170886617)
              ·
                refine ⟨18193353219527539628164963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24257804292703386170886617 18193353219527539628164963)
                ·
                  refine ⟨27290029829291309442247445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18193353219527539628164963 27290029829291309442247445)
                  ·
                    refine ⟨1279220148248030130105349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27290029829291309442247445 1279220148248030130105349)
                    ·
                      rfl

theorem cell23_7473817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_7473817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473817 prefixEnd_7473817 := by exact prefixLift 7473817
  have htrace : WordTrace (prefixWord ++ tailWord_7473817) baseStart_7473817 baseEnd_7473817 := by
    simpa [prefixWord, tailWord_7473817, baseEnd_7473817] using wordTrace_append hprefix tailTrace_7473817
  have hstable : (prefixWord ++ tailWord_7473817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473817).length < 2 ^ (prefixWord ++ tailWord_7473817).sum := by decide
  have hdescent : baseEnd_7473817 < baseStart_7473817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473827 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5]
def baseStart_7473827 : Nat := 118140960795 + 7473827 * 2 ^ 59
def prefixEnd_7473827 : Nat := 4983230072969 + 3 ^ 40 * 7473827 * 2
def baseEnd_7473827 : Nat := 3837665579550635351191001

theorem tailTrace_7473827 : CollatzResearch.WordTrace tailWord_7473827 prefixEnd_7473827 3837665579550635351191001 := by
  unfold tailWord_7473827
  simp only [CollatzResearch.WordTrace]
  refine ⟨272592865094608681875083735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181728576729739121250055823 272592865094608681875083735)
  ·
    refine ⟨408889297641913022812625603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272592865094608681875083735 408889297641913022812625603)
    ·
      refine ⟨613333946462869534218938405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408889297641913022812625603 613333946462869534218938405)
      ·
        refine ⟨115000114961788037666050951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 613333946462869534218938405 115000114961788037666050951)
        ·
          refine ⟨172500172442682056499076427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115000114961788037666050951 172500172442682056499076427)
          ·
            refine ⟨258750258664023084748614641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172500172442682056499076427 258750258664023084748614641)
            ·
              refine ⟨194062693998017313561460981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258750258664023084748614641 194062693998017313561460981)
              ·
                refine ⟨18193377562314123146386967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194062693998017313561460981 18193377562314123146386967)
                ·
                  refine ⟨27290066343471184719580451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18193377562314123146386967 27290066343471184719580451)
                  ·
                    refine ⟨40935099515206777079370677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27290066343471184719580451 40935099515206777079370677)
                    ·
                      refine ⟨3837665579550635351191001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40935099515206777079370677 3837665579550635351191001)
                      ·
                        rfl

theorem cell23_7473827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_7473827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473827 prefixEnd_7473827 := by exact prefixLift 7473827
  have htrace : WordTrace (prefixWord ++ tailWord_7473827) baseStart_7473827 baseEnd_7473827 := by
    simpa [prefixWord, tailWord_7473827, baseEnd_7473827] using wordTrace_append hprefix tailTrace_7473827
  have hstable : (prefixWord ++ tailWord_7473827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473827).length < 2 ^ (prefixWord ++ tailWord_7473827).sum := by decide
  have hdescent : baseEnd_7473827 < baseStart_7473827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473864 : List Nat := [2, 1, 3, 1, 2, 4, 3, 7]
def baseStart_7473864 : Nat := 118140960795 + 7473864 * 2 ^ 59
def prefixEnd_7473864 : Nat := 4983230072969 + 3 ^ 40 * 7473864 * 2
def baseEnd_7473864 : Nat := 142136465864253766904753

theorem tailTrace_7473864 : CollatzResearch.WordTrace tailWord_7473864 prefixEnd_7473864 142136465864253766904753 := by
  unfold tailWord_7473864
  simp only [CollatzResearch.WordTrace]
  refine ⟨136297107297737318597090323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181729476396983091462787097 136297107297737318597090323)
  ·
    refine ⟨204445660946605977895635485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136297107297737318597090323 204445660946605977895635485)
    ·
      refine ⟨76667122854977241710863307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204445660946605977895635485 76667122854977241710863307)
      ·
        refine ⟨115000684282465862566294961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76667122854977241710863307 115000684282465862566294961)
        ·
          refine ⟨86250513211849396924721221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115000684282465862566294961 86250513211849396924721221)
          ·
            refine ⟨16171971227221761923385229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86250513211849396924721221 16171971227221761923385229)
            ·
              refine ⟨6064489210208160721269461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16171971227221761923385229 6064489210208160721269461)
              ·
                refine ⟨142136465864253766904753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6064489210208160721269461 142136465864253766904753)
                ·
                  rfl

theorem cell23_7473864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 7].length) (baseStart_7473864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473864 prefixEnd_7473864 := by exact prefixLift 7473864
  have htrace : WordTrace (prefixWord ++ tailWord_7473864) baseStart_7473864 baseEnd_7473864 := by
    simpa [prefixWord, tailWord_7473864, baseEnd_7473864] using wordTrace_append hprefix tailTrace_7473864
  have hstable : (prefixWord ++ tailWord_7473864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473864).length < 2 ^ (prefixWord ++ tailWord_7473864).sum := by decide
  have hdescent : baseEnd_7473864 < baseStart_7473864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473897 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_7473897 : Nat := 118140960795 + 7473897 * 2 ^ 59
def prefixEnd_7473897 : Nat := 4983230072969 + 3 ^ 40 * 7473897 * 2
def baseEnd_7473897 : Nat := 3837701523196450077315679

theorem tailTrace_7473897 : CollatzResearch.WordTrace tailWord_7473897 prefixEnd_7473897 3837701523196450077315679 := by
  unfold tailWord_7473897
  simp only [CollatzResearch.WordTrace]
  refine ⟨272595418204355083830131945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181730278802903389220087963 272595418204355083830131945)
  ·
    refine ⟨204446563653266312872598959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272595418204355083830131945 204446563653266312872598959)
    ·
      refine ⟨306669845479899469308898439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204446563653266312872598959 306669845479899469308898439)
      ·
        refine ⟨460004768219849203963347659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306669845479899469308898439 460004768219849203963347659)
        ·
          refine ⟨690007152329773805945021489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460004768219849203963347659 690007152329773805945021489)
          ·
            refine ⟨517505364247330354458766117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690007152329773805945021489 517505364247330354458766117)
            ·
              refine ⟨97032255796374441461018647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517505364247330354458766117 97032255796374441461018647)
              ·
                refine ⟨145548383694561662191527971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97032255796374441461018647 145548383694561662191527971)
                ·
                  refine ⟨218322575541842493287291957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145548383694561662191527971 218322575541842493287291957)
                  ·
                    refine ⟨20467741457047733745683621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 218322575541842493287291957 20467741457047733745683621)
                    ·
                      refine ⟨3837701523196450077315679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20467741457047733745683621 3837701523196450077315679)
                      ·
                        rfl

theorem cell23_7473897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_7473897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473897 prefixEnd_7473897 := by exact prefixLift 7473897
  have htrace : WordTrace (prefixWord ++ tailWord_7473897) baseStart_7473897 baseEnd_7473897 := by
    simpa [prefixWord, tailWord_7473897, baseEnd_7473897] using wordTrace_append hprefix tailTrace_7473897
  have hstable : (prefixWord ++ tailWord_7473897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473897).length < 2 ^ (prefixWord ++ tailWord_7473897).sum := by decide
  have hdescent : baseEnd_7473897 < baseStart_7473897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473934 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_7473934 : Nat := 118140960795 + 7473934 * 2 ^ 59
def prefixEnd_7473934 : Nat := 4983230072969 + 3 ^ 40 * 7473934 * 2
def baseEnd_7473934 : Nat := 3837720521980666432553009

theorem tailTrace_7473934 : CollatzResearch.WordTrace tailWord_7473934 prefixEnd_7473934 3837720521980666432553009 := by
  unfold tailWord_7473934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34074595963152629893653607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181731178470147359432819237 34074595963152629893653607)
  ·
    refine ⟨51111893944728944840480411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34074595963152629893653607 51111893944728944840480411)
    ·
      refine ⟨76667840917093417260720617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51111893944728944840480411 76667840917093417260720617)
      ·
        refine ⟨57500880687820062945540463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76667840917093417260720617 57500880687820062945540463)
        ·
          refine ⟨86251321031730094418310695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57500880687820062945540463 86251321031730094418310695)
          ·
            refine ⟨129376981547595141627466043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86251321031730094418310695 129376981547595141627466043)
            ·
              refine ⟨194065472321392712441199065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129376981547595141627466043 194065472321392712441199065)
              ·
                refine ⟨145549104241044534330899299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194065472321392712441199065 145549104241044534330899299)
                ·
                  refine ⟨218323656361566801496348949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145549104241044534330899299 218323656361566801496348949)
                  ·
                    refine ⟨10233921391948443820141357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218323656361566801496348949 10233921391948443820141357)
                    ·
                      refine ⟨3837720521980666432553009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10233921391948443820141357 3837720521980666432553009)
                      ·
                        rfl

theorem cell23_7473934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_7473934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473934 prefixEnd_7473934 := by exact prefixLift 7473934
  have htrace : WordTrace (prefixWord ++ tailWord_7473934) baseStart_7473934 baseEnd_7473934 := by
    simpa [prefixWord, tailWord_7473934, baseEnd_7473934] using wordTrace_append hprefix tailTrace_7473934
  have hstable : (prefixWord ++ tailWord_7473934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473934).length < 2 ^ (prefixWord ++ tailWord_7473934).sum := by decide
  have hdescent : baseEnd_7473934 < baseStart_7473934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473937 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 9]
def baseStart_7473937 : Nat := 118140960795 + 7473937 * 2 ^ 59
def prefixEnd_7473937 : Nat := 4983230072969 + 3 ^ 40 * 7473937 * 2
def baseEnd_7473937 : Nat := 426413562491403324535055

theorem tailTrace_7473937 : CollatzResearch.WordTrace tailWord_7473937 prefixEnd_7473937 426413562491403324535055 := by
  unfold tailWord_7473937
  simp only [CollatzResearch.WordTrace]
  refine ⟨272596877124210170661588065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181731251416140113774392043 272596877124210170661588065)
  ·
    refine ⟨204447657843157627996191049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272596877124210170661588065 204447657843157627996191049)
    ·
      refine ⟨153335743382368220997143287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204447657843157627996191049 153335743382368220997143287)
      ·
        refine ⟨230003615073552331495714931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153335743382368220997143287 230003615073552331495714931)
        ·
          refine ⟨345005422610328497243572397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230003615073552331495714931 345005422610328497243572397)
          ·
            refine ⟨129377033478873186466339649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345005422610328497243572397 129377033478873186466339649)
            ·
              refine ⟨97032775109154889849754737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129377033478873186466339649 97032775109154889849754737)
              ·
                refine ⟨72774581331866167387316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97032775109154889849754737 72774581331866167387316053)
                ·
                  refine ⟨426413562491403324535055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72774581331866167387316053 426413562491403324535055)
                  ·
                    rfl

theorem cell23_7473937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 9].length) (baseStart_7473937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473937 prefixEnd_7473937 := by exact prefixLift 7473937
  have htrace : WordTrace (prefixWord ++ tailWord_7473937) baseStart_7473937 baseEnd_7473937 := by
    simpa [prefixWord, tailWord_7473937, baseEnd_7473937] using wordTrace_append hprefix tailTrace_7473937
  have hstable : (prefixWord ++ tailWord_7473937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473937).length < 2 ^ (prefixWord ++ tailWord_7473937).sum := by decide
  have hdescent : baseEnd_7473937 < baseStart_7473937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473948 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_7473948 : Nat := 118140960795 + 7473948 * 2 ^ 59
def prefixEnd_7473948 : Nat := 4983230072969 + 3 ^ 40 * 7473948 * 2
def baseEnd_7473948 : Nat := 3837727710709829377777945

theorem tailTrace_7473948 : CollatzResearch.WordTrace tailWord_7473948 prefixEnd_7473948 3837727710709829377777945 := by
  unfold tailWord_7473948
  simp only [CollatzResearch.WordTrace]
  refine ⟨136298639163585159770119249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181731518884780213026825665 136298639163585159770119249)
  ·
    refine ⟨102223979372688869827589437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136298639163585159770119249 102223979372688869827589437)
    ·
      refine ⟨38333992264758326185346039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102223979372688869827589437 38333992264758326185346039)
      ·
        refine ⟨57500988397137489278019059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38333992264758326185346039 57500988397137489278019059)
        ·
          refine ⟨86251482595706233917028589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57500988397137489278019059 86251482595706233917028589)
          ·
            refine ⟨32344305973389837718885721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86251482595706233917028589 32344305973389837718885721)
            ·
              refine ⟨24258229480042378289164291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32344305973389837718885721 24258229480042378289164291)
              ·
                refine ⟨36387344220063567433746437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24258229480042378289164291 36387344220063567433746437)
                ·
                  refine ⟨6822627041261918893827457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36387344220063567433746437 6822627041261918893827457)
                  ·
                    refine ⟨5116970280946439170370593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6822627041261918893827457 5116970280946439170370593)
                    ·
                      refine ⟨3837727710709829377777945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5116970280946439170370593 3837727710709829377777945)
                      ·
                        rfl

theorem cell23_7473948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_7473948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473948 prefixEnd_7473948 := by exact prefixLift 7473948
  have htrace : WordTrace (prefixWord ++ tailWord_7473948) baseStart_7473948 baseEnd_7473948 := by
    simpa [prefixWord, tailWord_7473948, baseEnd_7473948] using wordTrace_append hprefix tailTrace_7473948
  have hstable : (prefixWord ++ tailWord_7473948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473948).length < 2 ^ (prefixWord ++ tailWord_7473948).sum := by decide
  have hdescent : baseEnd_7473948 < baseStart_7473948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7473964 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_7473964 : Nat := 118140960795 + 7473964 * 2 ^ 59
def prefixEnd_7473964 : Nat := 4983230072969 + 3 ^ 40 * 7473964 * 2
def baseEnd_7473964 : Nat := 3837735926400301315177871

theorem tailTrace_7473964 : CollatzResearch.WordTrace tailWord_7473964 prefixEnd_7473964 3837735926400301315177871 := by
  unfold tailWord_7473964
  simp only [CollatzResearch.WordTrace]
  refine ⟨136298930947556177136410473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181731907930074902848547297 136298930947556177136410473)
  ·
    refine ⟨102224198210667132852307855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136298930947556177136410473 102224198210667132852307855)
    ·
      refine ⟨153336297316000699278461783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102224198210667132852307855 153336297316000699278461783)
      ·
        refine ⟨230004445974001048917692675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153336297316000699278461783 230004445974001048917692675)
        ·
          refine ⟨345006668961001573376539013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230004445974001048917692675 345006668961001573376539013)
          ·
            refine ⟨64688750430187795008101065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345006668961001573376539013 64688750430187795008101065)
            ·
              refine ⟨48516562822640846256075799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64688750430187795008101065 48516562822640846256075799)
              ·
                refine ⟨72774844233961269384113699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48516562822640846256075799 72774844233961269384113699)
                ·
                  refine ⟨109162266350941904076170549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72774844233961269384113699 109162266350941904076170549)
                  ·
                    refine ⟨10233962470400803507140989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109162266350941904076170549 10233962470400803507140989)
                    ·
                      refine ⟨3837735926400301315177871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10233962470400803507140989 3837735926400301315177871)
                      ·
                        rfl

theorem cell23_7473964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_7473964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7473964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7473964 prefixEnd_7473964 := by exact prefixLift 7473964
  have htrace : WordTrace (prefixWord ++ tailWord_7473964) baseStart_7473964 baseEnd_7473964 := by
    simpa [prefixWord, tailWord_7473964, baseEnd_7473964] using wordTrace_append hprefix tailTrace_7473964
  have hstable : (prefixWord ++ tailWord_7473964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7473964).length < 2 ^ (prefixWord ++ tailWord_7473964).sum := by decide
  have hdescent : baseEnd_7473964 < baseStart_7473964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7473964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474021 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 1, 6, 2]
def baseStart_7474021 : Nat := 118140960795 + 7474021 * 2 ^ 59
def prefixEnd_7474021 : Nat := 4983230072969 + 3 ^ 40 * 7474021 * 2
def baseEnd_7474021 : Nat := 3837765194797607592165109

theorem tailTrace_7474021 : CollatzResearch.WordTrace tailWord_7474021 prefixEnd_7474021 3837765194797607592165109 := by
  unfold tailWord_7474021
  simp only [CollatzResearch.WordTrace]
  refine ⟨272599940855905853007645917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181733293903937235338430611 272599940855905853007645917)
  ·
    refine ⟨102224977820964694877867219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272599940855905853007645917 102224977820964694877867219)
    ·
      refine ⟨153337466731447042316800829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102224977820964694877867219 153337466731447042316800829)
      ·
        refine ⟨57501550024292640868800311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153337466731447042316800829 57501550024292640868800311)
        ·
          refine ⟨86252325036438961303200467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57501550024292640868800311 86252325036438961303200467)
          ·
            refine ⟨129378487554658441954800701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86252325036438961303200467 129378487554658441954800701)
            ·
              refine ⟨48516932832996915733050263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129378487554658441954800701 48516932832996915733050263)
              ·
                refine ⟨72775399249495373599575395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48516932832996915733050263 72775399249495373599575395)
                ·
                  refine ⟨109163098874243060399363093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72775399249495373599575395 109163098874243060399363093)
                  ·
                    refine ⟨5117020259730143456220145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109163098874243060399363093 5117020259730143456220145)
                    ·
                      refine ⟨3837765194797607592165109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117020259730143456220145 3837765194797607592165109)
                      ·
                        rfl

theorem cell23_7474021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_7474021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474021 prefixEnd_7474021 := by exact prefixLift 7474021
  have htrace : WordTrace (prefixWord ++ tailWord_7474021) baseStart_7474021 baseEnd_7474021 := by
    simpa [prefixWord, tailWord_7474021, baseEnd_7474021] using wordTrace_append hprefix tailTrace_7474021
  have hstable : (prefixWord ++ tailWord_7474021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474021).length < 2 ^ (prefixWord ++ tailWord_7474021).sum := by decide
  have hdescent : baseEnd_7474021 < baseStart_7474021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474038 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7474038 : Nat := 118140960795 + 7474038 * 2 ^ 59
def prefixEnd_7474038 : Nat := 4983230072969 + 3 ^ 40 * 7474038 * 2
def baseEnd_7474038 : Nat := 3837773923968734025652531

theorem tailTrace_7474038 : CollatzResearch.WordTrace tailWord_7474038 prefixEnd_7474038 3837773923968734025652531 := by
  unfold tailWord_7474038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17037535056052766556938423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181733707264562843274009845 17037535056052766556938423)
  ·
    refine ⟨25556302584079149835407635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17037535056052766556938423 25556302584079149835407635)
    ·
      refine ⟨38334453876118724753111453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25556302584079149835407635 38334453876118724753111453)
      ·
        refine ⟨14375420203544521782416795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38334453876118724753111453 14375420203544521782416795)
        ·
          refine ⟨21563130305316782673625193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14375420203544521782416795 21563130305316782673625193)
          ·
            refine ⟨16172347728987587005218895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21563130305316782673625193 16172347728987587005218895)
            ·
              refine ⟨24258521593481380507828343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16172347728987587005218895 24258521593481380507828343)
              ·
                refine ⟨36387782390222070761742515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24258521593481380507828343 36387782390222070761742515)
                ·
                  refine ⟨54581673585333106142613773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36387782390222070761742515 54581673585333106142613773)
                  ·
                    refine ⟨20468127594499914803480165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54581673585333106142613773 20468127594499914803480165)
                    ·
                      refine ⟨3837773923968734025652531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20468127594499914803480165 3837773923968734025652531)
                      ·
                        rfl

theorem cell23_7474038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7474038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474038 prefixEnd_7474038 := by exact prefixLift 7474038
  have htrace : WordTrace (prefixWord ++ tailWord_7474038) baseStart_7474038 baseEnd_7474038 := by
    simpa [prefixWord, tailWord_7474038, baseEnd_7474038] using wordTrace_append hprefix tailTrace_7474038
  have hstable : (prefixWord ++ tailWord_7474038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474038).length < 2 ^ (prefixWord ++ tailWord_7474038).sum := by decide
  have hdescent : baseEnd_7474038 < baseStart_7474038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474041 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 3]
def baseStart_7474041 : Nat := 118140960795 + 7474041 * 2 ^ 59
def prefixEnd_7474041 : Nat := 4983230072969 + 3 ^ 40 * 7474041 * 2
def baseEnd_7474041 : Nat := 3837775464410697513915017

theorem tailTrace_7474041 : CollatzResearch.WordTrace tailWord_7474041 prefixEnd_7474041 3837775464410697513915017 := by
  unfold tailWord_7474041
  simp only [CollatzResearch.WordTrace]
  refine ⟨272600670315833396423373977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181733780210555597615582651 272600670315833396423373977)
  ·
    refine ⟨204450502736875047317530483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272600670315833396423373977 204450502736875047317530483)
    ·
      refine ⟨306675754105312570976295725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204450502736875047317530483 306675754105312570976295725)
      ·
        refine ⟨115003407789492214116110897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306675754105312570976295725 115003407789492214116110897)
        ·
          refine ⟨86252555842119160587083173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115003407789492214116110897 86252555842119160587083173)
          ·
            refine ⟨16172354220397342610078095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86252555842119160587083173 16172354220397342610078095)
            ·
              refine ⟨24258531330596013915117143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16172354220397342610078095 24258531330596013915117143)
              ·
                refine ⟨36387796995894020872675715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24258531330596013915117143 36387796995894020872675715)
                ·
                  refine ⟨54581695493841031309013573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36387796995894020872675715 54581695493841031309013573)
                  ·
                    refine ⟨10234067905095193370440045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54581695493841031309013573 10234067905095193370440045)
                    ·
                      refine ⟨3837775464410697513915017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10234067905095193370440045 3837775464410697513915017)
                      ·
                        rfl

theorem cell23_7474041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_7474041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474041 prefixEnd_7474041 := by exact prefixLift 7474041
  have htrace : WordTrace (prefixWord ++ tailWord_7474041) baseStart_7474041 baseEnd_7474041 := by
    simpa [prefixWord, tailWord_7474041, baseEnd_7474041] using wordTrace_append hprefix tailTrace_7474041
  have hstable : (prefixWord ++ tailWord_7474041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474041).length < 2 ^ (prefixWord ++ tailWord_7474041).sum := by decide
  have hdescent : baseEnd_7474041 < baseStart_7474041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474148 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_7474148 : Nat := 118140960795 + 7474148 * 2 ^ 59
def prefixEnd_7474148 : Nat := 4983230072969 + 3 ^ 40 * 7474148 * 2
def baseEnd_7474148 : Nat := 3837830406840728595277025

theorem tailTrace_7474148 : CollatzResearch.WordTrace tailWord_7474148 prefixEnd_7474148 3837830406840728595277025 := by
  unfold tailWord_7474148
  simp only [CollatzResearch.WordTrace]
  refine ⟨136302286463222876848759549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181736381950963835798346065 136302286463222876848759549)
  ·
    refine ⟨51113357423708578818284831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136302286463222876848759549 51113357423708578818284831)
    ·
      refine ⟨76670036135562868227427247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51113357423708578818284831 76670036135562868227427247)
      ·
        refine ⟨115005054203344302341140871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76670036135562868227427247 115005054203344302341140871)
        ·
          refine ⟨172507581305016453511711307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115005054203344302341140871 172507581305016453511711307)
          ·
            refine ⟨258761371957524680267566961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172507581305016453511711307 258761371957524680267566961)
            ·
              refine ⟨194071028968143510200675221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258761371957524680267566961 194071028968143510200675221)
              ·
                refine ⟨9097079482881727040656651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194071028968143510200675221 9097079482881727040656651)
                ·
                  refine ⟨13645619224322590560984977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097079482881727040656651 13645619224322590560984977)
                  ·
                    refine ⟨10234214418241942920738733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13645619224322590560984977 10234214418241942920738733)
                    ·
                      refine ⟨3837830406840728595277025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10234214418241942920738733 3837830406840728595277025)
                      ·
                        rfl

theorem cell23_7474148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_7474148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474148 prefixEnd_7474148 := by exact prefixLift 7474148
  have htrace : WordTrace (prefixWord ++ tailWord_7474148) baseStart_7474148 baseEnd_7474148 := by
    simpa [prefixWord, tailWord_7474148, baseEnd_7474148] using wordTrace_append hprefix tailTrace_7474148
  have hstable : (prefixWord ++ tailWord_7474148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474148).length < 2 ^ (prefixWord ++ tailWord_7474148).sum := by decide
  have hdescent : baseEnd_7474148 < baseStart_7474148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474151 : List Nat := [1, 1, 5, 2, 2, 1, 2, 9]
def baseStart_7474151 : Nat := 118140960795 + 7474151 * 2 ^ 59
def prefixEnd_7474151 : Nat := 4983230072969 + 3 ^ 40 * 7474151 * 2
def baseEnd_7474151 : Nat := 142141923973433040131093

theorem tailTrace_7474151 : CollatzResearch.WordTrace tailWord_7474151 prefixEnd_7474151 142141923973433040131093 := by
  unfold tailWord_7474151
  simp only [CollatzResearch.WordTrace]
  refine ⟨272604682345434885209878307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181736454896956590139918871 272604682345434885209878307)
  ·
    refine ⟨408907023518152327814817461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272604682345434885209878307 408907023518152327814817461)
    ·
      refine ⟨38335033454826780732639137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408907023518152327814817461 38335033454826780732639137)
      ·
        refine ⟨28751275091120085549479353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38335033454826780732639137 28751275091120085549479353)
        ·
          refine ⟨21563456318340064162109515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28751275091120085549479353 21563456318340064162109515)
          ·
            refine ⟨32345184477510096243164273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21563456318340064162109515 32345184477510096243164273)
            ·
              refine ⟨24258888358132572182373205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32345184477510096243164273 24258888358132572182373205)
              ·
                refine ⟨142141923973433040131093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24258888358132572182373205 142141923973433040131093)
                ·
                  rfl

theorem cell23_7474151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 9].length) (baseStart_7474151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474151 prefixEnd_7474151 := by exact prefixLift 7474151
  have htrace : WordTrace (prefixWord ++ tailWord_7474151) baseStart_7474151 baseEnd_7474151 := by
    simpa [prefixWord, tailWord_7474151, baseEnd_7474151] using wordTrace_append hprefix tailTrace_7474151
  have hstable : (prefixWord ++ tailWord_7474151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474151).length < 2 ^ (prefixWord ++ tailWord_7474151).sum := by decide
  have hdescent : baseEnd_7474151 < baseStart_7474151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474222 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_7474222 : Nat := 118140960795 + 7474222 * 2 ^ 59
def prefixEnd_7474222 : Nat := 4983230072969 + 3 ^ 40 * 7474222 * 2
def baseEnd_7474222 : Nat := 3837868404409161305751685

theorem tailTrace_7474222 : CollatzResearch.WordTrace tailWord_7474222 prefixEnd_7474222 3837868404409161305751685 := by
  unfold tailWord_7474222
  simp only [CollatzResearch.WordTrace]
  refine ⟨34075908991022208041964115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181738181285451776223808613 34075908991022208041964115)
  ·
    refine ⟨51113863486533312062946173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34075908991022208041964115 51113863486533312062946173)
    ·
      refine ⟨19167698807449992023604815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51113863486533312062946173 19167698807449992023604815)
      ·
        refine ⟨28751548211174988035407223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19167698807449992023604815 28751548211174988035407223)
        ·
          refine ⟨43127322316762482053110835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28751548211174988035407223 43127322316762482053110835)
          ·
            refine ⟨64690983475143723079666253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43127322316762482053110835 64690983475143723079666253)
            ·
              refine ⟨24259118803178896154874845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64690983475143723079666253 24259118803178896154874845)
              ·
                refine ⟨9097169551192086058078067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24259118803178896154874845 9097169551192086058078067)
                ·
                  refine ⟨13645754326788129087117101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097169551192086058078067 13645754326788129087117101)
                  ·
                    refine ⟨5117157872545548407668913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13645754326788129087117101 5117157872545548407668913)
                    ·
                      refine ⟨3837868404409161305751685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117157872545548407668913 3837868404409161305751685)
                      ·
                        rfl

theorem cell23_7474222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_7474222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474222 prefixEnd_7474222 := by exact prefixLift 7474222
  have htrace : WordTrace (prefixWord ++ tailWord_7474222) baseStart_7474222 baseEnd_7474222 := by
    simpa [prefixWord, tailWord_7474222, baseEnd_7474222] using wordTrace_append hprefix tailTrace_7474222
  have hstable : (prefixWord ++ tailWord_7474222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474222).length < 2 ^ (prefixWord ++ tailWord_7474222).sum := by decide
  have hdescent : baseEnd_7474222 < baseStart_7474222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474246 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7474246 : Nat := 118140960795 + 7474246 * 2 ^ 59
def prefixEnd_7474246 : Nat := 4983230072969 + 3 ^ 40 * 7474246 * 2
def baseEnd_7474246 : Nat := 3837880727944869211851575

theorem tailTrace_7474246 : CollatzResearch.WordTrace tailWord_7474246 prefixEnd_7474246 3837880727944869211851575 := by
  unfold tailWord_7474246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8519004602502834888580831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181738764853393810956391061 8519004602502834888580831)
  ·
    refine ⟨12778506903754252332871247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8519004602502834888580831 12778506903754252332871247)
    ·
      refine ⟨19167760355631378499306871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12778506903754252332871247 19167760355631378499306871)
      ·
        refine ⟨28751640533447067748960307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19167760355631378499306871 28751640533447067748960307)
        ·
          refine ⟨43127460800170601623440461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28751640533447067748960307 43127460800170601623440461)
          ·
            refine ⟨16172797800063975608790173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43127460800170601623440461 16172797800063975608790173)
            ·
              refine ⟨6064799175023990853296315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16172797800063975608790173 6064799175023990853296315)
              ·
                refine ⟨9097198762535986279944473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064799175023990853296315 9097198762535986279944473)
                ·
                  refine ⟨6822899071901989709958355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9097198762535986279944473 6822899071901989709958355)
                  ·
                    refine ⟨10234348607852984564937533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6822899071901989709958355 10234348607852984564937533)
                    ·
                      refine ⟨3837880727944869211851575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10234348607852984564937533 3837880727944869211851575)
                      ·
                        rfl

theorem cell23_7474246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7474246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474246 prefixEnd_7474246 := by exact prefixLift 7474246
  have htrace : WordTrace (prefixWord ++ tailWord_7474246) baseStart_7474246 baseEnd_7474246 := by
    simpa [prefixWord, tailWord_7474246, baseEnd_7474246] using wordTrace_append hprefix tailTrace_7474246
  have hstable : (prefixWord ++ tailWord_7474246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474246).length < 2 ^ (prefixWord ++ tailWord_7474246).sum := by decide
  have hdescent : baseEnd_7474246 < baseStart_7474246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474258 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 7]
def baseStart_7474258 : Nat := 118140960795 + 7474258 * 2 ^ 59
def prefixEnd_7474258 : Nat := 4983230072969 + 3 ^ 40 * 7474258 * 2
def baseEnd_7474258 : Nat := 426431876634747018322391

theorem tailTrace_7474258 : CollatzResearch.WordTrace tailWord_7474258 prefixEnd_7474258 426431876634747018322391 := by
  unfold tailWord_7474258
  simp only [CollatzResearch.WordTrace]
  refine ⟨68152146239011810621005857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181739056637364828322682285 68152146239011810621005857)
  ·
    refine ⟨51114109679258857965754393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68152146239011810621005857 51114109679258857965754393)
    ·
      refine ⟨38335582259444143474315795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51114109679258857965754393 38335582259444143474315795)
      ·
        refine ⟨57503373389166215211473693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38335582259444143474315795 57503373389166215211473693)
        ·
          refine ⟨21563765020937330704302635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57503373389166215211473693 21563765020937330704302635)
          ·
            refine ⟨32345647531405996056453953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21563765020937330704302635 32345647531405996056453953)
            ·
              refine ⟨24259235648554497042340465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32345647531405996056453953 24259235648554497042340465)
              ·
                refine ⟨18194426736415872781755349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24259235648554497042340465 18194426736415872781755349)
                ·
                  refine ⟨426431876634747018322391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18194426736415872781755349 426431876634747018322391)
                  ·
                    rfl

theorem cell23_7474258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_7474258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474258 prefixEnd_7474258 := by exact prefixLift 7474258
  have htrace : WordTrace (prefixWord ++ tailWord_7474258) baseStart_7474258 baseEnd_7474258 := by
    simpa [prefixWord, tailWord_7474258, baseEnd_7474258] using wordTrace_append hprefix tailTrace_7474258
  have hstable : (prefixWord ++ tailWord_7474258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474258).length < 2 ^ (prefixWord ++ tailWord_7474258).sum := by decide
  have hdescent : baseEnd_7474258 < baseStart_7474258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474271 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 1, 7]
def baseStart_7474271 : Nat := 118140960795 + 7474271 * 2 ^ 59
def prefixEnd_7474271 : Nat := 4983230072969 + 3 ^ 40 * 7474271 * 2
def baseEnd_7474271 : Nat := 1279297854987077204679653

theorem tailTrace_7474271 : CollatzResearch.WordTrace tailWord_7474271 prefixEnd_7474271 1279297854987077204679653 := by
  unfold tailWord_7474271
  simp only [CollatzResearch.WordTrace]
  refine ⟨272609059105000145704246667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181739372736666763802831111 272609059105000145704246667)
  ·
    refine ⟨408913588657500218556370001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272609059105000145704246667 408913588657500218556370001)
    ·
      refine ⟨306685191493125163917277501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408913588657500218556370001 306685191493125163917277501)
      ·
        refine ⟨115006946809921936468979063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306685191493125163917277501 115006946809921936468979063)
        ·
          refine ⟨172510420214882904703468595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115006946809921936468979063 172510420214882904703468595)
          ·
            refine ⟨258765630322324357055202893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172510420214882904703468595 258765630322324357055202893)
            ·
              refine ⟨97037111370871633895701085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258765630322324357055202893 97037111370871633895701085)
              ·
                refine ⟨36388916764076862710887907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97037111370871633895701085 36388916764076862710887907)
                ·
                  refine ⟨54583375146115294066331861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36388916764076862710887907 54583375146115294066331861)
                  ·
                    refine ⟨1279297854987077204679653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54583375146115294066331861 1279297854987077204679653)
                    ·
                      rfl

theorem cell23_7474271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_7474271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474271 prefixEnd_7474271 := by exact prefixLift 7474271
  have htrace : WordTrace (prefixWord ++ tailWord_7474271) baseStart_7474271 baseEnd_7474271 := by
    simpa [prefixWord, tailWord_7474271, baseEnd_7474271] using wordTrace_append hprefix tailTrace_7474271
  have hstable : (prefixWord ++ tailWord_7474271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474271).length < 2 ^ (prefixWord ++ tailWord_7474271).sum := by decide
  have hdescent : baseEnd_7474271 < baseStart_7474271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474288 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 2, 5]
def baseStart_7474288 : Nat := 118140960795 + 7474288 * 2 ^ 59
def prefixEnd_7474288 : Nat := 4983230072969 + 3 ^ 40 * 7474288 * 2
def baseEnd_7474288 : Nat := 1279300764710786015842127

theorem tailTrace_7474288 : CollatzResearch.WordTrace tailWord_7474288 prefixEnd_7474288 1279300764710786015842127 := by
  unfold tailWord_7474288
  simp only [CollatzResearch.WordTrace]
  refine ⟨136304839572969278803807759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181739786097292371738410345 136304839572969278803807759)
  ·
    refine ⟨204457259359453918205711639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136304839572969278803807759 204457259359453918205711639)
    ·
      refine ⟨306685889039180877308567459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204457259359453918205711639 306685889039180877308567459)
      ·
        refine ⟨460028833558771315962851189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306685889039180877308567459 460028833558771315962851189)
        ·
          refine ⟨43127703146134810871517299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 460028833558771315962851189 43127703146134810871517299)
          ·
            refine ⟨64691554719202216307275949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43127703146134810871517299 64691554719202216307275949)
            ·
              refine ⟨24259333019700831115228481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64691554719202216307275949 24259333019700831115228481)
              ·
                refine ⟨18194499764775623336421361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24259333019700831115228481 18194499764775623336421361)
                ·
                  refine ⟨13645874823581717502316021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18194499764775623336421361 13645874823581717502316021)
                  ·
                    refine ⟨1279300764710786015842127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13645874823581717502316021 1279300764710786015842127)
                    ·
                      rfl

theorem cell23_7474288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_7474288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474288 prefixEnd_7474288 := by exact prefixLift 7474288
  have htrace : WordTrace (prefixWord ++ tailWord_7474288) baseStart_7474288 baseEnd_7474288 := by
    simpa [prefixWord, tailWord_7474288, baseEnd_7474288] using wordTrace_append hprefix tailTrace_7474288
  have hstable : (prefixWord ++ tailWord_7474288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474288).length < 2 ^ (prefixWord ++ tailWord_7474288).sum := by decide
  have hdescent : baseEnd_7474288 < baseStart_7474288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474291 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4]
def baseStart_7474291 : Nat := 118140960795 + 7474291 * 2 ^ 59
def prefixEnd_7474291 : Nat := 4983230072969 + 3 ^ 40 * 7474291 * 2
def baseEnd_7474291 : Nat := 3837903834574321535788867

theorem tailTrace_7474291 : CollatzResearch.WordTrace tailWord_7474291 prefixEnd_7474291 3837903834574321535788867 := by
  unfold tailWord_7474291
  simp only [CollatzResearch.WordTrace]
  refine ⟨272609788564927689119974727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181739859043285126079983151 272609788564927689119974727)
  ·
    refine ⟨408914682847391533679962091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272609788564927689119974727 408914682847391533679962091)
    ·
      refine ⟨613372024271087300519943137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408914682847391533679962091 613372024271087300519943137)
      ·
        refine ⟨460029018203315475389957353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613372024271087300519943137 460029018203315475389957353)
        ·
          refine ⟨345021763652486606542468015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460029018203315475389957353 345021763652486606542468015)
          ·
            refine ⟨517532645478729909813702023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345021763652486606542468015 517532645478729909813702023)
            ·
              refine ⟨776298968218094864720553035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517532645478729909813702023 776298968218094864720553035)
              ·
                refine ⟨1164448452327142297080829553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776298968218094864720553035 1164448452327142297080829553)
                ·
                  refine ⟨873336339245356722810622165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1164448452327142297080829553 873336339245356722810622165)
                  ·
                    refine ⟨20468820451063048190873957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 873336339245356722810622165 20468820451063048190873957)
                    ·
                      refine ⟨3837903834574321535788867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20468820451063048190873957 3837903834574321535788867)
                      ·
                        rfl

theorem cell23_7474291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_7474291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474291 prefixEnd_7474291 := by exact prefixLift 7474291
  have htrace : WordTrace (prefixWord ++ tailWord_7474291) baseStart_7474291 baseEnd_7474291 := by
    simpa [prefixWord, tailWord_7474291, baseEnd_7474291] using wordTrace_append hprefix tailTrace_7474291
  have hstable : (prefixWord ++ tailWord_7474291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474291).length < 2 ^ (prefixWord ++ tailWord_7474291).sum := by decide
  have hdescent : baseEnd_7474291 < baseStart_7474291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474486 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7474486 : Nat := 118140960795 + 7474486 * 2 ^ 59
def prefixEnd_7474486 : Nat := 4983230072969 + 3 ^ 40 * 7474486 * 2
def baseEnd_7474486 : Nat := 3838003963301948272850471

theorem tailTrace_7474486 : CollatzResearch.WordTrace tailWord_7474486 prefixEnd_7474486 3838003963301948272850471 := by
  unfold tailWord_7474486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038556299951327338957707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181744600532814158282215541 17038556299951327338957707)
  ·
    refine ⟨25557834449926991008436561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17038556299951327338957707 25557834449926991008436561)
    ·
      refine ⟨19168375837445243256327421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25557834449926991008436561 19168375837445243256327421)
      ·
        refine ⟨7188140939041966221122783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19168375837445243256327421 7188140939041966221122783)
        ·
          refine ⟨10782211408562949331684175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188140939041966221122783 10782211408562949331684175)
          ·
            refine ⟨16173317112844423997526263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10782211408562949331684175 16173317112844423997526263)
            ·
              refine ⟨24259975669266635996289395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16173317112844423997526263 24259975669266635996289395)
              ·
                refine ⟨36389963503899953994434093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24259975669266635996289395 36389963503899953994434093)
                ·
                  refine ⟨13646236313962482747912785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36389963503899953994434093 13646236313962482747912785)
                  ·
                    refine ⟨10234677235471862060934589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13646236313962482747912785 10234677235471862060934589)
                    ·
                      refine ⟨3838003963301948272850471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10234677235471862060934589 3838003963301948272850471)
                      ·
                        rfl

theorem cell23_7474486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7474486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474486 prefixEnd_7474486 := by exact prefixLift 7474486
  have htrace : WordTrace (prefixWord ++ tailWord_7474486) baseStart_7474486 baseEnd_7474486 := by
    simpa [prefixWord, tailWord_7474486, baseEnd_7474486] using wordTrace_append hprefix tailTrace_7474486
  have hstable : (prefixWord ++ tailWord_7474486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474486).length < 2 ^ (prefixWord ++ tailWord_7474486).sum := by decide
  have hdescent : baseEnd_7474486 < baseStart_7474486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474488 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_7474488 : Nat := 118140960795 + 7474488 * 2 ^ 59
def prefixEnd_7474488 : Nat := 4983230072969 + 3 ^ 40 * 7474488 * 2
def baseEnd_7474488 : Nat := 3838004990263257265025461

theorem tailTrace_7474488 : CollatzResearch.WordTrace tailWord_7474488 prefixEnd_7474488 3838004990263257265025461 := by
  unfold tailWord_7474488
  simp only [CollatzResearch.WordTrace]
  refine ⟨136308486872606995882448059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181744649163475994509930745 136308486872606995882448059)
  ·
    refine ⟨204462730308910493823672089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136308486872606995882448059 204462730308910493823672089)
    ·
      refine ⟨153347047731682870367754067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204462730308910493823672089 153347047731682870367754067)
      ·
        refine ⟨230020571597524305551631101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153347047731682870367754067 230020571597524305551631101)
        ·
          refine ⟨86257714349071614581861663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230020571597524305551631101 86257714349071614581861663)
          ·
            refine ⟨129386571523607421872792495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86257714349071614581861663 129386571523607421872792495)
            ·
              refine ⟨194079857285411132809188743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129386571523607421872792495 194079857285411132809188743)
              ·
                refine ⟨291119785928116699213783115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194079857285411132809188743 291119785928116699213783115)
                ·
                  refine ⟨436679678892175048820674673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291119785928116699213783115 436679678892175048820674673)
                  ·
                    refine ⟨327509759169131286615506005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 436679678892175048820674673 327509759169131286615506005)
                    ·
                      refine ⟨3838004990263257265025461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 327509759169131286615506005 3838004990263257265025461)
                      ·
                        rfl

theorem cell23_7474488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_7474488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474488 prefixEnd_7474488 := by exact prefixLift 7474488
  have htrace : WordTrace (prefixWord ++ tailWord_7474488) baseStart_7474488 baseEnd_7474488 := by
    simpa [prefixWord, tailWord_7474488, baseEnd_7474488] using wordTrace_append hprefix tailTrace_7474488
  have hstable : (prefixWord ++ tailWord_7474488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474488).length < 2 ^ (prefixWord ++ tailWord_7474488).sum := by decide
  have hdescent : baseEnd_7474488 < baseStart_7474488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474555 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 3]
def baseStart_7474555 : Nat := 118140960795 + 7474555 * 2 ^ 59
def prefixEnd_7474555 : Nat := 4983230072969 + 3 ^ 40 * 7474555 * 2
def baseEnd_7474555 : Nat := 3838039393467108502887653

theorem tailTrace_7474555 : CollatzResearch.WordTrace tailWord_7474555 prefixEnd_7474555 3838039393467108502887653 := by
  unfold tailWord_7474555
  simp only [CollatzResearch.WordTrace]
  refine ⟨272619417435971262207585119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181746278290647508138390079 272619417435971262207585119)
  ·
    refine ⟨408929126153956893311377679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272619417435971262207585119 408929126153956893311377679)
    ·
      refine ⟨613393689230935339967066519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408929126153956893311377679 613393689230935339967066519)
      ·
        refine ⟨920090533846403009950599779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613393689230935339967066519 920090533846403009950599779)
        ·
          refine ⟨1380135800769604514925899669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920090533846403009950599779 1380135800769604514925899669)
          ·
            refine ⟨64693865661075211637151547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1380135800769604514925899669 64693865661075211637151547)
            ·
              refine ⟨97040798491612817455727321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64693865661075211637151547 97040798491612817455727321)
              ·
                refine ⟨72780598868709613091795491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97040798491612817455727321 72780598868709613091795491)
                ·
                  refine ⟨109170898303064419637693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72780598868709613091795491 109170898303064419637693237)
                  ·
                    refine ⟨10234771715912289341033741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109170898303064419637693237 10234771715912289341033741)
                    ·
                      refine ⟨3838039393467108502887653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10234771715912289341033741 3838039393467108502887653)
                      ·
                        rfl

theorem cell23_7474555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 3].length) (baseStart_7474555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474555 prefixEnd_7474555 := by exact prefixLift 7474555
  have htrace : WordTrace (prefixWord ++ tailWord_7474555) baseStart_7474555 baseEnd_7474555 := by
    simpa [prefixWord, tailWord_7474555, baseEnd_7474555] using wordTrace_append hprefix tailTrace_7474555
  have hstable : (prefixWord ++ tailWord_7474555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474555).length < 2 ^ (prefixWord ++ tailWord_7474555).sum := by decide
  have hdescent : baseEnd_7474555 < baseStart_7474555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474590 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7474590 : Nat := 118140960795 + 7474590 * 2 ^ 59
def prefixEnd_7474590 : Nat := 4983230072969 + 3 ^ 40 * 7474590 * 2
def baseEnd_7474590 : Nat := 3838057365290015865949993

theorem tailTrace_7474590 : CollatzResearch.WordTrace tailWord_7474590 prefixEnd_7474590 3838057365290015865949993 := by
  unfold tailWord_7474590
  simp only [CollatzResearch.WordTrace]
  refine ⟨34077586748855557898138653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181747129327229642123406149 34077586748855557898138653)
  ·
    refine ⟨12779095030820834211801995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34077586748855557898138653 12779095030820834211801995)
    ·
      refine ⟨19168642546231251317702993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12779095030820834211801995 19168642546231251317702993)
      ·
        refine ⟨14376481909673438488277245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19168642546231251317702993 14376481909673438488277245)
        ·
          refine ⟨5391180716127539433103967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14376481909673438488277245 5391180716127539433103967)
          ·
            refine ⟨8086771074191309149655951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391180716127539433103967 8086771074191309149655951)
            ·
              refine ⟨12130156611286963724483927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086771074191309149655951 12130156611286963724483927)
              ·
                refine ⟨18195234916930445586725891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12130156611286963724483927 18195234916930445586725891)
                ·
                  refine ⟨27292852375395668380088837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18195234916930445586725891 27292852375395668380088837)
                  ·
                    refine ⟨5117409820386687821266657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27292852375395668380088837 5117409820386687821266657)
                    ·
                      refine ⟨3838057365290015865949993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117409820386687821266657 3838057365290015865949993)
                      ·
                        rfl

theorem cell23_7474590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7474590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474590 prefixEnd_7474590 := by exact prefixLift 7474590
  have htrace : WordTrace (prefixWord ++ tailWord_7474590) baseStart_7474590 baseEnd_7474590 := by
    simpa [prefixWord, tailWord_7474590, baseEnd_7474590] using wordTrace_append hprefix tailTrace_7474590
  have hstable : (prefixWord ++ tailWord_7474590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474590).length < 2 ^ (prefixWord ++ tailWord_7474590).sum := by decide
  have hdescent : baseEnd_7474590 < baseStart_7474590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474595 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4]
def baseStart_7474595 : Nat := 118140960795 + 7474595 * 2 ^ 59
def prefixEnd_7474595 : Nat := 4983230072969 + 3 ^ 40 * 7474595 * 2
def baseEnd_7474595 : Nat := 3838059932693288346387469

theorem tailTrace_7474595 : CollatzResearch.WordTrace tailWord_7474595 prefixEnd_7474595 3838059932693288346387469 := by
  unfold tailWord_7474595
  simp only [CollatzResearch.WordTrace]
  refine ⟨272620876355826349039041239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181747250903884232692694159 272620876355826349039041239)
  ·
    refine ⟨408931314533739523558561859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272620876355826349039041239 408931314533739523558561859)
    ·
      refine ⟨613396971800609285337842789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408931314533739523558561859 613396971800609285337842789)
      ·
        refine ⟨115011932212614241000845523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 613396971800609285337842789 115011932212614241000845523)
        ·
          refine ⟨172517898318921361501268285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115011932212614241000845523 172517898318921361501268285)
          ·
            refine ⟨64694211869595510562975607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172517898318921361501268285 64694211869595510562975607)
            ·
              refine ⟨97041317804393265844463411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64694211869595510562975607 97041317804393265844463411)
              ·
                refine ⟨145561976706589898766695117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97041317804393265844463411 145561976706589898766695117)
                ·
                  refine ⟨54585741264971212037510669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145561976706589898766695117 54585741264971212037510669)
                  ·
                    refine ⟨20469652974364204514066501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54585741264971212037510669 20469652974364204514066501)
                    ·
                      refine ⟨3838059932693288346387469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20469652974364204514066501 3838059932693288346387469)
                      ·
                        rfl

theorem cell23_7474595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_7474595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474595 prefixEnd_7474595 := by exact prefixLift 7474595
  have htrace : WordTrace (prefixWord ++ tailWord_7474595) baseStart_7474595 baseEnd_7474595 := by
    simpa [prefixWord, tailWord_7474595, baseEnd_7474595] using wordTrace_append hprefix tailTrace_7474595
  have hstable : (prefixWord ++ tailWord_7474595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474595).length < 2 ^ (prefixWord ++ tailWord_7474595).sum := by decide
  have hdescent : baseEnd_7474595 < baseStart_7474595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474635 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 8]
def baseStart_7474635 : Nat := 118140960795 + 7474635 * 2 ^ 59
def prefixEnd_7474635 : Nat := 4983230072969 + 3 ^ 40 * 7474635 * 2
def baseEnd_7474635 : Nat := 426453385768829798876365

theorem tailTrace_7474635 : CollatzResearch.WordTrace tailWord_7474635 prefixEnd_7474635 426453385768829798876365 := by
  unfold tailWord_7474635
  simp only [CollatzResearch.WordTrace]
  refine ⟨272622335275681435870497359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181748223517120957246998239 272622335275681435870497359)
  ·
    refine ⟨408933502913522153805746039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272622335275681435870497359 408933502913522153805746039)
    ·
      refine ⟨613400254370283230708619059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408933502913522153805746039 613400254370283230708619059)
      ·
        refine ⟨920100381555424846062928589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613400254370283230708619059 920100381555424846062928589)
        ·
          refine ⟨345037643083284317273598221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920100381555424846062928589 345037643083284317273598221)
          ·
            refine ⟨129389116156231618977599333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345037643083284317273598221 129389116156231618977599333)
            ·
              refine ⟨24260459279293428558299875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129389116156231618977599333 24260459279293428558299875)
              ·
                refine ⟨36390688918940142837449813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24260459279293428558299875 36390688918940142837449813)
                ·
                  refine ⟨426453385768829798876365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36390688918940142837449813 426453385768829798876365)
                  ·
                    rfl

theorem cell23_7474635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 8].length) (baseStart_7474635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474635 prefixEnd_7474635 := by exact prefixLift 7474635
  have htrace : WordTrace (prefixWord ++ tailWord_7474635) baseStart_7474635 baseEnd_7474635 := by
    simpa [prefixWord, tailWord_7474635, baseEnd_7474635] using wordTrace_append hprefix tailTrace_7474635
  have hstable : (prefixWord ++ tailWord_7474635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474635).length < 2 ^ (prefixWord ++ tailWord_7474635).sum := by decide
  have hdescent : baseEnd_7474635 < baseStart_7474635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474639 : List Nat := [1, 1, 2, 1, 1, 4, 2, 6, 1, 4]
def baseStart_7474639 : Nat := 118140960795 + 7474639 * 2 ^ 59
def prefixEnd_7474639 : Nat := 4983230072969 + 3 ^ 40 * 7474639 * 2
def baseEnd_7474639 : Nat := 1279360841947362058079089

theorem tailTrace_7474639 : CollatzResearch.WordTrace tailWord_7474639 prefixEnd_7474639 1279360841947362058079089 := by
  unfold tailWord_7474639
  simp only [CollatzResearch.WordTrace]
  refine ⟨272622481167666944553642971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181748320778444629702428647 272622481167666944553642971)
  ·
    refine ⟨408933721751500416830464457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272622481167666944553642971 408933721751500416830464457)
    ·
      refine ⟨306700291313625312622848343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408933721751500416830464457 306700291313625312622848343)
      ·
        refine ⟨460050436970437968934272515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306700291313625312622848343 460050436970437968934272515)
        ·
          refine ⟨690075655455656953401408773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460050436970437968934272515 690075655455656953401408773)
          ·
            refine ⟨129389185397935678762764145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 690075655455656953401408773 129389185397935678762764145)
            ·
              refine ⟨97041889048451759072073109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129389185397935678762764145 97041889048451759072073109)
              ·
                refine ⟨4548838549146176206503427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97041889048451759072073109 4548838549146176206503427)
                ·
                  refine ⟨6823257823719264309755141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4548838549146176206503427 6823257823719264309755141)
                  ·
                    refine ⟨1279360841947362058079089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6823257823719264309755141 1279360841947362058079089)
                    ·
                      rfl

theorem cell23_7474639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 4].length) (baseStart_7474639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474639 prefixEnd_7474639 := by exact prefixLift 7474639
  have htrace : WordTrace (prefixWord ++ tailWord_7474639) baseStart_7474639 baseEnd_7474639 := by
    simpa [prefixWord, tailWord_7474639, baseEnd_7474639] using wordTrace_append hprefix tailTrace_7474639
  have hstable : (prefixWord ++ tailWord_7474639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474639).length < 2 ^ (prefixWord ++ tailWord_7474639).sum := by decide
  have hdescent : baseEnd_7474639 < baseStart_7474639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474666 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_7474666 : Nat := 118140960795 + 7474666 * 2 ^ 59
def prefixEnd_7474666 : Nat := 4983230072969 + 3 ^ 40 * 7474666 * 2
def baseEnd_7474666 : Nat := 3838096389819757568599643

theorem tailTrace_7474666 : CollatzResearch.WordTrace tailWord_7474666 prefixEnd_7474666 3838096389819757568599643 := by
  unfold tailWord_7474666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68155866484642282041218963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181748977292379418776583901 68155866484642282041218963)
  ·
    refine ⟨102233799726963423061828445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68155866484642282041218963 102233799726963423061828445)
    ·
      refine ⟨38337674897611283648185667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102233799726963423061828445 38337674897611283648185667)
      ·
        refine ⟨57506512346416925472278501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38337674897611283648185667 57506512346416925472278501)
        ·
          refine ⟨10782471064953173526052219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57506512346416925472278501 10782471064953173526052219)
          ·
            refine ⟨16173706597429760289078329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10782471064953173526052219 16173706597429760289078329)
            ·
              refine ⟨12130279948072320216808747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16173706597429760289078329 12130279948072320216808747)
              ·
                refine ⟨18195419922108480325213121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12130279948072320216808747 18195419922108480325213121)
                ·
                  refine ⟨13646564941581360243909841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18195419922108480325213121 13646564941581360243909841)
                  ·
                    refine ⟨10234923706186020182932381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13646564941581360243909841 10234923706186020182932381)
                    ·
                      refine ⟨3838096389819757568599643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10234923706186020182932381 3838096389819757568599643)
                      ·
                        rfl

theorem cell23_7474666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_7474666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474666 prefixEnd_7474666 := by exact prefixLift 7474666
  have htrace : WordTrace (prefixWord ++ tailWord_7474666) baseStart_7474666 baseEnd_7474666 := by
    simpa [prefixWord, tailWord_7474666, baseEnd_7474666] using wordTrace_append hprefix tailTrace_7474666
  have hstable : (prefixWord ++ tailWord_7474666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474666).length < 2 ^ (prefixWord ++ tailWord_7474666).sum := by decide
  have hdescent : baseEnd_7474666 < baseStart_7474666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474675 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5]
def baseStart_7474675 : Nat := 118140960795 + 7474675 * 2 ^ 59
def prefixEnd_7474675 : Nat := 4983230072969 + 3 ^ 40 * 7474675 * 2
def baseEnd_7474675 : Nat := 3838101011145648033387101

theorem tailTrace_7474675 : CollatzResearch.WordTrace tailWord_7474675 prefixEnd_7474675 3838101011145648033387101 := by
  unfold tailWord_7474675
  simp only [CollatzResearch.WordTrace]
  refine ⟨272623794195536522701953479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181749196130357681801302319 272623794195536522701953479)
  ·
    refine ⟨408935691293304784052930219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272623794195536522701953479 408935691293304784052930219)
    ·
      refine ⟨613403536939957176079395329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408935691293304784052930219 613403536939957176079395329)
      ·
        refine ⟨460052652704967882059546497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613403536939957176079395329 460052652704967882059546497)
        ·
          refine ⟨345039489528725911544659873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460052652704967882059546497 345039489528725911544659873)
          ·
            refine ⟨258779617146544433658494905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345039489528725911544659873 258779617146544433658494905)
            ·
              refine ⟨194084712859908325243871179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258779617146544433658494905 194084712859908325243871179)
              ·
                refine ⟨291127069289862487865806769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194084712859908325243871179 291127069289862487865806769)
                ·
                  refine ⟨218345301967396865899355077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291127069289862487865806769 218345301967396865899355077)
                  ·
                    refine ⟨40939744118886912356129077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218345301967396865899355077 40939744118886912356129077)
                    ·
                      refine ⟨3838101011145648033387101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40939744118886912356129077 3838101011145648033387101)
                      ·
                        rfl

theorem cell23_7474675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_7474675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474675 prefixEnd_7474675 := by exact prefixLift 7474675
  have htrace : WordTrace (prefixWord ++ tailWord_7474675) baseStart_7474675 baseEnd_7474675 := by
    simpa [prefixWord, tailWord_7474675, baseEnd_7474675] using wordTrace_append hprefix tailTrace_7474675
  have hstable : (prefixWord ++ tailWord_7474675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474675).length < 2 ^ (prefixWord ++ tailWord_7474675).sum := by decide
  have hdescent : baseEnd_7474675 < baseStart_7474675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474690 : List Nat := [3, 4, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7474690 : Nat := 118140960795 + 7474690 * 2 ^ 59
def prefixEnd_7474690 : Nat := 4983230072969 + 3 ^ 40 * 7474690 * 2
def baseEnd_7474690 : Nat := 1279369571118488491566511

theorem tailTrace_7474690 : CollatzResearch.WordTrace tailWord_7474690 prefixEnd_7474690 1279369571118488491566511 := by
  unfold tailWord_7474690
  simp only [CollatzResearch.WordTrace]
  refine ⟨68156085322620545065937381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181749560860321453509166349 68156085322620545065937381)
  ·
    refine ⟨12779265997991352199863259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68156085322620545065937381 12779265997991352199863259)
    ·
      refine ⟨19168898996987028299794889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12779265997991352199863259 19168898996987028299794889)
      ·
        refine ⟨14376674247740271224846167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19168898996987028299794889 14376674247740271224846167)
        ·
          refine ⟨21565011371610406837269251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14376674247740271224846167 21565011371610406837269251)
          ·
            refine ⟨32347517057415610255903877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21565011371610406837269251 32347517057415610255903877)
            ·
              refine ⟨6065159448265426922981977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32347517057415610255903877 6065159448265426922981977)
              ·
                refine ⟨4548869586199070192236483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6065159448265426922981977 4548869586199070192236483)
                ·
                  refine ⟨6823304379298605288354725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4548869586199070192236483 6823304379298605288354725)
                  ·
                    refine ⟨1279369571118488491566511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6823304379298605288354725 1279369571118488491566511)
                    ·
                      rfl

theorem cell23_7474690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7474690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474690 prefixEnd_7474690 := by exact prefixLift 7474690
  have htrace : WordTrace (prefixWord ++ tailWord_7474690) baseStart_7474690 baseEnd_7474690 := by
    simpa [prefixWord, tailWord_7474690, baseEnd_7474690] using wordTrace_append hprefix tailTrace_7474690
  have hstable : (prefixWord ++ tailWord_7474690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474690).length < 2 ^ (prefixWord ++ tailWord_7474690).sum := by decide
  have hdescent : baseEnd_7474690 < baseStart_7474690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474723 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 2, 3, 2]
def baseStart_7474723 : Nat := 118140960795 + 7474723 * 2 ^ 59
def prefixEnd_7474723 : Nat := 4983230072969 + 3 ^ 40 * 7474723 * 2
def baseEnd_7474723 : Nat := 3838125658217063845586881

theorem tailTrace_7474723 : CollatzResearch.WordTrace tailWord_7474723 prefixEnd_7474723 3838125658217063845586881 := by
  unfold tailWord_7474723
  simp only [CollatzResearch.WordTrace]
  refine ⟨272625544899362626899700823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181750363266241751266467215 272625544899362626899700823)
  ·
    refine ⟨408938317349043940349551235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272625544899362626899700823 408938317349043940349551235)
    ·
      refine ⟨613407476023565910524326853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408938317349043940349551235 613407476023565910524326853)
      ·
        refine ⟨115013901754418608223311285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 613407476023565910524326853 115013901754418608223311285)
        ·
          refine ⟨10782553289476744520935433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115013901754418608223311285 10782553289476744520935433)
          ·
            refine ⟨8086914967107558390701575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10782553289476744520935433 8086914967107558390701575)
            ·
              refine ⟨12130372450661337586052363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086914967107558390701575 12130372450661337586052363)
              ·
                refine ⟨18195558675992006379078545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12130372450661337586052363 18195558675992006379078545)
                ·
                  refine ⟨13646669006994004784308909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18195558675992006379078545 13646669006994004784308909)
                  ·
                    refine ⟨5117500877622751794115841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13646669006994004784308909 5117500877622751794115841)
                    ·
                      refine ⟨3838125658217063845586881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117500877622751794115841 3838125658217063845586881)
                      ·
                        rfl

theorem cell23_7474723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_7474723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474723 prefixEnd_7474723 := by exact prefixLift 7474723
  have htrace : WordTrace (prefixWord ++ tailWord_7474723) baseStart_7474723 baseEnd_7474723 := by
    simpa [prefixWord, tailWord_7474723, baseEnd_7474723] using wordTrace_append hprefix tailTrace_7474723
  have hstable : (prefixWord ++ tailWord_7474723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474723).length < 2 ^ (prefixWord ++ tailWord_7474723).sum := by decide
  have hdescent : baseEnd_7474723 < baseStart_7474723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474753 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_7474753 : Nat := 118140960795 + 7474753 * 2 ^ 59
def prefixEnd_7474753 : Nat := 4983230072969 + 3 ^ 40 * 7474753 * 2
def baseEnd_7474753 : Nat := 3838141062636698728211743

theorem tailTrace_7474753 : CollatzResearch.WordTrace tailWord_7474753 prefixEnd_7474753 3838141062636698728211743 := by
  unfold tailWord_7474753
  simp only [CollatzResearch.WordTrace]
  refine ⟨272626639089253942023292913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181751092726169294682195275 272626639089253942023292913)
  ·
    refine ⟨204469979316940456517469685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272626639089253942023292913 204469979316940456517469685)
    ·
      refine ⟨19169060560963167798512783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204469979316940456517469685 19169060560963167798512783)
      ·
        refine ⟨28753590841444751697769175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19169060560963167798512783 28753590841444751697769175)
        ·
          refine ⟨43130386262167127546653763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28753590841444751697769175 43130386262167127546653763)
          ·
            refine ⟨64695579393250691319980645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43130386262167127546653763 64695579393250691319980645)
            ·
              refine ⟨12130421136234504622496371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64695579393250691319980645 12130421136234504622496371)
              ·
                refine ⟨18195631704351756933744557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12130421136234504622496371 18195631704351756933744557)
                ·
                  refine ⟨6823361889131908850154209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18195631704351756933744557 6823361889131908850154209)
                  ·
                    refine ⟨5117521416848931637615657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6823361889131908850154209 5117521416848931637615657)
                    ·
                      refine ⟨3838141062636698728211743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117521416848931637615657 3838141062636698728211743)
                      ·
                        rfl

theorem cell23_7474753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_7474753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474753 prefixEnd_7474753 := by exact prefixLift 7474753
  have htrace : WordTrace (prefixWord ++ tailWord_7474753) baseStart_7474753 baseEnd_7474753 := by
    simpa [prefixWord, tailWord_7474753, baseEnd_7474753] using wordTrace_append hprefix tailTrace_7474753
  have hstable : (prefixWord ++ tailWord_7474753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474753).length < 2 ^ (prefixWord ++ tailWord_7474753).sum := by decide
  have hdescent : baseEnd_7474753 < baseStart_7474753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474812 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_7474812 : Nat := 118140960795 + 7474812 * 2 ^ 59
def prefixEnd_7474812 : Nat := 4983230072969 + 3 ^ 40 * 7474812 * 2
def baseEnd_7474812 : Nat := 3838171357995313997373971

theorem tailTrace_7474812 : CollatzResearch.WordTrace tailWord_7474812 prefixEnd_7474812 3838171357995313997373971 := by
  unfold tailWord_7474812
  simp only [CollatzResearch.WordTrace]
  refine ⟨136314395498020097549845345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181752527330693463399793793 136314395498020097549845345)
  ·
    refine ⟨102235796623515073162384009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136314395498020097549845345 102235796623515073162384009)
    ·
      refine ⟨76676847467636304871788007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102235796623515073162384009 76676847467636304871788007)
      ·
        refine ⟨115015271201454457307682011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76676847467636304871788007 115015271201454457307682011)
        ·
          refine ⟨172522906802181685961523017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115015271201454457307682011 172522906802181685961523017)
          ·
            refine ⟨129392180101636264471142263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172522906802181685961523017 129392180101636264471142263)
            ·
              refine ⟨194088270152454396706713395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129392180101636264471142263 194088270152454396706713395)
              ·
                refine ⟨291132405228681595060070093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194088270152454396706713395 291132405228681595060070093)
                ·
                  refine ⟨109174651960755598147526285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291132405228681595060070093 109174651960755598147526285)
                  ·
                    refine ⟨40940494485283349305322357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109174651960755598147526285 40940494485283349305322357)
                    ·
                      refine ⟨3838171357995313997373971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40940494485283349305322357 3838171357995313997373971)
                      ·
                        rfl

theorem cell23_7474812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_7474812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474812 prefixEnd_7474812 := by exact prefixLift 7474812
  have htrace : WordTrace (prefixWord ++ tailWord_7474812) baseStart_7474812 baseEnd_7474812 := by
    simpa [prefixWord, tailWord_7474812, baseEnd_7474812] using wordTrace_append hprefix tailTrace_7474812
  have hstable : (prefixWord ++ tailWord_7474812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474812).length < 2 ^ (prefixWord ++ tailWord_7474812).sum := by decide
  have hdescent : baseEnd_7474812 < baseStart_7474812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474830 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7474830 : Nat := 118140960795 + 7474830 * 2 ^ 59
def prefixEnd_7474830 : Nat := 4983230072969 + 3 ^ 40 * 7474830 * 2
def baseEnd_7474830 : Nat := 3838180600647094926948889

theorem tailTrace_7474830 : CollatzResearch.WordTrace tailWord_7474830 prefixEnd_7474830 3838180600647094926948889 := by
  unfold tailWord_7474830
  simp only [CollatzResearch.WordTrace]
  refine ⟨34078680938746873021730743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181752965006649989449230629 34078680938746873021730743)
  ·
    refine ⟨51118021408120309532596115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34078680938746873021730743 51118021408120309532596115)
    ·
      refine ⟨76677032112180464298894173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51118021408120309532596115 76677032112180464298894173)
      ·
        refine ⟨28753887042067674112085315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76677032112180464298894173 28753887042067674112085315)
        ·
          refine ⟨43130830563101511168127973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28753887042067674112085315 43130830563101511168127973)
          ·
            refine ⟨8087030730581533344023995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43130830563101511168127973 8087030730581533344023995)
            ·
              refine ⟨12130546095872300016035993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087030730581533344023995 12130546095872300016035993)
              ·
                refine ⟨9097909571904225012026995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12130546095872300016035993 9097909571904225012026995)
                ·
                  refine ⟨13646864357856337518040493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097909571904225012026995 13646864357856337518040493)
                  ·
                    refine ⟨5117574134196126569265185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13646864357856337518040493 5117574134196126569265185)
                    ·
                      refine ⟨3838180600647094926948889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117574134196126569265185 3838180600647094926948889)
                      ·
                        rfl

theorem cell23_7474830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7474830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474830 prefixEnd_7474830 := by exact prefixLift 7474830
  have htrace : WordTrace (prefixWord ++ tailWord_7474830) baseStart_7474830 baseEnd_7474830 := by
    simpa [prefixWord, tailWord_7474830, baseEnd_7474830] using wordTrace_append hprefix tailTrace_7474830
  have hstable : (prefixWord ++ tailWord_7474830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474830).length < 2 ^ (prefixWord ++ tailWord_7474830).sum := by decide
  have hdescent : baseEnd_7474830 < baseStart_7474830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474832 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 7]
def baseStart_7474832 : Nat := 118140960795 + 7474832 * 2 ^ 59
def prefixEnd_7474832 : Nat := 4983230072969 + 3 ^ 40 * 7474832 * 2
def baseEnd_7474832 : Nat := 426464625289822657680431

theorem tailTrace_7474832 : CollatzResearch.WordTrace tailWord_7474832 prefixEnd_7474832 426464625289822657680431 := by
  unfold tailWord_7474832
  simp only [CollatzResearch.WordTrace]
  refine ⟨136314760227983869257709375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181753013637311825676945833 136314760227983869257709375)
  ·
    refine ⟨204472140341975803886564063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136314760227983869257709375 204472140341975803886564063)
    ·
      refine ⟨306708210512963705829846095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204472140341975803886564063 306708210512963705829846095)
      ·
        refine ⟨460062315769445558744769143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306708210512963705829846095 460062315769445558744769143)
        ·
          refine ⟨690093473654168338117153715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460062315769445558744769143 690093473654168338117153715)
          ·
            refine ⟨1035140210481252507175730573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690093473654168338117153715 1035140210481252507175730573)
            ·
              refine ⟨388177578930469690190898965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1035140210481252507175730573 388177578930469690190898965)
              ·
                refine ⟨18195824012365766727698389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388177578930469690190898965 18195824012365766727698389)
                ·
                  refine ⟨426464625289822657680431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18195824012365766727698389 426464625289822657680431)
                  ·
                    rfl

theorem cell23_7474832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_7474832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474832 prefixEnd_7474832 := by exact prefixLift 7474832
  have htrace : WordTrace (prefixWord ++ tailWord_7474832) baseStart_7474832 baseEnd_7474832 := by
    simpa [prefixWord, tailWord_7474832, baseEnd_7474832] using wordTrace_append hprefix tailTrace_7474832
  have hstable : (prefixWord ++ tailWord_7474832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474832).length < 2 ^ (prefixWord ++ tailWord_7474832).sum := by decide
  have hdescent : baseEnd_7474832 < baseStart_7474832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474846 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_7474846 : Nat := 118140960795 + 7474846 * 2 ^ 59
def prefixEnd_7474846 : Nat := 4983230072969 + 3 ^ 40 * 7474846 * 2
def baseEnd_7474846 : Nat := 3838188816337566864348815

theorem tailTrace_7474846 : CollatzResearch.WordTrace tailWord_7474846 prefixEnd_7474846 3838188816337566864348815 := by
  unfold tailWord_7474846
  simp only [CollatzResearch.WordTrace]
  refine ⟨34078753884739627363303549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181753354051944679270952261 34078753884739627363303549)
  ·
    refine ⟨12779532706777360261238831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34078753884739627363303549 12779532706777360261238831)
    ·
      refine ⟨19169299060166040391858247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12779532706777360261238831 19169299060166040391858247)
      ·
        refine ⟨28753948590249060587787371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19169299060166040391858247 28753948590249060587787371)
        ·
          refine ⟨43130922885373590881681057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28753948590249060587787371 43130922885373590881681057)
          ·
            refine ⟨32348192164030193161260793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43130922885373590881681057 32348192164030193161260793)
            ·
              refine ⟨24261144123022644870945595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32348192164030193161260793 24261144123022644870945595)
              ·
                refine ⟨36391716184533967306418393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24261144123022644870945595 36391716184533967306418393)
                ·
                  refine ⟨27293787138400475479813795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36391716184533967306418393 27293787138400475479813795)
                  ·
                    refine ⟨40940680707600713219720693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27293787138400475479813795 40940680707600713219720693)
                    ·
                      refine ⟨3838188816337566864348815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40940680707600713219720693 3838188816337566864348815)
                      ·
                        rfl

theorem cell23_7474846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_7474846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474846 prefixEnd_7474846 := by exact prefixLift 7474846
  have htrace : WordTrace (prefixWord ++ tailWord_7474846) baseStart_7474846 baseEnd_7474846 := by
    simpa [prefixWord, tailWord_7474846, baseEnd_7474846] using wordTrace_append hprefix tailTrace_7474846
  have hstable : (prefixWord ++ tailWord_7474846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474846).length < 2 ^ (prefixWord ++ tailWord_7474846).sum := by decide
  have hdescent : baseEnd_7474846 < baseStart_7474846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474847 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7474847 : Nat := 118140960795 + 7474847 * 2 ^ 59
def prefixEnd_7474847 : Nat := 4983230072969 + 3 ^ 40 * 7474847 * 2
def baseEnd_7474847 : Nat := 3838189329818221360436311

theorem tailTrace_7474847 : CollatzResearch.WordTrace tailWord_7474847 prefixEnd_7474847 3838189329818221360436311 := by
  unfold tailWord_7474847
  simp only [CollatzResearch.WordTrace]
  refine ⟨272630067550913396077214795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181753378367275597384809863 272630067550913396077214795)
  ·
    refine ⟨408945101326370094115822193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272630067550913396077214795 408945101326370094115822193)
    ·
      refine ⟨306708825994777570586866645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408945101326370094115822193 306708825994777570586866645)
      ·
        refine ⟨7188488109252599310629687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 306708825994777570586866645 7188488109252599310629687)
        ·
          refine ⟨10782732163878898965944531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188488109252599310629687 10782732163878898965944531)
          ·
            refine ⟨16174098245818348448916797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10782732163878898965944531 16174098245818348448916797)
            ·
              refine ⟨6065286842181880668343799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16174098245818348448916797 6065286842181880668343799)
              ·
                refine ⟨9097930263272821002515699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065286842181880668343799 9097930263272821002515699)
                ·
                  refine ⟨13646895394909231503773549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097930263272821002515699 13646895394909231503773549)
                  ·
                    refine ⟨5117585773090961813915081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13646895394909231503773549 5117585773090961813915081)
                    ·
                      refine ⟨3838189329818221360436311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117585773090961813915081 3838189329818221360436311)
                      ·
                        rfl

theorem cell23_7474847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7474847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474847 prefixEnd_7474847 := by exact prefixLift 7474847
  have htrace : WordTrace (prefixWord ++ tailWord_7474847) baseStart_7474847 baseEnd_7474847 := by
    simpa [prefixWord, tailWord_7474847, baseEnd_7474847] using wordTrace_append hprefix tailTrace_7474847
  have hstable : (prefixWord ++ tailWord_7474847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474847).length < 2 ^ (prefixWord ++ tailWord_7474847).sum := by decide
  have hdescent : baseEnd_7474847 < baseStart_7474847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474876 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_7474876 : Nat := 118140960795 + 7474876 * 2 ^ 59
def prefixEnd_7474876 : Nat := 4983230072969 + 3 ^ 40 * 7474876 * 2
def baseEnd_7474876 : Nat := 3838204220757201746973677

theorem tailTrace_7474876 : CollatzResearch.WordTrace tailWord_7474876 prefixEnd_7474876 3838204220757201746973677 := by
  unfold tailWord_7474876
  simp only [CollatzResearch.WordTrace]
  refine ⟨136315562633904167015010241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181754083511872222686680321 136315562633904167015010241)
  ·
    refine ⟨102236671975428125261257681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136315562633904167015010241 102236671975428125261257681)
    ·
      refine ⟨76677503981571093945943261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102236671975428125261257681 76677503981571093945943261)
      ·
        refine ⟨28754063993089160229728723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76677503981571093945943261 28754063993089160229728723)
        ·
          refine ⟨43131095989633740344593085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28754063993089160229728723 43131095989633740344593085)
          ·
            refine ⟨16174160996112652629222407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43131095989633740344593085 16174160996112652629222407)
            ·
              refine ⟨24261241494168978943833611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16174160996112652629222407 24261241494168978943833611)
              ·
                refine ⟨36391862241253468415750417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24261241494168978943833611 36391862241253468415750417)
                ·
                  refine ⟨27293896680940101311812813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36391862241253468415750417 27293896680940101311812813)
                  ·
                    refine ⟨10235211255352537991929805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27293896680940101311812813 10235211255352537991929805)
                    ·
                      refine ⟨3838204220757201746973677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10235211255352537991929805 3838204220757201746973677)
                      ·
                        rfl

theorem cell23_7474876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_7474876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474876 prefixEnd_7474876 := by exact prefixLift 7474876
  have htrace : WordTrace (prefixWord ++ tailWord_7474876) baseStart_7474876 baseEnd_7474876 := by
    simpa [prefixWord, tailWord_7474876, baseEnd_7474876] using wordTrace_append hprefix tailTrace_7474876
  have hstable : (prefixWord ++ tailWord_7474876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474876).length < 2 ^ (prefixWord ++ tailWord_7474876).sum := by decide
  have hdescent : baseEnd_7474876 < baseStart_7474876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474916 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_7474916 : Nat := 118140960795 + 7474916 * 2 ^ 59
def prefixEnd_7474916 : Nat := 4983230072969 + 3 ^ 40 * 7474916 * 2
def baseEnd_7474916 : Nat := 3838224759983381590473493

theorem tailTrace_7474916 : CollatzResearch.WordTrace tailWord_7474916 prefixEnd_7474916 3838224759983381590473493 := by
  unfold tailWord_7474916
  simp only [CollatzResearch.WordTrace]
  refine ⟨136316292093831710430738301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181755056125108947240984401 136316292093831710430738301)
  ·
    refine ⟨51118609535186891411526863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136316292093831710430738301 51118609535186891411526863)
    ·
      refine ⟨76677914302780337117290295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51118609535186891411526863 76677914302780337117290295)
      ·
        refine ⟨115016871454170505675935443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76677914302780337117290295 115016871454170505675935443)
        ·
          refine ⟨172525307181255758513903165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115016871454170505675935443 172525307181255758513903165)
          ·
            refine ⟨64696990192970909442713687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172525307181255758513903165 64696990192970909442713687)
            ·
              refine ⟨97045485289456364164070531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64696990192970909442713687 97045485289456364164070531)
              ·
                refine ⟨145568227934184546246105797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97045485289456364164070531 145568227934184546246105797)
                ·
                  refine ⟨27294042737659602421144837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145568227934184546246105797 27294042737659602421144837)
                  ·
                    refine ⟨5117633013311175453964657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27294042737659602421144837 5117633013311175453964657)
                    ·
                      refine ⟨3838224759983381590473493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117633013311175453964657 3838224759983381590473493)
                      ·
                        rfl

theorem cell23_7474916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_7474916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474916 prefixEnd_7474916 := by exact prefixLift 7474916
  have htrace : WordTrace (prefixWord ++ tailWord_7474916) baseStart_7474916 baseEnd_7474916 := by
    simpa [prefixWord, tailWord_7474916, baseEnd_7474916] using wordTrace_append hprefix tailTrace_7474916
  have hstable : (prefixWord ++ tailWord_7474916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474916).length < 2 ^ (prefixWord ++ tailWord_7474916).sum := by decide
  have hdescent : baseEnd_7474916 < baseStart_7474916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7474946 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7474946 : Nat := 118140960795 + 7474946 * 2 ^ 59
def prefixEnd_7474946 : Nat := 4983230072969 + 3 ^ 40 * 7474946 * 2
def baseEnd_7474946 : Nat := 3838240164403016473098355

theorem tailTrace_7474946 : CollatzResearch.WordTrace tailWord_7474946 prefixEnd_7474946 3838240164403016473098355 := by
  unfold tailWord_7474946
  simp only [CollatzResearch.WordTrace]
  refine ⟨68158419594388683996267173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181755785585036490656712461 68158419594388683996267173)
  ·
    refine ⟨12779703673947878249300095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68158419594388683996267173 12779703673947878249300095)
    ·
      refine ⟨19169555510921817373950143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12779703673947878249300095 19169555510921817373950143)
      ·
        refine ⟨28754333266382726060925215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19169555510921817373950143 28754333266382726060925215)
        ·
          refine ⟨43131499899574089091387823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28754333266382726060925215 43131499899574089091387823)
          ·
            refine ⟨64697249849361133637081735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43131499899574089091387823 64697249849361133637081735)
            ·
              refine ⟨97045874774041700455622603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64697249849361133637081735 97045874774041700455622603)
              ·
                refine ⟨145568812161062550683433905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97045874774041700455622603 145568812161062550683433905)
                ·
                  refine ⟨109176609120796913012575429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145568812161062550683433905 109176609120796913012575429)
                  ·
                    refine ⟨20470614210149421189857893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109176609120796913012575429 20470614210149421189857893)
                    ·
                      refine ⟨3838240164403016473098355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20470614210149421189857893 3838240164403016473098355)
                      ·
                        rfl

theorem cell23_7474946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7474946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7474946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7474946 prefixEnd_7474946 := by exact prefixLift 7474946
  have htrace : WordTrace (prefixWord ++ tailWord_7474946) baseStart_7474946 baseEnd_7474946 := by
    simpa [prefixWord, tailWord_7474946, baseEnd_7474946] using wordTrace_append hprefix tailTrace_7474946
  have hstable : (prefixWord ++ tailWord_7474946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7474946).length < 2 ^ (prefixWord ++ tailWord_7474946).sum := by decide
  have hdescent : baseEnd_7474946 < baseStart_7474946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7474946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475016 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 1, 6]
def baseStart_7475016 : Nat := 118140960795 + 7475016 * 2 ^ 59
def prefixEnd_7475016 : Nat := 4983230072969 + 3 ^ 40 * 7475016 * 2
def baseEnd_7475016 : Nat := 1279425369349610399741011

theorem tailTrace_7475016 : CollatzResearch.WordTrace tailWord_7475016 prefixEnd_7475016 1279425369349610399741011 := by
  unfold tailWord_7475016
  simp only [CollatzResearch.WordTrace]
  refine ⟨136318115743650568970058451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181757487658200758626744601 136318115743650568970058451)
  ·
    refine ⟨204477173615475853455087677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136318115743650568970058451 204477173615475853455087677)
    ·
      refine ⟨76678940105803445045657879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204477173615475853455087677 76678940105803445045657879)
      ·
        refine ⟨115018410158705167568486819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76678940105803445045657879 115018410158705167568486819)
        ·
          refine ⟨172527615238057751352730229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115018410158705167568486819 172527615238057751352730229)
          ·
            refine ⟨16174463928567914189318459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172527615238057751352730229 16174463928567914189318459)
            ·
              refine ⟨24261695892851871283977689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16174463928567914189318459 24261695892851871283977689)
              ·
                refine ⟨18196271919638903462983267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24261695892851871283977689 18196271919638903462983267)
                ·
                  refine ⟨27294407879458355194474901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18196271919638903462983267 27294407879458355194474901)
                  ·
                    refine ⟨1279425369349610399741011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27294407879458355194474901 1279425369349610399741011)
                    ·
                      rfl

theorem cell23_7475016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_7475016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475016 prefixEnd_7475016 := by exact prefixLift 7475016
  have htrace : WordTrace (prefixWord ++ tailWord_7475016) baseStart_7475016 baseEnd_7475016 := by
    simpa [prefixWord, tailWord_7475016, baseEnd_7475016] using wordTrace_append hprefix tailTrace_7475016
  have hstable : (prefixWord ++ tailWord_7475016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475016).length < 2 ^ (prefixWord ++ tailWord_7475016).sum := by decide
  have hdescent : baseEnd_7475016 < baseStart_7475016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475020 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_7475020 : Nat := 118140960795 + 7475020 * 2 ^ 59
def prefixEnd_7475020 : Nat := 4983230072969 + 3 ^ 40 * 7475020 * 2
def baseEnd_7475020 : Nat := 1279426053990483061191005

theorem tailTrace_7475020 : CollatzResearch.WordTrace tailWord_7475020 prefixEnd_7475020 1279426053990483061191005 := by
  unfold tailWord_7475020
  simp only [CollatzResearch.WordTrace]
  refine ⟨136318188689643323311631257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181757584919524431082175009 136318188689643323311631257)
  ·
    refine ⟨102238641517232492483723443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136318188689643323311631257 102238641517232492483723443)
    ·
      refine ⟨153357962275848738725585165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102238641517232492483723443 153357962275848738725585165)
      ·
        refine ⟨57509235853443277022094437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153357962275848738725585165 57509235853443277022094437)
        ·
          refine ⟨10782981722520614441642707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57509235853443277022094437 10782981722520614441642707)
          ·
            refine ⟨16174472583780921662464061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10782981722520614441642707 16174472583780921662464061)
            ·
              refine ⟨6065427218917845623424023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16174472583780921662464061 6065427218917845623424023)
              ·
                refine ⟨9098140828376768435136035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065427218917845623424023 9098140828376768435136035)
                ·
                  refine ⟨13647211242565152652704053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9098140828376768435136035 13647211242565152652704053)
                  ·
                    refine ⟨1279426053990483061191005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13647211242565152652704053 1279426053990483061191005)
                    ·
                      rfl

theorem cell23_7475020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_7475020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475020 prefixEnd_7475020 := by exact prefixLift 7475020
  have htrace : WordTrace (prefixWord ++ tailWord_7475020) baseStart_7475020 baseEnd_7475020 := by
    simpa [prefixWord, tailWord_7475020, baseEnd_7475020] using wordTrace_append hprefix tailTrace_7475020
  have hstable : (prefixWord ++ tailWord_7475020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475020).length < 2 ^ (prefixWord ++ tailWord_7475020).sum := by decide
  have hdescent : baseEnd_7475020 < baseStart_7475020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475029 : List Nat := [1, 3, 2, 2, 2, 13]
def baseStart_7475029 : Nat := 118140960795 + 7475029 * 2 ^ 59
def prefixEnd_7475029 : Nat := 4983230072969 + 3 ^ 40 * 7475029 * 2
def baseEnd_7475029 : Nat := 15795402400400574684611

theorem tailTrace_7475029 : CollatzResearch.WordTrace tailWord_7475029 prefixEnd_7475029 15795402400400574684611 := by
  unfold tailWord_7475029
  simp only [CollatzResearch.WordTrace]
  refine ⟨272636705636254041160340141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181757803757502694106893427 272636705636254041160340141)
  ·
    refine ⟨102238764613595265435127553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272636705636254041160340141 102238764613595265435127553)
    ·
      refine ⟨76679073460196449076345665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102238764613595265435127553 76679073460196449076345665)
      ·
        refine ⟨57509305095147336807259249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76679073460196449076345665 57509305095147336807259249)
        ·
          refine ⟨43131978821360502605444437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57509305095147336807259249 43131978821360502605444437)
          ·
            refine ⟨15795402400400574684611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 43131978821360502605444437 15795402400400574684611)
            ·
              rfl

theorem cell23_7475029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 13].length) (baseStart_7475029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475029 prefixEnd_7475029 := by exact prefixLift 7475029
  have htrace : WordTrace (prefixWord ++ tailWord_7475029) baseStart_7475029 baseEnd_7475029 := by
    simpa [prefixWord, tailWord_7475029, baseEnd_7475029] using wordTrace_append hprefix tailTrace_7475029
  have hstable : (prefixWord ++ tailWord_7475029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475029).length < 2 ^ (prefixWord ++ tailWord_7475029).sum := by decide
  have hdescent : baseEnd_7475029 < baseStart_7475029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475033 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 2, 4]
def baseStart_7475033 : Nat := 118140960795 + 7475033 * 2 ^ 59
def prefixEnd_7475033 : Nat := 4983230072969 + 3 ^ 40 * 7475033 * 2
def baseEnd_7475033 : Nat := 1279428279073319210903485

theorem tailTrace_7475033 : CollatzResearch.WordTrace tailWord_7475033 prefixEnd_7475033 1279428279073319210903485 := by
  unfold tailWord_7475033
  simp only [CollatzResearch.WordTrace]
  refine ⟨272636851528239549843485753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181757901018826366562323835 272636851528239549843485753)
  ·
    refine ⟨204477638646179662382614315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272636851528239549843485753 204477638646179662382614315)
    ·
      refine ⟨306716457969269493573921473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204477638646179662382614315 306716457969269493573921473)
      ·
        refine ⟨230037343476952120180441105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306716457969269493573921473 230037343476952120180441105)
        ·
          refine ⟨172528007607714090135330829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230037343476952120180441105 172528007607714090135330829)
          ·
            refine ⟨64698002852892783800749061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172528007607714090135330829 64698002852892783800749061)
            ·
              refine ⟨12130875534917396962640449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64698002852892783800749061 12130875534917396962640449)
              ·
                refine ⟨9098156651188047721980337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12130875534917396962640449 9098156651188047721980337)
                ·
                  refine ⟨6823617488391035791485253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9098156651188047721980337 6823617488391035791485253)
                  ·
                    refine ⟨1279428279073319210903485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6823617488391035791485253 1279428279073319210903485)
                    ·
                      rfl

theorem cell23_7475033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_7475033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475033 prefixEnd_7475033 := by exact prefixLift 7475033
  have htrace : WordTrace (prefixWord ++ tailWord_7475033) baseStart_7475033 baseEnd_7475033 := by
    simpa [prefixWord, tailWord_7475033, baseEnd_7475033] using wordTrace_append hprefix tailTrace_7475033
  have hstable : (prefixWord ++ tailWord_7475033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475033).length < 2 ^ (prefixWord ++ tailWord_7475033).sum := by decide
  have hdescent : baseEnd_7475033 < baseStart_7475033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475049 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_7475049 : Nat := 118140960795 + 7475049 * 2 ^ 59
def prefixEnd_7475049 : Nat := 4983230072969 + 3 ^ 40 * 7475049 * 2
def baseEnd_7475049 : Nat := 3838293052910429570110381

theorem tailTrace_7475049 : CollatzResearch.WordTrace tailWord_7475049 prefixEnd_7475049 3838293052910429570110381 := by
  unfold tailWord_7475049
  simp only [CollatzResearch.WordTrace]
  refine ⟨272637435096181584576068201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181758290064121056384045467 272637435096181584576068201)
  ·
    refine ⟨204478076322136188432051151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272637435096181584576068201 204478076322136188432051151)
    ·
      refine ⟨306717114483204282648076727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204478076322136188432051151 306717114483204282648076727)
      ·
        refine ⟨460075671724806423972115091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306717114483204282648076727 460075671724806423972115091)
        ·
          refine ⟨690113507587209635958172637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460075671724806423972115091 690113507587209635958172637)
          ·
            refine ⟨258792565345203613484314739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 690113507587209635958172637 258792565345203613484314739)
            ·
              refine ⟨388188848017805420226472109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258792565345203613484314739 388188848017805420226472109)
              ·
                refine ⟨145570818006677032584927041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388188848017805420226472109 145570818006677032584927041)
                ·
                  refine ⟨109178113505007774438695281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145570818006677032584927041 109178113505007774438695281)
                  ·
                    refine ⟨81883585128755830829021461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109178113505007774438695281 81883585128755830829021461)
                    ·
                      refine ⟨3838293052910429570110381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81883585128755830829021461 3838293052910429570110381)
                      ·
                        rfl

theorem cell23_7475049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_7475049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475049 prefixEnd_7475049 := by exact prefixLift 7475049
  have htrace : WordTrace (prefixWord ++ tailWord_7475049) baseStart_7475049 baseEnd_7475049 := by
    simpa [prefixWord, tailWord_7475049, baseEnd_7475049] using wordTrace_append hprefix tailTrace_7475049
  have hstable : (prefixWord ++ tailWord_7475049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475049).length < 2 ^ (prefixWord ++ tailWord_7475049).sum := by decide
  have hdescent : baseEnd_7475049 < baseStart_7475049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475050 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_7475050 : Nat := 118140960795 + 7475050 * 2 ^ 59
def prefixEnd_7475050 : Nat := 4983230072969 + 3 ^ 40 * 7475050 * 2
def baseEnd_7475050 : Nat := 1279431188797028022065959

theorem tailTrace_7475050 : CollatzResearch.WordTrace tailWord_7475050 prefixEnd_7475050 1279431188797028022065959 := by
  unfold tailWord_7475050
  simp only [CollatzResearch.WordTrace]
  refine ⟨68159367892294490436713651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181758314379451974497903069 68159367892294490436713651)
  ·
    refine ⟨102239051838441735655070477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68159367892294490436713651 102239051838441735655070477)
    ·
      refine ⟨38339644439415650870651429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102239051838441735655070477 38339644439415650870651429)
      ·
        refine ⟨7188683332390434538247143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38339644439415650870651429 7188683332390434538247143)
        ·
          refine ⟨10783024998585651807370715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188683332390434538247143 10783024998585651807370715)
          ·
            refine ⟨16174537497878477711056073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10783024998585651807370715 16174537497878477711056073)
            ·
              refine ⟨12130903123408858283292055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16174537497878477711056073 12130903123408858283292055)
              ·
                refine ⟨18196354685113287424938083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12130903123408858283292055 18196354685113287424938083)
                ·
                  refine ⟨27294532027669931137407125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18196354685113287424938083 27294532027669931137407125)
                  ·
                    refine ⟨1279431188797028022065959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27294532027669931137407125 1279431188797028022065959)
                    ·
                      rfl

theorem cell23_7475050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_7475050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475050 prefixEnd_7475050 := by exact prefixLift 7475050
  have htrace : WordTrace (prefixWord ++ tailWord_7475050) baseStart_7475050 baseEnd_7475050 := by
    simpa [prefixWord, tailWord_7475050, baseEnd_7475050] using wordTrace_append hprefix tailTrace_7475050
  have hstable : (prefixWord ++ tailWord_7475050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475050).length < 2 ^ (prefixWord ++ tailWord_7475050).sum := by decide
  have hdescent : baseEnd_7475050 < baseStart_7475050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475059 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 4, 7]
def baseStart_7475059 : Nat := 118140960795 + 7475059 * 2 ^ 59
def prefixEnd_7475059 : Nat := 4983230072969 + 3 ^ 40 * 7475059 * 2
def baseEnd_7475059 : Nat := 1279432729238991510328445

theorem tailTrace_7475059 : CollatzResearch.WordTrace tailWord_7475059 prefixEnd_7475059 1279432729238991510328445 := by
  unfold tailWord_7475059
  simp only [CollatzResearch.WordTrace]
  refine ⟨272637799826145356283932231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181758533217430237522621487 272637799826145356283932231)
  ·
    refine ⟨408956699739218034425898347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272637799826145356283932231 408956699739218034425898347)
    ·
      refine ⟨613435049608827051638847521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408956699739218034425898347 613435049608827051638847521)
      ·
        refine ⟨460076287206620288729135641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613435049608827051638847521 460076287206620288729135641)
        ·
          refine ⟨345057215404965216546851731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460076287206620288729135641 345057215404965216546851731)
          ·
            refine ⟨517585823107447824820277597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345057215404965216546851731 517585823107447824820277597)
            ·
              refine ⟨194094683665292934307604099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517585823107447824820277597 194094683665292934307604099)
              ·
                refine ⟨291142025497939401461406149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194094683665292934307604099 291142025497939401461406149)
                ·
                  refine ⟨54589129780863637774013653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291142025497939401461406149 54589129780863637774013653)
                  ·
                    refine ⟨1279432729238991510328445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54589129780863637774013653 1279432729238991510328445)
                    ·
                      rfl

theorem cell23_7475059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 7].length) (baseStart_7475059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475059 prefixEnd_7475059 := by exact prefixLift 7475059
  have htrace : WordTrace (prefixWord ++ tailWord_7475059) baseStart_7475059 baseEnd_7475059 := by
    simpa [prefixWord, tailWord_7475059, baseEnd_7475059] using wordTrace_append hprefix tailTrace_7475059
  have hstable : (prefixWord ++ tailWord_7475059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475059).length < 2 ^ (prefixWord ++ tailWord_7475059).sum := by decide
  have hdescent : baseEnd_7475059 < baseStart_7475059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475070 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7475070 : Nat := 118140960795 + 7475070 * 2 ^ 59
def prefixEnd_7475070 : Nat := 4983230072969 + 3 ^ 40 * 7475070 * 2
def baseEnd_7475070 : Nat := 3838303836004173987947785

theorem tailTrace_7475070 : CollatzResearch.WordTrace tailWord_7475070 prefixEnd_7475070 3838303836004173987947785 := by
  unfold tailWord_7475070
  simp only [CollatzResearch.WordTrace]
  refine ⟨34079775128638188145322833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181758800686070336775055109 34079775128638188145322833)
  ·
    refine ⟨25559831346478641108992125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34079775128638188145322833 25559831346478641108992125)
    ·
      refine ⟨9584936754929490415872047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25559831346478641108992125 9584936754929490415872047)
      ·
        refine ⟨14377405132394235623808071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584936754929490415872047 14377405132394235623808071)
        ·
          refine ⟨21566107698591353435712107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14377405132394235623808071 21566107698591353435712107)
          ·
            refine ⟨32349161547887030153568161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21566107698591353435712107 32349161547887030153568161)
            ·
              refine ⟨24261871160915272615176121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32349161547887030153568161 24261871160915272615176121)
              ·
                refine ⟨18196403370686454461382091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24261871160915272615176121 18196403370686454461382091)
                ·
                  refine ⟨27294605056029681692073137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18196403370686454461382091 27294605056029681692073137)
                  ·
                    refine ⟨20470953792022261269054853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27294605056029681692073137 20470953792022261269054853)
                    ·
                      refine ⟨3838303836004173987947785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20470953792022261269054853 3838303836004173987947785)
                      ·
                        rfl

theorem cell23_7475070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7475070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475070 prefixEnd_7475070 := by exact prefixLift 7475070
  have htrace : WordTrace (prefixWord ++ tailWord_7475070) baseStart_7475070 baseEnd_7475070 := by
    simpa [prefixWord, tailWord_7475070, baseEnd_7475070] using wordTrace_append hprefix tailTrace_7475070
  have hstable : (prefixWord ++ tailWord_7475070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475070).length < 2 ^ (prefixWord ++ tailWord_7475070).sum := by decide
  have hdescent : baseEnd_7475070 < baseStart_7475070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475113 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 1, 4, 2]
def baseStart_7475113 : Nat := 118140960795 + 7475113 * 2 ^ 59
def prefixEnd_7475113 : Nat := 4983230072969 + 3 ^ 40 * 7475113 * 2
def baseEnd_7475113 : Nat := 3838325915672317319710087

theorem tailTrace_7475113 : CollatzResearch.WordTrace tailWord_7475113 prefixEnd_7475113 3838325915672317319710087 := by
  unfold tailWord_7475113
  simp only [CollatzResearch.WordTrace]
  refine ⟨272639769367949723506397993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181759846245299815670931995 272639769367949723506397993)
  ·
    refine ⟨204479827025962292629798495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272639769367949723506397993 204479827025962292629798495)
    ·
      refine ⟨306719740538943438944697743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204479827025962292629798495 306719740538943438944697743)
      ·
        refine ⟨460079610808415158417046615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306719740538943438944697743 460079610808415158417046615)
        ·
          refine ⟨690119416212622737625569923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460079610808415158417046615 690119416212622737625569923)
          ·
            refine ⟨1035179124318934106438354885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690119416212622737625569923 1035179124318934106438354885)
            ·
              refine ⟨194096085809800144957191541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1035179124318934106438354885 194096085809800144957191541)
              ·
                refine ⟨18196508044668763589736707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194096085809800144957191541 18196508044668763589736707)
                ·
                  refine ⟨27294762067003145384605061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18196508044668763589736707 27294762067003145384605061)
                  ·
                    refine ⟨5117767887563089759613449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27294762067003145384605061 5117767887563089759613449)
                    ·
                      refine ⟨3838325915672317319710087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117767887563089759613449 3838325915672317319710087)
                      ·
                        rfl

theorem cell23_7475113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 4, 2].length) (baseStart_7475113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475113 prefixEnd_7475113 := by exact prefixLift 7475113
  have htrace : WordTrace (prefixWord ++ tailWord_7475113) baseStart_7475113 baseEnd_7475113 := by
    simpa [prefixWord, tailWord_7475113, baseEnd_7475113] using wordTrace_append hprefix tailTrace_7475113
  have hstable : (prefixWord ++ tailWord_7475113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475113).length < 2 ^ (prefixWord ++ tailWord_7475113).sum := by decide
  have hdescent : baseEnd_7475113 < baseStart_7475113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475133 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7475133 : Nat := 118140960795 + 7475133 * 2 ^ 59
def prefixEnd_7475133 : Nat := 4983230072969 + 3 ^ 40 * 7475133 * 2
def baseEnd_7475133 : Nat := 3838336185285407241459995

theorem tailTrace_7475133 : CollatzResearch.WordTrace tailWord_7475133 prefixEnd_7475133 3838336185285407241459995 := by
  unfold tailWord_7475133
  simp only [CollatzResearch.WordTrace]
  refine ⟨272640498827877266922126053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181760332551918177948084035 272640498827877266922126053)
  ·
    refine ⟨51120093530226987547898635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272640498827877266922126053 51120093530226987547898635)
    ·
      refine ⟨76680140295340481321847953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51120093530226987547898635 76680140295340481321847953)
      ·
        refine ⟨57510105221505360991385965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76680140295340481321847953 57510105221505360991385965)
        ·
          refine ⟨21566289458064510371769737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57510105221505360991385965 21566289458064510371769737)
          ·
            refine ⟨16174717093548382778827303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21566289458064510371769737 16174717093548382778827303)
            ·
              refine ⟨24262075640322574168240955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16174717093548382778827303 24262075640322574168240955)
              ·
                refine ⟨36393113460483861252361433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24262075640322574168240955 36393113460483861252361433)
                ·
                  refine ⟨27294835095362895939271075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36393113460483861252361433 27294835095362895939271075)
                  ·
                    refine ⟨40942252643044343908906613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27294835095362895939271075 40942252643044343908906613)
                    ·
                      refine ⟨3838336185285407241459995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40942252643044343908906613 3838336185285407241459995)
                      ·
                        rfl

theorem cell23_7475133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7475133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475133 prefixEnd_7475133 := by exact prefixLift 7475133
  have htrace : WordTrace (prefixWord ++ tailWord_7475133) baseStart_7475133 baseEnd_7475133 := by
    simpa [prefixWord, tailWord_7475133, baseEnd_7475133] using wordTrace_append hprefix tailTrace_7475133
  have hstable : (prefixWord ++ tailWord_7475133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475133).length < 2 ^ (prefixWord ++ tailWord_7475133).sum := by decide
  have hdescent : baseEnd_7475133 < baseStart_7475133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475158 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_7475158 : Nat := 118140960795 + 7475158 * 2 ^ 59
def prefixEnd_7475158 : Nat := 4983230072969 + 3 ^ 40 * 7475158 * 2
def baseEnd_7475158 : Nat := 3838349022301769643647381

theorem tailTrace_7475158 : CollatzResearch.WordTrace tailWord_7475158 prefixEnd_7475158 3838349022301769643647381 := by
  unfold tailWord_7475158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17040088165799168511986633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181760940435191130794524085 17040088165799168511986633)
  ·
    refine ⟨12780066124349376383989975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17040088165799168511986633 12780066124349376383989975)
    ·
      refine ⟨19170099186524064575984963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12780066124349376383989975 19170099186524064575984963)
      ·
        refine ⟨28755148779786096863977445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19170099186524064575984963 28755148779786096863977445)
        ·
          refine ⟨5391590396209893161995771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28755148779786096863977445 5391590396209893161995771)
          ·
            refine ⟨8087385594314839742993657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391590396209893161995771 8087385594314839742993657)
            ·
              refine ⟨6065539195736129807245243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8087385594314839742993657 6065539195736129807245243)
              ·
                refine ⟨9098308793604194710867865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065539195736129807245243 9098308793604194710867865)
                ·
                  refine ⟨6823731595203146033150899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9098308793604194710867865 6823731595203146033150899)
                  ·
                    refine ⟨10235597392804719049726349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6823731595203146033150899 10235597392804719049726349)
                    ·
                      refine ⟨3838349022301769643647381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10235597392804719049726349 3838349022301769643647381)
                      ·
                        rfl

theorem cell23_7475158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_7475158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475158 prefixEnd_7475158 := by exact prefixLift 7475158
  have htrace : WordTrace (prefixWord ++ tailWord_7475158) baseStart_7475158 baseEnd_7475158 := by
    simpa [prefixWord, tailWord_7475158, baseEnd_7475158] using wordTrace_append hprefix tailTrace_7475158
  have hstable : (prefixWord ++ tailWord_7475158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475158).length < 2 ^ (prefixWord ++ tailWord_7475158).sum := by decide
  have hdescent : baseEnd_7475158 < baseStart_7475158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475176 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7475176 : Nat := 118140960795 + 7475176 * 2 ^ 59
def prefixEnd_7475176 : Nat := 4983230072969 + 3 ^ 40 * 7475176 * 2
def baseEnd_7475176 : Nat := 3838358264953550573222297

theorem tailTrace_7475176 : CollatzResearch.WordTrace tailWord_7475176 prefixEnd_7475176 3838358264953550573222297 := by
  unfold tailWord_7475176
  simp only [CollatzResearch.WordTrace]
  refine ⟨136321033583360742632970691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181761378111147656843960921 136321033583360742632970691)
  ·
    refine ⟨204481550375041113949456037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136321033583360742632970691 204481550375041113949456037)
    ·
      refine ⟨38340290695320208865523007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204481550375041113949456037 38340290695320208865523007)
      ·
        refine ⟨57510436042980313298284511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38340290695320208865523007 57510436042980313298284511)
        ·
          refine ⟨86265654064470469947426767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57510436042980313298284511 86265654064470469947426767)
          ·
            refine ⟨129398481096705704921140151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86265654064470469947426767 129398481096705704921140151)
            ·
              refine ⟨194097721645058557381710227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129398481096705704921140151 194097721645058557381710227)
              ·
                refine ⟨291146582467587836072565341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194097721645058557381710227 291146582467587836072565341)
                ·
                  refine ⟨109179968425345438527212003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291146582467587836072565341 109179968425345438527212003)
                  ·
                    refine ⟨163769952638018157790818005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109179968425345438527212003 163769952638018157790818005)
                    ·
                      refine ⟨3838358264953550573222297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163769952638018157790818005 3838358264953550573222297)
                      ·
                        rfl

theorem cell23_7475176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7475176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475176 prefixEnd_7475176 := by exact prefixLift 7475176
  have htrace : WordTrace (prefixWord ++ tailWord_7475176) baseStart_7475176 baseEnd_7475176 := by
    simpa [prefixWord, tailWord_7475176, baseEnd_7475176] using wordTrace_append hprefix tailTrace_7475176
  have hstable : (prefixWord ++ tailWord_7475176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475176).length < 2 ^ (prefixWord ++ tailWord_7475176).sum := by decide
  have hdescent : baseEnd_7475176 < baseStart_7475176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475183 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 2, 5]
def baseStart_7475183 : Nat := 118140960795 + 7475183 * 2 ^ 59
def prefixEnd_7475183 : Nat := 4983230072969 + 3 ^ 40 * 7475183 * 2
def baseEnd_7475183 : Nat := 1279453953106044015278255

theorem tailTrace_7475183 : CollatzResearch.WordTrace tailWord_7475183 prefixEnd_7475183 1279453953106044015278255 := by
  unfold tailWord_7475183
  simp only [CollatzResearch.WordTrace]
  refine ⟨272642322477696125461446203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181761548318464083640964135 272642322477696125461446203)
  ·
    refine ⟨408963483716544188192169305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272642322477696125461446203 408963483716544188192169305)
    ·
      refine ⟨306722612787408141144126979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408963483716544188192169305 306722612787408141144126979)
      ·
        refine ⟨460083919181112211716190469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306722612787408141144126979 460083919181112211716190469)
        ·
          refine ⟨86265734846458539696785713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460083919181112211716190469 86265734846458539696785713)
          ·
            refine ⟨64699301134843904772589285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86265734846458539696785713 64699301134843904772589285)
            ·
              refine ⟨12131118962783232144860491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64699301134843904772589285 12131118962783232144860491)
              ·
                refine ⟨18196678444174848217290737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12131118962783232144860491 18196678444174848217290737)
                ·
                  refine ⟨13647508833131136162968053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18196678444174848217290737 13647508833131136162968053)
                  ·
                    refine ⟨1279453953106044015278255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13647508833131136162968053 1279453953106044015278255)
                    ·
                      rfl

theorem cell23_7475183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_7475183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475183 prefixEnd_7475183 := by exact prefixLift 7475183
  have htrace : WordTrace (prefixWord ++ tailWord_7475183) baseStart_7475183 baseEnd_7475183 := by
    simpa [prefixWord, tailWord_7475183, baseEnd_7475183] using wordTrace_append hprefix tailTrace_7475183
  have hstable : (prefixWord ++ tailWord_7475183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475183).length < 2 ^ (prefixWord ++ tailWord_7475183).sum := by decide
  have hdescent : baseEnd_7475183 < baseStart_7475183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475203 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 3, 6, 2]
def baseStart_7475203 : Nat := 118140960795 + 7475203 * 2 ^ 59
def prefixEnd_7475203 : Nat := 4983230072969 + 3 ^ 40 * 7475203 * 2
def baseEnd_7475203 : Nat := 3838372128931221967584673

theorem tailTrace_7475203 : CollatzResearch.WordTrace tailWord_7475203 prefixEnd_7475203 3838372128931221967584673 := by
  unfold tailWord_7475203
  simp only [CollatzResearch.WordTrace]
  refine ⟨272643051937623668877174263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181762034625082445918116175 272643051937623668877174263)
  ·
    refine ⟨408964577906435503315761395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272643051937623668877174263 408964577906435503315761395)
    ·
      refine ⟨613446866859653254973642093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408964577906435503315761395 613446866859653254973642093)
      ·
        refine ⟨230042575072369970615115785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 613446866859653254973642093 230042575072369970615115785)
        ·
          refine ⟨172531931304277477961336839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230042575072369970615115785 172531931304277477961336839)
          ·
            refine ⟨258797896956416216942005259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172531931304277477961336839 258797896956416216942005259)
            ·
              refine ⟨388196845434624325413007889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258797896956416216942005259 388196845434624325413007889)
              ·
                refine ⟨291147634075968244059755917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388196845434624325413007889 291147634075968244059755917)
                ·
                  refine ⟨109180362778488091522408469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291147634075968244059755917 109180362778488091522408469)
                  ·
                    refine ⟨5117829505241629290112897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109180362778488091522408469 5117829505241629290112897)
                    ·
                      refine ⟨3838372128931221967584673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117829505241629290112897 3838372128931221967584673)
                      ·
                        rfl

theorem cell23_7475203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_7475203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475203 prefixEnd_7475203 := by exact prefixLift 7475203
  have htrace : WordTrace (prefixWord ++ tailWord_7475203) baseStart_7475203 baseEnd_7475203 := by
    simpa [prefixWord, tailWord_7475203, baseEnd_7475203] using wordTrace_append hprefix tailTrace_7475203
  have hstable : (prefixWord ++ tailWord_7475203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475203).length < 2 ^ (prefixWord ++ tailWord_7475203).sum := by decide
  have hdescent : baseEnd_7475203 < baseStart_7475203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475216 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_7475216 : Nat := 118140960795 + 7475216 * 2 ^ 59
def prefixEnd_7475216 : Nat := 4983230072969 + 3 ^ 40 * 7475216 * 2
def baseEnd_7475216 : Nat := 3838378804179730416722113

theorem tailTrace_7475216 : CollatzResearch.WordTrace tailWord_7475216 prefixEnd_7475216 3838378804179730416722113 := by
  unfold tailWord_7475216
  simp only [CollatzResearch.WordTrace]
  refine ⟨136321763043288286048698751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181762350724384381398265001 136321763043288286048698751)
  ·
    refine ⟨204482644564932429073048127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136321763043288286048698751 204482644564932429073048127)
    ·
      refine ⟨306723966847398643609572191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204482644564932429073048127 306723966847398643609572191)
      ·
        refine ⟨460085950271097965414358287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306723966847398643609572191 460085950271097965414358287)
        ·
          refine ⟨690128925406646948121537431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460085950271097965414358287 690128925406646948121537431)
          ·
            refine ⟨1035193388109970422182306147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690128925406646948121537431 1035193388109970422182306147)
            ·
              refine ⟨1552790082164955633273459221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035193388109970422182306147 1552790082164955633273459221)
              ·
                refine ⟨72787035101482295309693401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1552790082164955633273459221 72787035101482295309693401)
                ·
                  refine ⟨54590276326111721482270051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72787035101482295309693401 54590276326111721482270051)
                  ·
                    refine ⟨81885414489167582223405077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54590276326111721482270051 81885414489167582223405077)
                    ·
                      refine ⟨3838378804179730416722113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81885414489167582223405077 3838378804179730416722113)
                      ·
                        rfl

theorem cell23_7475216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_7475216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475216 prefixEnd_7475216 := by exact prefixLift 7475216
  have htrace : WordTrace (prefixWord ++ tailWord_7475216) baseStart_7475216 baseEnd_7475216 := by
    simpa [prefixWord, tailWord_7475216, baseEnd_7475216] using wordTrace_append hprefix tailTrace_7475216
  have hstable : (prefixWord ++ tailWord_7475216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475216).length < 2 ^ (prefixWord ++ tailWord_7475216).sum := by decide
  have hdescent : baseEnd_7475216 < baseStart_7475216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475277 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 6]
def baseStart_7475277 : Nat := 118140960795 + 7475277 * 2 ^ 59
def prefixEnd_7475277 : Nat := 4983230072969 + 3 ^ 40 * 7475277 * 2
def baseEnd_7475277 : Nat := 426490014055517186451037

theorem tailTrace_7475277 : CollatzResearch.WordTrace tailWord_7475277 prefixEnd_7475277 426490014055517186451037 := by
  unfold tailWord_7475277
  simp only [CollatzResearch.WordTrace]
  refine ⟨272645750939355579515368085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181763833959570386343578723 272645750939355579515368085)
  ·
    refine ⟨12780269575282292789782879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 272645750939355579515368085 12780269575282292789782879)
    ·
      refine ⟨19170404362923439184674319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12780269575282292789782879 19170404362923439184674319)
      ·
        refine ⟨28755606544385158777011479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19170404362923439184674319 28755606544385158777011479)
        ·
          refine ⟨43133409816577738165517219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28755606544385158777011479 43133409816577738165517219)
          ·
            refine ⟨64700114724866607248275829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43133409816577738165517219 64700114724866607248275829)
            ·
              refine ⟨6065635755456244429525859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64700114724866607248275829 6065635755456244429525859)
              ·
                refine ⟨9098453633184366644288789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065635755456244429525859 9098453633184366644288789)
                ·
                  refine ⟨426490014055517186451037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9098453633184366644288789 426490014055517186451037)
                  ·
                    rfl

theorem cell23_7475277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_7475277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475277 prefixEnd_7475277 := by exact prefixLift 7475277
  have htrace : WordTrace (prefixWord ++ tailWord_7475277) baseStart_7475277 baseEnd_7475277 := by
    simpa [prefixWord, tailWord_7475277, baseEnd_7475277] using wordTrace_append hprefix tailTrace_7475277
  have hstable : (prefixWord ++ tailWord_7475277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475277).length < 2 ^ (prefixWord ++ tailWord_7475277).sum := by decide
  have hdescent : baseEnd_7475277 < baseStart_7475277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475290 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_7475290 : Nat := 118140960795 + 7475290 * 2 ^ 59
def prefixEnd_7475290 : Nat := 4983230072969 + 3 ^ 40 * 7475290 * 2
def baseEnd_7475290 : Nat := 1279472267249387709065591

theorem tailTrace_7475290 : CollatzResearch.WordTrace tailWord_7475290 prefixEnd_7475290 1279472267249387709065591 := by
  unfold tailWord_7475290
  simp only [CollatzResearch.WordTrace]
  refine ⟨68161556272077120683897831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181764150058872321823727549 68161556272077120683897831)
  ·
    refine ⟨102242334408115681025846747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68161556272077120683897831 102242334408115681025846747)
    ·
      refine ⟨153363501612173521538770121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102242334408115681025846747 153363501612173521538770121)
      ·
        refine ⟨115022626209130141154077591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153363501612173521538770121 115022626209130141154077591)
        ·
          refine ⟨172533939313695211731116387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115022626209130141154077591 172533939313695211731116387)
          ·
            refine ⟨258800908970542817596674581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172533939313695211731116387 258800908970542817596674581)
            ·
              refine ⟨12131292607994194574844121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 258800908970542817596674581 12131292607994194574844121)
              ·
                refine ⟨9098469455995645931133091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12131292607994194574844121 9098469455995645931133091)
                ·
                  refine ⟨13647704183993468896699637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9098469455995645931133091 13647704183993468896699637)
                  ·
                    refine ⟨1279472267249387709065591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13647704183993468896699637 1279472267249387709065591)
                    ·
                      rfl

theorem cell23_7475290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_7475290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475290 prefixEnd_7475290 := by exact prefixLift 7475290
  have htrace : WordTrace (prefixWord ++ tailWord_7475290) baseStart_7475290 baseEnd_7475290 := by
    simpa [prefixWord, tailWord_7475290, baseEnd_7475290] using wordTrace_append hprefix tailTrace_7475290
  have hstable : (prefixWord ++ tailWord_7475290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475290).length < 2 ^ (prefixWord ++ tailWord_7475290).sum := by decide
  have hdescent : baseEnd_7475290 < baseStart_7475290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475298 : List Nat := [3, 3, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_7475298 : Nat := 118140960795 + 7475298 * 2 ^ 59
def prefixEnd_7475298 : Nat := 4983230072969 + 3 ^ 40 * 7475298 * 2
def baseEnd_7475298 : Nat := 1279473636531133031965579

theorem tailTrace_7475298 : CollatzResearch.WordTrace tailWord_7475298 prefixEnd_7475298 1279473636531133031965579 := by
  unfold tailWord_7475298
  simp only [CollatzResearch.WordTrace]
  refine ⟨68161629218069875025470637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181764344581519666734588365 68161629218069875025470637)
  ·
    refine ⟨25560610956776203134551489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68161629218069875025470637 25560610956776203134551489)
    ·
      refine ⟨19170458217582152350913617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25560610956776203134551489 19170458217582152350913617)
      ·
        refine ⟨14377843663186614263185213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19170458217582152350913617 14377843663186614263185213)
        ·
          refine ⟨5391691373694980348694455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14377843663186614263185213 5391691373694980348694455)
          ·
            refine ⟨8087537060542470523041683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391691373694980348694455 8087537060542470523041683)
            ·
              refine ⟨12131305590813705784562525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087537060542470523041683 12131305590813705784562525)
              ·
                refine ⟨4549239596555139669210947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12131305590813705784562525 4549239596555139669210947)
                ·
                  refine ⟨6823859394832709503816421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549239596555139669210947 6823859394832709503816421)
                  ·
                    refine ⟨1279473636531133031965579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6823859394832709503816421 1279473636531133031965579)
                    ·
                      rfl

theorem cell23_7475298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_7475298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475298 prefixEnd_7475298 := by exact prefixLift 7475298
  have htrace : WordTrace (prefixWord ++ tailWord_7475298) baseStart_7475298 baseEnd_7475298 := by
    simpa [prefixWord, tailWord_7475298, baseEnd_7475298] using wordTrace_append hprefix tailTrace_7475298
  have hstable : (prefixWord ++ tailWord_7475298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475298).length < 2 ^ (prefixWord ++ tailWord_7475298).sum := by decide
  have hdescent : baseEnd_7475298 < baseStart_7475298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475303 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 3, 6]
def baseStart_7475303 : Nat := 118140960795 + 7475303 * 2 ^ 59
def prefixEnd_7475303 : Nat := 4983230072969 + 3 ^ 40 * 7475303 * 2
def baseEnd_7475303 : Nat := 1279474492332223858778071

theorem tailTrace_7475303 : CollatzResearch.WordTrace tailWord_7475303 prefixEnd_7475303 1279474492332223858778071 := by
  unfold tailWord_7475303
  simp only [CollatzResearch.WordTrace]
  refine ⟨272646699237261385955814563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181764466158174257303876375 272646699237261385955814563)
  ·
    refine ⟨408970048855892078933721845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272646699237261385955814563 408970048855892078933721845)
    ·
      refine ⟨38340942080239882400036423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408970048855892078933721845 38340942080239882400036423)
      ·
        refine ⟨57511413120359823600054635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38340942080239882400036423 57511413120359823600054635)
        ·
          refine ⟨86267119680539735400081953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57511413120359823600054635 86267119680539735400081953)
          ·
            refine ⟨64700339760404801550061465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86267119680539735400081953 64700339760404801550061465)
            ·
              refine ⟨48525254820303601162546099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64700339760404801550061465 48525254820303601162546099)
              ·
                refine ⟨72787882230455401743819149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48525254820303601162546099 72787882230455401743819149)
                ·
                  refine ⟨27295455836420775653932181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72787882230455401743819149 27295455836420775653932181)
                  ·
                    refine ⟨1279474492332223858778071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27295455836420775653932181 1279474492332223858778071)
                    ·
                      rfl

theorem cell23_7475303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_7475303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475303 prefixEnd_7475303 := by exact prefixLift 7475303
  have htrace : WordTrace (prefixWord ++ tailWord_7475303) baseStart_7475303 baseEnd_7475303 := by
    simpa [prefixWord, tailWord_7475303, baseEnd_7475303] using wordTrace_append hprefix tailTrace_7475303
  have hstable : (prefixWord ++ tailWord_7475303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475303).length < 2 ^ (prefixWord ++ tailWord_7475303).sum := by decide
  have hdescent : baseEnd_7475303 < baseStart_7475303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475320 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 2, 4]
def baseStart_7475320 : Nat := 118140960795 + 7475320 * 2 ^ 59
def prefixEnd_7475320 : Nat := 4983230072969 + 3 ^ 40 * 7475320 * 2
def baseEnd_7475320 : Nat := 1279477402055932669940545

theorem tailTrace_7475320 : CollatzResearch.WordTrace tailWord_7475320 prefixEnd_7475320 1279477402055932669940545 := by
  unfold tailWord_7475320
  simp only [CollatzResearch.WordTrace]
  refine ⟨136323659639099898929591707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181764879518799865239455609 136323659639099898929591707)
  ·
    refine ⟨204485489458649848394387561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136323659639099898929591707 204485489458649848394387561)
    ·
      refine ⟨153364117093987386295790671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204485489458649848394387561 153364117093987386295790671)
      ·
        refine ⟨230046175640981079443686007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153364117093987386295790671 230046175640981079443686007)
        ·
          refine ⟨345069263461471619165529011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230046175640981079443686007 345069263461471619165529011)
          ·
            refine ⟨517603895192207428748293517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345069263461471619165529011 517603895192207428748293517)
            ·
              refine ⟨194101460697077785780610069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517603895192207428748293517 194101460697077785780610069)
              ·
                refine ⟨9098505970175521208466097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194101460697077785780610069 9098505970175521208466097)
                ·
                  refine ⟨6823879477631640906349573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9098505970175521208466097 6823879477631640906349573)
                  ·
                    refine ⟨1279477402055932669940545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6823879477631640906349573 1279477402055932669940545)
                    ·
                      rfl

theorem cell23_7475320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_7475320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475320 prefixEnd_7475320 := by exact prefixLift 7475320
  have htrace : WordTrace (prefixWord ++ tailWord_7475320) baseStart_7475320 baseEnd_7475320 := by
    simpa [prefixWord, tailWord_7475320, baseEnd_7475320] using wordTrace_append hprefix tailTrace_7475320
  have hstable : (prefixWord ++ tailWord_7475320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475320).length < 2 ^ (prefixWord ++ tailWord_7475320).sum := by decide
  have hdescent : baseEnd_7475320 < baseStart_7475320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475321 : List Nat := [1, 2, 1, 3, 4, 2, 3, 2, 1, 1, 3]
def baseStart_7475321 : Nat := 118140960795 + 7475321 * 2 ^ 59
def prefixEnd_7475321 : Nat := 4983230072969 + 3 ^ 40 * 7475321 * 2
def baseEnd_7475321 : Nat := 3838432719648452505909131

theorem tailTrace_7475321 : CollatzResearch.WordTrace tailWord_7475321 prefixEnd_7475321 3838432719648452505909131 := by
  unfold tailWord_7475321
  simp only [CollatzResearch.WordTrace]
  refine ⟨272647355751196175029969817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181764903834130783353313211 272647355751196175029969817)
  ·
    refine ⟨204485516813397131272477363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272647355751196175029969817 204485516813397131272477363)
    ·
      refine ⟨306728275220095696908716045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204485516813397131272477363 306728275220095696908716045)
      ·
        refine ⟨115023103207535886340768517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306728275220095696908716045 115023103207535886340768517)
        ·
          refine ⟨21566831851412978688894097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115023103207535886340768517 21566831851412978688894097)
          ·
            refine ⟨16175123888559734016670573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21566831851412978688894097 16175123888559734016670573)
            ·
              refine ⟨6065671458209900256251465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16175123888559734016670573 6065671458209900256251465)
              ·
                refine ⟨4549253593657425192188599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6065671458209900256251465 4549253593657425192188599)
                ·
                  refine ⟨6823880390486137788282899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549253593657425192188599 6823880390486137788282899)
                  ·
                    refine ⟨10235820585729206682424349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6823880390486137788282899 10235820585729206682424349)
                    ·
                      refine ⟨3838432719648452505909131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10235820585729206682424349 3838432719648452505909131)
                      ·
                        rfl

theorem cell23_7475321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_7475321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475321 prefixEnd_7475321 := by exact prefixLift 7475321
  have htrace : WordTrace (prefixWord ++ tailWord_7475321) baseStart_7475321 baseEnd_7475321 := by
    simpa [prefixWord, tailWord_7475321, baseEnd_7475321] using wordTrace_append hprefix tailTrace_7475321
  have hstable : (prefixWord ++ tailWord_7475321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475321).length < 2 ^ (prefixWord ++ tailWord_7475321).sum := by decide
  have hdescent : baseEnd_7475321 < baseStart_7475321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475333 : List Nat := [1, 3, 1, 1, 5, 1, 1, 10]
def baseStart_7475333 : Nat := 118140960795 + 7475333 * 2 ^ 59
def prefixEnd_7475333 : Nat := 4983230072969 + 3 ^ 40 * 7475333 * 2
def baseEnd_7475333 : Nat := 142164403015418757739225

theorem tailTrace_7475333 : CollatzResearch.WordTrace tailWord_7475333 prefixEnd_7475333 142164403015418757739225 := by
  unfold tailWord_7475333
  simp only [CollatzResearch.WordTrace]
  refine ⟨272647793427152701079406653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181765195618101800719604435 272647793427152701079406653)
  ·
    refine ⟨102242922535182262904777495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272647793427152701079406653 102242922535182262904777495)
    ·
      refine ⟨153364383802773394357166243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102242922535182262904777495 153364383802773394357166243)
      ·
        refine ⟨230046575704160091535749365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153364383802773394357166243 230046575704160091535749365)
        ·
          refine ⟨21566866472265008581476503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230046575704160091535749365 21566866472265008581476503)
          ·
            refine ⟨32350299708397512872214755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21566866472265008581476503 32350299708397512872214755)
            ·
              refine ⟨48525449562596269308322133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32350299708397512872214755 48525449562596269308322133)
              ·
                refine ⟨142164403015418757739225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48525449562596269308322133 142164403015418757739225)
                ·
                  rfl

theorem cell23_7475333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 10].length) (baseStart_7475333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475333 prefixEnd_7475333 := by exact prefixLift 7475333
  have htrace : WordTrace (prefixWord ++ tailWord_7475333) baseStart_7475333 baseEnd_7475333 := by
    simpa [prefixWord, tailWord_7475333, baseEnd_7475333] using wordTrace_append hprefix tailTrace_7475333
  have hstable : (prefixWord ++ tailWord_7475333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475333).length < 2 ^ (prefixWord ++ tailWord_7475333).sum := by decide
  have hdescent : baseEnd_7475333 < baseStart_7475333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475343 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 3]
def baseStart_7475343 : Nat := 118140960795 + 7475343 * 2 ^ 59
def prefixEnd_7475343 : Nat := 4983230072969 + 3 ^ 40 * 7475343 * 2
def baseEnd_7475343 : Nat := 3838444016222851419834029

theorem tailTrace_7475343 : CollatzResearch.WordTrace tailWord_7475343 prefixEnd_7475343 3838444016222851419834029 := by
  unfold tailWord_7475343
  simp only [CollatzResearch.WordTrace]
  refine ⟨272648158157116472787270683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181765438771410981858180455 272648158157116472787270683)
  ·
    refine ⟨408972237235674709180906025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272648158157116472787270683 408972237235674709180906025)
    ·
      refine ⟨306729177926756031885679519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408972237235674709180906025 306729177926756031885679519)
      ·
        refine ⟨460093766890134047828519279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306729177926756031885679519 460093766890134047828519279)
        ·
          refine ⟨690140650335201071742778919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460093766890134047828519279 690140650335201071742778919)
          ·
            refine ⟨1035210975502801607614168379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690140650335201071742778919 1035210975502801607614168379)
            ·
              refine ⟨1552816463254202411421252569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035210975502801607614168379 1552816463254202411421252569)
              ·
                refine ⟨1164612347440651808565939427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552816463254202411421252569 1164612347440651808565939427)
                ·
                  refine ⟨1746918521160977712848909141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164612347440651808565939427 1746918521160977712848909141)
                  ·
                    refine ⟨10235850709927603786224077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1746918521160977712848909141 10235850709927603786224077)
                    ·
                      refine ⟨3838444016222851419834029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10235850709927603786224077 3838444016222851419834029)
                      ·
                        rfl

theorem cell23_7475343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_7475343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475343 prefixEnd_7475343 := by exact prefixLift 7475343
  have htrace : WordTrace (prefixWord ++ tailWord_7475343) baseStart_7475343 baseEnd_7475343 := by
    simpa [prefixWord, tailWord_7475343, baseEnd_7475343] using wordTrace_append hprefix tailTrace_7475343
  have hstable : (prefixWord ++ tailWord_7475343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475343).length < 2 ^ (prefixWord ++ tailWord_7475343).sum := by decide
  have hdescent : baseEnd_7475343 < baseStart_7475343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475360 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3]
def baseStart_7475360 : Nat := 118140960795 + 7475360 * 2 ^ 59
def prefixEnd_7475360 : Nat := 4983230072969 + 3 ^ 40 * 7475360 * 2
def baseEnd_7475360 : Nat := 3838452745393977853321451

theorem tailTrace_7475360 : CollatzResearch.WordTrace tailWord_7475360 prefixEnd_7475360 3838452745393977853321451 := by
  unfold tailWord_7475360
  simp only [CollatzResearch.WordTrace]
  refine ⟨136324389099027442345319767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181765852132036589793759689 136324389099027442345319767)
  ·
    refine ⟨204486583648541163517979651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136324389099027442345319767 204486583648541163517979651)
    ·
      refine ⟨306729875472811745276969477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204486583648541163517979651 306729875472811745276969477)
      ·
        refine ⟨57511851651152202239431777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306729875472811745276969477 57511851651152202239431777)
        ·
          refine ⟨43133888738364151679573833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57511851651152202239431777 43133888738364151679573833)
          ·
            refine ⟨32350416553773113759680375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43133888738364151679573833 32350416553773113759680375)
            ·
              refine ⟨48525624830659670639520563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32350416553773113759680375 48525624830659670639520563)
              ·
                refine ⟨72788437245989505959280845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48525624830659670639520563 72788437245989505959280845)
                ·
                  refine ⟨27295663967246064734730317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72788437245989505959280845 27295663967246064734730317)
                  ·
                    refine ⟨10235873987717274275523869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27295663967246064734730317 10235873987717274275523869)
                    ·
                      refine ⟨3838452745393977853321451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10235873987717274275523869 3838452745393977853321451)
                      ·
                        rfl

theorem cell23_7475360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_7475360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475360 prefixEnd_7475360 := by exact prefixLift 7475360
  have htrace : WordTrace (prefixWord ++ tailWord_7475360) baseStart_7475360 baseEnd_7475360 := by
    simpa [prefixWord, tailWord_7475360, baseEnd_7475360] using wordTrace_append hprefix tailTrace_7475360
  have hstable : (prefixWord ++ tailWord_7475360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475360).length < 2 ^ (prefixWord ++ tailWord_7475360).sum := by decide
  have hdescent : baseEnd_7475360 < baseStart_7475360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475364 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_7475364 : Nat := 118140960795 + 7475364 * 2 ^ 59
def prefixEnd_7475364 : Nat := 4983230072969 + 3 ^ 40 * 7475364 * 2
def baseEnd_7475364 : Nat := 3838454799316595837671433

theorem tailTrace_7475364 : CollatzResearch.WordTrace tailWord_7475364 prefixEnd_7475364 3838454799316595837671433 := by
  unfold tailWord_7475364
  simp only [CollatzResearch.WordTrace]
  refine ⟨136324462045020196686892573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181765949393360262249190097 136324462045020196686892573)
  ·
    refine ⟨51121673266882573757584715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136324462045020196686892573 51121673266882573757584715)
    ·
      refine ⟨76682509900323860636377073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51121673266882573757584715 76682509900323860636377073)
      ·
        refine ⟨57511882425242895477282805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76682509900323860636377073 57511882425242895477282805)
        ·
          refine ⟨5391738977366521450995263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57511882425242895477282805 5391738977366521450995263)
          ·
            refine ⟨8087608466049782176492895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391738977366521450995263 8087608466049782176492895)
            ·
              refine ⟨12131412699074673264739343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087608466049782176492895 12131412699074673264739343)
              ·
                refine ⟨18197119048612009897109015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12131412699074673264739343 18197119048612009897109015)
                ·
                  refine ⟨27295678572918014845663523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18197119048612009897109015 27295678572918014845663523)
                  ·
                    refine ⟨40943517859377022268495285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27295678572918014845663523 40943517859377022268495285)
                    ·
                      refine ⟨3838454799316595837671433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40943517859377022268495285 3838454799316595837671433)
                      ·
                        rfl

theorem cell23_7475364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_7475364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475364 prefixEnd_7475364 := by exact prefixLift 7475364
  have htrace : WordTrace (prefixWord ++ tailWord_7475364) baseStart_7475364 baseEnd_7475364 := by
    simpa [prefixWord, tailWord_7475364, baseEnd_7475364] using wordTrace_append hprefix tailTrace_7475364
  have hstable : (prefixWord ++ tailWord_7475364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475364).length < 2 ^ (prefixWord ++ tailWord_7475364).sum := by decide
  have hdescent : baseEnd_7475364 < baseStart_7475364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475417 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 1, 4, 2]
def baseStart_7475417 : Nat := 118140960795 + 7475417 * 2 ^ 59
def prefixEnd_7475417 : Nat := 4983230072969 + 3 ^ 40 * 7475417 * 2
def baseEnd_7475417 : Nat := 3838482013791284130308689

theorem tailTrace_7475417 : CollatzResearch.WordTrace tailWord_7475417 prefixEnd_7475417 3838482013791284130308689 := by
  unfold tailWord_7475417
  simp only [CollatzResearch.WordTrace]
  refine ⟨272650857158848383425464505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181767238105898922283643003 272650857158848383425464505)
  ·
    refine ⟨204488142869136287569098379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272650857158848383425464505 204488142869136287569098379)
    ·
      refine ⟨306732214303704431353647569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204488142869136287569098379 306732214303704431353647569)
      ·
        refine ⟨230049160727778323515235677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306732214303704431353647569 230049160727778323515235677)
        ·
          refine ⟨86268435272916871318213379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230049160727778323515235677 86268435272916871318213379)
          ·
            refine ⟨129402652909375306977320069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86268435272916871318213379 129402652909375306977320069)
            ·
              refine ⟨24262997420507870058247513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129402652909375306977320069 24262997420507870058247513)
              ·
                refine ⟨18197248065380902543685635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24262997420507870058247513 18197248065380902543685635)
                ·
                  refine ⟨27295872098071353815528453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18197248065380902543685635 27295872098071353815528453)
                  ·
                    refine ⟨5117976018388378840411585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27295872098071353815528453 5117976018388378840411585)
                    ·
                      refine ⟨3838482013791284130308689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117976018388378840411585 3838482013791284130308689)
                      ·
                        rfl

theorem cell23_7475417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_7475417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475417 prefixEnd_7475417 := by exact prefixLift 7475417
  have htrace : WordTrace (prefixWord ++ tailWord_7475417) baseStart_7475417 baseEnd_7475417 := by
    simpa [prefixWord, tailWord_7475417, baseEnd_7475417] using wordTrace_append hprefix tailTrace_7475417
  have hstable : (prefixWord ++ tailWord_7475417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475417).length < 2 ^ (prefixWord ++ tailWord_7475417).sum := by decide
  have hdescent : baseEnd_7475417 < baseStart_7475417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475421 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7475421 : Nat := 118140960795 + 7475421 * 2 ^ 59
def prefixEnd_7475421 : Nat := 4983230072969 + 3 ^ 40 * 7475421 * 2
def baseEnd_7475421 : Nat := 3838484067713902114658671

theorem tailTrace_7475421 : CollatzResearch.WordTrace tailWord_7475421 prefixEnd_7475421 3838484067713902114658671 := by
  unfold tailWord_7475421
  simp only [CollatzResearch.WordTrace]
  refine ⟨272651003050833892108610117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181767335367222594739073411 272651003050833892108610117)
  ·
    refine ⟨51122063072031354770364397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272651003050833892108610117 51122063072031354770364397)
    ·
      refine ⟨19170773652011758038886649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51122063072031354770364397 19170773652011758038886649)
      ·
        refine ⟨14378080239008818529164987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19170773652011758038886649 14378080239008818529164987)
        ·
          refine ⟨21567120358513227793747481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14378080239008818529164987 21567120358513227793747481)
          ·
            refine ⟨16175340268884920845310611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21567120358513227793747481 16175340268884920845310611)
            ·
              refine ⟨24263010403327381267965917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16175340268884920845310611 24263010403327381267965917)
              ·
                refine ⟨9098628901247767975487219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24263010403327381267965917 9098628901247767975487219)
                ·
                  refine ⟨13647943351871651963230829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9098628901247767975487219 13647943351871651963230829)
                  ·
                    refine ⟨5117978756951869486211561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13647943351871651963230829 5117978756951869486211561)
                    ·
                      refine ⟨3838484067713902114658671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117978756951869486211561 3838484067713902114658671)
                      ·
                        rfl

theorem cell23_7475421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7475421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475421 prefixEnd_7475421 := by exact prefixLift 7475421
  have htrace : WordTrace (prefixWord ++ tailWord_7475421) baseStart_7475421 baseEnd_7475421 := by
    simpa [prefixWord, tailWord_7475421, baseEnd_7475421] using wordTrace_append hprefix tailTrace_7475421
  have hstable : (prefixWord ++ tailWord_7475421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475421).length < 2 ^ (prefixWord ++ tailWord_7475421).sum := by decide
  have hdescent : baseEnd_7475421 < baseStart_7475421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475423 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 11]
def baseStart_7475423 : Nat := 118140960795 + 7475423 * 2 ^ 59
def prefixEnd_7475423 : Nat := 4983230072969 + 3 ^ 40 * 7475423 * 2
def baseEnd_7475423 : Nat := 426498343852801234092629

theorem tailTrace_7475423 : CollatzResearch.WordTrace tailWord_7475423 prefixEnd_7475423 426498343852801234092629 := by
  unfold tailWord_7475423
  simp only [CollatzResearch.WordTrace]
  refine ⟨272651075996826646450182923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181767383997884430966788615 272651075996826646450182923)
  ·
    refine ⟨408976613995239969675274385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272651075996826646450182923 408976613995239969675274385)
    ·
      refine ⟨306732460496429977256455789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408976613995239969675274385 306732460496429977256455789)
      ·
        refine ⟨115024672686161241471170921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306732460496429977256455789 115024672686161241471170921)
        ·
          refine ⟨86268504514620931103378191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115024672686161241471170921 86268504514620931103378191)
          ·
            refine ⟨129402756771931396655067287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86268504514620931103378191 129402756771931396655067287)
            ·
              refine ⟨194104135157897094982600931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129402756771931396655067287 194104135157897094982600931)
              ·
                refine ⟨291156202736845642473901397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194104135157897094982600931 291156202736845642473901397)
                ·
                  refine ⟨426498343852801234092629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 291156202736845642473901397 426498343852801234092629)
                  ·
                    rfl

theorem cell23_7475423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 11].length) (baseStart_7475423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475423 prefixEnd_7475423 := by exact prefixLift 7475423
  have htrace : WordTrace (prefixWord ++ tailWord_7475423) baseStart_7475423 baseEnd_7475423 := by
    simpa [prefixWord, tailWord_7475423, baseEnd_7475423] using wordTrace_append hprefix tailTrace_7475423
  have hstable : (prefixWord ++ tailWord_7475423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475423).length < 2 ^ (prefixWord ++ tailWord_7475423).sum := by decide
  have hdescent : baseEnd_7475423 < baseStart_7475423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475433 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_7475433 : Nat := 118140960795 + 7475433 * 2 ^ 59
def prefixEnd_7475433 : Nat := 4983230072969 + 3 ^ 40 * 7475433 * 2
def baseEnd_7475433 : Nat := 3838490229481756067708615

theorem tailTrace_7475433 : CollatzResearch.WordTrace tailWord_7475433 prefixEnd_7475433 3838490229481756067708615 := by
  unfold tailWord_7475433
  simp only [CollatzResearch.WordTrace]
  refine ⟨272651440726790418158046953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181767627151193612105364635 272651440726790418158046953)
  ·
    refine ⟨204488580545092813618535215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272651440726790418158046953 204488580545092813618535215)
    ·
      refine ⟨306732870817639220427802823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204488580545092813618535215 306732870817639220427802823)
      ·
        refine ⟨460099306226458830641704235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306732870817639220427802823 460099306226458830641704235)
        ·
          refine ⟨690148959339688245962556353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460099306226458830641704235 690148959339688245962556353)
          ·
            refine ⟨517611719504766184471917265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690148959339688245962556353 517611719504766184471917265)
            ·
              refine ⟨388208789628574638353937949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517611719504766184471917265 388208789628574638353937949)
              ·
                refine ⟨145578296110715489382726731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388208789628574638353937949 145578296110715489382726731)
                ·
                  refine ⟨218367444166073234074090097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145578296110715489382726731 218367444166073234074090097)
                  ·
                    refine ⟨163775583124554925555567573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218367444166073234074090097 163775583124554925555567573)
                    ·
                      refine ⟨3838490229481756067708615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163775583124554925555567573 3838490229481756067708615)
                      ·
                        rfl

theorem cell23_7475433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_7475433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475433 prefixEnd_7475433 := by exact prefixLift 7475433
  have htrace : WordTrace (prefixWord ++ tailWord_7475433) baseStart_7475433 baseEnd_7475433 := by
    simpa [prefixWord, tailWord_7475433, baseEnd_7475433] using wordTrace_append hprefix tailTrace_7475433
  have hstable : (prefixWord ++ tailWord_7475433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475433).length < 2 ^ (prefixWord ++ tailWord_7475433).sum := by decide
  have hdescent : baseEnd_7475433 < baseStart_7475433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475434 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_7475434 : Nat := 118140960795 + 7475434 * 2 ^ 59
def prefixEnd_7475434 : Nat := 4983230072969 + 3 ^ 40 * 7475434 * 2
def baseEnd_7475434 : Nat := 3838490742962410563796111

theorem tailTrace_7475434 : CollatzResearch.WordTrace tailWord_7475434 prefixEnd_7475434 3838490742962410563796111 := by
  unfold tailWord_7475434
  simp only [CollatzResearch.WordTrace]
  refine ⟨68162869299946698832208339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181767651466524530219222237 68162869299946698832208339)
  ·
    refine ⟨102244303949920048248312509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68162869299946698832208339 102244303949920048248312509)
    ·
      refine ⟨38341613981220018093117191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102244303949920048248312509 38341613981220018093117191)
      ·
        refine ⟨57512420971830027139675787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38341613981220018093117191 57512420971830027139675787)
        ·
          refine ⟨86268631457745040709513681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57512420971830027139675787 86268631457745040709513681)
          ·
            refine ⟨64701473593308780532135261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86268631457745040709513681 64701473593308780532135261)
            ·
              refine ⟨24263052597490792699550723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64701473593308780532135261 24263052597490792699550723)
              ·
                refine ⟨36394578896236189049326085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24263052597490792699550723 36394578896236189049326085)
                ·
                  refine ⟨6823983543044285446748641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36394578896236189049326085 6823983543044285446748641)
                  ·
                    refine ⟨5117987657283214085061481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6823983543044285446748641 5117987657283214085061481)
                    ·
                      refine ⟨3838490742962410563796111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5117987657283214085061481 3838490742962410563796111)
                      ·
                        rfl

theorem cell23_7475434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_7475434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475434 prefixEnd_7475434 := by exact prefixLift 7475434
  have htrace : WordTrace (prefixWord ++ tailWord_7475434) baseStart_7475434 baseEnd_7475434 := by
    simpa [prefixWord, tailWord_7475434, baseEnd_7475434] using wordTrace_append hprefix tailTrace_7475434
  have hstable : (prefixWord ++ tailWord_7475434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475434).length < 2 ^ (prefixWord ++ tailWord_7475434).sum := by decide
  have hdescent : baseEnd_7475434 < baseStart_7475434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475470 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_7475470 : Nat := 118140960795 + 7475470 * 2 ^ 59
def prefixEnd_7475470 : Nat := 4983230072969 + 3 ^ 40 * 7475470 * 2
def baseEnd_7475470 : Nat := 1279503076088657474315315

theorem tailTrace_7475470 : CollatzResearch.WordTrace tailWord_7475470 prefixEnd_7475470 1279503076088657474315315 := by
  unfold tailWord_7475470
  simp only [CollatzResearch.WordTrace]
  refine ⟨34081598778457046684642983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181768526818437582318095909 34081598778457046684642983)
  ·
    refine ⟨51122398167685570026964475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34081598778457046684642983 51122398167685570026964475)
    ·
      refine ⟨76683597251528355040446713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51122398167685570026964475 76683597251528355040446713)
      ·
        refine ⟨57512697938646266280335035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76683597251528355040446713 57512697938646266280335035)
        ·
          refine ⟨86269046907969399420502553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57512697938646266280335035 86269046907969399420502553)
          ·
            refine ⟨64701785180977049565376915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86269046907969399420502553 64701785180977049565376915)
            ·
              refine ⟨97052677771465574348065373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64701785180977049565376915 97052677771465574348065373)
              ·
                refine ⟨36394754164299590380524515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97052677771465574348065373 36394754164299590380524515)
                ·
                  refine ⟨54592131246449385570786773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36394754164299590380524515 54592131246449385570786773)
                  ·
                    refine ⟨1279503076088657474315315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54592131246449385570786773 1279503076088657474315315)
                    ·
                      rfl

theorem cell23_7475470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_7475470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475470 prefixEnd_7475470 := by exact prefixLift 7475470
  have htrace : WordTrace (prefixWord ++ tailWord_7475470) baseStart_7475470 baseEnd_7475470 := by
    simpa [prefixWord, tailWord_7475470, baseEnd_7475470] using wordTrace_append hprefix tailTrace_7475470
  have hstable : (prefixWord ++ tailWord_7475470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475470).length < 2 ^ (prefixWord ++ tailWord_7475470).sum := by decide
  have hdescent : baseEnd_7475470 < baseStart_7475470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7475480 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_7475480 : Nat := 118140960795 + 7475480 * 2 ^ 59
def prefixEnd_7475480 : Nat := 4983230072969 + 3 ^ 40 * 7475480 * 2
def baseEnd_7475480 : Nat := 3838514363072517383820899

theorem tailTrace_7475480 : CollatzResearch.WordTrace tailWord_7475480 prefixEnd_7475480 3838514363072517383820899 := by
  unfold tailWord_7475480
  simp only [CollatzResearch.WordTrace]
  refine ⟨136326577478810072592503947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181768769971746763456671929 136326577478810072592503947)
  ·
    refine ⟨204489866218215108888755921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136326577478810072592503947 204489866218215108888755921)
    ·
      refine ⟨153367399663661331666566941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204489866218215108888755921 153367399663661331666566941)
      ·
        refine ⟨57512774873872999374962603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153367399663661331666566941 57512774873872999374962603)
        ·
          refine ⟨86269162310809499062443905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57512774873872999374962603 86269162310809499062443905)
          ·
            refine ⟨64701871733107124296832929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86269162310809499062443905 64701871733107124296832929)
            ·
              refine ⟨48526403799830343222624697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64701871733107124296832929 48526403799830343222624697)
              ·
                refine ⟨36394802849872757416968523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48526403799830343222624697 36394802849872757416968523)
                ·
                  refine ⟨54592204274809136125452785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36394802849872757416968523 54592204274809136125452785)
                  ·
                    refine ⟨40944153206106852094089589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54592204274809136125452785 40944153206106852094089589)
                    ·
                      refine ⟨3838514363072517383820899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40944153206106852094089589 3838514363072517383820899)
                      ·
                        rfl

theorem cell23_7475480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_7475480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7475480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7475480 prefixEnd_7475480 := by exact prefixLift 7475480
  have htrace : WordTrace (prefixWord ++ tailWord_7475480) baseStart_7475480 baseEnd_7475480 := by
    simpa [prefixWord, tailWord_7475480, baseEnd_7475480] using wordTrace_append hprefix tailTrace_7475480
  have hstable : (prefixWord ++ tailWord_7475480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7475480).length < 2 ^ (prefixWord ++ tailWord_7475480).sum := by decide
  have hdescent : baseEnd_7475480 < baseStart_7475480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7475480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
