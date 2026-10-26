import V185TrunkScan23Chunk0307

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1821932 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_1821932 : Nat := 118140960795 + 1821932 * 2 ^ 59
def prefixEnd_1821932 : Nat := 4983230072969 + 3 ^ 40 * 1821932 * 2
def baseEnd_1821932 : Nat := 311842278602490305457031

theorem tailTrace_1821932 : CollatzResearch.WordTrace tailWord_1821932 prefixEnd_1821932 311842278602490305457031 := by
  unfold tailWord_1821932
  simp only [CollatzResearch.WordTrace]
  refine ⟨33225659617729500028950025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44300879490306000038600033 33225659617729500028950025)
  ·
    refine ⟨24919244713297125021712519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33225659617729500028950025 24919244713297125021712519)
    ·
      refine ⟨37378867069945687532568779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24919244713297125021712519 37378867069945687532568779)
      ·
        refine ⟨56068300604918531298853169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37378867069945687532568779 56068300604918531298853169)
        ·
          refine ⟨42051225453688898474139877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56068300604918531298853169 42051225453688898474139877)
          ·
            refine ⟨7884604772566668463901227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42051225453688898474139877 7884604772566668463901227)
            ·
              refine ⟨11826907158850002695851841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884604772566668463901227 11826907158850002695851841)
              ·
                refine ⟨8870180369137502021888881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11826907158850002695851841 8870180369137502021888881)
                ·
                  refine ⟨6652635276853126516416661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8870180369137502021888881 6652635276853126516416661)
                  ·
                    refine ⟨311842278602490305457031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6652635276853126516416661 311842278602490305457031)
                    ·
                      rfl

theorem cell23_1821932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_1821932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821932 prefixEnd_1821932 := by exact prefixLift 1821932
  have htrace : WordTrace (prefixWord ++ tailWord_1821932) baseStart_1821932 baseEnd_1821932 := by
    simpa [prefixWord, tailWord_1821932, baseEnd_1821932] using wordTrace_append hprefix tailTrace_1821932
  have hstable : (prefixWord ++ tailWord_1821932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821932).length < 2 ^ (prefixWord ++ tailWord_1821932).sum := by decide
  have hdescent : baseEnd_1821932 < baseStart_1821932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821933 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1821933 : Nat := 118140960795 + 1821933 * 2 ^ 59
def prefixEnd_1821933 : Nat := 4983230072969 + 3 ^ 40 * 1821933 * 2
def baseEnd_1821933 : Nat := 935527349288125412458589

theorem tailTrace_1821933 : CollatzResearch.WordTrace tailWord_1821933 prefixEnd_1821933 935527349288125412458589 := by
  unfold tailWord_1821933
  simp only [CollatzResearch.WordTrace]
  refine ⟨66451355708455377228686453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44300903805636918152457635 66451355708455377228686453)
  ·
    refine ⟨6229814597667691615189355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66451355708455377228686453 6229814597667691615189355)
    ·
      refine ⟨9344721896501537422784033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6229814597667691615189355 9344721896501537422784033)
      ·
        refine ⟨7008541422376153067088025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9344721896501537422784033 7008541422376153067088025)
        ·
          refine ⟨5256406066782114800316019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7008541422376153067088025 5256406066782114800316019)
          ·
            refine ⟨7884609100173172200474029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256406066782114800316019 7884609100173172200474029)
            ·
              refine ⟨2956728412564939575177761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7884609100173172200474029 2956728412564939575177761)
              ·
                refine ⟨2217546309423704681383321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956728412564939575177761 2217546309423704681383321)
                ·
                  refine ⟨1663159732067778511037491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2217546309423704681383321 1663159732067778511037491)
                  ·
                    refine ⟨2494739598101667766556237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1663159732067778511037491 2494739598101667766556237)
                    ·
                      refine ⟨935527349288125412458589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2494739598101667766556237 935527349288125412458589)
                      ·
                        rfl

theorem cell23_1821933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1821933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821933 prefixEnd_1821933 := by exact prefixLift 1821933
  have htrace : WordTrace (prefixWord ++ tailWord_1821933) baseStart_1821933 baseEnd_1821933 := by
    simpa [prefixWord, tailWord_1821933, baseEnd_1821933] using wordTrace_append hprefix tailTrace_1821933
  have hstable : (prefixWord ++ tailWord_1821933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821933).length < 2 ^ (prefixWord ++ tailWord_1821933).sum := by decide
  have hdescent : baseEnd_1821933 < baseStart_1821933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821950 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1821950 : Nat := 118140960795 + 1821950 * 2 ^ 59
def prefixEnd_1821950 : Nat := 4983230072969 + 3 ^ 40 * 1821950 * 2
def baseEnd_1821950 : Nat := 935536078459251845946011

theorem tailTrace_1821950 : CollatzResearch.WordTrace tailWord_1821950 prefixEnd_1821950 935536078459251845946011 := by
  unfold tailWord_1821950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306496968674223641506913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44301317166262526088036869 8306496968674223641506913)
  ·
    refine ⟨6229872726505667731130185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8306496968674223641506913 6229872726505667731130185)
    ·
      refine ⟨4672404544879250798347639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6229872726505667731130185 4672404544879250798347639)
      ·
        refine ⟨7008606817318876197521459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672404544879250798347639 7008606817318876197521459)
        ·
          refine ⟨10512910225978314296282189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008606817318876197521459 10512910225978314296282189)
          ·
            refine ⟨3942341334741867861105821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10512910225978314296282189 3942341334741867861105821)
            ·
              refine ⟨1478378000528200447914683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3942341334741867861105821 1478378000528200447914683)
              ·
                refine ⟨2217567000792300671872025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478378000528200447914683 2217567000792300671872025)
                ·
                  refine ⟨1663175250594225503904019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2217567000792300671872025 1663175250594225503904019)
                  ·
                    refine ⟨2494762875891338255856029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1663175250594225503904019 2494762875891338255856029)
                    ·
                      refine ⟨935536078459251845946011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2494762875891338255856029 935536078459251845946011)
                      ·
                        rfl

theorem cell23_1821950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1821950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821950 prefixEnd_1821950 := by exact prefixLift 1821950
  have htrace : WordTrace (prefixWord ++ tailWord_1821950) baseStart_1821950 baseEnd_1821950 := by
    simpa [prefixWord, tailWord_1821950, baseEnd_1821950] using wordTrace_append hprefix tailTrace_1821950
  have hstable : (prefixWord ++ tailWord_1821950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821950).length < 2 ^ (prefixWord ++ tailWord_1821950).sum := by decide
  have hdescent : baseEnd_1821950 < baseStart_1821950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821999 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 2, 5, 2]
def baseStart_1821999 : Nat := 118140960795 + 1821999 * 2 ^ 59
def prefixEnd_1821999 : Nat := 4983230072969 + 3 ^ 40 * 1821999 * 2
def baseEnd_1821999 : Nat := 935561239011322154233285

theorem tailTrace_1821999 : CollatzResearch.WordTrace tailWord_1821999 prefixEnd_1821999 935561239011322154233285 := by
  unfold tailWord_1821999
  simp only [CollatzResearch.WordTrace]
  refine ⟨66453762926216270500589051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44302508617477513667059367 66453762926216270500589051)
  ·
    refine ⟨99680644389324405750883577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66453762926216270500589051 99680644389324405750883577)
    ·
      refine ⟨74760483291993304313162683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99680644389324405750883577 74760483291993304313162683)
      ·
        refine ⟨112140724937989956469744025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74760483291993304313162683 112140724937989956469744025)
        ·
          refine ⟨84105543703492467352308019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112140724937989956469744025 84105543703492467352308019)
          ·
            refine ⟨126158315555238701028462029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84105543703492467352308019 126158315555238701028462029)
            ·
              refine ⟨47309368333214512885673261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126158315555238701028462029 47309368333214512885673261)
              ·
                refine ⟨17741013124955442332127473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47309368333214512885673261 17741013124955442332127473)
                ·
                  refine ⟨13305759843716581749095605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17741013124955442332127473 13305759843716581749095605)
                  ·
                    refine ⟨1247414985348429538977713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13305759843716581749095605 1247414985348429538977713)
                    ·
                      refine ⟨935561239011322154233285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247414985348429538977713 935561239011322154233285)
                      ·
                        rfl

theorem cell23_1821999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5, 2].length) (baseStart_1821999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1821999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1821999 prefixEnd_1821999 := by exact prefixLift 1821999
  have htrace : WordTrace (prefixWord ++ tailWord_1821999) baseStart_1821999 baseEnd_1821999 := by
    simpa [prefixWord, tailWord_1821999, baseEnd_1821999] using wordTrace_append hprefix tailTrace_1821999
  have hstable : (prefixWord ++ tailWord_1821999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821999).length < 2 ^ (prefixWord ++ tailWord_1821999).sum := by decide
  have hdescent : baseEnd_1821999 < baseStart_1821999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822083 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 3]
def baseStart_1822083 : Nat := 118140960795 + 1822083 * 2 ^ 59
def prefixEnd_1822083 : Nat := 4983230072969 + 3 ^ 40 * 1822083 * 2
def baseEnd_1822083 : Nat := 935604371386299825582899

theorem tailTrace_1822083 : CollatzResearch.WordTrace tailWord_1822083 prefixEnd_1822083 935604371386299825582899 := by
  unfold tailWord_1822083
  simp only [CollatzResearch.WordTrace]
  refine ⟨66456826657911952846646903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44304551105274635231097935 66456826657911952846646903)
  ·
    refine ⟨99685239986867929269970355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66456826657911952846646903 99685239986867929269970355)
    ·
      refine ⟨149527859980301893904955533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99685239986867929269970355 149527859980301893904955533)
      ·
        refine ⟨56072947492613210214358325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149527859980301893904955533 56072947492613210214358325)
        ·
          refine ⟨5256838827432488457596093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56072947492613210214358325 5256838827432488457596093)
          ·
            refine ⟨1971314560287183171598535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5256838827432488457596093 1971314560287183171598535)
            ·
              refine ⟨2956971840430774757397803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971314560287183171598535 2956971840430774757397803)
              ·
                refine ⟨4435457760646162136096705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956971840430774757397803 4435457760646162136096705)
                ·
                  refine ⟨3326593320484621602072529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4435457760646162136096705 3326593320484621602072529)
                  ·
                    refine ⟨2494944990363466201554397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3326593320484621602072529 2494944990363466201554397)
                    ·
                      refine ⟨935604371386299825582899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2494944990363466201554397 935604371386299825582899)
                      ·
                        rfl

theorem cell23_1822083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_1822083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822083 prefixEnd_1822083 := by exact prefixLift 1822083
  have htrace : WordTrace (prefixWord ++ tailWord_1822083) baseStart_1822083 baseEnd_1822083 := by
    simpa [prefixWord, tailWord_1822083, baseEnd_1822083] using wordTrace_append hprefix tailTrace_1822083
  have hstable : (prefixWord ++ tailWord_1822083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822083).length < 2 ^ (prefixWord ++ tailWord_1822083).sum := by decide
  have hdescent : baseEnd_1822083 < baseStart_1822083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822120 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 6]
def baseStart_1822120 : Nat := 118140960795 + 1822120 * 2 ^ 59
def prefixEnd_1822120 : Nat := 4983230072969 + 3 ^ 40 * 1822120 * 2
def baseEnd_1822120 : Nat := 103958152241168464535581

theorem tailTrace_1822120 : CollatzResearch.WordTrace tailWord_1822120 prefixEnd_1822120 103958152241168464535581 := by
  unfold tailWord_1822120
  simp only [CollatzResearch.WordTrace]
  refine ⟨33229088079388954082871907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44305450772518605443829209 33229088079388954082871907)
  ·
    refine ⟨49843632119083431124307861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33229088079388954082871907 49843632119083431124307861)
    ·
      refine ⟨2336420255582035833951931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49843632119083431124307861 2336420255582035833951931)
      ·
        refine ⟨3504630383373053750927897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336420255582035833951931 3504630383373053750927897)
        ·
          refine ⟨2628472787529790313195923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3504630383373053750927897 2628472787529790313195923)
          ·
            refine ⟨3942709181294685469793885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628472787529790313195923 3942709181294685469793885)
            ·
              refine ⟨1478515942985507051172707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3942709181294685469793885 1478515942985507051172707)
              ·
                refine ⟨2217773914478260576759061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478515942985507051172707 2217773914478260576759061)
                ·
                  refine ⟨103958152241168464535581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2217773914478260576759061 103958152241168464535581)
                  ·
                    rfl

theorem cell23_1822120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 6].length) (baseStart_1822120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822120 prefixEnd_1822120 := by exact prefixLift 1822120
  have htrace : WordTrace (prefixWord ++ tailWord_1822120) baseStart_1822120 baseEnd_1822120 := by
    simpa [prefixWord, tailWord_1822120, baseEnd_1822120] using wordTrace_append hprefix tailTrace_1822120
  have hstable : (prefixWord ++ tailWord_1822120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822120).length < 2 ^ (prefixWord ++ tailWord_1822120).sum := by decide
  have hdescent : baseEnd_1822120 < baseStart_1822120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822133 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1822133 : Nat := 118140960795 + 1822133 * 2 ^ 59
def prefixEnd_1822133 : Nat := 4983230072969 + 3 ^ 40 * 1822133 * 2
def baseEnd_1822133 : Nat := 311876681806341543319223

theorem tailTrace_1822133 : CollatzResearch.WordTrace tailWord_1822133 prefixEnd_1822133 311876681806341543319223 := by
  unfold tailWord_1822133
  simp only [CollatzResearch.WordTrace]
  refine ⟨66458650307730811385967053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44305766871820540923978035 66458650307730811385967053)
  ·
    refine ⟨24921993865399054269737645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66458650307730811385967053 24921993865399054269737645)
    ·
      refine ⟨9345747699524645351151617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24921993865399054269737645 9345747699524645351151617)
      ·
        refine ⟨7009310774643484013363713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9345747699524645351151617 7009310774643484013363713)
        ·
          refine ⟨5256983080982613010022785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009310774643484013363713 5256983080982613010022785)
          ·
            refine ⟨3942737310736959757517089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256983080982613010022785 3942737310736959757517089)
            ·
              refine ⟨2957052983052719818137817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942737310736959757517089 2957052983052719818137817)
              ·
                refine ⟨2217789737289539863603363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957052983052719818137817 2217789737289539863603363)
                ·
                  refine ⟨3326684605934309795405045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217789737289539863603363 3326684605934309795405045)
                  ·
                    refine ⟨311876681806341543319223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3326684605934309795405045 311876681806341543319223)
                    ·
                      rfl

theorem cell23_1822133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1822133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822133 prefixEnd_1822133 := by exact prefixLift 1822133
  have htrace : WordTrace (prefixWord ++ tailWord_1822133) baseStart_1822133 baseEnd_1822133 := by
    simpa [prefixWord, tailWord_1822133, baseEnd_1822133] using wordTrace_append hprefix tailTrace_1822133
  have hstable : (prefixWord ++ tailWord_1822133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822133).length < 2 ^ (prefixWord ++ tailWord_1822133).sum := by decide
  have hdescent : baseEnd_1822133 < baseStart_1822133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822136 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_1822136 : Nat := 118140960795 + 1822136 * 2 ^ 59
def prefixEnd_1822136 : Nat := 4983230072969 + 3 ^ 40 * 1822136 * 2
def baseEnd_1822136 : Nat := 935631585860988118220155

theorem tailTrace_1822136 : CollatzResearch.WordTrace tailWord_1822136 prefixEnd_1822136 935631585860988118220155 := by
  unfold tailWord_1822136
  simp only [CollatzResearch.WordTrace]
  refine ⟨33229379863359971449163131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44305839817813295265550841 33229379863359971449163131)
  ·
    refine ⟨49844069795039957173744697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33229379863359971449163131 49844069795039957173744697)
    ·
      refine ⟨37383052346279967880308523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49844069795039957173744697 37383052346279967880308523)
      ·
        refine ⟨56074578519419951820462785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37383052346279967880308523 56074578519419951820462785)
        ·
          refine ⟨42055933889564963865347089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56074578519419951820462785 42055933889564963865347089)
          ·
            refine ⟨31541950417173722899010317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42055933889564963865347089 31541950417173722899010317)
            ·
              refine ⟨11828231406440146087128869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31541950417173722899010317 11828231406440146087128869)
              ·
                refine ⟨2217793388707527391336663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11828231406440146087128869 2217793388707527391336663)
                ·
                  refine ⟨3326690083061291087004995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217793388707527391336663 3326690083061291087004995)
                  ·
                    refine ⟨4990035124591936630507493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3326690083061291087004995 4990035124591936630507493)
                    ·
                      refine ⟨935631585860988118220155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4990035124591936630507493 935631585860988118220155)
                      ·
                        rfl

theorem cell23_1822136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_1822136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822136 prefixEnd_1822136 := by exact prefixLift 1822136
  have htrace : WordTrace (prefixWord ++ tailWord_1822136) baseStart_1822136 baseEnd_1822136 := by
    simpa [prefixWord, tailWord_1822136, baseEnd_1822136] using wordTrace_append hprefix tailTrace_1822136
  have hstable : (prefixWord ++ tailWord_1822136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822136).length < 2 ^ (prefixWord ++ tailWord_1822136).sum := by decide
  have hdescent : baseEnd_1822136 < baseStart_1822136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822156 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1822156 : Nat := 118140960795 + 1822156 * 2 ^ 59
def prefixEnd_1822156 : Nat := 4983230072969 + 3 ^ 40 * 1822156 * 2
def baseEnd_1822156 : Nat := 935641855474078039970063

theorem tailTrace_1822156 : CollatzResearch.WordTrace tailWord_1822156 prefixEnd_1822156 935641855474078039970063 := by
  unfold tailWord_1822156
  simp only [CollatzResearch.WordTrace]
  refine ⟨33229744593323743157027161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44306326124431657542702881 33229744593323743157027161)
  ·
    refine ⟨24922308444992807367770371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33229744593323743157027161 24922308444992807367770371)
    ·
      refine ⟨37383462667489211051655557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24922308444992807367770371 37383462667489211051655557)
      ·
        refine ⟨7009399250154227072185417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37383462667489211051655557 7009399250154227072185417)
        ·
          refine ⟨5257049437615670304139063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009399250154227072185417 5257049437615670304139063)
          ·
            refine ⟨7885574156423505456208595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257049437615670304139063 7885574156423505456208595)
            ·
              refine ⟨11828361234635258184312893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885574156423505456208595 11828361234635258184312893)
              ·
                refine ⟨4435635462988221819117335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11828361234635258184312893 4435635462988221819117335)
                ·
                  refine ⟨6653453194482332728676003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435635462988221819117335 6653453194482332728676003)
                  ·
                    refine ⟨9980179791723499093014005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6653453194482332728676003 9980179791723499093014005)
                    ·
                      refine ⟨935641855474078039970063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9980179791723499093014005 935641855474078039970063)
                      ·
                        rfl

theorem cell23_1822156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1822156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822156 prefixEnd_1822156 := by exact prefixLift 1822156
  have htrace : WordTrace (prefixWord ++ tailWord_1822156) baseStart_1822156 baseEnd_1822156 := by
    simpa [prefixWord, tailWord_1822156, baseEnd_1822156] using wordTrace_append hprefix tailTrace_1822156
  have hstable : (prefixWord ++ tailWord_1822156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822156).length < 2 ^ (prefixWord ++ tailWord_1822156).sum := by decide
  have hdescent : baseEnd_1822156 < baseStart_1822156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822164 : List Nat := [2, 4, 1, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_1822164 : Nat := 118140960795 + 1822164 * 2 ^ 59
def prefixEnd_1822164 : Nat := 4983230072969 + 3 ^ 40 * 1822164 * 2
def baseEnd_1822164 : Nat := 935645963319314008670027

theorem tailTrace_1822164 : CollatzResearch.WordTrace tailWord_1822164 prefixEnd_1822164 935645963319314008670027 := by
  unfold tailWord_1822164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33229890485309251840172773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44306520647079002453563697 33229890485309251840172773)
  ·
    refine ⟨6230604465995484720032395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33229890485309251840172773 6230604465995484720032395)
    ·
      refine ⟨9345906698993227080048593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6230604465995484720032395 9345906698993227080048593)
      ·
        refine ⟨7009430024244920310036445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9345906698993227080048593 7009430024244920310036445)
        ·
          refine ⟨2628536259091845116263667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7009430024244920310036445 2628536259091845116263667)
          ·
            refine ⟨3942804388637767674395501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628536259091845116263667 3942804388637767674395501)
            ·
              refine ⟨1478551645739162877898313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3942804388637767674395501 1478551645739162877898313)
              ·
                refine ⟨1108913734304372158423735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478551645739162877898313 1108913734304372158423735)
                ·
                  refine ⟨1663370601456558237635603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108913734304372158423735 1663370601456558237635603)
                  ·
                    refine ⟨2495055902184837356453405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1663370601456558237635603 2495055902184837356453405)
                    ·
                      refine ⟨935645963319314008670027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2495055902184837356453405 935645963319314008670027)
                      ·
                        rfl

theorem cell23_1822164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_1822164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822164 prefixEnd_1822164 := by exact prefixLift 1822164
  have htrace : WordTrace (prefixWord ++ tailWord_1822164) baseStart_1822164 baseEnd_1822164 := by
    simpa [prefixWord, tailWord_1822164, baseEnd_1822164] using wordTrace_append hprefix tailTrace_1822164
  have hstable : (prefixWord ++ tailWord_1822164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822164).length < 2 ^ (prefixWord ++ tailWord_1822164).sum := by decide
  have hdescent : baseEnd_1822164 < baseStart_1822164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822170 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2]
def baseStart_1822170 : Nat := 118140960795 + 1822170 * 2 ^ 59
def prefixEnd_1822170 : Nat := 4983230072969 + 3 ^ 40 * 1822170 * 2
def baseEnd_1822170 : Nat := 935649044203240985194999

theorem tailTrace_1822170 : CollatzResearch.WordTrace tailWord_1822170 prefixEnd_1822170 935649044203240985194999 := by
  unfold tailWord_1822170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614999952149191676265991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44306666539064511136709309 16614999952149191676265991)
  ·
    refine ⟨24922499928223787514398987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16614999952149191676265991 24922499928223787514398987)
    ·
      refine ⟨37383749892335681271598481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24922499928223787514398987 37383749892335681271598481)
      ·
        refine ⟨28037812419251760953698861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37383749892335681271598481 28037812419251760953698861)
        ·
          refine ⟨10514179657219410357637073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28037812419251760953698861 10514179657219410357637073)
          ·
            refine ⟨7885634742914557768227805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10514179657219410357637073 7885634742914557768227805)
            ·
              refine ⟨2957113028592959163085427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7885634742914557768227805 2957113028592959163085427)
              ·
                refine ⟨4435669542889438744628141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957113028592959163085427 4435669542889438744628141)
                ·
                  refine ⟨1663376078583539529235553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4435669542889438744628141 1663376078583539529235553)
                  ·
                    refine ⟨1247532058937654646926665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1663376078583539529235553 1247532058937654646926665)
                    ·
                      refine ⟨935649044203240985194999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247532058937654646926665 935649044203240985194999)
                      ·
                        rfl

theorem cell23_1822170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_1822170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822170 prefixEnd_1822170 := by exact prefixLift 1822170
  have htrace : WordTrace (prefixWord ++ tailWord_1822170) baseStart_1822170 baseEnd_1822170 := by
    simpa [prefixWord, tailWord_1822170, baseEnd_1822170] using wordTrace_append hprefix tailTrace_1822170
  have hstable : (prefixWord ++ tailWord_1822170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822170).length < 2 ^ (prefixWord ++ tailWord_1822170).sum := by decide
  have hdescent : baseEnd_1822170 < baseStart_1822170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822199 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1822199 : Nat := 118140960795 + 1822199 * 2 ^ 59
def prefixEnd_1822199 : Nat := 4983230072969 + 3 ^ 40 * 1822199 * 2
def baseEnd_1822199 : Nat := 935663935142221371732365

theorem tailTrace_1822199 : CollatzResearch.WordTrace tailWord_1822199 prefixEnd_1822199 935663935142221371732365 := by
  unfold tailWord_1822199
  simp only [CollatzResearch.WordTrace]
  refine ⟨66461057525491704657869651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44307371683661136438579767 66461057525491704657869651)
  ·
    refine ⟨99691586288237556986804477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66461057525491704657869651 99691586288237556986804477)
    ·
      refine ⟨37384344858089083870051679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99691586288237556986804477 37384344858089083870051679)
      ·
        refine ⟨56076517287133625805077519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37384344858089083870051679 56076517287133625805077519)
        ·
          refine ⟨84114775930700438707616279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56076517287133625805077519 84114775930700438707616279)
          ·
            refine ⟨126172163896050658061424419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84114775930700438707616279 126172163896050658061424419)
            ·
              refine ⟨189258245844075987092136629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126172163896050658061424419 189258245844075987092136629)
              ·
                refine ⟨17742960547882123789887809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189258245844075987092136629 17742960547882123789887809)
                ·
                  refine ⟨13307220410911592842415857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17742960547882123789887809 13307220410911592842415857)
                  ·
                    refine ⟨9980415308183694631811893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13307220410911592842415857 9980415308183694631811893)
                    ·
                      refine ⟨935663935142221371732365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9980415308183694631811893 935663935142221371732365)
                      ·
                        rfl

theorem cell23_1822199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1822199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822199 prefixEnd_1822199 := by exact prefixLift 1822199
  have htrace : WordTrace (prefixWord ++ tailWord_1822199) baseStart_1822199 baseEnd_1822199 := by
    simpa [prefixWord, tailWord_1822199, baseEnd_1822199] using wordTrace_append hprefix tailTrace_1822199
  have hstable : (prefixWord ++ tailWord_1822199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822199).length < 2 ^ (prefixWord ++ tailWord_1822199).sum := by decide
  have hdescent : baseEnd_1822199 < baseStart_1822199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822236 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1822236 : Nat := 118140960795 + 1822236 * 2 ^ 59
def prefixEnd_1822236 : Nat := 4983230072969 + 3 ^ 40 * 1822236 * 2
def baseEnd_1822236 : Nat := 311894311308812575656565

theorem tailTrace_1822236 : CollatzResearch.WordTrace tailWord_1822236 prefixEnd_1822236 311894311308812575656565 := by
  unfold tailWord_1822236
  simp only [CollatzResearch.WordTrace]
  refine ⟨33231203513178829988483281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44308271350905106651311041 33231203513178829988483281)
  ·
    refine ⟨24923402634884122491362461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33231203513178829988483281 24923402634884122491362461)
    ·
      refine ⟨9346275988081545934260923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24923402634884122491362461 9346275988081545934260923)
      ·
        refine ⟨14019413982122318901391385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9346275988081545934260923 14019413982122318901391385)
        ·
          refine ⟨10514560486591739176043539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14019413982122318901391385 10514560486591739176043539)
          ·
            refine ⟨15771840729887608764065309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10514560486591739176043539 15771840729887608764065309)
            ·
              refine ⟨5914440273707853286524491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15771840729887608764065309 5914440273707853286524491)
              ·
                refine ⟨8871660410561779929786737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914440273707853286524491 8871660410561779929786737)
                ·
                  refine ⟨6653745307921334947340053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8871660410561779929786737 6653745307921334947340053)
                  ·
                    refine ⟨311894311308812575656565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6653745307921334947340053 311894311308812575656565)
                    ·
                      rfl

theorem cell23_1822236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1822236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822236 prefixEnd_1822236 := by exact prefixLift 1822236
  have htrace : WordTrace (prefixWord ++ tailWord_1822236) baseStart_1822236 baseEnd_1822236 := by
    simpa [prefixWord, tailWord_1822236, baseEnd_1822236] using wordTrace_append hprefix tailTrace_1822236
  have hstable : (prefixWord ++ tailWord_1822236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822236).length < 2 ^ (prefixWord ++ tailWord_1822236).sum := by decide
  have hdescent : baseEnd_1822236 < baseStart_1822236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822317 : List Nat := [1, 5, 1, 1, 4, 2, 1, 3, 5]
def baseStart_1822317 : Nat := 118140960795 + 1822317 * 2 ^ 59
def prefixEnd_1822317 : Nat := 4983230072969 + 3 ^ 40 * 1822317 * 2
def baseEnd_1822317 : Nat := 103969391762161323339647

theorem tailTrace_1822317 : CollatzResearch.WordTrace tailWord_1822317 prefixEnd_1822317 103969391762161323339647 := by
  unfold tailWord_1822317
  simp only [CollatzResearch.WordTrace]
  refine ⟨66465361339064210810665205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44310240892709473873776803 66465361339064210810665205)
  ·
    refine ⟨6231127625537269763499863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66465361339064210810665205 6231127625537269763499863)
    ·
      refine ⟨9346691438305904645249795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6231127625537269763499863 9346691438305904645249795)
      ·
        refine ⟨14020037157458856967874693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9346691438305904645249795 14020037157458856967874693)
        ·
          refine ⟨2628756967023535681476505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14020037157458856967874693 2628756967023535681476505)
          ·
            refine ⟨1971567725267651761107379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2628756967023535681476505 1971567725267651761107379)
            ·
              refine ⟨2957351587901477641661069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971567725267651761107379 2957351587901477641661069)
              ·
                refine ⟨1109006845463054115622901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2957351587901477641661069 1109006845463054115622901)
                ·
                  refine ⟨103969391762161323339647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1109006845463054115622901 103969391762161323339647)
                  ·
                    rfl

theorem cell23_1822317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_1822317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822317 prefixEnd_1822317 := by exact prefixLift 1822317
  have htrace : WordTrace (prefixWord ++ tailWord_1822317) baseStart_1822317 baseEnd_1822317 := by
    simpa [prefixWord, tailWord_1822317, baseEnd_1822317] using wordTrace_append hprefix tailTrace_1822317
  have hstable : (prefixWord ++ tailWord_1822317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822317).length < 2 ^ (prefixWord ++ tailWord_1822317).sum := by decide
  have hdescent : baseEnd_1822317 < baseStart_1822317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822333 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_1822333 : Nat := 118140960795 + 1822333 * 2 ^ 59
def prefixEnd_1822333 : Nat := 4983230072969 + 3 ^ 40 * 1822333 * 2
def baseEnd_1822333 : Nat := 935732741549923847456749

theorem tailTrace_1822333 : CollatzResearch.WordTrace tailWord_1822333 prefixEnd_1822333 935732741549923847456749 := by
  unfold tailWord_1822333
  simp only [CollatzResearch.WordTrace]
  refine ⟨66465944907006245543247653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44310629938004163695498435 66465944907006245543247653)
  ·
    refine ⟨12462364670063671039358935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66465944907006245543247653 12462364670063671039358935)
    ·
      refine ⟨18693547005095506559038403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12462364670063671039358935 18693547005095506559038403)
      ·
        refine ⟨28040320507643259838557605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18693547005095506559038403 28040320507643259838557605)
        ·
          refine ⟨5257560095183111219729551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28040320507643259838557605 5257560095183111219729551)
          ·
            refine ⟨7886340142774666829594327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257560095183111219729551 7886340142774666829594327)
            ·
              refine ⟨11829510214162000244391491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886340142774666829594327 11829510214162000244391491)
              ·
                refine ⟨17744265321243000366587237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11829510214162000244391491 17744265321243000366587237)
                ·
                  refine ⟨3327049747733062568735107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17744265321243000366587237 3327049747733062568735107)
                  ·
                    refine ⟨4990574621599593853102661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3327049747733062568735107 4990574621599593853102661)
                    ·
                      refine ⟨935732741549923847456749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4990574621599593853102661 935732741549923847456749)
                      ·
                        rfl

theorem cell23_1822333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_1822333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822333 prefixEnd_1822333 := by exact prefixLift 1822333
  have htrace : WordTrace (prefixWord ++ tailWord_1822333) baseStart_1822333 baseEnd_1822333 := by
    simpa [prefixWord, tailWord_1822333, baseEnd_1822333] using wordTrace_append hprefix tailTrace_1822333
  have hstable : (prefixWord ++ tailWord_1822333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822333).length < 2 ^ (prefixWord ++ tailWord_1822333).sum := by decide
  have hdescent : baseEnd_1822333 < baseStart_1822333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822367 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1822367 : Nat := 118140960795 + 1822367 * 2 ^ 59
def prefixEnd_1822367 : Nat := 4983230072969 + 3 ^ 40 * 1822367 * 2
def baseEnd_1822367 : Nat := 935750199892176714431593

theorem tailTrace_1822367 : CollatzResearch.WordTrace tailWord_1822367 prefixEnd_1822367 935750199892176714431593 := by
  unfold tailWord_1822367
  simp only [CollatzResearch.WordTrace]
  refine ⟨66467184988883069349985355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44311456659255379566656903 66467184988883069349985355)
  ·
    refine ⟨99700777483324604024978033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66467184988883069349985355 99700777483324604024978033)
    ·
      refine ⟨74775583112493453018733525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99700777483324604024978033 74775583112493453018733525)
      ·
        refine ⟨1752552729199065305126567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 74775583112493453018733525 1752552729199065305126567)
        ·
          refine ⟨2628829093798597957689851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752552729199065305126567 2628829093798597957689851)
          ·
            refine ⟨3943243640697896936534777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628829093798597957689851 3943243640697896936534777)
            ·
              refine ⟨2957432730523422702401083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943243640697896936534777 2957432730523422702401083)
              ·
                refine ⟨4436149095785134053601625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957432730523422702401083 4436149095785134053601625)
                ·
                  refine ⟨3327111821838850540201219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4436149095785134053601625 3327111821838850540201219)
                  ·
                    refine ⟨4990667732758275810301829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3327111821838850540201219 4990667732758275810301829)
                    ·
                      refine ⟨935750199892176714431593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4990667732758275810301829 935750199892176714431593)
                      ·
                        rfl

theorem cell23_1822367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1822367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822367 prefixEnd_1822367 := by exact prefixLift 1822367
  have htrace : WordTrace (prefixWord ++ tailWord_1822367) baseStart_1822367 baseEnd_1822367 := by
    simpa [prefixWord, tailWord_1822367, baseEnd_1822367] using wordTrace_append hprefix tailTrace_1822367
  have hstable : (prefixWord ++ tailWord_1822367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822367).length < 2 ^ (prefixWord ++ tailWord_1822367).sum := by decide
  have hdescent : baseEnd_1822367 < baseStart_1822367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822394 : List Nat := [3, 1, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_1822394 : Nat := 118140960795 + 1822394 * 2 ^ 59
def prefixEnd_1822394 : Nat := 4983230072969 + 3 ^ 40 * 1822394 * 2
def baseEnd_1822394 : Nat := 311921354623282702931323

theorem tailTrace_1822394 : CollatzResearch.WordTrace tailWord_1822394 prefixEnd_1822394 311921354623282702931323 := by
  unfold tailWord_1822394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16617042439946313240304559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44312113173190168640812157 16617042439946313240304559)
  ·
    refine ⟨24925563659919469860456839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16617042439946313240304559 24925563659919469860456839)
    ·
      refine ⟨37388345489879204790685259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24925563659919469860456839 37388345489879204790685259)
      ·
        refine ⟨56082518234818807186027889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37388345489879204790685259 56082518234818807186027889)
        ·
          refine ⟨42061888676114105389520917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56082518234818807186027889 42061888676114105389520917)
          ·
            refine ⟨1971651031692848690133793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42061888676114105389520917 1971651031692848690133793)
            ·
              refine ⟨1478738273769636517600345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1971651031692848690133793 1478738273769636517600345)
              ·
                refine ⟨1109053705327227388200259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478738273769636517600345 1109053705327227388200259)
                ·
                  refine ⟨1663580557990841082300389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109053705327227388200259 1663580557990841082300389)
                  ·
                    refine ⟨311921354623282702931323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1663580557990841082300389 311921354623282702931323)
                    ·
                      rfl

theorem cell23_1822394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_1822394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822394 prefixEnd_1822394 := by exact prefixLift 1822394
  have htrace : WordTrace (prefixWord ++ tailWord_1822394) baseStart_1822394 baseEnd_1822394 := by
    simpa [prefixWord, tailWord_1822394, baseEnd_1822394] using wordTrace_append hprefix tailTrace_1822394
  have hstable : (prefixWord ++ tailWord_1822394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822394).length < 2 ^ (prefixWord ++ tailWord_1822394).sum := by decide
  have hdescent : baseEnd_1822394 < baseStart_1822394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822400 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 3, 1, 3]
def baseStart_1822400 : Nat := 118140960795 + 1822400 * 2 ^ 59
def prefixEnd_1822400 : Nat := 4983230072969 + 3 ^ 40 * 1822400 * 2
def baseEnd_1822400 : Nat := 935767144753775085318941

theorem tailTrace_1822400 : CollatzResearch.WordTrace tailWord_1822400 prefixEnd_1822400 935767144753775085318941 := by
  unfold tailWord_1822400
  simp only [CollatzResearch.WordTrace]
  refine ⟨33234194298881757992968327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44312259065175677323957769 33234194298881757992968327)
  ·
    refine ⟨49851291448322636989452491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33234194298881757992968327 49851291448322636989452491)
    ·
      refine ⟨74776937172483955484178737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49851291448322636989452491 74776937172483955484178737)
      ·
        refine ⟨56082702879362966613134053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74776937172483955484178737 56082702879362966613134053)
        ·
          refine ⟨10515506789880556239962635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56082702879362966613134053 10515506789880556239962635)
          ·
            refine ⟨15773260184820834359943953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10515506789880556239962635 15773260184820834359943953)
            ·
              refine ⟨11829945138615625769957965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15773260184820834359943953 11829945138615625769957965)
              ·
                refine ⟨4436229426980859663734237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11829945138615625769957965 4436229426980859663734237)
                ·
                  refine ⟨1663586035117822373900339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4436229426980859663734237 1663586035117822373900339)
                  ·
                    refine ⟨2495379052676733560850509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1663586035117822373900339 2495379052676733560850509)
                    ·
                      refine ⟨935767144753775085318941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2495379052676733560850509 935767144753775085318941)
                      ·
                        rfl

theorem cell23_1822400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_1822400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822400 prefixEnd_1822400 := by exact prefixLift 1822400
  have htrace : WordTrace (prefixWord ++ tailWord_1822400) baseStart_1822400 baseEnd_1822400 := by
    simpa [prefixWord, tailWord_1822400, baseEnd_1822400] using wordTrace_append hprefix tailTrace_1822400
  have hstable : (prefixWord ++ tailWord_1822400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822400).length < 2 ^ (prefixWord ++ tailWord_1822400).sum := by decide
  have hdescent : baseEnd_1822400 < baseStart_1822400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822420 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1822420 : Nat := 118140960795 + 1822420 * 2 ^ 59
def prefixEnd_1822420 : Nat := 4983230072969 + 3 ^ 40 * 1822420 * 2
def baseEnd_1822420 : Nat := 311925804788955002356283

theorem tailTrace_1822420 : CollatzResearch.WordTrace tailWord_1822420 prefixEnd_1822420 311925804788955002356283 := by
  unfold tailWord_1822420
  simp only [CollatzResearch.WordTrace]
  refine ⟨33234559028845529700832357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44312745371794039601109809 33234559028845529700832357)
  ·
    refine ⟨6231479817908536818906067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33234559028845529700832357 6231479817908536818906067)
    ·
      refine ⟨9347219726862805228359101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6231479817908536818906067 9347219726862805228359101)
      ·
        refine ⟨3505207397573551960634663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9347219726862805228359101 3505207397573551960634663)
        ·
          refine ⟨5257811096360327940951995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3505207397573551960634663 5257811096360327940951995)
          ·
            refine ⟨7886716644540491911427993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257811096360327940951995 7886716644540491911427993)
            ·
              refine ⟨5915037483405368933570995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7886716644540491911427993 5915037483405368933570995)
              ·
                refine ⟨8872556225108053400356493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5915037483405368933570995 8872556225108053400356493)
                ·
                  refine ⟨3327208584415520025133685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8872556225108053400356493 3327208584415520025133685)
                  ·
                    refine ⟨311925804788955002356283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3327208584415520025133685 311925804788955002356283)
                    ·
                      rfl

theorem cell23_1822420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1822420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822420 prefixEnd_1822420 := by exact prefixLift 1822420
  have htrace : WordTrace (prefixWord ++ tailWord_1822420) baseStart_1822420 baseEnd_1822420 := by
    simpa [prefixWord, tailWord_1822420, baseEnd_1822420] using wordTrace_append hprefix tailTrace_1822420
  have hstable : (prefixWord ++ tailWord_1822420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822420).length < 2 ^ (prefixWord ++ tailWord_1822420).sum := by decide
  have hdescent : baseEnd_1822420 < baseStart_1822420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822423 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1822423 : Nat := 118140960795 + 1822423 * 2 ^ 59
def prefixEnd_1822423 : Nat := 4983230072969 + 3 ^ 40 * 1822423 * 2
def baseEnd_1822423 : Nat := 935778954808828495331335

theorem tailTrace_1822423 : CollatzResearch.WordTrace tailWord_1822423 prefixEnd_1822423 935778954808828495331335 := by
  unfold tailWord_1822423
  simp only [CollatzResearch.WordTrace]
  refine ⟨66469227476680190914023923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44312818317786793942682615 66469227476680190914023923)
  ·
    refine ⟨99703841215020286371035885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66469227476680190914023923 99703841215020286371035885)
    ·
      refine ⟨37388940455632607389138457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99703841215020286371035885 37388940455632607389138457)
      ·
        refine ⟨28041705341724455541853843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37388940455632607389138457 28041705341724455541853843)
        ·
          refine ⟨42062558012586683312780765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28041705341724455541853843 42062558012586683312780765)
          ·
            refine ⟨15773459254720006242292787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42062558012586683312780765 15773459254720006242292787)
            ·
              refine ⟨23660188882080009363439181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15773459254720006242292787 23660188882080009363439181)
              ·
                refine ⟨8872570830780003511289693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23660188882080009363439181 8872570830780003511289693)
                ·
                  refine ⟨3327214061542501316733635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8872570830780003511289693 3327214061542501316733635)
                  ·
                    refine ⟨4990821092313751975100453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3327214061542501316733635 4990821092313751975100453)
                    ·
                      refine ⟨935778954808828495331335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4990821092313751975100453 935778954808828495331335)
                      ·
                        rfl

theorem cell23_1822423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1822423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822423 prefixEnd_1822423 := by exact prefixLift 1822423
  have htrace : WordTrace (prefixWord ++ tailWord_1822423) baseStart_1822423 baseEnd_1822423 := by
    simpa [prefixWord, tailWord_1822423, baseEnd_1822423] using wordTrace_append hprefix tailTrace_1822423
  have hstable : (prefixWord ++ tailWord_1822423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822423).length < 2 ^ (prefixWord ++ tailWord_1822423).sum := by decide
  have hdescent : baseEnd_1822423 < baseStart_1822423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822450 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_1822450 : Nat := 118140960795 + 1822450 * 2 ^ 59
def prefixEnd_1822450 : Nat := 4983230072969 + 3 ^ 40 * 1822450 * 2
def baseEnd_1822450 : Nat := 311930939595499963231237

theorem tailTrace_1822450 : CollatzResearch.WordTrace tailWord_1822450 prefixEnd_1822450 311930939595499963231237 := by
  unfold tailWord_1822450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16617553061895593631314201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44313474831721583016837869 16617553061895593631314201)
  ·
    refine ⟨12463164796421695223485651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16617553061895593631314201 12463164796421695223485651)
    ·
      refine ⟨18694747194632542835228477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12463164796421695223485651 18694747194632542835228477)
      ·
        refine ⟨7010530197987203563210679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18694747194632542835228477 7010530197987203563210679)
        ·
          refine ⟨10515795296980805344816019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7010530197987203563210679 10515795296980805344816019)
          ·
            refine ⟨15773692945471208017224029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10515795296980805344816019 15773692945471208017224029)
            ·
              refine ⟨5915134854551703006459011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15773692945471208017224029 5915134854551703006459011)
              ·
                refine ⟨8872702281827554509688517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5915134854551703006459011 8872702281827554509688517)
                ·
                  refine ⟨1663631677842666470566597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8872702281827554509688517 1663631677842666470566597)
                  ·
                    refine ⟨311930939595499963231237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1663631677842666470566597 311930939595499963231237)
                    ·
                      rfl

theorem cell23_1822450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_1822450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822450 prefixEnd_1822450 := by exact prefixLift 1822450
  have htrace : WordTrace (prefixWord ++ tailWord_1822450) baseStart_1822450 baseEnd_1822450 := by
    simpa [prefixWord, tailWord_1822450, baseEnd_1822450] using wordTrace_append hprefix tailTrace_1822450
  have hstable : (prefixWord ++ tailWord_1822450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822450).length < 2 ^ (prefixWord ++ tailWord_1822450).sum := by decide
  have hdescent : baseEnd_1822450 < baseStart_1822450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822524 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_1822524 : Nat := 118140960795 + 1822524 * 2 ^ 59
def prefixEnd_1822524 : Nat := 4983230072969 + 3 ^ 40 * 1822524 * 2
def baseEnd_1822524 : Nat := 935830816354932600168371

theorem tailTrace_1822524 : CollatzResearch.WordTrace tailWord_1822524 prefixEnd_1822524 935830816354932600168371 := by
  unfold tailWord_1822524
  simp only [CollatzResearch.WordTrace]
  refine ⟨33236455624657142581725313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44315274166209523442300417 33236455624657142581725313)
  ·
    refine ⟨24927341718492856936293985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33236455624657142581725313 24927341718492856936293985)
    ·
      refine ⟨18695506288869642702220489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24927341718492856936293985 18695506288869642702220489)
      ·
        refine ⟨14021629716652232026665367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18695506288869642702220489 14021629716652232026665367)
        ·
          refine ⟨21032444574978348039998051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14021629716652232026665367 21032444574978348039998051)
          ·
            refine ⟨31548666862467522059997077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21032444574978348039998051 31548666862467522059997077)
            ·
              refine ⟨1478843759178165096562363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31548666862467522059997077 1478843759178165096562363)
              ·
                refine ⟨2218265638767247644843545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478843759178165096562363 2218265638767247644843545)
                ·
                  refine ⟨1663699229075435733632659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218265638767247644843545 1663699229075435733632659)
                  ·
                    refine ⟨2495548843613153600448989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1663699229075435733632659 2495548843613153600448989)
                    ·
                      refine ⟨935830816354932600168371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2495548843613153600448989 935830816354932600168371)
                      ·
                        rfl

theorem cell23_1822524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_1822524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822524 prefixEnd_1822524 := by exact prefixLift 1822524
  have htrace : WordTrace (prefixWord ++ tailWord_1822524) baseStart_1822524 baseEnd_1822524 := by
    simpa [prefixWord, tailWord_1822524, baseEnd_1822524] using wordTrace_append hprefix tailTrace_1822524
  have hstable : (prefixWord ++ tailWord_1822524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822524).length < 2 ^ (prefixWord ++ tailWord_1822524).sum := by decide
  have hdescent : baseEnd_1822524 < baseStart_1822524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822533 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_1822533 : Nat := 118140960795 + 1822533 * 2 ^ 59
def prefixEnd_1822533 : Nat := 4983230072969 + 3 ^ 40 * 1822533 * 2
def baseEnd_1822533 : Nat := 935835437680823064955829

theorem tailTrace_1822533 : CollatzResearch.WordTrace tailWord_1822533 prefixEnd_1822533 935835437680823064955829 := by
  unfold tailWord_1822533
  simp only [CollatzResearch.WordTrace]
  refine ⟨66473239506281679700528253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44315493004187786467018835 66473239506281679700528253)
  ·
    refine ⟨24927464814855629887698095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66473239506281679700528253 24927464814855629887698095)
    ·
      refine ⟨37391197222283444831547143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24927464814855629887698095 37391197222283444831547143)
      ·
        refine ⟨56086795833425167247320715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37391197222283444831547143 56086795833425167247320715)
        ·
          refine ⟨84130193750137750870981073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56086795833425167247320715 84130193750137750870981073)
          ·
            refine ⟨63097645312603313153235805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84130193750137750870981073 63097645312603313153235805)
            ·
              refine ⟨23661616992226242432463427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63097645312603313153235805 23661616992226242432463427)
              ·
                refine ⟨35492425488339363648695141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23661616992226242432463427 35492425488339363648695141)
                ·
                  refine ⟨6654829779063630684130339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35492425488339363648695141 6654829779063630684130339)
                  ·
                    refine ⟨9982244668595446026195509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6654829779063630684130339 9982244668595446026195509)
                    ·
                      refine ⟨935835437680823064955829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9982244668595446026195509 935835437680823064955829)
                      ·
                        rfl

theorem cell23_1822533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_1822533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822533 prefixEnd_1822533 := by exact prefixLift 1822533
  have htrace : WordTrace (prefixWord ++ tailWord_1822533) baseStart_1822533 baseEnd_1822533 := by
    simpa [prefixWord, tailWord_1822533, baseEnd_1822533] using wordTrace_append hprefix tailTrace_1822533
  have hstable : (prefixWord ++ tailWord_1822533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822533).length < 2 ^ (prefixWord ++ tailWord_1822533).sum := by decide
  have hdescent : baseEnd_1822533 < baseStart_1822533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822551 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 1, 3, 2]
def baseStart_1822551 : Nat := 118140960795 + 1822551 * 2 ^ 59
def prefixEnd_1822551 : Nat := 4983230072969 + 3 ^ 40 * 1822551 * 2
def baseEnd_1822551 : Nat := 935844680332603994530747

theorem tailTrace_1822551 : CollatzResearch.WordTrace tailWord_1822551 prefixEnd_1822551 935844680332603994530747 := by
  unfold tailWord_1822551
  simp only [CollatzResearch.WordTrace]
  refine ⟨66473896020216468774683507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44315930680144312516455671 66473896020216468774683507)
  ·
    refine ⟨99710844030324703162025261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66473896020216468774683507 99710844030324703162025261)
    ·
      refine ⟨37391566511371763685759473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99710844030324703162025261 37391566511371763685759473)
      ·
        refine ⟨28043674883528822764319605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37391566511371763685759473 28043674883528822764319605)
        ·
          refine ⟨2629094520330827134154963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28043674883528822764319605 2629094520330827134154963)
          ·
            refine ⟨3943641780496240701232445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629094520330827134154963 3943641780496240701232445)
            ·
              refine ⟨1478865667686090262962167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3943641780496240701232445 1478865667686090262962167)
              ·
                refine ⟨2218298501529135394443251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478865667686090262962167 2218298501529135394443251)
                ·
                  refine ⟨3327447752293703091664877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218298501529135394443251 3327447752293703091664877)
                  ·
                    refine ⟨1247792907110138659374329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327447752293703091664877 1247792907110138659374329)
                    ·
                      refine ⟨935844680332603994530747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247792907110138659374329 935844680332603994530747)
                      ·
                        rfl

theorem cell23_1822551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_1822551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822551 prefixEnd_1822551 := by exact prefixLift 1822551
  have htrace : WordTrace (prefixWord ++ tailWord_1822551) baseStart_1822551 baseEnd_1822551 := by
    simpa [prefixWord, tailWord_1822551, baseEnd_1822551] using wordTrace_append hprefix tailTrace_1822551
  have hstable : (prefixWord ++ tailWord_1822551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822551).length < 2 ^ (prefixWord ++ tailWord_1822551).sum := by decide
  have hdescent : baseEnd_1822551 < baseStart_1822551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822681 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 3, 4]
def baseStart_1822681 : Nat := 118140960795 + 1822681 * 2 ^ 59
def prefixEnd_1822681 : Nat := 4983230072969 + 3 ^ 40 * 1822681 * 2
def baseEnd_1822681 : Nat := 311970477605896161968383

theorem tailTrace_1822681 : CollatzResearch.WordTrace tailWord_1822681 prefixEnd_1822681 311970477605896161968383 := by
  unfold tailWord_1822681
  simp only [CollatzResearch.WordTrace]
  refine ⟨66478637509745500976915897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44319091673163667317943931 66478637509745500976915897)
  ·
    refine ⟨49858978132309125732686923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66478637509745500976915897 49858978132309125732686923)
    ·
      refine ⟨74788467198463688599030385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49858978132309125732686923 74788467198463688599030385)
      ·
        refine ⟨56091350398847766449272789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74788467198463688599030385 56091350398847766449272789)
        ·
          refine ⟨1314641024972994526154831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 56091350398847766449272789 1314641024972994526154831)
          ·
            refine ⟨1971961537459491789232247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314641024972994526154831 1971961537459491789232247)
            ·
              refine ⟨2957942306189237683848371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971961537459491789232247 2957942306189237683848371)
              ·
                refine ⟨4436913459283856525772557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957942306189237683848371 4436913459283856525772557)
                ·
                  refine ⟨1663842547231446197164709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4436913459283856525772557 1663842547231446197164709)
                  ·
                    refine ⟨311970477605896161968383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1663842547231446197164709 311970477605896161968383)
                    ·
                      rfl

theorem cell23_1822681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 4].length) (baseStart_1822681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822681 prefixEnd_1822681 := by exact prefixLift 1822681
  have htrace : WordTrace (prefixWord ++ tailWord_1822681) baseStart_1822681 baseEnd_1822681 := by
    simpa [prefixWord, tailWord_1822681, baseEnd_1822681] using wordTrace_append hprefix tailTrace_1822681
  have hstable : (prefixWord ++ tailWord_1822681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822681).length < 2 ^ (prefixWord ++ tailWord_1822681).sum := by decide
  have hdescent : baseEnd_1822681 < baseStart_1822681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822721 : List Nat := [1, 2, 4, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_1822721 : Nat := 118140960795 + 1822721 * 2 ^ 59
def prefixEnd_1822721 : Nat := 4983230072969 + 3 ^ 40 * 1822721 * 2
def baseEnd_1822721 : Nat := 935931972043868329404965

theorem tailTrace_1822721 : CollatzResearch.WordTrace tailWord_1822721 prefixEnd_1822721 935931972043868329404965 := by
  unfold tailWord_1822721
  simp only [CollatzResearch.WordTrace]
  refine ⟨66480096429600587808372017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44320064286400391872248011 66480096429600587808372017)
  ·
    refine ⟨49860072322200440856279013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66480096429600587808372017 49860072322200440856279013)
    ·
      refine ⟨9348763560412582660552315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49860072322200440856279013 9348763560412582660552315)
      ·
        refine ⟨14023145340618873990828473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9348763560412582660552315 14023145340618873990828473)
        ·
          refine ⟨10517359005464155493121355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14023145340618873990828473 10517359005464155493121355)
          ·
            refine ⟨15776038508196233239682033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517359005464155493121355 15776038508196233239682033)
            ·
              refine ⟨11832028881147174929761525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15776038508196233239682033 11832028881147174929761525)
              ·
                refine ⟨1109252707607547649665143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11832028881147174929761525 1109252707607547649665143)
                ·
                  refine ⟨1663879061411321474497715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109252707607547649665143 1663879061411321474497715)
                  ·
                    refine ⟨2495818592116982211746573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1663879061411321474497715 2495818592116982211746573)
                    ·
                      refine ⟨935931972043868329404965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2495818592116982211746573 935931972043868329404965)
                      ·
                        rfl

theorem cell23_1822721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_1822721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822721 prefixEnd_1822721 := by exact prefixLift 1822721
  have htrace : WordTrace (prefixWord ++ tailWord_1822721) baseStart_1822721 baseEnd_1822721 := by
    simpa [prefixWord, tailWord_1822721, baseEnd_1822721] using wordTrace_append hprefix tailTrace_1822721
  have hstable : (prefixWord ++ tailWord_1822721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822721).length < 2 ^ (prefixWord ++ tailWord_1822721).sum := by decide
  have hdescent : baseEnd_1822721 < baseStart_1822721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822754 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1822754 : Nat := 118140960795 + 1822754 * 2 ^ 59
def prefixEnd_1822754 : Nat := 4983230072969 + 3 ^ 40 * 1822754 * 2
def baseEnd_1822754 : Nat := 311982972301822233430771

theorem tailTrace_1822754 : CollatzResearch.WordTrace tailWord_1822754 prefixEnd_1822754 311982972301822233430771 := by
  unfold tailWord_1822754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16620325009620258611080829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44320866692320689629548877 16620325009620258611080829)
  ·
    refine ⟨6232621878607596979155311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16620325009620258611080829 6232621878607596979155311)
    ·
      refine ⟨9348932817911395468732967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6232621878607596979155311 9348932817911395468732967)
      ·
        refine ⟨14023399226867093203099451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9348932817911395468732967 14023399226867093203099451)
        ·
          refine ⟨21035098840300639804649177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14023399226867093203099451 21035098840300639804649177)
          ·
            refine ⟨15776324130225479853486883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21035098840300639804649177 15776324130225479853486883)
            ·
              refine ⟨23664486195338219780230325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15776324130225479853486883 23664486195338219780230325)
              ·
                refine ⟨2218545580812958104396593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23664486195338219780230325 2218545580812958104396593)
                ·
                  refine ⟨1663909185609718578297445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218545580812958104396593 1663909185609718578297445)
                  ·
                    refine ⟨311982972301822233430771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1663909185609718578297445 311982972301822233430771)
                    ·
                      rfl

theorem cell23_1822754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1822754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822754 prefixEnd_1822754 := by exact prefixLift 1822754
  have htrace : WordTrace (prefixWord ++ tailWord_1822754) baseStart_1822754 baseEnd_1822754 := by
    simpa [prefixWord, tailWord_1822754, baseEnd_1822754] using wordTrace_append hprefix tailTrace_1822754
  have hstable : (prefixWord ++ tailWord_1822754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822754).length < 2 ^ (prefixWord ++ tailWord_1822754).sum := by decide
  have hdescent : baseEnd_1822754 < baseStart_1822754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822757 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_1822757 : Nat := 118140960795 + 1822757 * 2 ^ 59
def prefixEnd_1822757 : Nat := 4983230072969 + 3 ^ 40 * 1822757 * 2
def baseEnd_1822757 : Nat := 935950457347430188554799

theorem tailTrace_1822757 : CollatzResearch.WordTrace tailWord_1822757 prefixEnd_1822757 935950457347430188554799 := by
  unfold tailWord_1822757
  simp only [CollatzResearch.WordTrace]
  refine ⟨66481409457470165956682525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44320939638313443971121683 66481409457470165956682525)
  ·
    refine ⟨24930528546551312233755947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66481409457470165956682525 24930528546551312233755947)
    ·
      refine ⟨37395792819826968350633921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24930528546551312233755947 37395792819826968350633921)
      ·
        refine ⟨28046844614870226262975441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37395792819826968350633921 28046844614870226262975441)
        ·
          refine ⟨21035133461152669697231581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28046844614870226262975441 21035133461152669697231581)
          ·
            refine ⟨7888175047932251136461843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21035133461152669697231581 7888175047932251136461843)
            ·
              refine ⟨11832262571898376704692765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7888175047932251136461843 11832262571898376704692765)
              ·
                refine ⟨4437098464461891264259787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11832262571898376704692765 4437098464461891264259787)
                ·
                  refine ⟨6655647696692836896389681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437098464461891264259787 6655647696692836896389681)
                  ·
                    refine ⟨4991735772519627672292261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655647696692836896389681 4991735772519627672292261)
                    ·
                      refine ⟨935950457347430188554799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4991735772519627672292261 935950457347430188554799)
                      ·
                        rfl

theorem cell23_1822757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_1822757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822757 prefixEnd_1822757 := by exact prefixLift 1822757
  have htrace : WordTrace (prefixWord ++ tailWord_1822757) baseStart_1822757 baseEnd_1822757 := by
    simpa [prefixWord, tailWord_1822757, baseEnd_1822757] using wordTrace_append hprefix tailTrace_1822757
  have hstable : (prefixWord ++ tailWord_1822757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822757).length < 2 ^ (prefixWord ++ tailWord_1822757).sum := by decide
  have hdescent : baseEnd_1822757 < baseStart_1822757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822774 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1822774 : Nat := 118140960795 + 1822774 * 2 ^ 59
def prefixEnd_1822774 : Nat := 4983230072969 + 3 ^ 40 * 1822774 * 2
def baseEnd_1822774 : Nat := 935959186518556622042221

theorem tailTrace_1822774 : CollatzResearch.WordTrace tailWord_1822774 prefixEnd_1822774 935959186518556622042221 := by
  unfold tailWord_1822774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155126843650536116253211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44321352998939051906700917 4155126843650536116253211)
  ·
    refine ⟨6232690265475804174379817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155126843650536116253211 6232690265475804174379817)
    ·
      refine ⟨4674517699106853130784863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6232690265475804174379817 4674517699106853130784863)
      ·
        refine ⟨7011776548660279696177295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674517699106853130784863 7011776548660279696177295)
        ·
          refine ⟨10517664822990419544265943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7011776548660279696177295 10517664822990419544265943)
          ·
            refine ⟨15776497234485629316398915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10517664822990419544265943 15776497234485629316398915)
            ·
              refine ⟨23664745851728443974598373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15776497234485629316398915 23664745851728443974598373)
              ·
                refine ⟨4437139847199083245237195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23664745851728443974598373 4437139847199083245237195)
                ·
                  refine ⟨6655709770798624867855793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437139847199083245237195 6655709770798624867855793)
                  ·
                    refine ⟨4991782328098968650891845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655709770798624867855793 4991782328098968650891845)
                    ·
                      refine ⟨935959186518556622042221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4991782328098968650891845 935959186518556622042221)
                      ·
                        rfl

theorem cell23_1822774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1822774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822774 prefixEnd_1822774 := by exact prefixLift 1822774
  have htrace : WordTrace (prefixWord ++ tailWord_1822774) baseStart_1822774 baseEnd_1822774 := by
    simpa [prefixWord, tailWord_1822774, baseEnd_1822774] using wordTrace_append hprefix tailTrace_1822774
  have hstable : (prefixWord ++ tailWord_1822774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822774).length < 2 ^ (prefixWord ++ tailWord_1822774).sum := by decide
  have hdescent : baseEnd_1822774 < baseStart_1822774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822818 : List Nat := [3, 3, 2, 2, 3, 1, 2, 7]
def baseStart_1822818 : Nat := 118140960795 + 1822818 * 2 ^ 59
def prefixEnd_1822818 : Nat := 4983230072969 + 3 ^ 40 * 1822818 * 2
def baseEnd_1822818 : Nat := 34665991839531646292297

theorem tailTrace_1822818 : CollatzResearch.WordTrace tailWord_1822818 prefixEnd_1822818 34665991839531646292297 := by
  unfold tailWord_1822818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16620908577562293343663277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44322422873499448916435405 16620908577562293343663277)
  ·
    refine ⟨6232840716585860003873729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16620908577562293343663277 6232840716585860003873729)
    ·
      refine ⟨4674630537439395002905297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6232840716585860003873729 4674630537439395002905297)
      ·
        refine ⟨3505972903079546252178973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4674630537439395002905297 3505972903079546252178973)
        ·
          refine ⟨1314739838654829844567115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3505972903079546252178973 1314739838654829844567115)
          ·
            refine ⟨1972109757982244766850673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314739838654829844567115 1972109757982244766850673)
            ·
              refine ⟨1479082318486683575138005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972109757982244766850673 1479082318486683575138005)
              ·
                refine ⟨34665991839531646292297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1479082318486683575138005 34665991839531646292297)
                ·
                  rfl

theorem cell23_1822818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 7].length) (baseStart_1822818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822818 prefixEnd_1822818 := by exact prefixLift 1822818
  have htrace : WordTrace (prefixWord ++ tailWord_1822818) baseStart_1822818 baseEnd_1822818 := by
    simpa [prefixWord, tailWord_1822818, baseEnd_1822818] using wordTrace_append hprefix tailTrace_1822818
  have hstable : (prefixWord ++ tailWord_1822818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822818).length < 2 ^ (prefixWord ++ tailWord_1822818).sum := by decide
  have hdescent : baseEnd_1822818 < baseStart_1822818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822821 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 1, 3, 2]
def baseStart_1822821 : Nat := 118140960795 + 1822821 * 2 ^ 59
def prefixEnd_1822821 : Nat := 4983230072969 + 3 ^ 40 * 1822821 * 2
def baseEnd_1822821 : Nat := 935983320109317938154505

theorem tailTrace_1822821 : CollatzResearch.WordTrace tailWord_1822821 prefixEnd_1822821 935983320109317938154505 := by
  unfold tailWord_1822821
  simp only [CollatzResearch.WordTrace]
  refine ⟨66483743729238304887012317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44322495819492203258008211 66483743729238304887012317)
  ·
    refine ⟨24931403898464364332629619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66483743729238304887012317 24931403898464364332629619)
    ·
      refine ⟨37397105847696546498944429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24931403898464364332629619 37397105847696546498944429)
      ·
        refine ⟨14023914692886204937104161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37397105847696546498944429 14023914692886204937104161)
        ·
          refine ⟨10517936019664653702828121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14023914692886204937104161 10517936019664653702828121)
          ·
            refine ⟨7888452014748490277121091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10517936019664653702828121 7888452014748490277121091)
            ·
              refine ⟨11832678022122735415681637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7888452014748490277121091 11832678022122735415681637)
              ·
                refine ⟨2218627129148012890440307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11832678022122735415681637 2218627129148012890440307)
                ·
                  refine ⟨3327940693722019335660461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218627129148012890440307 3327940693722019335660461)
                  ·
                    refine ⟨1247977760145757250872673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327940693722019335660461 1247977760145757250872673)
                    ·
                      refine ⟨935983320109317938154505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247977760145757250872673 935983320109317938154505)
                      ·
                        rfl

theorem cell23_1822821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_1822821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822821 prefixEnd_1822821 := by exact prefixLift 1822821
  have htrace : WordTrace (prefixWord ++ tailWord_1822821) baseStart_1822821 baseEnd_1822821 := by
    simpa [prefixWord, tailWord_1822821, baseEnd_1822821] using wordTrace_append hprefix tailTrace_1822821
  have hstable : (prefixWord ++ tailWord_1822821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822821).length < 2 ^ (prefixWord ++ tailWord_1822821).sum := by decide
  have hdescent : baseEnd_1822821 < baseStart_1822821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822838 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1822838 : Nat := 118140960795 + 1822838 * 2 ^ 59
def prefixEnd_1822838 : Nat := 4983230072969 + 3 ^ 40 * 1822838 * 2
def baseEnd_1822838 : Nat := 935992049280444371641927

theorem tailTrace_1822838 : CollatzResearch.WordTrace tailWord_1822838 prefixEnd_1822838 935992049280444371641927 := by
  unfold tailWord_1822838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155272735636044799398823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44322909180117811193587445 4155272735636044799398823)
  ·
    refine ⟨6232909103454067199098235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155272735636044799398823 6232909103454067199098235)
    ·
      refine ⟨9349363655181100798647353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6232909103454067199098235 9349363655181100798647353)
      ·
        refine ⟨7012022741385825598985515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9349363655181100798647353 7012022741385825598985515)
        ·
          refine ⟨10518034112078738398478273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7012022741385825598985515 10518034112078738398478273)
          ·
            refine ⟨7888525584059053798858705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10518034112078738398478273 7888525584059053798858705)
            ·
              refine ⟨5916394188044290349144029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888525584059053798858705 5916394188044290349144029)
              ·
                refine ⟨2218647820516608880929011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5916394188044290349144029 2218647820516608880929011)
                ·
                  refine ⟨3327971730774913321393517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218647820516608880929011 3327971730774913321393517)
                  ·
                    refine ⟨1247989399040592495522569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3327971730774913321393517 1247989399040592495522569)
                    ·
                      refine ⟨935992049280444371641927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247989399040592495522569 935992049280444371641927)
                      ·
                        rfl

theorem cell23_1822838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1822838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822838 prefixEnd_1822838 := by exact prefixLift 1822838
  have htrace : WordTrace (prefixWord ++ tailWord_1822838) baseStart_1822838 baseEnd_1822838 := by
    simpa [prefixWord, tailWord_1822838, baseEnd_1822838] using wordTrace_append hprefix tailTrace_1822838
  have hstable : (prefixWord ++ tailWord_1822838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822838).length < 2 ^ (prefixWord ++ tailWord_1822838).sum := by decide
  have hdescent : baseEnd_1822838 < baseStart_1822838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822851 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 4, 2, 2]
def baseStart_1822851 : Nat := 118140960795 + 1822851 * 2 ^ 59
def prefixEnd_1822851 : Nat := 4983230072969 + 3 ^ 40 * 1822851 * 2
def baseEnd_1822851 : Nat := 935998724528952820779367

theorem tailTrace_1822851 : CollatzResearch.WordTrace tailWord_1822851 prefixEnd_1822851 935998724528952820779367 := by
  unfold tailWord_1822851
  simp only [CollatzResearch.WordTrace]
  refine ⟨66484837919129620010604407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44323225279419746673736271 66484837919129620010604407)
  ·
    refine ⟨99727256878694430015906611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66484837919129620010604407 99727256878694430015906611)
    ·
      refine ⟨149590885318041645023859917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99727256878694430015906611 149590885318041645023859917)
      ·
        refine ⟨56096581994265616883947469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149590885318041645023859917 56096581994265616883947469)
        ·
          refine ⟨21036218247849606331480301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56096581994265616883947469 21036218247849606331480301)
          ·
            refine ⟨7888581842943602374305113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21036218247849606331480301 7888581842943602374305113)
            ·
              refine ⟨5916436382207701780728835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888581842943602374305113 5916436382207701780728835)
              ·
                refine ⟨8874654573311552671093253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916436382207701780728835 8874654573311552671093253)
                ·
                  refine ⟨1663997732495916125829985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8874654573311552671093253 1663997732495916125829985)
                  ·
                    refine ⟨1247998299371937094372489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1663997732495916125829985 1247998299371937094372489)
                    ·
                      refine ⟨935998724528952820779367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1247998299371937094372489 935998724528952820779367)
                      ·
                        rfl

theorem cell23_1822851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_1822851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822851 prefixEnd_1822851 := by exact prefixLift 1822851
  have htrace : WordTrace (prefixWord ++ tailWord_1822851) baseStart_1822851 baseEnd_1822851 := by
    simpa [prefixWord, tailWord_1822851, baseEnd_1822851] using wordTrace_append hprefix tailTrace_1822851
  have hstable : (prefixWord ++ tailWord_1822851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822851).length < 2 ^ (prefixWord ++ tailWord_1822851).sum := by decide
  have hdescent : baseEnd_1822851 < baseStart_1822851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822862 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_1822862 : Nat := 118140960795 + 1822862 * 2 ^ 59
def prefixEnd_1822862 : Nat := 4983230072969 + 3 ^ 40 * 1822862 * 2
def baseEnd_1822862 : Nat := 936004372816152277741817

theorem tailTrace_1822862 : CollatzResearch.WordTrace tailWord_1822862 prefixEnd_1822862 936004372816152277741817 := by
  unfold tailWord_1822862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310654890261221111156855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44323492748059845926169893 8310654890261221111156855)
  ·
    refine ⟨12465982335391831666735283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8310654890261221111156855 12465982335391831666735283)
    ·
      refine ⟨18698973503087747500102925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12465982335391831666735283 18698973503087747500102925)
      ·
        refine ⟨7012115063657905312538597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18698973503087747500102925 7012115063657905312538597)
        ·
          refine ⟨1314771574435857246100987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7012115063657905312538597 1314771574435857246100987)
          ·
            refine ⟨1972157361653785869151481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314771574435857246100987 1972157361653785869151481)
            ·
              refine ⟨1479118021240339401863611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972157361653785869151481 1479118021240339401863611)
              ·
                refine ⟨2218677031860509102795417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479118021240339401863611 2218677031860509102795417)
                ·
                  refine ⟨1664007773895381827096563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218677031860509102795417 1664007773895381827096563)
                  ·
                    refine ⟨2496011660843072740644845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1664007773895381827096563 2496011660843072740644845)
                    ·
                      refine ⟨936004372816152277741817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496011660843072740644845 936004372816152277741817)
                      ·
                        rfl

theorem cell23_1822862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_1822862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822862 prefixEnd_1822862 := by exact prefixLift 1822862
  have htrace : WordTrace (prefixWord ++ tailWord_1822862) baseStart_1822862 baseEnd_1822862 := by
    simpa [prefixWord, tailWord_1822862, baseEnd_1822862] using wordTrace_append hprefix tailTrace_1822862
  have hstable : (prefixWord ++ tailWord_1822862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822862).length < 2 ^ (prefixWord ++ tailWord_1822862).sum := by decide
  have hdescent : baseEnd_1822862 < baseStart_1822862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822867 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 3]
def baseStart_1822867 : Nat := 118140960795 + 1822867 * 2 ^ 59
def prefixEnd_1822867 : Nat := 4983230072969 + 3 ^ 40 * 1822867 * 2
def baseEnd_1822867 : Nat := 936006940219424758179293

theorem tailTrace_1822867 : CollatzResearch.WordTrace tailWord_1822867 prefixEnd_1822867 936006940219424758179293 := by
  unfold tailWord_1822867
  simp only [CollatzResearch.WordTrace]
  refine ⟨66485421487071654743186855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44323614324714436495457903 66485421487071654743186855)
  ·
    refine ⟨99728132230607482114780283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66485421487071654743186855 99728132230607482114780283)
    ·
      refine ⟨149592198345911223172170425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99728132230607482114780283 149592198345911223172170425)
      ·
        refine ⟨112194148759433417379127819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149592198345911223172170425 112194148759433417379127819)
        ·
          refine ⟨168291223139150126068691729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112194148759433417379127819 168291223139150126068691729)
          ·
            refine ⟨126218417354362594551518797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168291223139150126068691729 126218417354362594551518797)
            ·
              refine ⟨47331906507885972956819549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126218417354362594551518797 47331906507885972956819549)
              ·
                refine ⟨17749464940457239858807331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47331906507885972956819549 17749464940457239858807331)
                ·
                  refine ⟨26624197410685859788210997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17749464940457239858807331 26624197410685859788210997)
                  ·
                    refine ⟨2496018507251799355144781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26624197410685859788210997 2496018507251799355144781)
                    ·
                      refine ⟨936006940219424758179293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496018507251799355144781 936006940219424758179293)
                      ·
                        rfl

theorem cell23_1822867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_1822867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822867 prefixEnd_1822867 := by exact prefixLift 1822867
  have htrace : WordTrace (prefixWord ++ tailWord_1822867) baseStart_1822867 baseEnd_1822867 := by
    simpa [prefixWord, tailWord_1822867, baseEnd_1822867] using wordTrace_append hprefix tailTrace_1822867
  have hstable : (prefixWord ++ tailWord_1822867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822867).length < 2 ^ (prefixWord ++ tailWord_1822867).sum := by decide
  have hdescent : baseEnd_1822867 < baseStart_1822867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822941 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1822941 : Nat := 118140960795 + 1822941 * 2 ^ 59
def prefixEnd_1822941 : Nat := 4983230072969 + 3 ^ 40 * 1822941 * 2
def baseEnd_1822941 : Nat := 936044937787857468653953

theorem tailTrace_1822941 : CollatzResearch.WordTrace tailWord_1822941 prefixEnd_1822941 936044937787857468653953 := by
  unfold tailWord_1822941
  simp only [CollatzResearch.WordTrace]
  refine ⟨66488120488803565381380677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44325413659202376920920451 66488120488803565381380677)
  ·
    refine ⟨12466522591650668509008877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66488120488803565381380677 12466522591650668509008877)
    ·
      refine ⟨4674945971869000690878329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12466522591650668509008877 4674945971869000690878329)
      ·
        refine ⟨3506209478901750518158747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4674945971869000690878329 3506209478901750518158747)
        ·
          refine ⟨5259314218352625777238121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506209478901750518158747 5259314218352625777238121)
          ·
            refine ⟨3944485663764469332928591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5259314218352625777238121 3944485663764469332928591)
            ·
              refine ⟨5916728495646703999392887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944485663764469332928591 5916728495646703999392887)
              ·
                refine ⟨8875092743470055999089331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916728495646703999392887 8875092743470055999089331)
                ·
                  refine ⟨13312639115205083998633997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8875092743470055999089331 13312639115205083998633997)
                  ·
                    refine ⟨4992239668201906499487749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13312639115205083998633997 4992239668201906499487749)
                    ·
                      refine ⟨936044937787857468653953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4992239668201906499487749 936044937787857468653953)
                      ·
                        rfl

theorem cell23_1822941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1822941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822941 prefixEnd_1822941 := by exact prefixLift 1822941
  have htrace : WordTrace (prefixWord ++ tailWord_1822941) baseStart_1822941 baseEnd_1822941 := by
    simpa [prefixWord, tailWord_1822941, baseEnd_1822941] using wordTrace_append hprefix tailTrace_1822941
  have hstable : (prefixWord ++ tailWord_1822941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822941).length < 2 ^ (prefixWord ++ tailWord_1822941).sum := by decide
  have hdescent : baseEnd_1822941 < baseStart_1822941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822944 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3]
def baseStart_1822944 : Nat := 118140960795 + 1822944 * 2 ^ 59
def prefixEnd_1822944 : Nat := 4983230072969 + 3 ^ 40 * 1822944 * 2
def baseEnd_1822944 : Nat := 936046478229820956916439

theorem tailTrace_1822944 : CollatzResearch.WordTrace tailWord_1822944 prefixEnd_1822944 936046478229820956916439 := by
  unfold tailWord_1822944
  simp only [CollatzResearch.WordTrace]
  refine ⟨33244114953896348446869943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44325486605195131262493257 33244114953896348446869943)
  ·
    refine ⟨49866172430844522670304915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33244114953896348446869943 49866172430844522670304915)
    ·
      refine ⟨74799258646266784005457373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49866172430844522670304915 74799258646266784005457373)
      ·
        refine ⟨28049721992350044002046515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74799258646266784005457373 28049721992350044002046515)
        ·
          refine ⟨42074582988525066003069773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28049721992350044002046515 42074582988525066003069773)
          ·
            refine ⟨15777968620696899751151165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42074582988525066003069773 15777968620696899751151165)
            ·
              refine ⟨5916738232761337406681687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15777968620696899751151165 5916738232761337406681687)
              ·
                refine ⟨8875107349142006110022531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916738232761337406681687 8875107349142006110022531)
                ·
                  refine ⟨13312661023713009165033797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8875107349142006110022531 13312661023713009165033797)
                  ·
                    refine ⟨2496123941946189218443837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13312661023713009165033797 2496123941946189218443837)
                    ·
                      refine ⟨936046478229820956916439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496123941946189218443837 936046478229820956916439)
                      ·
                        rfl

theorem cell23_1822944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_1822944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1822944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1822944 prefixEnd_1822944 := by exact prefixLift 1822944
  have htrace : WordTrace (prefixWord ++ tailWord_1822944) baseStart_1822944 baseEnd_1822944 := by
    simpa [prefixWord, tailWord_1822944, baseEnd_1822944] using wordTrace_append hprefix tailTrace_1822944
  have hstable : (prefixWord ++ tailWord_1822944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822944).length < 2 ^ (prefixWord ++ tailWord_1822944).sum := by decide
  have hdescent : baseEnd_1822944 < baseStart_1822944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823002 : List Nat := [3, 1, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_1823002 : Nat := 118140960795 + 1823002 * 2 ^ 59
def prefixEnd_1823002 : Nat := 4983230072969 + 3 ^ 40 * 1823002 * 2
def baseEnd_1823002 : Nat := 312025420035927243330391

theorem tailTrace_1823002 : CollatzResearch.WordTrace tailWord_1823002 prefixEnd_1823002 312025420035927243330391 := by
  unfold tailWord_1823002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16622586335395643199837815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44326896894388381866234173 16622586335395643199837815)
  ·
    refine ⟨24933879503093464799756723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16622586335395643199837815 24933879503093464799756723)
    ·
      refine ⟨37400819254640197199635085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24933879503093464799756723 37400819254640197199635085)
      ·
        refine ⟨14025307220490073949863157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37400819254640197199635085 14025307220490073949863157)
        ·
          refine ⟨1314872551920944432799671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14025307220490073949863157 1314872551920944432799671)
          ·
            refine ⟨1972308827881416649199507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314872551920944432799671 1972308827881416649199507)
            ·
              refine ⟨2958463241822124973799261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972308827881416649199507 2958463241822124973799261)
              ·
                refine ⟨1109423715683296865174723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2958463241822124973799261 1109423715683296865174723)
                ·
                  refine ⟨1664135573524945297762085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109423715683296865174723 1664135573524945297762085)
                  ·
                    refine ⟨312025420035927243330391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1664135573524945297762085 312025420035927243330391)
                    ·
                      rfl

theorem cell23_1823002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_1823002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823002 prefixEnd_1823002 := by exact prefixLift 1823002
  have htrace : WordTrace (prefixWord ++ tailWord_1823002) baseStart_1823002 baseEnd_1823002 := by
    simpa [prefixWord, tailWord_1823002, baseEnd_1823002] using wordTrace_append hprefix tailTrace_1823002
  have hstable : (prefixWord ++ tailWord_1823002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823002).length < 2 ^ (prefixWord ++ tailWord_1823002).sum := by decide
  have hdescent : baseEnd_1823002 < baseStart_1823002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823025 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_1823025 : Nat := 118140960795 + 1823025 * 2 ^ 59
def prefixEnd_1823025 : Nat := 4983230072969 + 3 ^ 40 * 1823025 * 2
def baseEnd_1823025 : Nat := 936088070162835140003567

theorem tailTrace_1823025 : CollatzResearch.WordTrace tailWord_1823025 prefixEnd_1823025 936088070162835140003567 := by
  unfold tailWord_1823025
  simp only [CollatzResearch.WordTrace]
  refine ⟨66491184220499247727438529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44327456146999498484959019 66491184220499247727438529)
  ·
    refine ⟨49868388165374435795578897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66491184220499247727438529 49868388165374435795578897)
    ·
      refine ⟨37401291124030826846684173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49868388165374435795578897 37401291124030826846684173)
      ·
        refine ⟨14025484171511560067506565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37401291124030826846684173 14025484171511560067506565)
        ·
          refine ⟨2629778282158417512657481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14025484171511560067506565 2629778282158417512657481)
          ·
            refine ⟨1972333711618813134493111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2629778282158417512657481 1972333711618813134493111)
            ·
              refine ⟨2958500567428219701739667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972333711618813134493111 2958500567428219701739667)
              ·
                refine ⟨4437750851142329552609501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958500567428219701739667 4437750851142329552609501)
                ·
                  refine ⟨1664156569178373582228563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4437750851142329552609501 1664156569178373582228563)
                  ·
                    refine ⟨2496234853767560373342845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1664156569178373582228563 2496234853767560373342845)
                    ·
                      refine ⟨936088070162835140003567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496234853767560373342845 936088070162835140003567)
                      ·
                        rfl

theorem cell23_1823025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_1823025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823025 prefixEnd_1823025 := by exact prefixLift 1823025
  have htrace : WordTrace (prefixWord ++ tailWord_1823025) baseStart_1823025 baseEnd_1823025 := by
    simpa [prefixWord, tailWord_1823025, baseEnd_1823025] using wordTrace_append hprefix tailTrace_1823025
  have hstable : (prefixWord ++ tailWord_1823025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823025).length < 2 ^ (prefixWord ++ tailWord_1823025).sum := by decide
  have hdescent : baseEnd_1823025 < baseStart_1823025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823048 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_1823048 : Nat := 118140960795 + 1823048 * 2 ^ 59
def prefixEnd_1823048 : Nat := 4983230072969 + 3 ^ 40 * 1823048 * 2
def baseEnd_1823048 : Nat := 936099880217888550015961

theorem tailTrace_1823048 : CollatzResearch.WordTrace tailWord_1823048 prefixEnd_1823048 936099880217888550015961 := by
  unfold tailWord_1823048
  simp only [CollatzResearch.WordTrace]
  refine ⟨33246011549707961327762899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44328015399610615103683865 33246011549707961327762899)
  ·
    refine ⟨49869017324561941991644349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33246011549707961327762899 49869017324561941991644349)
    ·
      refine ⟨18700881496710728246866631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49869017324561941991644349 18700881496710728246866631)
      ·
        refine ⟨28051322245066092370299947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18700881496710728246866631 28051322245066092370299947)
        ·
          refine ⟨42076983367599138555449921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28051322245066092370299947 42076983367599138555449921)
          ·
            refine ⟨31557737525699353916587441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42076983367599138555449921 31557737525699353916587441)
            ·
              refine ⟨23668303144274515437440581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31557737525699353916587441 23668303144274515437440581)
              ·
                refine ⟨4437806839551471644520109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23668303144274515437440581 4437806839551471644520109)
                ·
                  refine ⟨1664177564831801866695041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4437806839551471644520109 1664177564831801866695041)
                  ·
                    refine ⟨1248133173623851400021281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1664177564831801866695041 1248133173623851400021281)
                    ·
                      refine ⟨936099880217888550015961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248133173623851400021281 936099880217888550015961)
                      ·
                        rfl

theorem cell23_1823048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_1823048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823048 prefixEnd_1823048 := by exact prefixLift 1823048
  have htrace : WordTrace (prefixWord ++ tailWord_1823048) baseStart_1823048 baseEnd_1823048 := by
    simpa [prefixWord, tailWord_1823048, baseEnd_1823048] using wordTrace_append hprefix tailTrace_1823048
  have hstable : (prefixWord ++ tailWord_1823048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823048).length < 2 ^ (prefixWord ++ tailWord_1823048).sum := by decide
  have hdescent : baseEnd_1823048 < baseStart_1823048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823051 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 3]
def baseStart_1823051 : Nat := 118140960795 + 1823051 * 2 ^ 59
def prefixEnd_1823051 : Nat := 4983230072969 + 3 ^ 40 * 1823051 * 2
def baseEnd_1823051 : Nat := 936101420659852038278447

theorem tailTrace_1823051 : CollatzResearch.WordTrace tailWord_1823051 prefixEnd_1823051 936101420659852038278447 := by
  unfold tailWord_1823051
  simp only [CollatzResearch.WordTrace]
  refine ⟨66492132518405054167885007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44328088345603369445256671 66492132518405054167885007)
  ·
    refine ⟨99738198777607581251827511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66492132518405054167885007 99738198777607581251827511)
    ·
      refine ⟨149607298166411371877741267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99738198777607581251827511 149607298166411371877741267)
      ·
        refine ⟨224410947249617057816611901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149607298166411371877741267 224410947249617057816611901)
        ·
          refine ⟨84154105218606396681229463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224410947249617057816611901 84154105218606396681229463)
          ·
            refine ⟨126231157827909595021844195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84154105218606396681229463 126231157827909595021844195)
            ·
              refine ⟨189346736741864392532766293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126231157827909595021844195 189346736741864392532766293)
              ·
                refine ⟨2218907071193723349993355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 189346736741864392532766293 2218907071193723349993355)
                ·
                  refine ⟨3328360606790585024990033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218907071193723349993355 3328360606790585024990033)
                  ·
                    refine ⟨2496270455092938768742525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328360606790585024990033 2496270455092938768742525)
                    ·
                      refine ⟨936101420659852038278447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496270455092938768742525 936101420659852038278447)
                      ·
                        rfl

theorem cell23_1823051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 3].length) (baseStart_1823051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823051 prefixEnd_1823051 := by exact prefixLift 1823051
  have htrace : WordTrace (prefixWord ++ tailWord_1823051) baseStart_1823051 baseEnd_1823051 := by
    simpa [prefixWord, tailWord_1823051, baseEnd_1823051] using wordTrace_append hprefix tailTrace_1823051
  have hstable : (prefixWord ++ tailWord_1823051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823051).length < 2 ^ (prefixWord ++ tailWord_1823051).sum := by decide
  have hdescent : baseEnd_1823051 < baseStart_1823051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823065 : List Nat := [1, 2, 1, 2, 2, 2, 1, 7, 1, 2, 2]
def baseStart_1823065 : Nat := 118140960795 + 1823065 * 2 ^ 59
def prefixEnd_1823065 : Nat := 4983230072969 + 3 ^ 40 * 1823065 * 2
def baseEnd_1823065 : Nat := 936108609389014983503383

theorem tailTrace_1823065 : CollatzResearch.WordTrace tailWord_1823065 prefixEnd_1823065 936108609389014983503383 := by
  unfold tailWord_1823065
  simp only [CollatzResearch.WordTrace]
  refine ⟨66492643140354334558894649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44328428760236223039263099 66492643140354334558894649)
  ·
    refine ⟨49869482355265750919170987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66492643140354334558894649 49869482355265750919170987)
    ·
      refine ⟨74804223532898626378756481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49869482355265750919170987 74804223532898626378756481)
      ·
        refine ⟨56103167649673969784067361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74804223532898626378756481 56103167649673969784067361)
        ·
          refine ⟨42077375737255477338050521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56103167649673969784067361 42077375737255477338050521)
          ·
            refine ⟨31558031802941608003537891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42077375737255477338050521 31558031802941608003537891)
            ·
              refine ⟨47337047704412412005306837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31558031802941608003537891 47337047704412412005306837)
              ·
                refine ⟨1109462055572165906374379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47337047704412412005306837 1109462055572165906374379)
                ·
                  refine ⟨1664193083358248859561569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109462055572165906374379 1664193083358248859561569)
                  ·
                    refine ⟨1248144812518686644671177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1664193083358248859561569 1248144812518686644671177)
                    ·
                      refine ⟨936108609389014983503383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248144812518686644671177 936108609389014983503383)
                      ·
                        rfl

theorem cell23_1823065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_1823065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823065 prefixEnd_1823065 := by exact prefixLift 1823065
  have htrace : WordTrace (prefixWord ++ tailWord_1823065) baseStart_1823065 baseEnd_1823065 := by
    simpa [prefixWord, tailWord_1823065, baseEnd_1823065] using wordTrace_append hprefix tailTrace_1823065
  have hstable : (prefixWord ++ tailWord_1823065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823065).length < 2 ^ (prefixWord ++ tailWord_1823065).sum := by decide
  have hdescent : baseEnd_1823065 < baseStart_1823065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823070 : List Nat := [4, 4, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1823070 : Nat := 118140960795 + 1823070 * 2 ^ 59
def prefixEnd_1823070 : Nat := 4983230072969 + 3 ^ 40 * 1823070 * 2
def baseEnd_1823070 : Nat := 312037058930762487980287

theorem tailTrace_1823070 : CollatzResearch.WordTrace tailWord_1823070 prefixEnd_1823070 312037058930762487980287 := by
  unfold tailWord_1823070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311603188167027551603333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44328550336890813608551109 8311603188167027551603333)
  ·
    refine ⟨1558425597781317665925625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8311603188167027551603333 1558425597781317665925625)
    ·
      refine ⟨1168819198335988249444219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1558425597781317665925625 1168819198335988249444219)
      ·
        refine ⟨1753228797503982374166329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168819198335988249444219 1753228797503982374166329)
        ·
          refine ⟨1314921598127986780624747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753228797503982374166329 1314921598127986780624747)
          ·
            refine ⟨1972382397191980170937121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314921598127986780624747 1972382397191980170937121)
            ·
              refine ⟨1479286797893985128202841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972382397191980170937121 1479286797893985128202841)
              ·
                refine ⟨1109465098420488846152131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479286797893985128202841 1109465098420488846152131)
                ·
                  refine ⟨1664197647630733269228197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109465098420488846152131 1664197647630733269228197)
                  ·
                    refine ⟨312037058930762487980287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1664197647630733269228197 312037058930762487980287)
                    ·
                      rfl

theorem cell23_1823070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1823070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823070 prefixEnd_1823070 := by exact prefixLift 1823070
  have htrace : WordTrace (prefixWord ++ tailWord_1823070) baseStart_1823070 baseEnd_1823070 := by
    simpa [prefixWord, tailWord_1823070, baseEnd_1823070] using wordTrace_append hprefix tailTrace_1823070
  have hstable : (prefixWord ++ tailWord_1823070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823070).length < 2 ^ (prefixWord ++ tailWord_1823070).sum := by decide
  have hdescent : baseEnd_1823070 < baseStart_1823070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823108 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_1823108 : Nat := 118140960795 + 1823108 * 2 ^ 59
def prefixEnd_1823108 : Nat := 4983230072969 + 3 ^ 40 * 1823108 * 2
def baseEnd_1823108 : Nat := 936130689057158315265685

theorem tailTrace_1823108 : CollatzResearch.WordTrace tailWord_1823108 prefixEnd_1823108 936130689057158315265685 := by
  unfold tailWord_1823108
  simp only [CollatzResearch.WordTrace]
  refine ⟨33247105739599276451354989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44329474319465701935139985 33247105739599276451354989)
  ·
    refine ⟨12467664652349728669258121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33247105739599276451354989 12467664652349728669258121)
    ·
      refine ⟨9350748489262296501943591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12467664652349728669258121 9350748489262296501943591)
      ·
        refine ⟨14026122733893444752915387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9350748489262296501943591 14026122733893444752915387)
        ·
          refine ⟨21039184100840167129373081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14026122733893444752915387 21039184100840167129373081)
          ·
            refine ⟨15779388075630125347029811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21039184100840167129373081 15779388075630125347029811)
            ·
              refine ⟨23669082113445188020544717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15779388075630125347029811 23669082113445188020544717)
              ·
                refine ⟨8875905792541945507704269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23669082113445188020544717 8875905792541945507704269)
                ·
                  refine ⟨3328464672203229565389101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8875905792541945507704269 3328464672203229565389101)
                  ·
                    refine ⟨1248174252076211087020913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3328464672203229565389101 1248174252076211087020913)
                    ·
                      refine ⟨936130689057158315265685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248174252076211087020913 936130689057158315265685)
                      ·
                        rfl

theorem cell23_1823108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_1823108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823108 prefixEnd_1823108 := by exact prefixLift 1823108
  have htrace : WordTrace (prefixWord ++ tailWord_1823108) baseStart_1823108 baseEnd_1823108 := by
    simpa [prefixWord, tailWord_1823108, baseEnd_1823108] using wordTrace_append hprefix tailTrace_1823108
  have hstable : (prefixWord ++ tailWord_1823108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823108).length < 2 ^ (prefixWord ++ tailWord_1823108).sum := by decide
  have hdescent : baseEnd_1823108 < baseStart_1823108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823126 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1823126 : Nat := 118140960795 + 1823126 * 2 ^ 59
def prefixEnd_1823126 : Nat := 4983230072969 + 3 ^ 40 * 1823126 * 2
def baseEnd_1823126 : Nat := 312046643902979748280201

theorem tailTrace_1823126 : CollatzResearch.WordTrace tailWord_1823126 prefixEnd_1823126 312046643902979748280201 := by
  unfold tailWord_1823126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155929249570833873554077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44329911995422227984576821 4155929249570833873554077)
  ·
    refine ⟨1558473468589062702582779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4155929249570833873554077 1558473468589062702582779)
    ·
      refine ⟨2337710202883594053874169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558473468589062702582779 2337710202883594053874169)
      ·
        refine ⟨1753282652162695540405627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2337710202883594053874169 1753282652162695540405627)
        ·
          refine ⟨2629923978244043310608441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753282652162695540405627 2629923978244043310608441)
          ·
            refine ⟨1972442983683032482956331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2629923978244043310608441 1972442983683032482956331)
            ·
              refine ⟨2958664475524548724434497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972442983683032482956331 2958664475524548724434497)
              ·
                refine ⟨2218998356643411543325873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2958664475524548724434497 2218998356643411543325873)
                ·
                  refine ⟨1664248767482558657494405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218998356643411543325873 1664248767482558657494405)
                  ·
                    refine ⟨312046643902979748280201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1664248767482558657494405 312046643902979748280201)
                    ·
                      rfl

theorem cell23_1823126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1823126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823126 prefixEnd_1823126 := by exact prefixLift 1823126
  have htrace : WordTrace (prefixWord ++ tailWord_1823126) baseStart_1823126 baseEnd_1823126 := by
    simpa [prefixWord, tailWord_1823126, baseEnd_1823126] using wordTrace_append hprefix tailTrace_1823126
  have hstable : (prefixWord ++ tailWord_1823126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823126).length < 2 ^ (prefixWord ++ tailWord_1823126).sum := by decide
  have hdescent : baseEnd_1823126 < baseStart_1823126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823149 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_1823149 : Nat := 118140960795 + 1823149 * 2 ^ 59
def prefixEnd_1823149 : Nat := 4983230072969 + 3 ^ 40 * 1823149 * 2
def baseEnd_1823149 : Nat := 936151741763992654852997

theorem tailTrace_1823149 : CollatzResearch.WordTrace tailWord_1823149 prefixEnd_1823149 936151741763992654852997 := by
  unfold tailWord_1823149
  simp only [CollatzResearch.WordTrace]
  refine ⟨66495706872050016904952501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44330471248033344603301667 66495706872050016904952501)
  ·
    refine ⟨6233972519254689084839297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66495706872050016904952501 6233972519254689084839297)
    ·
      refine ⟨4675479389441016813629473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6233972519254689084839297 4675479389441016813629473)
      ·
        refine ⟨3506609542080762610222105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4675479389441016813629473 3506609542080762610222105)
        ·
          refine ⟨2629957156560571957666579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3506609542080762610222105 2629957156560571957666579)
          ·
            refine ⟨3944935734840857936499869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629957156560571957666579 3944935734840857936499869)
            ·
              refine ⟨1479350900565321726187451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3944935734840857936499869 1479350900565321726187451)
              ·
                refine ⟨2219026350847982589281177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479350900565321726187451 2219026350847982589281177)
                ·
                  refine ⟨1664269763135986941960883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2219026350847982589281177 1664269763135986941960883)
                  ·
                    refine ⟨2496404644703980412941325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1664269763135986941960883 2496404644703980412941325)
                    ·
                      refine ⟨936151741763992654852997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496404644703980412941325 936151741763992654852997)
                      ·
                        rfl

theorem cell23_1823149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_1823149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823149 prefixEnd_1823149 := by exact prefixLift 1823149
  have htrace : WordTrace (prefixWord ++ tailWord_1823149) baseStart_1823149 baseEnd_1823149 := by
    simpa [prefixWord, tailWord_1823149, baseEnd_1823149] using wordTrace_append hprefix tailTrace_1823149
  have hstable : (prefixWord ++ tailWord_1823149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823149).length < 2 ^ (prefixWord ++ tailWord_1823149).sum := by decide
  have hdescent : baseEnd_1823149 < baseStart_1823149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823161 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 7]
def baseStart_1823161 : Nat := 118140960795 + 1823161 * 2 ^ 59
def prefixEnd_1823161 : Nat := 4983230072969 + 3 ^ 40 * 1823161 * 2
def baseEnd_1823161 : Nat := 104017544836871845322549

theorem tailTrace_1823161 : CollatzResearch.WordTrace tailWord_1823161 prefixEnd_1823161 104017544836871845322549 := by
  unfold tailWord_1823161
  simp only [CollatzResearch.WordTrace]
  refine ⟨66496144548006542954389337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44330763032004361969592891 66496144548006542954389337)
  ·
    refine ⟨49872108411004907215792003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66496144548006542954389337 49872108411004907215792003)
    ·
      refine ⟨74808162616507360823688005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49872108411004907215792003 74808162616507360823688005)
      ·
        refine ⟨14026530490595130154441501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74808162616507360823688005 14026530490595130154441501)
        ·
          refine ⟨5259948933973173807915563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14026530490595130154441501 5259948933973173807915563)
          ·
            refine ⟨7889923400959760711873345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259948933973173807915563 7889923400959760711873345)
            ·
              refine ⟨5917442550719820533905009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889923400959760711873345 5917442550719820533905009)
              ·
                refine ⟨4438081913039865400428757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917442550719820533905009 4438081913039865400428757)
                ·
                  refine ⟨104017544836871845322549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4438081913039865400428757 104017544836871845322549)
                  ·
                    rfl

theorem cell23_1823161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_1823161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823161 prefixEnd_1823161 := by exact prefixLift 1823161
  have htrace : WordTrace (prefixWord ++ tailWord_1823161) baseStart_1823161 baseEnd_1823161 := by
    simpa [prefixWord, tailWord_1823161, baseEnd_1823161] using wordTrace_append hprefix tailTrace_1823161
  have hstable : (prefixWord ++ tailWord_1823161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823161).length < 2 ^ (prefixWord ++ tailWord_1823161).sum := by decide
  have hdescent : baseEnd_1823161 < baseStart_1823161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823201 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1823201 : Nat := 118140960795 + 1823201 * 2 ^ 59
def prefixEnd_1823201 : Nat := 4983230072969 + 3 ^ 40 * 1823201 * 2
def baseEnd_1823201 : Nat := 936178442758026451402757

theorem tailTrace_1823201 : CollatzResearch.WordTrace tailWord_1823201 prefixEnd_1823201 936178442758026451402757 := by
  unfold tailWord_1823201
  simp only [CollatzResearch.WordTrace]
  refine ⟨66497603467861629785845457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44331735645241086523896971 66497603467861629785845457)
  ·
    refine ⟨49873202600896222339384093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66497603467861629785845457 49873202600896222339384093)
    ·
      refine ⟨18702450975336083377269035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49873202600896222339384093 18702450975336083377269035)
      ·
        refine ⟨28053676463004125065903553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18702450975336083377269035 28053676463004125065903553)
        ·
          refine ⟨21040257347253093799427665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28053676463004125065903553 21040257347253093799427665)
          ·
            refine ⟨15780193010439820349570749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21040257347253093799427665 15780193010439820349570749)
            ·
              refine ⟨5917572378914932631089031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15780193010439820349570749 5917572378914932631089031)
              ·
                refine ⟨8876358568372398946633547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917572378914932631089031 8876358568372398946633547)
                ·
                  refine ⟨13314537852558598419950321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8876358568372398946633547 13314537852558598419950321)
                  ·
                    refine ⟨9985903389418948814962741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13314537852558598419950321 9985903389418948814962741)
                    ·
                      refine ⟨936178442758026451402757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9985903389418948814962741 936178442758026451402757)
                      ·
                        rfl

theorem cell23_1823201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1823201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823201 prefixEnd_1823201 := by exact prefixLift 1823201
  have htrace : WordTrace (prefixWord ++ tailWord_1823201) baseStart_1823201 baseEnd_1823201 := by
    simpa [prefixWord, tailWord_1823201, baseEnd_1823201] using wordTrace_append hprefix tailTrace_1823201
  have hstable : (prefixWord ++ tailWord_1823201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823201).length < 2 ^ (prefixWord ++ tailWord_1823201).sum := by decide
  have hdescent : baseEnd_1823201 < baseStart_1823201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823211 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 4]
def baseStart_1823211 : Nat := 118140960795 + 1823211 * 2 ^ 59
def prefixEnd_1823211 : Nat := 4983230072969 + 3 ^ 40 * 1823211 * 2
def baseEnd_1823211 : Nat := 936183577564571412277711

theorem tailTrace_1823211 : CollatzResearch.WordTrace tailWord_1823211 prefixEnd_1823211 936183577564571412277711 := by
  unfold tailWord_1823211
  simp only [CollatzResearch.WordTrace]
  refine ⟨66497968197825401493709487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44331978798550267662472991 66497968197825401493709487)
  ·
    refine ⟨99746952296738102240564231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66497968197825401493709487 99746952296738102240564231)
    ·
      refine ⟨149620428445107153360846347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99746952296738102240564231 149620428445107153360846347)
      ·
        refine ⟨224430642667660730041269521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149620428445107153360846347 224430642667660730041269521)
        ·
          refine ⟨168322982000745547530952141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224430642667660730041269521 168322982000745547530952141)
          ·
            refine ⟨63121118250279580324107053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168322982000745547530952141 63121118250279580324107053)
            ·
              refine ⟨23670419343854842621540145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63121118250279580324107053 23670419343854842621540145)
              ·
                refine ⟨17752814507891131966155109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23670419343854842621540145 17752814507891131966155109)
                ·
                  refine ⟨3328652720229587243654083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17752814507891131966155109 3328652720229587243654083)
                  ·
                    refine ⟨4992979080344380865481125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328652720229587243654083 4992979080344380865481125)
                    ·
                      refine ⟨936183577564571412277711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4992979080344380865481125 936183577564571412277711)
                      ·
                        rfl

theorem cell23_1823211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 4].length) (baseStart_1823211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823211 prefixEnd_1823211 := by exact prefixLift 1823211
  have htrace : WordTrace (prefixWord ++ tailWord_1823211) baseStart_1823211 baseEnd_1823211 := by
    simpa [prefixWord, tailWord_1823211, baseEnd_1823211] using wordTrace_append hprefix tailTrace_1823211
  have hstable : (prefixWord ++ tailWord_1823211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823211).length < 2 ^ (prefixWord ++ tailWord_1823211).sum := by decide
  have hdescent : baseEnd_1823211 < baseStart_1823211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823228 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_1823228 : Nat := 118140960795 + 1823228 * 2 ^ 59
def prefixEnd_1823228 : Nat := 4983230072969 + 3 ^ 40 * 1823228 * 2
def baseEnd_1823228 : Nat := 936192306735697845765133

theorem tailTrace_1823228 : CollatzResearch.WordTrace tailWord_1823228 prefixEnd_1823228 936192306735697845765133 := by
  unfold tailWord_1823228
  simp only [CollatzResearch.WordTrace]
  refine ⟨33249294119381906698539169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44332392159175875598052225 33249294119381906698539169)
  ·
    refine ⟨24936970589536430023904377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33249294119381906698539169 24936970589536430023904377)
    ·
      refine ⟨18702727942152322517928283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24936970589536430023904377 18702727942152322517928283)
      ·
        refine ⟨28054091913228483776892425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18702727942152322517928283 28054091913228483776892425)
        ·
          refine ⟨21040568934921362832669319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28054091913228483776892425 21040568934921362832669319)
          ·
            refine ⟨31560853402382044249003979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21040568934921362832669319 31560853402382044249003979)
            ·
              refine ⟨47341280103573066373505969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31560853402382044249003979 47341280103573066373505969)
              ·
                refine ⟨35505960077679799780129477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47341280103573066373505969 35505960077679799780129477)
                ·
                  refine ⟨6657367514564962458774277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35505960077679799780129477 6657367514564962458774277)
                  ·
                    refine ⟨1248256408980930461020177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6657367514564962458774277 1248256408980930461020177)
                    ·
                      refine ⟨936192306735697845765133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248256408980930461020177 936192306735697845765133)
                      ·
                        rfl

theorem cell23_1823228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_1823228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823228 prefixEnd_1823228 := by exact prefixLift 1823228
  have htrace : WordTrace (prefixWord ++ tailWord_1823228) baseStart_1823228 baseEnd_1823228 := by
    simpa [prefixWord, tailWord_1823228, baseEnd_1823228] using wordTrace_append hprefix tailTrace_1823228
  have hstable : (prefixWord ++ tailWord_1823228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823228).length < 2 ^ (prefixWord ++ tailWord_1823228).sum := by decide
  have hdescent : baseEnd_1823228 < baseStart_1823228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823302 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1823302 : Nat := 118140960795 + 1823302 * 2 ^ 59
def prefixEnd_1823302 : Nat := 4983230072969 + 3 ^ 40 * 1823302 * 2
def baseEnd_1823302 : Nat := 104025589367125617359977

theorem tailTrace_1823302 : CollatzResearch.WordTrace tailWord_1823302 prefixEnd_1823302 104025589367125617359977 := by
  unfold tailWord_1823302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078165226265491376102255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44334191493663816023514773 2078165226265491376102255)
  ·
    refine ⟨3117247839398237064153383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2078165226265491376102255 3117247839398237064153383)
    ·
      refine ⟨4675871759097355596230075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3117247839398237064153383 4675871759097355596230075)
      ·
        refine ⟨7013807638646033394345113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4675871759097355596230075 7013807638646033394345113)
        ·
          refine ⟨5260355728984525045758835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7013807638646033394345113 5260355728984525045758835)
          ·
            refine ⟨7890533593476787568638253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260355728984525045758835 7890533593476787568638253)
            ·
              refine ⟨2958950097553795338239345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7890533593476787568638253 2958950097553795338239345)
              ·
                refine ⟨2219212573165346503679509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2958950097553795338239345 2219212573165346503679509)
                ·
                  refine ⟨104025589367125617359977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2219212573165346503679509 104025589367125617359977)
                  ·
                    rfl

theorem cell23_1823302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1823302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823302 prefixEnd_1823302 := by exact prefixLift 1823302
  have htrace : WordTrace (prefixWord ++ tailWord_1823302) baseStart_1823302 baseEnd_1823302 := by
    simpa [prefixWord, tailWord_1823302, baseEnd_1823302] using wordTrace_append hprefix tailTrace_1823302
  have hstable : (prefixWord ++ tailWord_1823302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823302).length < 2 ^ (prefixWord ++ tailWord_1823302).sum := by decide
  have hdescent : baseEnd_1823302 < baseStart_1823302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823311 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 3, 6]
def baseStart_1823311 : Nat := 118140960795 + 1823311 * 2 ^ 59
def prefixEnd_1823311 : Nat := 4983230072969 + 3 ^ 40 * 1823311 * 2
def baseEnd_1823311 : Nat := 312078308543340340342417

theorem tailTrace_1823311 : CollatzResearch.WordTrace tailWord_1823311 prefixEnd_1823311 312078308543340340342417 := by
  unfold tailWord_1823311
  simp only [CollatzResearch.WordTrace]
  refine ⟨66501615497463118572349787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44334410331642079048233191 66501615497463118572349787)
  ·
    refine ⟨99752423246194677858524681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66501615497463118572349787 99752423246194677858524681)
    ·
      refine ⟨74814317434646008393893511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99752423246194677858524681 74814317434646008393893511)
      ·
        refine ⟨112221476151969012590840267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74814317434646008393893511 112221476151969012590840267)
        ·
          refine ⟨168332214227953518886260401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112221476151969012590840267 168332214227953518886260401)
          ·
            refine ⟨126249160670965139164695301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168332214227953518886260401 126249160670965139164695301)
            ·
              refine ⟨23671717625805963593380369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126249160670965139164695301 23671717625805963593380369)
              ·
                refine ⟨17753788219354472695035277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23671717625805963593380369 17753788219354472695035277)
                ·
                  refine ⟨6657670582257927260638229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17753788219354472695035277 6657670582257927260638229)
                  ·
                    refine ⟨312078308543340340342417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6657670582257927260638229 312078308543340340342417)
                    ·
                      rfl

theorem cell23_1823311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_1823311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823311 prefixEnd_1823311 := by exact prefixLift 1823311
  have htrace : WordTrace (prefixWord ++ tailWord_1823311) baseStart_1823311 baseEnd_1823311 := by
    simpa [prefixWord, tailWord_1823311, baseEnd_1823311] using wordTrace_append hprefix tailTrace_1823311
  have hstable : (prefixWord ++ tailWord_1823311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823311).length < 2 ^ (prefixWord ++ tailWord_1823311).sum := by decide
  have hdescent : baseEnd_1823311 < baseStart_1823311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823328 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 1, 6]
def baseStart_1823328 : Nat := 118140960795 + 1823328 * 2 ^ 59
def prefixEnd_1823328 : Nat := 4983230072969 + 3 ^ 40 * 1823328 * 2
def baseEnd_1823328 : Nat := 312081218267049151504891

theorem tailTrace_1823328 : CollatzResearch.WordTrace tailWord_1823328 prefixEnd_1823328 312081218267049151504891 := by
  unfold tailWord_1823328
  simp only [CollatzResearch.WordTrace]
  refine ⟨33251117769200765237859319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44334823692267686983812425 33251117769200765237859319)
  ·
    refine ⟨49876676653801147856788979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33251117769200765237859319 49876676653801147856788979)
    ·
      refine ⟨74815014980701721785183469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49876676653801147856788979 74815014980701721785183469)
      ·
        refine ⟨28055630617763145669443801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74815014980701721785183469 28055630617763145669443801)
        ·
          refine ⟨21041722963322359252082851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28055630617763145669443801 21041722963322359252082851)
          ·
            refine ⟨31562584444983538878124277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21041722963322359252082851 31562584444983538878124277)
            ·
              refine ⟨2958992291717206769824151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31562584444983538878124277 2958992291717206769824151)
              ·
                refine ⟨4438488437575810154736227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958992291717206769824151 4438488437575810154736227)
                ·
                  refine ⟨6657732656363715232104341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438488437575810154736227 6657732656363715232104341)
                  ·
                    refine ⟨312081218267049151504891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6657732656363715232104341 312081218267049151504891)
                    ·
                      rfl

theorem cell23_1823328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_1823328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823328 prefixEnd_1823328 := by exact prefixLift 1823328
  have htrace : WordTrace (prefixWord ++ tailWord_1823328) baseStart_1823328 baseEnd_1823328 := by
    simpa [prefixWord, tailWord_1823328, baseEnd_1823328] using wordTrace_append hprefix tailTrace_1823328
  have hstable : (prefixWord ++ tailWord_1823328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823328).length < 2 ^ (prefixWord ++ tailWord_1823328).sum := by decide
  have hdescent : baseEnd_1823328 < baseStart_1823328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823338 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1823338 : Nat := 118140960795 + 1823338 * 2 ^ 59
def prefixEnd_1823338 : Nat := 4983230072969 + 3 ^ 40 * 1823338 * 2
def baseEnd_1823338 : Nat := 936248789607692415389627

theorem tailTrace_1823338 : CollatzResearch.WordTrace tailWord_1823338 prefixEnd_1823338 936248789607692415389627 := by
  unfold tailWord_1823338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16625650067091325545895667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44335066845576868122388445 16625650067091325545895667)
  ·
    refine ⟨24938475100636988318843501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16625650067091325545895667 24938475100636988318843501)
    ·
      refine ⟨9351928162738870619566313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24938475100636988318843501 9351928162738870619566313)
      ·
        refine ⟨7013946122054152964674735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9351928162738870619566313 7013946122054152964674735)
        ·
          refine ⟨10520919183081229447012103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7013946122054152964674735 10520919183081229447012103)
          ·
            refine ⟨15781378774621844170518155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520919183081229447012103 15781378774621844170518155)
            ·
              refine ⟨23672068161932766255777233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15781378774621844170518155 23672068161932766255777233)
              ·
                refine ⟨17754051121449574691832925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23672068161932766255777233 17754051121449574691832925)
                ·
                  refine ⟨6657769170543590509437347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17754051121449574691832925 6657769170543590509437347)
                  ·
                    refine ⟨9986653755815385764156021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6657769170543590509437347 9986653755815385764156021)
                    ·
                      refine ⟨936248789607692415389627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9986653755815385764156021 936248789607692415389627)
                      ·
                        rfl

theorem cell23_1823338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1823338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823338 prefixEnd_1823338 := by exact prefixLift 1823338
  have htrace : WordTrace (prefixWord ++ tailWord_1823338) baseStart_1823338 baseEnd_1823338 := by
    simpa [prefixWord, tailWord_1823338, baseEnd_1823338] using wordTrace_append hprefix tailTrace_1823338
  have hstable : (prefixWord ++ tailWord_1823338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823338).length < 2 ^ (prefixWord ++ tailWord_1823338).sum := by decide
  have hdescent : baseEnd_1823338 < baseStart_1823338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823346 : List Nat := [3, 2, 1, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_1823346 : Nat := 118140960795 + 1823346 * 2 ^ 59
def prefixEnd_1823346 : Nat := 4983230072969 + 3 ^ 40 * 1823346 * 2
def baseEnd_1823346 : Nat := 936252897452928384089591

theorem tailTrace_1823346 : CollatzResearch.WordTrace tailWord_1823346 prefixEnd_1823346 936252897452928384089591 := by
  unfold tailWord_1823346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16625723013084079887468473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44335261368224213033249261 16625723013084079887468473)
  ·
    refine ⟨12469292259813059915601355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16625723013084079887468473 12469292259813059915601355)
    ·
      refine ⟨18703938389719589873402033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12469292259813059915601355 18703938389719589873402033)
      ·
        refine ⟨14027953792289692405051525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18703938389719589873402033 14027953792289692405051525)
        ·
          refine ⟨2630241336054317325947161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14027953792289692405051525 2630241336054317325947161)
          ·
            refine ⟨1972681002040737994460371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2630241336054317325947161 1972681002040737994460371)
            ·
              refine ⟨2959021503061106991690557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972681002040737994460371 2959021503061106991690557)
              ·
                refine ⟨1109633063647915121883959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2959021503061106991690557 1109633063647915121883959)
                ·
                  refine ⟨1664449595471872682825939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109633063647915121883959 1664449595471872682825939)
                  ·
                    refine ⟨2496674393207809024238909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1664449595471872682825939 2496674393207809024238909)
                    ·
                      refine ⟨936252897452928384089591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496674393207809024238909 936252897452928384089591)
                      ·
                        rfl

theorem cell23_1823346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_1823346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823346 prefixEnd_1823346 := by exact prefixLift 1823346
  have htrace : WordTrace (prefixWord ++ tailWord_1823346) baseStart_1823346 baseEnd_1823346 := by
    simpa [prefixWord, tailWord_1823346, baseEnd_1823346] using wordTrace_append hprefix tailTrace_1823346
  have hstable : (prefixWord ++ tailWord_1823346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823346).length < 2 ^ (prefixWord ++ tailWord_1823346).sum := by decide
  have hdescent : baseEnd_1823346 < baseStart_1823346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823386 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1823386 : Nat := 118140960795 + 1823386 * 2 ^ 59
def prefixEnd_1823386 : Nat := 4983230072969 + 3 ^ 40 * 1823386 * 2
def baseEnd_1823386 : Nat := 936273436679108227589407

theorem tailTrace_1823386 : CollatzResearch.WordTrace tailWord_1823386 prefixEnd_1823386 936273436679108227589407 := by
  unfold tailWord_1823386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16626087743047851595332503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44336233981460937587553341 16626087743047851595332503)
  ·
    refine ⟨24939131614571777392998755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16626087743047851595332503 24939131614571777392998755)
    ·
      refine ⟨37408697421857666089498133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24939131614571777392998755 37408697421857666089498133)
      ·
        refine ⟨1753532691649578097945225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37408697421857666089498133 1753532691649578097945225)
        ·
          refine ⟨1315149518737183573458919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753532691649578097945225 1315149518737183573458919)
          ·
            refine ⟨1972724278105775360188379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315149518737183573458919 1972724278105775360188379)
            ·
              refine ⟨2959086417158663040282569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972724278105775360188379 2959086417158663040282569)
              ·
                refine ⟨2219314812868997280211927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959086417158663040282569 2219314812868997280211927)
                ·
                  refine ⟨3328972219303495920317891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219314812868997280211927 3328972219303495920317891)
                  ·
                    refine ⟨4993458328955243880476837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328972219303495920317891 4993458328955243880476837)
                    ·
                      refine ⟨936273436679108227589407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4993458328955243880476837 936273436679108227589407)
                      ·
                        rfl

theorem cell23_1823386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1823386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823386 prefixEnd_1823386 := by exact prefixLift 1823386
  have htrace : WordTrace (prefixWord ++ tailWord_1823386) baseStart_1823386 baseEnd_1823386 := by
    simpa [prefixWord, tailWord_1823386, baseEnd_1823386] using wordTrace_append hprefix tailTrace_1823386
  have hstable : (prefixWord ++ tailWord_1823386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823386).length < 2 ^ (prefixWord ++ tailWord_1823386).sum := by decide
  have hdescent : baseEnd_1823386 < baseStart_1823386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823406 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1823406 : Nat := 118140960795 + 1823406 * 2 ^ 59
def prefixEnd_1823406 : Nat := 4983230072969 + 3 ^ 40 * 1823406 * 2
def baseEnd_1823406 : Nat := 936283706292198149339315

theorem tailTrace_1823406 : CollatzResearch.WordTrace tailWord_1823406 prefixEnd_1823406 936283706292198149339315 := by
  unfold tailWord_1823406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313135054014868724632259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44336720288079299864705381 8313135054014868724632259)
  ·
    refine ⟨12469702581022303086948389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8313135054014868724632259 12469702581022303086948389)
    ·
      refine ⟨2338069233941681828802823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12469702581022303086948389 2338069233941681828802823)
      ·
        refine ⟨3507103850912522743204235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338069233941681828802823 3507103850912522743204235)
        ·
          refine ⟨5260655776368784114806353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507103850912522743204235 5260655776368784114806353)
          ·
            refine ⟨3945491832276588086104765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5260655776368784114806353 3945491832276588086104765)
            ·
              refine ⟨1479559437103720532289287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3945491832276588086104765 1479559437103720532289287)
              ·
                refine ⟨2219339155655580798433931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479559437103720532289287 2219339155655580798433931)
                ·
                  refine ⟨3329008733483371197650897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219339155655580798433931 3329008733483371197650897)
                  ·
                    refine ⟨2496756550112528398238173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3329008733483371197650897 2496756550112528398238173)
                    ·
                      refine ⟨936283706292198149339315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496756550112528398238173 936283706292198149339315)
                      ·
                        rfl

theorem cell23_1823406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1823406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823406 prefixEnd_1823406 := by exact prefixLift 1823406
  have htrace : WordTrace (prefixWord ++ tailWord_1823406) baseStart_1823406 baseEnd_1823406 := by
    simpa [prefixWord, tailWord_1823406, baseEnd_1823406] using wordTrace_append hprefix tailTrace_1823406
  have hstable : (prefixWord ++ tailWord_1823406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823406).length < 2 ^ (prefixWord ++ tailWord_1823406).sum := by decide
  have hdescent : baseEnd_1823406 < baseStart_1823406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823418 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_1823418 : Nat := 118140960795 + 1823418 * 2 ^ 59
def prefixEnd_1823418 : Nat := 4983230072969 + 3 ^ 40 * 1823418 * 2
def baseEnd_1823418 : Nat := 312096622686684034129753

theorem tailTrace_1823418 : CollatzResearch.WordTrace tailWord_1823418 prefixEnd_1823418 312096622686684034129753 := by
  unfold tailWord_1823418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16626379527018868961623727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44337012072050317230996605 16626379527018868961623727)
  ·
    refine ⟨24939569290528303442435591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16626379527018868961623727 24939569290528303442435591)
    ·
      refine ⟨37409353935792455163653387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24939569290528303442435591 37409353935792455163653387)
      ·
        refine ⟨56114030903688682745480081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37409353935792455163653387 56114030903688682745480081)
        ·
          refine ⟨42085523177766512059110061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56114030903688682745480081 42085523177766512059110061)
          ·
            refine ⟨15782071191662442022166273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42085523177766512059110061 15782071191662442022166273)
            ·
              refine ⟨11836553393746831516624705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15782071191662442022166273 11836553393746831516624705)
              ·
                refine ⟨8877415045310123637468529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11836553393746831516624705 8877415045310123637468529)
                ·
                  refine ⟨6658061283982592728101397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8877415045310123637468529 6658061283982592728101397)
                  ·
                    refine ⟨312096622686684034129753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6658061283982592728101397 312096622686684034129753)
                    ·
                      rfl

theorem cell23_1823418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_1823418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823418 prefixEnd_1823418 := by exact prefixLift 1823418
  have htrace : WordTrace (prefixWord ++ tailWord_1823418) baseStart_1823418 baseEnd_1823418 := by
    simpa [prefixWord, tailWord_1823418, baseEnd_1823418] using wordTrace_append hprefix tailTrace_1823418
  have hstable : (prefixWord ++ tailWord_1823418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823418).length < 2 ^ (prefixWord ++ tailWord_1823418).sum := by decide
  have hdescent : baseEnd_1823418 < baseStart_1823418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823448 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 9]
def baseStart_1823448 : Nat := 118140960795 + 1823448 * 2 ^ 59
def prefixEnd_1823448 : Nat := 4983230072969 + 3 ^ 40 * 1823448 * 2
def baseEnd_1823448 : Nat := 104033919164409665001569

theorem tailTrace_1823448 : CollatzResearch.WordTrace tailWord_1823448 prefixEnd_1823448 104033919164409665001569 := by
  unfold tailWord_1823448
  simp only [CollatzResearch.WordTrace]
  refine ⟨33253306148983395485043499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44337741531977860646724665 33253306148983395485043499)
  ·
    refine ⟨49879959223475093227565249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33253306148983395485043499 49879959223475093227565249)
    ·
      refine ⟨37409969417606319920673937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49879959223475093227565249 37409969417606319920673937)
      ·
        refine ⟨28057477063204739940505453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37409969417606319920673937 28057477063204739940505453)
        ·
          refine ⟨10521553898701777477689545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28057477063204739940505453 10521553898701777477689545)
          ·
            refine ⟨7891165424026333108267159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10521553898701777477689545 7891165424026333108267159)
            ·
              refine ⟨11836748136039499662400739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891165424026333108267159 11836748136039499662400739)
              ·
                refine ⟨17755122204059249493601109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11836748136039499662400739 17755122204059249493601109)
                ·
                  refine ⟨104033919164409665001569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17755122204059249493601109 104033919164409665001569)
                  ·
                    rfl

theorem cell23_1823448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 9].length) (baseStart_1823448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823448 prefixEnd_1823448 := by exact prefixLift 1823448
  have htrace : WordTrace (prefixWord ++ tailWord_1823448) baseStart_1823448 baseEnd_1823448 := by
    simpa [prefixWord, tailWord_1823448, baseEnd_1823448] using wordTrace_append hprefix tailTrace_1823448
  have hstable : (prefixWord ++ tailWord_1823448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823448).length < 2 ^ (prefixWord ++ tailWord_1823448).sum := by decide
  have hdescent : baseEnd_1823448 < baseStart_1823448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823465 : List Nat := [1, 2, 1, 1, 1, 2, 5, 5, 5]
def baseStart_1823465 : Nat := 118140960795 + 1823465 * 2 ^ 59
def prefixEnd_1823465 : Nat := 4983230072969 + 3 ^ 40 * 1823465 * 2
def baseEnd_1823465 : Nat := 104034889072312602055727

theorem tailTrace_1823465 : CollatzResearch.WordTrace tailWord_1823465 prefixEnd_1823465 104034889072312602055727 := by
  unfold tailWord_1823465
  simp only [CollatzResearch.WordTrace]
  refine ⟨66507232338905202873455849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44338154892603468582303899 66507232338905202873455849)
  ·
    refine ⟨49880424254178902155091887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66507232338905202873455849 49880424254178902155091887)
    ·
      refine ⟨74820636381268353232637831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49880424254178902155091887 74820636381268353232637831)
      ·
        refine ⟨112230954571902529848956747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74820636381268353232637831 112230954571902529848956747)
        ·
          refine ⟨168346431857853794773435121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112230954571902529848956747 168346431857853794773435121)
          ·
            refine ⟨126259823893390346080076341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168346431857853794773435121 126259823893390346080076341)
            ·
              refine ⟨11836858490005344945007157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126259823893390346080076341 11836858490005344945007157)
              ·
                refine ⟨1109705483438001088594421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11836858490005344945007157 1109705483438001088594421)
                ·
                  refine ⟨104034889072312602055727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1109705483438001088594421 104034889072312602055727)
                  ·
                    rfl

theorem cell23_1823465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 5].length) (baseStart_1823465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823465 prefixEnd_1823465 := by exact prefixLift 1823465
  have htrace : WordTrace (prefixWord ++ tailWord_1823465) baseStart_1823465 baseEnd_1823465 := by
    simpa [prefixWord, tailWord_1823465, baseEnd_1823465] using wordTrace_append hprefix tailTrace_1823465
  have hstable : (prefixWord ++ tailWord_1823465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823465).length < 2 ^ (prefixWord ++ tailWord_1823465).sum := by decide
  have hdescent : baseEnd_1823465 < baseStart_1823465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823495 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 1, 7]
def baseStart_1823495 : Nat := 118140960795 + 1823495 * 2 ^ 59
def prefixEnd_1823495 : Nat := 4983230072969 + 3 ^ 40 * 1823495 * 2
def baseEnd_1823495 : Nat := 312109802023482767042135

theorem tailTrace_1823495 : CollatzResearch.WordTrace tailWord_1823495 prefixEnd_1823495 312109802023482767042135 := by
  unfold tailWord_1823495
  simp only [CollatzResearch.WordTrace]
  refine ⟨66508326528796517997047939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44338884352531011998031959 66508326528796517997047939)
  ·
    refine ⟨99762489793194776995571909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66508326528796517997047939 99762489793194776995571909)
    ·
      refine ⟨18705466836224020686669733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99762489793194776995571909 18705466836224020686669733)
      ·
        refine ⟨3507275031792003878750575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18705466836224020686669733 3507275031792003878750575)
        ·
          refine ⟨5260912547688005818125863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507275031792003878750575 5260912547688005818125863)
          ·
            refine ⟨7891368821532008727188795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260912547688005818125863 7891368821532008727188795)
            ·
              refine ⟨11837053232298013090783193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891368821532008727188795 11837053232298013090783193)
              ·
                refine ⟨8877789924223509818087395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11837053232298013090783193 8877789924223509818087395)
                ·
                  refine ⟨13316684886335264727131093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877789924223509818087395 13316684886335264727131093)
                  ·
                    refine ⟨312109802023482767042135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13316684886335264727131093 312109802023482767042135)
                    ·
                      rfl

theorem cell23_1823495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_1823495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823495 prefixEnd_1823495 := by exact prefixLift 1823495
  have htrace : WordTrace (prefixWord ++ tailWord_1823495) baseStart_1823495 baseEnd_1823495 := by
    simpa [prefixWord, tailWord_1823495, baseEnd_1823495] using wordTrace_append hprefix tailTrace_1823495
  have hstable : (prefixWord ++ tailWord_1823495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823495).length < 2 ^ (prefixWord ++ tailWord_1823495).sum := by decide
  have hdescent : baseEnd_1823495 < baseStart_1823495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823533 : List Nat := [1, 5, 3, 2, 1, 1, 3, 2, 5]
def baseStart_1823533 : Nat := 118140960795 + 1823533 * 2 ^ 59
def prefixEnd_1823533 : Nat := 4983230072969 + 3 ^ 40 * 1823533 * 2
def baseEnd_1823533 : Nat := 104038768703924350272359

theorem tailTrace_1823533 : CollatzResearch.WordTrace tailWord_1823533 prefixEnd_1823533 104038768703924350272359 := by
  unfold tailWord_1823533
  simp only [CollatzResearch.WordTrace]
  refine ⟨66509712502658850486931253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44339808335105900324620835 66509712502658850486931253)
  ·
    refine ⟨6235285547124267233149805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66509712502658850486931253 6235285547124267233149805)
    ·
      refine ⟨2338232080171600212431177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6235285547124267233149805 2338232080171600212431177)
      ·
        refine ⟨1753674060128700159323383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2338232080171600212431177 1753674060128700159323383)
        ·
          refine ⟨2630511090193050238985075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753674060128700159323383 2630511090193050238985075)
          ·
            refine ⟨3945766635289575358477613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630511090193050238985075 3945766635289575358477613)
            ·
              refine ⟨1479662488233590759429105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3945766635289575358477613 1479662488233590759429105)
              ·
                refine ⟨1109746866175193069571829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479662488233590759429105 1109746866175193069571829)
                ·
                  refine ⟨104038768703924350272359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1109746866175193069571829 104038768703924350272359)
                  ·
                    rfl

theorem cell23_1823533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_1823533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823533 prefixEnd_1823533 := by exact prefixLift 1823533
  have htrace : WordTrace (prefixWord ++ tailWord_1823533) baseStart_1823533 baseEnd_1823533 := by
    simpa [prefixWord, tailWord_1823533, baseEnd_1823533] using wordTrace_append hprefix tailTrace_1823533
  have hstable : (prefixWord ++ tailWord_1823533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823533).length < 2 ^ (prefixWord ++ tailWord_1823533).sum := by decide
  have hdescent : baseEnd_1823533 < baseStart_1823533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823555 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 6]
def baseStart_1823555 : Nat := 118140960795 + 1823555 * 2 ^ 59
def prefixEnd_1823555 : Nat := 4983230072969 + 3 ^ 40 * 1823555 * 2
def baseEnd_1823555 : Nat := 104040023878857562930681

theorem tailTrace_1823555 : CollatzResearch.WordTrace tailWord_1823555 prefixEnd_1823555 104040023878857562930681 := by
  unfold tailWord_1823555
  simp only [CollatzResearch.WordTrace]
  refine ⟨66510514908579148244232119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44340343272386098829488079 66510514908579148244232119)
  ·
    refine ⟨99765772362868722366348179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66510514908579148244232119 99765772362868722366348179)
    ·
      refine ⟨149648658544303083549522269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99765772362868722366348179 149648658544303083549522269)
      ·
        refine ⟨56118246954113656331070851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149648658544303083549522269 56118246954113656331070851)
        ·
          refine ⟨84177370431170484496606277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56118246954113656331070851 84177370431170484496606277)
          ·
            refine ⟨15783256955844465843113677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84177370431170484496606277 15783256955844465843113677)
            ·
              refine ⟨5918721358441674691167629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15783256955844465843113677 5918721358441674691167629)
              ·
                refine ⟨2219520509415628009187861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5918721358441674691167629 2219520509415628009187861)
                ·
                  refine ⟨104040023878857562930681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2219520509415628009187861 104040023878857562930681)
                  ·
                    rfl

theorem cell23_1823555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 6].length) (baseStart_1823555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823555 prefixEnd_1823555 := by exact prefixLift 1823555
  have htrace : WordTrace (prefixWord ++ tailWord_1823555) baseStart_1823555 baseEnd_1823555 := by
    simpa [prefixWord, tailWord_1823555, baseEnd_1823555] using wordTrace_append hprefix tailTrace_1823555
  have hstable : (prefixWord ++ tailWord_1823555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823555).length < 2 ^ (prefixWord ++ tailWord_1823555).sum := by decide
  have hdescent : baseEnd_1823555 < baseStart_1823555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823569 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_1823569 : Nat := 118140960795 + 1823569 * 2 ^ 59
def prefixEnd_1823569 : Nat := 4983230072969 + 3 ^ 40 * 1823569 * 2
def baseEnd_1823569 : Nat := 936367403638881011601065

theorem tailTrace_1823569 : CollatzResearch.WordTrace tailWord_1823569 prefixEnd_1823569 936367403638881011601065 := by
  unfold tailWord_1823569
  simp only [CollatzResearch.WordTrace]
  refine ⟨66511025530528428635241761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44340683687018952423494507 66511025530528428635241761)
  ·
    refine ⟨49883269147896321476431321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66511025530528428635241761 49883269147896321476431321)
    ·
      refine ⟨37412451860922241107323491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49883269147896321476431321 37412451860922241107323491)
      ·
        refine ⟨56118677791383361660985237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37412451860922241107323491 56118677791383361660985237)
        ·
          refine ⟨2630563021471095077858683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56118677791383361660985237 2630563021471095077858683)
          ·
            refine ⟨3945844532206642616788025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630563021471095077858683 3945844532206642616788025)
            ·
              refine ⟨2959383399154981962591019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3945844532206642616788025 2959383399154981962591019)
              ·
                refine ⟨4439075098732472943886529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959383399154981962591019 4439075098732472943886529)
                ·
                  refine ⟨3329306324049354707914897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4439075098732472943886529 3329306324049354707914897)
                  ·
                    refine ⟨2496979743037016030936173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3329306324049354707914897 2496979743037016030936173)
                    ·
                      refine ⟨936367403638881011601065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2496979743037016030936173 936367403638881011601065)
                      ·
                        rfl

theorem cell23_1823569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_1823569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823569 prefixEnd_1823569 := by exact prefixLift 1823569
  have htrace : WordTrace (prefixWord ++ tailWord_1823569) baseStart_1823569 baseEnd_1823569 := by
    simpa [prefixWord, tailWord_1823569, baseEnd_1823569] using wordTrace_append hprefix tailTrace_1823569
  have hstable : (prefixWord ++ tailWord_1823569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823569).length < 2 ^ (prefixWord ++ tailWord_1823569).sum := by decide
  have hdescent : baseEnd_1823569 < baseStart_1823569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823615 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 1, 6]
def baseStart_1823615 : Nat := 118140960795 + 1823615 * 2 ^ 59
def prefixEnd_1823615 : Nat := 4983230072969 + 3 ^ 40 * 1823615 * 2
def baseEnd_1823615 : Nat := 312130341249662610541951

theorem tailTrace_1823615 : CollatzResearch.WordTrace tailWord_1823615 prefixEnd_1823615 312130341249662610541951 := by
  unfold tailWord_1823615
  simp only [CollatzResearch.WordTrace]
  refine ⟨66512703288361778491416299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44341802192241185660944199 66512703288361778491416299)
  ·
    refine ⟨99769054932542667737124449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66512703288361778491416299 99769054932542667737124449)
    ·
      refine ⟨74826791199407000802843337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99769054932542667737124449 74826791199407000802843337)
      ·
        refine ⟨56120093399555250602132503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74826791199407000802843337 56120093399555250602132503)
        ·
          refine ⟨84180140099332875903198755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56120093399555250602132503 84180140099332875903198755)
          ·
            refine ⟨126270210148999313854798133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84180140099332875903198755 126270210148999313854798133)
            ·
              refine ⟨11837832201468685673887325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126270210148999313854798133 11837832201468685673887325)
              ·
                refine ⟨4439187075550757127707747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11837832201468685673887325 4439187075550757127707747)
                ·
                  refine ⟨6658780613326135691561621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439187075550757127707747 6658780613326135691561621)
                  ·
                    refine ⟨312130341249662610541951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6658780613326135691561621 312130341249662610541951)
                    ·
                      rfl

theorem cell23_1823615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_1823615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823615 prefixEnd_1823615 := by exact prefixLift 1823615
  have htrace : WordTrace (prefixWord ++ tailWord_1823615) baseStart_1823615 baseEnd_1823615 := by
    simpa [prefixWord, tailWord_1823615, baseEnd_1823615] using wordTrace_append hprefix tailTrace_1823615
  have hstable : (prefixWord ++ tailWord_1823615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823615).length < 2 ^ (prefixWord ++ tailWord_1823615).sum := by decide
  have hdescent : baseEnd_1823615 < baseStart_1823615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823626 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_1823626 : Nat := 118140960795 + 1823626 * 2 ^ 59
def prefixEnd_1823626 : Nat := 4983230072969 + 3 ^ 40 * 1823626 * 2
def baseEnd_1823626 : Nat := 936396672036187288588303

theorem tailTrace_1823626 : CollatzResearch.WordTrace tailWord_1823626 prefixEnd_1823626 936396672036187288588303 := by
  unfold tailWord_1823626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16628276122830481842516683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44342069660881284913377821 16628276122830481842516683)
  ·
    refine ⟨24942414184245722763775025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16628276122830481842516683 24942414184245722763775025)
    ·
      refine ⟨18706810638184292072831269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24942414184245722763775025 18706810638184292072831269)
      ·
        refine ⟨3507526994659554763655863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18706810638184292072831269 3507526994659554763655863)
        ·
          refine ⟨5261290491989332145483795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507526994659554763655863 5261290491989332145483795)
          ·
            refine ⟨7891935737983998218225693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261290491989332145483795 7891935737983998218225693)
            ·
              refine ⟨2959475901743999331834635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7891935737983998218225693 2959475901743999331834635)
              ·
                refine ⟨4439213852615998997751953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959475901743999331834635 4439213852615998997751953)
                ·
                  refine ⟨3329410389461999248313965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4439213852615998997751953 3329410389461999248313965)
                  ·
                    refine ⟨1248528896048249718117737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3329410389461999248313965 1248528896048249718117737)
                    ·
                      refine ⟨936396672036187288588303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248528896048249718117737 936396672036187288588303)
                      ·
                        rfl

theorem cell23_1823626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_1823626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823626 prefixEnd_1823626 := by exact prefixLift 1823626
  have htrace : WordTrace (prefixWord ++ tailWord_1823626) baseStart_1823626 baseEnd_1823626 := by
    simpa [prefixWord, tailWord_1823626, baseEnd_1823626] using wordTrace_append hprefix tailTrace_1823626
  have hstable : (prefixWord ++ tailWord_1823626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823626).length < 2 ^ (prefixWord ++ tailWord_1823626).sum := by decide
  have hdescent : baseEnd_1823626 < baseStart_1823626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823635 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4]
def baseStart_1823635 : Nat := 118140960795 + 1823635 * 2 ^ 59
def prefixEnd_1823635 : Nat := 4983230072969 + 3 ^ 40 * 1823635 * 2
def baseEnd_1823635 : Nat := 936401293362077753375761

theorem tailTrace_1823635 : CollatzResearch.WordTrace tailWord_1823635 prefixEnd_1823635 936401293362077753375761 := by
  unfold tailWord_1823635
  simp only [CollatzResearch.WordTrace]
  refine ⟨66513432748289321907144359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44342288498859547938096239 66513432748289321907144359)
  ·
    refine ⟨99770149122433982860716539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66513432748289321907144359 99770149122433982860716539)
    ·
      refine ⟨149655223683650974291074809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99770149122433982860716539 149655223683650974291074809)
      ·
        refine ⟨112241417762738230718306107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149655223683650974291074809 112241417762738230718306107)
        ·
          refine ⟨168362126644107346077459161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112241417762738230718306107 168362126644107346077459161)
          ·
            refine ⟨126271594983080509558094371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168362126644107346077459161 126271594983080509558094371)
            ·
              refine ⟨189407392474620764337141557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126271594983080509558094371 189407392474620764337141557)
              ·
                refine ⟨17756943044495696656607021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189407392474620764337141557 17756943044495696656607021)
                ·
                  refine ⟨6658853641685886246227633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17756943044495696656607021 6658853641685886246227633)
                  ·
                    refine ⟨4994140231264414684670725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6658853641685886246227633 4994140231264414684670725)
                    ·
                      refine ⟨936401293362077753375761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4994140231264414684670725 936401293362077753375761)
                      ·
                        rfl

theorem cell23_1823635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_1823635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823635 prefixEnd_1823635 := by exact prefixLift 1823635
  have htrace : WordTrace (prefixWord ++ tailWord_1823635) baseStart_1823635 baseEnd_1823635 := by
    simpa [prefixWord, tailWord_1823635, baseEnd_1823635] using wordTrace_append hprefix tailTrace_1823635
  have hstable : (prefixWord ++ tailWord_1823635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823635).length < 2 ^ (prefixWord ++ tailWord_1823635).sum := by decide
  have hdescent : baseEnd_1823635 < baseStart_1823635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823639 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 5, 2, 2]
def baseStart_1823639 : Nat := 118140960795 + 1823639 * 2 ^ 59
def prefixEnd_1823639 : Nat := 4983230072969 + 3 ^ 40 * 1823639 * 2
def baseEnd_1823639 : Nat := 936403347284695737725743

theorem tailTrace_1823639 : CollatzResearch.WordTrace tailWord_1823639 prefixEnd_1823639 936403347284695737725743 := by
  unfold tailWord_1823639
  simp only [CollatzResearch.WordTrace]
  refine ⟨66513578640274830590289971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44342385760183220393526647 66513578640274830590289971)
  ·
    refine ⟨99770367960412245885434957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66513578640274830590289971 99770367960412245885434957)
    ·
      refine ⟨37413887985154592207038109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99770367960412245885434957 37413887985154592207038109)
      ·
        refine ⟨14030207994432972077639291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37413887985154592207038109 14030207994432972077639291)
        ·
          refine ⟨21045311991649458116458937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14030207994432972077639291 21045311991649458116458937)
          ·
            refine ⟨15783983993737093587344203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21045311991649458116458937 15783983993737093587344203)
            ·
              refine ⟨23675975990605640381016305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15783983993737093587344203 23675975990605640381016305)
              ·
                refine ⟨17756981992954230285762229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23675975990605640381016305 17756981992954230285762229)
                ·
                  refine ⟨1664717061839459089290209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17756981992954230285762229 1664717061839459089290209)
                  ·
                    refine ⟨1248537796379594316967657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1664717061839459089290209 1248537796379594316967657)
                    ·
                      refine ⟨936403347284695737725743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248537796379594316967657 936403347284695737725743)
                      ·
                        rfl

theorem cell23_1823639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_1823639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823639 prefixEnd_1823639 := by exact prefixLift 1823639
  have htrace : WordTrace (prefixWord ++ tailWord_1823639) baseStart_1823639 baseEnd_1823639 := by
    simpa [prefixWord, tailWord_1823639, baseEnd_1823639] using wordTrace_append hprefix tailTrace_1823639
  have hstable : (prefixWord ++ tailWord_1823639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823639).length < 2 ^ (prefixWord ++ tailWord_1823639).sum := by decide
  have hdescent : baseEnd_1823639 < baseStart_1823639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823645 : List Nat := [1, 4, 2, 1, 2, 1, 12]
def baseStart_1823645 : Nat := 118140960795 + 1823645 * 2 ^ 59
def prefixEnd_1823645 : Nat := 4983230072969 + 3 ^ 40 * 1823645 * 2
def baseEnd_1823645 : Nat := 11560573187266947089515

theorem tailTrace_1823645 : CollatzResearch.WordTrace tailWord_1823645 prefixEnd_1823645 11560573187266947089515 := by
  unfold tailWord_1823645
  simp only [CollatzResearch.WordTrace]
  refine ⟨66513797478253093615008389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44342531652168729076672259 66513797478253093615008389)
  ·
    refine ⟨12471337027172455052814073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66513797478253093615008389 12471337027172455052814073)
    ·
      refine ⟨9353502770379341289610555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12471337027172455052814073 9353502770379341289610555)
      ·
        refine ⟨14030254155569011934415833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9353502770379341289610555 14030254155569011934415833)
        ·
          refine ⟨10522690616676758950811875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14030254155569011934415833 10522690616676758950811875)
          ·
            refine ⟨15784035925015138426217813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10522690616676758950811875 15784035925015138426217813)
            ·
              refine ⟨11560573187266947089515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 15784035925015138426217813 11560573187266947089515)
              ·
                rfl

theorem cell23_1823645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 12].length) (baseStart_1823645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823645 prefixEnd_1823645 := by exact prefixLift 1823645
  have htrace : WordTrace (prefixWord ++ tailWord_1823645) baseStart_1823645 baseEnd_1823645 := by
    simpa [prefixWord, tailWord_1823645, baseEnd_1823645] using wordTrace_append hprefix tailTrace_1823645
  have hstable : (prefixWord ++ tailWord_1823645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823645).length < 2 ^ (prefixWord ++ tailWord_1823645).sum := by decide
  have hdescent : baseEnd_1823645 < baseStart_1823645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823649 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 4, 4]
def baseStart_1823649 : Nat := 118140960795 + 1823649 * 2 ^ 59
def prefixEnd_1823649 : Nat := 4983230072969 + 3 ^ 40 * 1823649 * 2
def baseEnd_1823649 : Nat := 312136160697080232866899

theorem tailTrace_1823649 : CollatzResearch.WordTrace tailWord_1823649 prefixEnd_1823649 312136160697080232866899 := by
  unfold tailWord_1823649
  simp only [CollatzResearch.WordTrace]
  refine ⟨66513943370238602298154001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44342628913492401532102667 66513943370238602298154001)
  ·
    refine ⟨49885457527678951723615501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66513943370238602298154001 49885457527678951723615501)
    ·
      refine ⟨18707046572879606896355813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49885457527678951723615501 18707046572879606896355813)
      ·
        refine ⟨3507571232414926293066715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18707046572879606896355813 3507571232414926293066715)
        ·
          refine ⟨5261356848622389439600073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507571232414926293066715 5261356848622389439600073)
          ·
            refine ⟨3946017636466792079700055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5261356848622389439600073 3946017636466792079700055)
            ·
              refine ⟨5919026454700188119550083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946017636466792079700055 5919026454700188119550083)
              ·
                refine ⟨8878539682050282179325125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919026454700188119550083 8878539682050282179325125)
                ·
                  refine ⟨1664726190384427908623461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8878539682050282179325125 1664726190384427908623461)
                  ·
                    refine ⟨312136160697080232866899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1664726190384427908623461 312136160697080232866899)
                    ·
                      rfl

theorem cell23_1823649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_1823649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823649 prefixEnd_1823649 := by exact prefixLift 1823649
  have htrace : WordTrace (prefixWord ++ tailWord_1823649) baseStart_1823649 baseEnd_1823649 := by
    simpa [prefixWord, tailWord_1823649, baseEnd_1823649] using wordTrace_append hprefix tailTrace_1823649
  have hstable : (prefixWord ++ tailWord_1823649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823649).length < 2 ^ (prefixWord ++ tailWord_1823649).sum := by decide
  have hdescent : baseEnd_1823649 < baseStart_1823649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823670 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1823670 : Nat := 118140960795 + 1823670 * 2 ^ 59
def prefixEnd_1823670 : Nat := 4983230072969 + 3 ^ 40 * 1823670 * 2
def baseEnd_1823670 : Nat := 312139755061661705479367

theorem tailTrace_1823670 : CollatzResearch.WordTrace tailWord_1823670 prefixEnd_1823670 312139755061661705479367 := by
  unfold tailWord_1823670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4157169331447657680291779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44343139535441681923112309 4157169331447657680291779)
  ·
    refine ⟨6235753997171486520437669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4157169331447657680291779 6235753997171486520437669)
    ·
      refine ⟨1169203874469653722582063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6235753997171486520437669 1169203874469653722582063)
      ·
        refine ⟨1753805811704480583873095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169203874469653722582063 1753805811704480583873095)
        ·
          refine ⟨2630708717556720875809643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753805811704480583873095 2630708717556720875809643)
          ·
            refine ⟨3946063076335081313714465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630708717556720875809643 3946063076335081313714465)
            ·
              refine ⟨2959547307251310985285849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946063076335081313714465 2959547307251310985285849)
              ·
                refine ⟨2219660480438483238964387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959547307251310985285849 2219660480438483238964387)
                ·
                  refine ⟨3329490720657724858446581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219660480438483238964387 3329490720657724858446581)
                  ·
                    refine ⟨312139755061661705479367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3329490720657724858446581 312139755061661705479367)
                    ·
                      rfl

theorem cell23_1823670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1823670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823670 prefixEnd_1823670 := by exact prefixLift 1823670
  have htrace : WordTrace (prefixWord ++ tailWord_1823670) baseStart_1823670 baseEnd_1823670 := by
    simpa [prefixWord, tailWord_1823670, baseEnd_1823670] using wordTrace_append hprefix tailTrace_1823670
  have hstable : (prefixWord ++ tailWord_1823670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823670).length < 2 ^ (prefixWord ++ tailWord_1823670).sum := by decide
  have hdescent : baseEnd_1823670 < baseStart_1823670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823776 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1823776 : Nat := 118140960795 + 1823776 * 2 ^ 59
def prefixEnd_1823776 : Nat := 4983230072969 + 3 ^ 40 * 1823776 * 2
def baseEnd_1823776 : Nat := 936473694134361701712613

theorem tailTrace_1823776 : CollatzResearch.WordTrace tailWord_1823776 prefixEnd_1823776 936473694134361701712613 := by
  unfold tailWord_1823776
  simp only [CollatzResearch.WordTrace]
  refine ⟨33259287720389251494013591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44345716960519001992018121 33259287720389251494013591)
  ·
    refine ⟨49888931580583877241020387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33259287720389251494013591 49888931580583877241020387)
    ·
      refine ⟨74833397370875815861530581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49888931580583877241020387 74833397370875815861530581)
      ·
        refine ⟨1753907750879901934254623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 74833397370875815861530581 1753907750879901934254623)
        ·
          refine ⟨2630861626319852901381935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753907750879901934254623 2630861626319852901381935)
          ·
            refine ⟨3946292439479779352072903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630861626319852901381935 3946292439479779352072903)
            ·
              refine ⟨5919438659219669028109355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946292439479779352072903 5919438659219669028109355)
              ·
                refine ⟨8879157988829503542164033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919438659219669028109355 8879157988829503542164033)
                ·
                  refine ⟨6659368491622127656623025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8879157988829503542164033 6659368491622127656623025)
                  ·
                    refine ⟨4994526368716595742467269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6659368491622127656623025 4994526368716595742467269)
                    ·
                      refine ⟨936473694134361701712613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4994526368716595742467269 936473694134361701712613)
                      ·
                        rfl

theorem cell23_1823776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1823776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823776 prefixEnd_1823776 := by exact prefixLift 1823776
  have htrace : WordTrace (prefixWord ++ tailWord_1823776) baseStart_1823776 baseEnd_1823776 := by
    simpa [prefixWord, tailWord_1823776, baseEnd_1823776] using wordTrace_append hprefix tailTrace_1823776
  have hstable : (prefixWord ++ tailWord_1823776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823776).length < 2 ^ (prefixWord ++ tailWord_1823776).sum := by decide
  have hdescent : baseEnd_1823776 < baseStart_1823776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823779 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1823779 : Nat := 118140960795 + 1823779 * 2 ^ 59
def prefixEnd_1823779 : Nat := 4983230072969 + 3 ^ 40 * 1823779 * 2
def baseEnd_1823779 : Nat := 936475234576325189975099

theorem tailTrace_1823779 : CollatzResearch.WordTrace tailWord_1823779 prefixEnd_1823779 936475234576325189975099 := by
  unfold tailWord_1823779
  simp only [CollatzResearch.WordTrace]
  refine ⟨66518684859767634500386391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44345789906511756333590927 66518684859767634500386391)
  ·
    refine ⟨99778027289651451750579587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66518684859767634500386391 99778027289651451750579587)
    ·
      refine ⟨149667040934477177625869381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99778027289651451750579587 149667040934477177625869381)
      ·
        refine ⟨28062570175214470804850509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149667040934477177625869381 28062570175214470804850509)
        ·
          refine ⟨10523463815705426551818941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28062570175214470804850509 10523463815705426551818941)
          ·
            refine ⟨3946298930889534956932103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10523463815705426551818941 3946298930889534956932103)
            ·
              refine ⟨5919448396334302435398155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946298930889534956932103 5919448396334302435398155)
              ·
                refine ⟨8879172594501453653097233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919448396334302435398155 8879172594501453653097233)
                ·
                  refine ⟨6659379445876090239822925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8879172594501453653097233 6659379445876090239822925)
                  ·
                    refine ⟨2497267292203533839933597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6659379445876090239822925 2497267292203533839933597)
                    ·
                      refine ⟨936475234576325189975099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2497267292203533839933597 936475234576325189975099)
                      ·
                        rfl

theorem cell23_1823779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1823779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823779 prefixEnd_1823779 := by exact prefixLift 1823779
  have htrace : WordTrace (prefixWord ++ tailWord_1823779) baseStart_1823779 baseEnd_1823779 := by
    simpa [prefixWord, tailWord_1823779, baseEnd_1823779] using wordTrace_append hprefix tailTrace_1823779
  have hstable : (prefixWord ++ tailWord_1823779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823779).length < 2 ^ (prefixWord ++ tailWord_1823779).sum := by decide
  have hdescent : baseEnd_1823779 < baseStart_1823779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823832 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1823832 : Nat := 118140960795 + 1823832 * 2 ^ 59
def prefixEnd_1823832 : Nat := 4983230072969 + 3 ^ 40 * 1823832 * 2
def baseEnd_1823832 : Nat := 936502449051013482612355

theorem tailTrace_1823832 : CollatzResearch.WordTrace tailWord_1823832 prefixEnd_1823832 936502449051013482612355 := by
  unfold tailWord_1823832
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260308964287812276032875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44347078619050416368043833 33260308964287812276032875)
  ·
    refine ⟨49890463446431718414049313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33260308964287812276032875 49890463446431718414049313)
    ·
      refine ⟨37417847584823788810536985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49890463446431718414049313 37417847584823788810536985)
      ·
        refine ⟨28063385688617841607902739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37417847584823788810536985 28063385688617841607902739)
        ·
          refine ⟨42095078532926762411854109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28063385688617841607902739 42095078532926762411854109)
          ·
            refine ⟨15785654449847535904445291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42095078532926762411854109 15785654449847535904445291)
            ·
              refine ⟨23678481674771303856667937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15785654449847535904445291 23678481674771303856667937)
              ·
                refine ⟨17758861256078477892500953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23678481674771303856667937 17758861256078477892500953)
                ·
                  refine ⟨13319145942058858419375715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17758861256078477892500953 13319145942058858419375715)
                  ·
                    refine ⟨19978718913088287629063573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13319145942058858419375715 19978718913088287629063573)
                    ·
                      refine ⟨936502449051013482612355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19978718913088287629063573 936502449051013482612355)
                      ·
                        rfl

theorem cell23_1823832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1823832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823832 prefixEnd_1823832 := by exact prefixLift 1823832
  have htrace : WordTrace (prefixWord ++ tailWord_1823832) baseStart_1823832 baseEnd_1823832 := by
    simpa [prefixWord, tailWord_1823832, baseEnd_1823832] using wordTrace_append hprefix tailTrace_1823832
  have hstable : (prefixWord ++ tailWord_1823832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823832).length < 2 ^ (prefixWord ++ tailWord_1823832).sum := by decide
  have hdescent : baseEnd_1823832 < baseStart_1823832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823836 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_1823836 : Nat := 118140960795 + 1823836 * 2 ^ 59
def prefixEnd_1823836 : Nat := 4983230072969 + 3 ^ 40 * 1823836 * 2
def baseEnd_1823836 : Nat := 936504502973631466962337

theorem tailTrace_1823836 : CollatzResearch.WordTrace tailWord_1823836 prefixEnd_1823836 936504502973631466962337 := by
  unfold tailWord_1823836
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260381910280566617605681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44347175880374088823474241 33260381910280566617605681)
  ·
    refine ⟨24945286432710424963204261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33260381910280566617605681 24945286432710424963204261)
    ·
      refine ⟨4677241206133204680600799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24945286432710424963204261 4677241206133204680600799)
      ·
        refine ⟨7015861809199807020901199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677241206133204680600799 7015861809199807020901199)
        ·
          refine ⟨10523792713799710531351799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7015861809199807020901199 10523792713799710531351799)
          ·
            refine ⟨15785689070699565797027699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523792713799710531351799 15785689070699565797027699)
            ·
              refine ⟨23678533606049348695541549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15785689070699565797027699 23678533606049348695541549)
              ·
                refine ⟨8879450102268505760828081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23678533606049348695541549 8879450102268505760828081)
                ·
                  refine ⟨6659587576701379320621061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8879450102268505760828081 6659587576701379320621061)
                  ·
                    refine ⟨1248672670631508622616449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6659587576701379320621061 1248672670631508622616449)
                    ·
                      refine ⟨936504502973631466962337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248672670631508622616449 936504502973631466962337)
                      ·
                        rfl

theorem cell23_1823836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_1823836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823836 prefixEnd_1823836 := by exact prefixLift 1823836
  have htrace : WordTrace (prefixWord ++ tailWord_1823836) baseStart_1823836 baseEnd_1823836 := by
    simpa [prefixWord, tailWord_1823836, baseEnd_1823836] using wordTrace_append hprefix tailTrace_1823836
  have hstable : (prefixWord ++ tailWord_1823836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823836).length < 2 ^ (prefixWord ++ tailWord_1823836).sum := by decide
  have hdescent : baseEnd_1823836 < baseStart_1823836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823880 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 3, 4]
def baseStart_1823880 : Nat := 118140960795 + 1823880 * 2 ^ 59
def prefixEnd_1823880 : Nat := 4983230072969 + 3 ^ 40 * 1823880 * 2
def baseEnd_1823880 : Nat := 312175698707476431604045

theorem tailTrace_1823880 : CollatzResearch.WordTrace tailWord_1823880 prefixEnd_1823880 312175698707476431604045 := by
  unfold tailWord_1823880
  simp only [CollatzResearch.WordTrace]
  refine ⟨33261184316200864374906547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44348245754934485833208729 33261184316200864374906547)
  ·
    refine ⟨49891776474301296562359821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33261184316200864374906547 49891776474301296562359821)
    ·
      refine ⟨18709416177862986210884933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49891776474301296562359821 18709416177862986210884933)
      ·
        refine ⟨3508015533349309914540925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18709416177862986210884933 3508015533349309914540925)
        ·
          refine ⟨1315505825005991217952847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3508015533349309914540925 1315505825005991217952847)
          ·
            refine ⟨1973258737508986826929271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315505825005991217952847 1973258737508986826929271)
            ·
              refine ⟨2959888106263480240393907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973258737508986826929271 2959888106263480240393907)
              ·
                refine ⟨4439832159395220360590861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959888106263480240393907 4439832159395220360590861)
                ·
                  refine ⟨1664937059773207635221573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4439832159395220360590861 1664937059773207635221573)
                  ·
                    refine ⟨312175698707476431604045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1664937059773207635221573 312175698707476431604045)
                    ·
                      rfl

theorem cell23_1823880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_1823880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823880 prefixEnd_1823880 := by exact prefixLift 1823880
  have htrace : WordTrace (prefixWord ++ tailWord_1823880) baseStart_1823880 baseEnd_1823880 := by
    simpa [prefixWord, tailWord_1823880, baseEnd_1823880] using wordTrace_append hprefix tailTrace_1823880
  have hstable : (prefixWord ++ tailWord_1823880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823880).length < 2 ^ (prefixWord ++ tailWord_1823880).sum := by decide
  have hdescent : baseEnd_1823880 < baseStart_1823880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823919 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 6, 4]
def baseStart_1823919 : Nat := 118140960795 + 1823919 * 2 ^ 59
def prefixEnd_1823919 : Nat := 4983230072969 + 3 ^ 40 * 1823919 * 2
def baseEnd_1823919 : Nat := 312182373955984880741485

theorem tailTrace_1823919 : CollatzResearch.WordTrace tailWord_1823919 prefixEnd_1823919 312182373955984880741485 := by
  unfold tailWord_1823919
  simp only [CollatzResearch.WordTrace]
  refine ⟨66523791079260438410482811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44349194052840292273655207 66523791079260438410482811)
  ·
    refine ⟨99785686618890657615724217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66523791079260438410482811 99785686618890657615724217)
    ·
      refine ⟨74839264964167993211793163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99785686618890657615724217 74839264964167993211793163)
      ·
        refine ⟨112258897446251989817689745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74839264964167993211793163 112258897446251989817689745)
        ·
          refine ⟨84194173084688992363267309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112258897446251989817689745 84194173084688992363267309)
          ·
            refine ⟨31572814906758372136225241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84194173084688992363267309 31572814906758372136225241)
            ·
              refine ⟨23679611180068779102168931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31572814906758372136225241 23679611180068779102168931)
              ·
                refine ⟨35519416770103168653253397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23679611180068779102168931 35519416770103168653253397)
                ·
                  refine ⟨1664972661098586030621253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35519416770103168653253397 1664972661098586030621253)
                  ·
                    refine ⟨312182373955984880741485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1664972661098586030621253 312182373955984880741485)
                    ·
                      rfl

theorem cell23_1823919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_1823919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823919 prefixEnd_1823919 := by exact prefixLift 1823919
  have htrace : WordTrace (prefixWord ++ tailWord_1823919) baseStart_1823919 baseEnd_1823919 := by
    simpa [prefixWord, tailWord_1823919, baseEnd_1823919] using wordTrace_append hprefix tailTrace_1823919
  have hstable : (prefixWord ++ tailWord_1823919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823919).length < 2 ^ (prefixWord ++ tailWord_1823919).sum := by decide
  have hdescent : baseEnd_1823919 < baseStart_1823919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823937 : List Nat := [1, 2, 6, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1823937 : Nat := 118140960795 + 1823937 * 2 ^ 59
def prefixEnd_1823937 : Nat := 4983230072969 + 3 ^ 40 * 1823937 * 2
def baseEnd_1823937 : Nat := 936556364519735571799373

theorem tailTrace_1823937 : CollatzResearch.WordTrace tailWord_1823937 prefixEnd_1823937 936556364519735571799373 := by
  unfold tailWord_1823937
  simp only [CollatzResearch.WordTrace]
  refine ⟨66524447593195227484638065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44349631728796818323092043 66524447593195227484638065)
  ·
    refine ⟨49893335694896420613478549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66524447593195227484638065 49893335694896420613478549)
    ·
      refine ⟨2338750110698269716256807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49893335694896420613478549 2338750110698269716256807)
      ·
        refine ⟨3508125166047404574385211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338750110698269716256807 3508125166047404574385211)
        ·
          refine ⟨5262187749071106861577817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508125166047404574385211 5262187749071106861577817)
          ·
            refine ⟨3946640811803330146183363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5262187749071106861577817 3946640811803330146183363)
            ·
              refine ⟨5919961217704995219275045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946640811803330146183363 5919961217704995219275045)
              ·
                refine ⟨1109992728319686603614071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5919961217704995219275045 1109992728319686603614071)
                ·
                  refine ⟨1664989092479529905421107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1109992728319686603614071 1664989092479529905421107)
                  ·
                    refine ⟨2497483638719294858131661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1664989092479529905421107 2497483638719294858131661)
                    ·
                      refine ⟨936556364519735571799373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2497483638719294858131661 936556364519735571799373)
                      ·
                        rfl

theorem cell23_1823937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1823937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823937 prefixEnd_1823937 := by exact prefixLift 1823937
  have htrace : WordTrace (prefixWord ++ tailWord_1823937) baseStart_1823937 baseEnd_1823937 := by
    simpa [prefixWord, tailWord_1823937, baseEnd_1823937] using wordTrace_append hprefix tailTrace_1823937
  have hstable : (prefixWord ++ tailWord_1823937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823937).length < 2 ^ (prefixWord ++ tailWord_1823937).sum := by decide
  have hdescent : baseEnd_1823937 < baseStart_1823937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823946 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_1823946 : Nat := 118140960795 + 1823946 * 2 ^ 59
def prefixEnd_1823946 : Nat := 4983230072969 + 3 ^ 40 * 1823946 * 2
def baseEnd_1823946 : Nat := 936560985845626036586831

theorem tailTrace_1823946 : CollatzResearch.WordTrace tailWord_1823946 prefixEnd_1823946 936560985845626036586831 := by
  unfold tailWord_1823946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16631193962540655505428923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44349850566775081347810461 16631193962540655505428923)
  ·
    refine ⟨24946790943810983258143385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16631193962540655505428923 24946790943810983258143385)
    ·
      refine ⟨18710093207858237443607539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24946790943810983258143385 18710093207858237443607539)
      ·
        refine ⟨28065139811787356165411309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18710093207858237443607539 28065139811787356165411309)
        ·
          refine ⟨10524427429420258562029241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28065139811787356165411309 10524427429420258562029241)
          ·
            refine ⟨7893320572065193921521931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10524427429420258562029241 7893320572065193921521931)
            ·
              refine ⟨11839980858097790882282897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893320572065193921521931 11839980858097790882282897)
              ·
                refine ⟨8879985643573343161712173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11839980858097790882282897 8879985643573343161712173)
                ·
                  refine ⟨3329994616340003685642065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8879985643573343161712173 3329994616340003685642065)
                  ·
                    refine ⟨2497495962255002764231549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3329994616340003685642065 2497495962255002764231549)
                    ·
                      refine ⟨936560985845626036586831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2497495962255002764231549 936560985845626036586831)
                      ·
                        rfl

theorem cell23_1823946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_1823946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823946 prefixEnd_1823946 := by exact prefixLift 1823946
  have htrace : WordTrace (prefixWord ++ tailWord_1823946) baseStart_1823946 baseEnd_1823946 := by
    simpa [prefixWord, tailWord_1823946, baseEnd_1823946] using wordTrace_append hprefix tailTrace_1823946
  have hstable : (prefixWord ++ tailWord_1823946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823946).length < 2 ^ (prefixWord ++ tailWord_1823946).sum := by decide
  have hdescent : baseEnd_1823946 < baseStart_1823946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823960 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 3, 2, 2]
def baseStart_1823960 : Nat := 118140960795 + 1823960 * 2 ^ 59
def prefixEnd_1823960 : Nat := 4983230072969 + 3 ^ 40 * 1823960 * 2
def baseEnd_1823960 : Nat := 936568174574788981811767

theorem tailTrace_1823960 : CollatzResearch.WordTrace tailWord_1823960 prefixEnd_1823960 936568174574788981811767 := by
  unfold tailWord_1823960
  simp only [CollatzResearch.WordTrace]
  refine ⟨33262643236055951206362667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44350190981407934941816889 33262643236055951206362667)
  ·
    refine ⟨49893964854083926809544001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33262643236055951206362667 49893964854083926809544001)
    ·
      refine ⟨37420473640562945107158001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49893964854083926809544001 37420473640562945107158001)
      ·
        refine ⟨28065355230422208830368501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37420473640562945107158001 28065355230422208830368501)
        ·
          refine ⟨2631127052852082077847047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28065355230422208830368501 2631127052852082077847047)
          ·
            refine ⟨3946690579278123116770571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631127052852082077847047 3946690579278123116770571)
            ·
              refine ⟨5920035868917184675155857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946690579278123116770571 5920035868917184675155857)
              ·
                refine ⟨4440026901687888506366893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5920035868917184675155857 4440026901687888506366893)
                ·
                  refine ⟨1665010088132958189887585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4440026901687888506366893 1665010088132958189887585)
                  ·
                    refine ⟨1248757566099718642415689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1665010088132958189887585 1248757566099718642415689)
                    ·
                      refine ⟨936568174574788981811767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248757566099718642415689 936568174574788981811767)
                      ·
                        rfl

theorem cell23_1823960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_1823960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823960 prefixEnd_1823960 := by exact prefixLift 1823960
  have htrace : WordTrace (prefixWord ++ tailWord_1823960) baseStart_1823960 baseEnd_1823960 := by
    simpa [prefixWord, tailWord_1823960, baseEnd_1823960] using wordTrace_append hprefix tailTrace_1823960
  have hstable : (prefixWord ++ tailWord_1823960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823960).length < 2 ^ (prefixWord ++ tailWord_1823960).sum := by decide
  have hdescent : baseEnd_1823960 < baseStart_1823960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823976 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1823976 : Nat := 118140960795 + 1823976 * 2 ^ 59
def prefixEnd_1823976 : Nat := 4983230072969 + 3 ^ 40 * 1823976 * 2
def baseEnd_1823976 : Nat := 936576390265260919211693

theorem tailTrace_1823976 : CollatzResearch.WordTrace tailWord_1823976 prefixEnd_1823976 936576390265260919211693 := by
  unfold tailWord_1823976
  simp only [CollatzResearch.WordTrace]
  refine ⟨33262935020026968572653891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44350580026702624763538521 33262935020026968572653891)
  ·
    refine ⟨49894402530040452858980837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33262935020026968572653891 49894402530040452858980837)
    ·
      refine ⟨9355200474382584911058907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49894402530040452858980837 9355200474382584911058907)
      ·
        refine ⟨14032800711573877366588361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9355200474382584911058907 14032800711573877366588361)
        ·
          refine ⟨10524600533680408024941271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14032800711573877366588361 10524600533680408024941271)
          ·
            refine ⟨15786900800520612037411907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10524600533680408024941271 15786900800520612037411907)
            ·
              refine ⟨23680351200780918056117861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15786900800520612037411907 23680351200780918056117861)
              ·
                refine ⟨4440065850146422135522099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23680351200780918056117861 4440065850146422135522099)
                ·
                  refine ⟨6660098775219633203283149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440065850146422135522099 6660098775219633203283149)
                  ·
                    refine ⟨2497537040707362451231181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6660098775219633203283149 2497537040707362451231181)
                    ·
                      refine ⟨936576390265260919211693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2497537040707362451231181 936576390265260919211693)
                      ·
                        rfl

theorem cell23_1823976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1823976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823976 prefixEnd_1823976 := by exact prefixLift 1823976
  have htrace : WordTrace (prefixWord ++ tailWord_1823976) baseStart_1823976 baseEnd_1823976 := by
    simpa [prefixWord, tailWord_1823976, baseEnd_1823976] using wordTrace_append hprefix tailTrace_1823976
  have hstable : (prefixWord ++ tailWord_1823976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823976).length < 2 ^ (prefixWord ++ tailWord_1823976).sum := by decide
  have hdescent : baseEnd_1823976 < baseStart_1823976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823980 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 3]
def baseStart_1823980 : Nat := 118140960795 + 1823980 * 2 ^ 59
def prefixEnd_1823980 : Nat := 4983230072969 + 3 ^ 40 * 1823980 * 2
def baseEnd_1823980 : Nat := 936578444187878903561675

theorem tailTrace_1823980 : CollatzResearch.WordTrace tailWord_1823980 prefixEnd_1823980 936578444187878903561675 := by
  unfold tailWord_1823980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33263007966019722914226697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44350677288026297218968929 33263007966019722914226697)
  ·
    refine ⟨24947255974514792185670023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33263007966019722914226697 24947255974514792185670023)
    ·
      refine ⟨37420883961772188278505035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24947255974514792185670023 37420883961772188278505035)
      ·
        refine ⟨56131325942658282417757553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37420883961772188278505035 56131325942658282417757553)
        ·
          refine ⟨42098494456993711813318165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56131325942658282417757553 42098494456993711813318165)
          ·
            refine ⟨1973366927671580241249289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42098494456993711813318165 1973366927671580241249289)
            ·
              refine ⟨1480025195753685180936967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973366927671580241249289 1480025195753685180936967)
              ·
                refine ⟨2220037793630527771405451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480025195753685180936967 2220037793630527771405451)
                ·
                  refine ⟨3330056690445791657108177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220037793630527771405451 3330056690445791657108177)
                  ·
                    refine ⟨2497542517834343742831133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3330056690445791657108177 2497542517834343742831133)
                    ·
                      refine ⟨936578444187878903561675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2497542517834343742831133 936578444187878903561675)
                      ·
                        rfl

theorem cell23_1823980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_1823980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1823980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1823980 prefixEnd_1823980 := by exact prefixLift 1823980
  have htrace : WordTrace (prefixWord ++ tailWord_1823980) baseStart_1823980 baseEnd_1823980 := by
    simpa [prefixWord, tailWord_1823980, baseEnd_1823980] using wordTrace_append hprefix tailTrace_1823980
  have hstable : (prefixWord ++ tailWord_1823980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823980).length < 2 ^ (prefixWord ++ tailWord_1823980).sum := by decide
  have hdescent : baseEnd_1823980 < baseStart_1823980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824009 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 2, 6]
def baseStart_1824009 : Nat := 118140960795 + 1824009 * 2 ^ 59
def prefixEnd_1824009 : Nat := 4983230072969 + 3 ^ 40 * 1824009 * 2
def baseEnd_1824009 : Nat := 312197778375619763366347

theorem tailTrace_1824009 : CollatzResearch.WordTrace tailWord_1824009 prefixEnd_1824009 312197778375619763366347 := by
  unfold tailWord_1824009
  simp only [CollatzResearch.WordTrace]
  refine ⟨66527073648934383781259081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44351382432622922520839387 66527073648934383781259081)
  ·
    refine ⟨49895305236700787835944311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66527073648934383781259081 49895305236700787835944311)
    ·
      refine ⟨74842957855051181753916467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49895305236700787835944311 74842957855051181753916467)
      ·
        refine ⟨112264436782576772630874701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74842957855051181753916467 112264436782576772630874701)
        ·
          refine ⟨42099163793466289736578013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112264436782576772630874701 42099163793466289736578013)
          ·
            refine ⟨15787186422549858651216755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42099163793466289736578013 15787186422549858651216755)
            ·
              refine ⟨23680779633824787976825133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15787186422549858651216755 23680779633824787976825133)
              ·
                refine ⟨8880292362684295491309425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23680779633824787976825133 8880292362684295491309425)
                ·
                  refine ⟨6660219272013221618482069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8880292362684295491309425 6660219272013221618482069)
                  ·
                    refine ⟨312197778375619763366347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6660219272013221618482069 312197778375619763366347)
                    ·
                      rfl

theorem cell23_1824009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_1824009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824009 prefixEnd_1824009 := by exact prefixLift 1824009
  have htrace : WordTrace (prefixWord ++ tailWord_1824009) baseStart_1824009 baseEnd_1824009 := by
    simpa [prefixWord, tailWord_1824009, baseEnd_1824009] using wordTrace_append hprefix tailTrace_1824009
  have hstable : (prefixWord ++ tailWord_1824009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824009).length < 2 ^ (prefixWord ++ tailWord_1824009).sum := by decide
  have hdescent : baseEnd_1824009 < baseStart_1824009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824036 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1824036 : Nat := 118140960795 + 1824036 * 2 ^ 59
def prefixEnd_1824036 : Nat := 4983230072969 + 3 ^ 40 * 1824036 * 2
def baseEnd_1824036 : Nat := 936607199104530684461417

theorem tailTrace_1824036 : CollatzResearch.WordTrace tailWord_1824036 prefixEnd_1824036 936607199104530684461417 := by
  unfold tailWord_1824036
  simp only [CollatzResearch.WordTrace]
  refine ⟨33264029209918283696245981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44352038946557711594994641 33264029209918283696245981)
  ·
    refine ⟨12474010953719356386092243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33264029209918283696245981 12474010953719356386092243)
    ·
      refine ⟨18711016430579034579138365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12474010953719356386092243 18711016430579034579138365)
      ·
        refine ⟨7016631161467137967176887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18711016430579034579138365 7016631161467137967176887)
        ·
          refine ⟨10524946742200706950765331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016631161467137967176887 10524946742200706950765331)
          ·
            refine ⟨15787420113301060426147997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10524946742200706950765331 15787420113301060426147997)
            ·
              refine ⟨5920282542487897659805499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15787420113301060426147997 5920282542487897659805499)
              ·
                refine ⟨8880423813731846489708249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5920282542487897659805499 8880423813731846489708249)
                ·
                  refine ⟨6660317860298884867281187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8880423813731846489708249 6660317860298884867281187)
                  ·
                    refine ⟨9990476790448327300921781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6660317860298884867281187 9990476790448327300921781)
                    ·
                      refine ⟨936607199104530684461417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9990476790448327300921781 936607199104530684461417)
                      ·
                        rfl

theorem cell23_1824036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1824036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824036 prefixEnd_1824036 := by exact prefixLift 1824036
  have htrace : WordTrace (prefixWord ++ tailWord_1824036) baseStart_1824036 baseEnd_1824036 := by
    simpa [prefixWord, tailWord_1824036, baseEnd_1824036] using wordTrace_append hprefix tailTrace_1824036
  have hstable : (prefixWord ++ tailWord_1824036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824036).length < 2 ^ (prefixWord ++ tailWord_1824036).sum := by decide
  have hdescent : baseEnd_1824036 < baseStart_1824036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824050 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_1824050 : Nat := 118140960795 + 1824050 * 2 ^ 59
def prefixEnd_1824050 : Nat := 4983230072969 + 3 ^ 40 * 1824050 * 2
def baseEnd_1824050 : Nat := 936614387833693629686353

theorem tailTrace_1824050 : CollatzResearch.WordTrace tailWord_1824050 prefixEnd_1824050 936614387833693629686353 := by
  unfold tailWord_1824050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16632142260446461945875401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44352379361190565189001069 16632142260446461945875401)
  ·
    refine ⟨12474106695334846459406551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16632142260446461945875401 12474106695334846459406551)
    ·
      refine ⟨18711160043002269689109827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12474106695334846459406551 18711160043002269689109827)
      ·
        refine ⟨28066740064503404533664741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18711160043002269689109827 28066740064503404533664741)
        ·
          refine ⟨5262513762094388350062139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28066740064503404533664741 5262513762094388350062139)
          ·
            refine ⟨7893770643141582525093209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262513762094388350062139 7893770643141582525093209)
            ·
              refine ⟨5920327982356186893819907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7893770643141582525093209 5920327982356186893819907)
              ·
                refine ⟨8880491973534280340729861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5920327982356186893819907 8880491973534280340729861)
                ·
                  refine ⟨1665092245037677563886849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8880491973534280340729861 1665092245037677563886849)
                  ·
                    refine ⟨1248819183778258172915137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1665092245037677563886849 1248819183778258172915137)
                    ·
                      refine ⟨936614387833693629686353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248819183778258172915137 936614387833693629686353)
                      ·
                        rfl

theorem cell23_1824050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_1824050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824050 prefixEnd_1824050 := by exact prefixLift 1824050
  have htrace : WordTrace (prefixWord ++ tailWord_1824050) baseStart_1824050 baseEnd_1824050 := by
    simpa [prefixWord, tailWord_1824050, baseEnd_1824050] using wordTrace_append hprefix tailTrace_1824050
  have hstable : (prefixWord ++ tailWord_1824050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824050).length < 2 ^ (prefixWord ++ tailWord_1824050).sum := by decide
  have hdescent : baseEnd_1824050 < baseStart_1824050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824061 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1824061 : Nat := 118140960795 + 1824061 * 2 ^ 59
def prefixEnd_1824061 : Nat := 4983230072969 + 3 ^ 40 * 1824061 * 2
def baseEnd_1824061 : Nat := 936620036120893086648803

theorem tailTrace_1824061 : CollatzResearch.WordTrace tailWord_1824061 prefixEnd_1824061 936620036120893086648803 := by
  unfold tailWord_1824061
  simp only [CollatzResearch.WordTrace]
  refine ⟨66528970244745996662152037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44352646829830664441434691 66528970244745996662152037)
  ·
    refine ⟨12474181920889874374153507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66528970244745996662152037 12474181920889874374153507)
    ·
      refine ⟨18711272881334811561230261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12474181920889874374153507 18711272881334811561230261)
      ·
        refine ⟨1754181832625138583865337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18711272881334811561230261 1754181832625138583865337)
        ·
          refine ⟨1315636374468853937899003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1754181832625138583865337 1315636374468853937899003)
          ·
            refine ⟨1973454561703280906848505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315636374468853937899003 1973454561703280906848505)
            ·
              refine ⟨1480090921277460680136379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973454561703280906848505 1480090921277460680136379)
              ·
                refine ⟨2220136381916191020204569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480090921277460680136379 2220136381916191020204569)
                ·
                  refine ⟨1665102286437143265153427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2220136381916191020204569 1665102286437143265153427)
                  ·
                    refine ⟨2497653429655714897730141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1665102286437143265153427 2497653429655714897730141)
                    ·
                      refine ⟨936620036120893086648803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2497653429655714897730141 936620036120893086648803)
                      ·
                        rfl

theorem cell23_1824061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1824061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824061 prefixEnd_1824061 := by exact prefixLift 1824061
  have htrace : WordTrace (prefixWord ++ tailWord_1824061) baseStart_1824061 baseEnd_1824061 := by
    simpa [prefixWord, tailWord_1824061, baseEnd_1824061] using wordTrace_append hprefix tailTrace_1824061
  have hstable : (prefixWord ++ tailWord_1824061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824061).length < 2 ^ (prefixWord ++ tailWord_1824061).sum := by decide
  have hdescent : baseEnd_1824061 < baseStart_1824061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824069 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_1824069 : Nat := 118140960795 + 1824069 * 2 ^ 59
def prefixEnd_1824069 : Nat := 4983230072969 + 3 ^ 40 * 1824069 * 2
def baseEnd_1824069 : Nat := 312208047988709685116255

theorem tailTrace_1824069 : CollatzResearch.WordTrace tailWord_1824069 prefixEnd_1824069 312208047988709685116255 := by
  unfold tailWord_1824069
  simp only [CollatzResearch.WordTrace]
  refine ⟨66529262028717014028443261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44352841352478009352295507 66529262028717014028443261)
  ·
    refine ⟨24948473260768880260666223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66529262028717014028443261 24948473260768880260666223)
    ·
      refine ⟨37422709891153320390999335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24948473260768880260666223 37422709891153320390999335)
      ·
        refine ⟨56134064836729980586499003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37422709891153320390999335 56134064836729980586499003)
        ·
          refine ⟨84201097255094970879748505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56134064836729980586499003 84201097255094970879748505)
          ·
            refine ⟨63150822941321228159811379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84201097255094970879748505 63150822941321228159811379)
            ·
              refine ⟨94726234411981842239717069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63150822941321228159811379 94726234411981842239717069)
              ·
                refine ⟨35522337904493190839893901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94726234411981842239717069 35522337904493190839893901)
                ·
                  refine ⟨13320876714184946564960213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35522337904493190839893901 13320876714184946564960213)
                  ·
                    refine ⟨312208047988709685116255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13320876714184946564960213 312208047988709685116255)
                    ·
                      rfl

theorem cell23_1824069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_1824069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824069 prefixEnd_1824069 := by exact prefixLift 1824069
  have htrace : WordTrace (prefixWord ++ tailWord_1824069) baseStart_1824069 baseEnd_1824069 := by
    simpa [prefixWord, tailWord_1824069, baseEnd_1824069] using wordTrace_append hprefix tailTrace_1824069
  have hstable : (prefixWord ++ tailWord_1824069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824069).length < 2 ^ (prefixWord ++ tailWord_1824069).sum := by decide
  have hdescent : baseEnd_1824069 < baseStart_1824069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824096 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1824096 : Nat := 118140960795 + 1824096 * 2 ^ 59
def prefixEnd_1824096 : Nat := 4983230072969 + 3 ^ 40 * 1824096 * 2
def baseEnd_1824096 : Nat := 936638007943800449711141

theorem tailTrace_1824096 : CollatzResearch.WordTrace tailWord_1824096 prefixEnd_1824096 936638007943800449711141 := by
  unfold tailWord_1824096
  simp only [CollatzResearch.WordTrace]
  refine ⟨33265123399809598819838071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44353497866412798426450761 33265123399809598819838071)
  ·
    refine ⟨49897685099714398229757107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33265123399809598819838071 49897685099714398229757107)
    ·
      refine ⟨74846527649571597344635661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49897685099714398229757107 74846527649571597344635661)
      ·
        refine ⟨28067447868589349004238373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74846527649571597344635661 28067447868589349004238373)
        ·
          refine ⟨5262646475360502938294695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28067447868589349004238373 5262646475360502938294695)
          ·
            refine ⟨7893969713040754407442043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262646475360502938294695 7893969713040754407442043)
            ·
              refine ⟨11840954569561131611163065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893969713040754407442043 11840954569561131611163065)
              ·
                refine ⟨8880715927170848708372299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11840954569561131611163065 8880715927170848708372299)
                ·
                  refine ⟨13321073890756273062558449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8880715927170848708372299 13321073890756273062558449)
                  ·
                    refine ⟨9990805418067204796918837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13321073890756273062558449 9990805418067204796918837)
                    ·
                      refine ⟨936638007943800449711141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9990805418067204796918837 936638007943800449711141)
                      ·
                        rfl

theorem cell23_1824096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1824096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824096 prefixEnd_1824096 := by exact prefixLift 1824096
  have htrace : WordTrace (prefixWord ++ tailWord_1824096) baseStart_1824096 baseEnd_1824096 := by
    simpa [prefixWord, tailWord_1824096, baseEnd_1824096] using wordTrace_append hprefix tailTrace_1824096
  have hstable : (prefixWord ++ tailWord_1824096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824096).length < 2 ^ (prefixWord ++ tailWord_1824096).sum := by decide
  have hdescent : baseEnd_1824096 < baseStart_1824096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824123 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 2, 4, 2]
def baseStart_1824123 : Nat := 118140960795 + 1824123 * 2 ^ 59
def prefixEnd_1824123 : Nat := 4983230072969 + 3 ^ 40 * 1824123 * 2
def baseEnd_1824123 : Nat := 936651871921471844073517

theorem tailTrace_1824123 : CollatzResearch.WordTrace tailWord_1824123 prefixEnd_1824123 936651871921471844073517 := by
  unfold tailWord_1824123
  simp only [CollatzResearch.WordTrace]
  refine ⟨66531231570521381250909023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44354154380347587500606015 66531231570521381250909023)
  ·
    refine ⟨99796847355782071876363535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66531231570521381250909023 99796847355782071876363535)
    ·
      refine ⟨149695271033673107814545303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99796847355782071876363535 149695271033673107814545303)
      ·
        refine ⟨224542906550509661721817955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149695271033673107814545303 224542906550509661721817955)
        ·
          refine ⟨336814359825764492582726933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224542906550509661721817955 336814359825764492582726933)
          ·
            refine ⟨15788173116832710589815325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 336814359825764492582726933 15788173116832710589815325)
            ·
              refine ⟨5920564918812266471180747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15788173116832710589815325 5920564918812266471180747)
              ·
                refine ⟨8880847378218399706771121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5920564918812266471180747 8880847378218399706771121)
                ·
                  refine ⟨6660635533663799780078341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8880847378218399706771121 6660635533663799780078341)
                  ·
                    refine ⟨1248869162561962458764689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6660635533663799780078341 1248869162561962458764689)
                    ·
                      refine ⟨936651871921471844073517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248869162561962458764689 936651871921471844073517)
                      ·
                        rfl

theorem cell23_1824123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4, 2].length) (baseStart_1824123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824123 prefixEnd_1824123 := by exact prefixLift 1824123
  have htrace : WordTrace (prefixWord ++ tailWord_1824123) baseStart_1824123 baseEnd_1824123 := by
    simpa [prefixWord, tailWord_1824123, baseEnd_1824123] using wordTrace_append hprefix tailTrace_1824123
  have hstable : (prefixWord ++ tailWord_1824123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824123).length < 2 ^ (prefixWord ++ tailWord_1824123).sum := by decide
  have hdescent : baseEnd_1824123 < baseStart_1824123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824176 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 3, 5]
def baseStart_1824176 : Nat := 118140960795 + 1824176 * 2 ^ 59
def prefixEnd_1824176 : Nat := 4983230072969 + 3 ^ 40 * 1824176 * 2
def baseEnd_1824176 : Nat := 312226362132053378903591

theorem tailTrace_1824176 : CollatzResearch.WordTrace tailWord_1824176 prefixEnd_1824176 312226362132053378903591 := by
  unfold tailWord_1824176
  simp only [CollatzResearch.WordTrace]
  refine ⟨33266582319664685651294191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44355443092886247535058921 33266582319664685651294191)
  ·
    refine ⟨49899873479497028476941287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33266582319664685651294191 49899873479497028476941287)
    ·
      refine ⟨74849810219245542715411931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49899873479497028476941287 74849810219245542715411931)
      ·
        refine ⟨112274715328868314073117897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74849810219245542715411931 112274715328868314073117897)
        ·
          refine ⟨84206036496651235554838423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112274715328868314073117897 84206036496651235554838423)
          ·
            refine ⟨126309054744976853332257635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84206036496651235554838423 126309054744976853332257635)
            ·
              refine ⟨189463582117465279998386453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126309054744976853332257635 189463582117465279998386453)
              ·
                refine ⟨8881105411756184999924365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189463582117465279998386453 8881105411756184999924365)
                ·
                  refine ⟨3330414529408569374971637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8881105411756184999924365 3330414529408569374971637)
                  ·
                    refine ⟨312226362132053378903591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3330414529408569374971637 312226362132053378903591)
                    ·
                      rfl

theorem cell23_1824176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_1824176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824176 prefixEnd_1824176 := by exact prefixLift 1824176
  have htrace : WordTrace (prefixWord ++ tailWord_1824176) baseStart_1824176 baseEnd_1824176 := by
    simpa [prefixWord, tailWord_1824176, baseEnd_1824176] using wordTrace_append hprefix tailTrace_1824176
  have hstable : (prefixWord ++ tailWord_1824176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824176).length < 2 ^ (prefixWord ++ tailWord_1824176).sum := by decide
  have hdescent : baseEnd_1824176 < baseStart_1824176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824183 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 3, 5, 2]
def baseStart_1824183 : Nat := 118140960795 + 1824183 * 2 ^ 59
def prefixEnd_1824183 : Nat := 4983230072969 + 3 ^ 40 * 1824183 * 2
def baseEnd_1824183 : Nat := 936682680760741609323241

theorem tailTrace_1824183 : CollatzResearch.WordTrace tailWord_1824183 prefixEnd_1824183 936682680760741609323241 := by
  unfold tailWord_1824183
  simp only [CollatzResearch.WordTrace]
  refine ⟨66533419950304011498093203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44355613300202674332062135 66533419950304011498093203)
  ·
    refine ⟨99800129925456017247139805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66533419950304011498093203 99800129925456017247139805)
    ·
      refine ⟨37425048722046006467677427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99800129925456017247139805 37425048722046006467677427)
      ·
        refine ⟨56137573083069009701516141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37425048722046006467677427 56137573083069009701516141)
        ·
          refine ⟨21051589906150878638068553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56137573083069009701516141 21051589906150878638068553)
          ·
            refine ⟨15788692429613158978551415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21051589906150878638068553 15788692429613158978551415)
            ·
              refine ⟨23683038644419738467827123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15788692429613158978551415 23683038644419738467827123)
              ·
                refine ⟨35524557966629607701740685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23683038644419738467827123 35524557966629607701740685)
                ·
                  refine ⟨13321709237486102888152757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35524557966629607701740685 13321709237486102888152757)
                  ·
                    refine ⟨1248910241014322145764321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13321709237486102888152757 1248910241014322145764321)
                    ·
                      refine ⟨936682680760741609323241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248910241014322145764321 936682680760741609323241)
                      ·
                        rfl

theorem cell23_1824183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_1824183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824183 prefixEnd_1824183 := by exact prefixLift 1824183
  have htrace : WordTrace (prefixWord ++ tailWord_1824183) baseStart_1824183 baseEnd_1824183 := by
    simpa [prefixWord, tailWord_1824183, baseEnd_1824183] using wordTrace_append hprefix tailTrace_1824183
  have hstable : (prefixWord ++ tailWord_1824183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824183).length < 2 ^ (prefixWord ++ tailWord_1824183).sum := by decide
  have hdescent : baseEnd_1824183 < baseStart_1824183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824200 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_1824200 : Nat := 118140960795 + 1824200 * 2 ^ 59
def prefixEnd_1824200 : Nat := 4983230072969 + 3 ^ 40 * 1824200 * 2
def baseEnd_1824200 : Nat := 936691409931868042810663

theorem tailTrace_1824200 : CollatzResearch.WordTrace tailWord_1824200 prefixEnd_1824200 936691409931868042810663 := by
  unfold tailWord_1824200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33267019995621211700731027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44356026660828282267641369 33267019995621211700731027)
  ·
    refine ⟨49900529993431817551096541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33267019995621211700731027 49900529993431817551096541)
    ·
      refine ⟨18712698747536931581661203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49900529993431817551096541 18712698747536931581661203)
      ·
        refine ⟨28069048121305397372491805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18712698747536931581661203 28069048121305397372491805)
        ·
          refine ⟨10525893045489524014684427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28069048121305397372491805 10525893045489524014684427)
          ·
            refine ⟨15788839568234286022026641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10525893045489524014684427 15788839568234286022026641)
            ·
              refine ⟨11841629676175714516519981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15788839568234286022026641 11841629676175714516519981)
              ·
                refine ⟨4440611128565892943694993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11841629676175714516519981 4440611128565892943694993)
                ·
                  refine ⟨3330458346424419707771245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4440611128565892943694993 3330458346424419707771245)
                  ·
                    refine ⟨1248921879909157390414217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3330458346424419707771245 1248921879909157390414217)
                    ·
                      refine ⟨936691409931868042810663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1248921879909157390414217 936691409931868042810663)
                      ·
                        rfl

theorem cell23_1824200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_1824200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824200 prefixEnd_1824200 := by exact prefixLift 1824200
  have htrace : WordTrace (prefixWord ++ tailWord_1824200) baseStart_1824200 baseEnd_1824200 := by
    simpa [prefixWord, tailWord_1824200, baseEnd_1824200] using wordTrace_append hprefix tailTrace_1824200
  have hstable : (prefixWord ++ tailWord_1824200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824200).length < 2 ^ (prefixWord ++ tailWord_1824200).sum := by decide
  have hdescent : baseEnd_1824200 < baseStart_1824200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824207 : List Nat := [1, 1, 2, 1, 1, 4, 5, 3, 1, 1, 3]
def baseStart_1824207 : Nat := 118140960795 + 1824207 * 2 ^ 59
def prefixEnd_1824207 : Nat := 4983230072969 + 3 ^ 40 * 1824207 * 2
def baseEnd_1824207 : Nat := 936695004296449515423131

theorem tailTrace_1824207 : CollatzResearch.WordTrace tailWord_1824207 prefixEnd_1824207 936695004296449515423131 := by
  unfold tailWord_1824207
  simp only [CollatzResearch.WordTrace]
  refine ⟨66534295302217063596966875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44356196868144709064644583 66534295302217063596966875)
  ·
    refine ⟨99801442953325595395450313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66534295302217063596966875 99801442953325595395450313)
    ·
      refine ⟨74851082214994196546587735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99801442953325595395450313 74851082214994196546587735)
      ·
        refine ⟨112276623322491294819881603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74851082214994196546587735 112276623322491294819881603)
        ·
          refine ⟨168414934983736942229822405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112276623322491294819881603 168414934983736942229822405)
          ·
            refine ⟨31577800309450676668091701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168414934983736942229822405 31577800309450676668091701)
            ·
              refine ⟨2960418779011000937633597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31577800309450676668091701 2960418779011000937633597)
              ·
                refine ⟨1110157042129125351612599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2960418779011000937633597 1110157042129125351612599)
                ·
                  refine ⟨1665235563193688027418899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110157042129125351612599 1665235563193688027418899)
                  ·
                    refine ⟨2497853344790532041128349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1665235563193688027418899 2497853344790532041128349)
                    ·
                      refine ⟨936695004296449515423131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2497853344790532041128349 936695004296449515423131)
                      ·
                        rfl

theorem cell23_1824207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 1, 3].length) (baseStart_1824207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824207 prefixEnd_1824207 := by exact prefixLift 1824207
  have htrace : WordTrace (prefixWord ++ tailWord_1824207) baseStart_1824207 baseEnd_1824207 := by
    simpa [prefixWord, tailWord_1824207, baseEnd_1824207] using wordTrace_append hprefix tailTrace_1824207
  have hstable : (prefixWord ++ tailWord_1824207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824207).length < 2 ^ (prefixWord ++ tailWord_1824207).sum := by decide
  have hdescent : baseEnd_1824207 < baseStart_1824207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824223 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 4, 4]
def baseStart_1824223 : Nat := 118140960795 + 1824223 * 2 ^ 59
def prefixEnd_1824223 : Nat := 4983230072969 + 3 ^ 40 * 1824223 * 2
def baseEnd_1824223 : Nat := 312234406662307150941019

theorem tailTrace_1824223 : CollatzResearch.WordTrace tailWord_1824223 prefixEnd_1824223 312234406662307150941019 := by
  unfold tailWord_1824223
  simp only [CollatzResearch.WordTrace]
  refine ⟨66534878870159098329549323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44356585913439398886366215 66534878870159098329549323)
  ·
    refine ⟨99802318305238647494323985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66534878870159098329549323 99802318305238647494323985)
    ·
      refine ⟨74851738728928985620742989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99802318305238647494323985 74851738728928985620742989)
      ·
        refine ⟨28069402023348369607778621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74851738728928985620742989 28069402023348369607778621)
        ·
          refine ⟨10526025758755638602916983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28069402023348369607778621 10526025758755638602916983)
          ·
            refine ⟨15789038638133457904375475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10526025758755638602916983 15789038638133457904375475)
            ·
              refine ⟨23683557957200186856563213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15789038638133457904375475 23683557957200186856563213)
              ·
                refine ⟨8881334233950070071211205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23683557957200186856563213 8881334233950070071211205)
                ·
                  refine ⟨1665250168865638138352101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8881334233950070071211205 1665250168865638138352101)
                  ·
                    refine ⟨312234406662307150941019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1665250168865638138352101 312234406662307150941019)
                    ·
                      rfl

theorem cell23_1824223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_1824223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824223 prefixEnd_1824223 := by exact prefixLift 1824223
  have htrace : WordTrace (prefixWord ++ tailWord_1824223) baseStart_1824223 baseEnd_1824223 := by
    simpa [prefixWord, tailWord_1824223, baseEnd_1824223] using wordTrace_append hprefix tailTrace_1824223
  have hstable : (prefixWord ++ tailWord_1824223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824223).length < 2 ^ (prefixWord ++ tailWord_1824223).sum := by decide
  have hdescent : baseEnd_1824223 < baseStart_1824223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824240 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 2, 4]
def baseStart_1824240 : Nat := 118140960795 + 1824240 * 2 ^ 59
def prefixEnd_1824240 : Nat := 4983230072969 + 3 ^ 40 * 1824240 * 2
def baseEnd_1824240 : Nat := 312237316386015962103493

theorem tailTrace_1824240 : CollatzResearch.WordTrace tailWord_1824240 prefixEnd_1824240 312237316386015962103493 := by
  unfold tailWord_1824240
  simp only [CollatzResearch.WordTrace]
  refine ⟨33267749455548755116459087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44356999274065006821945449 33267749455548755116459087)
  ·
    refine ⟨49901624183323132674688631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33267749455548755116459087 49901624183323132674688631)
    ·
      refine ⟨74852436274984699012032947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49901624183323132674688631 74852436274984699012032947)
      ·
        refine ⟨112278654412477048518049421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74852436274984699012032947 112278654412477048518049421)
        ·
          refine ⟨42104495404678893194268533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112278654412477048518049421 42104495404678893194268533)
          ·
            refine ⟨3947296444188646236962675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42104495404678893194268533 3947296444188646236962675)
            ·
              refine ⟨5920944666282969355444013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947296444188646236962675 5920944666282969355444013)
              ·
                refine ⟨2220354249856113508291505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5920944666282969355444013 2220354249856113508291505)
                ·
                  refine ⟨1665265687392085131218629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2220354249856113508291505 1665265687392085131218629)
                  ·
                    refine ⟨312237316386015962103493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1665265687392085131218629 312237316386015962103493)
                    ·
                      rfl

theorem cell23_1824240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_1824240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824240 prefixEnd_1824240 := by exact prefixLift 1824240
  have htrace : WordTrace (prefixWord ++ tailWord_1824240) baseStart_1824240 baseEnd_1824240 := by
    simpa [prefixWord, tailWord_1824240, baseEnd_1824240] using wordTrace_append hprefix tailTrace_1824240
  have hstable : (prefixWord ++ tailWord_1824240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824240).length < 2 ^ (prefixWord ++ tailWord_1824240).sum := by decide
  have hdescent : baseEnd_1824240 < baseStart_1824240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824267 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 5]
def baseStart_1824267 : Nat := 118140960795 + 1824267 * 2 ^ 59
def prefixEnd_1824267 : Nat := 4983230072969 + 3 ^ 40 * 1824267 * 2
def baseEnd_1824267 : Nat := 936725813135719280672855

theorem tailTrace_1824267 : CollatzResearch.WordTrace tailWord_1824267 prefixEnd_1824267 936725813135719280672855 := by
  unfold tailWord_1824267
  simp only [CollatzResearch.WordTrace]
  refine ⟨66536483681999693844151055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44357655787999795896100703 66536483681999693844151055)
  ·
    refine ⟨99804725522999540766226583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66536483681999693844151055 99804725522999540766226583)
    ·
      refine ⟨149707088284499311149339875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99804725522999540766226583 149707088284499311149339875)
      ·
        refine ⟨224560632426748966724009813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149707088284499311149339875 224560632426748966724009813)
        ·
          refine ⟨1315784955625482226898495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 224560632426748966724009813 1315784955625482226898495)
          ·
            refine ⟨1973677433438223340347743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315784955625482226898495 1973677433438223340347743)
            ·
              refine ⟨2960516150157335010521615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973677433438223340347743 2960516150157335010521615)
              ·
                refine ⟨4440774225236002515782423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960516150157335010521615 4440774225236002515782423)
                ·
                  refine ⟨6661161337854003773673635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440774225236002515782423 6661161337854003773673635)
                  ·
                    refine ⟨9991742006781005660510453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6661161337854003773673635 9991742006781005660510453)
                    ·
                      refine ⟨936725813135719280672855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9991742006781005660510453 936725813135719280672855)
                      ·
                        rfl

theorem cell23_1824267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 5].length) (baseStart_1824267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824267 prefixEnd_1824267 := by exact prefixLift 1824267
  have htrace : WordTrace (prefixWord ++ tailWord_1824267) baseStart_1824267 baseEnd_1824267 := by
    simpa [prefixWord, tailWord_1824267, baseEnd_1824267] using wordTrace_append hprefix tailTrace_1824267
  have hstable : (prefixWord ++ tailWord_1824267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824267).length < 2 ^ (prefixWord ++ tailWord_1824267).sum := by decide
  have hdescent : baseEnd_1824267 < baseStart_1824267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824337 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 4, 2, 2]
def baseStart_1824337 : Nat := 118140960795 + 1824337 * 2 ^ 59
def prefixEnd_1824337 : Nat := 4983230072969 + 3 ^ 40 * 1824337 * 2
def baseEnd_1824337 : Nat := 936761756781534006797533

theorem tailTrace_1824337 : CollatzResearch.WordTrace tailWord_1824337 prefixEnd_1824337 936761756781534006797533 := by
  unfold tailWord_1824337
  simp only [CollatzResearch.WordTrace]
  refine ⟨66539036791746095799199265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44359357861164063866132843 66539036791746095799199265)
  ·
    refine ⟨49904277593809571849399449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66539036791746095799199265 49904277593809571849399449)
    ·
      refine ⟨37428208195357178887049587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49904277593809571849399449 37428208195357178887049587)
      ·
        refine ⟨56142312293035768330574381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37428208195357178887049587 56142312293035768330574381)
        ·
          refine ⟨21053367109888413123965393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56142312293035768330574381 21053367109888413123965393)
          ·
            refine ⟨15790025332416309842974045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21053367109888413123965393 15790025332416309842974045)
            ·
              refine ⟨5921259499656116191115267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15790025332416309842974045 5921259499656116191115267)
              ·
                refine ⟨8881889249484174286672901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921259499656116191115267 8881889249484174286672901)
                ·
                  refine ⟨1665354234278282678751169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8881889249484174286672901 1665354234278282678751169)
                  ·
                    refine ⟨1249015675708712009063377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1665354234278282678751169 1249015675708712009063377)
                    ·
                      refine ⟨936761756781534006797533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249015675708712009063377 936761756781534006797533)
                      ·
                        rfl

theorem cell23_1824337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_1824337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824337 prefixEnd_1824337 := by exact prefixLift 1824337
  have htrace : WordTrace (prefixWord ++ tailWord_1824337) baseStart_1824337 baseEnd_1824337 := by
    simpa [prefixWord, tailWord_1824337, baseEnd_1824337] using wordTrace_append hprefix tailTrace_1824337
  have hstable : (prefixWord ++ tailWord_1824337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824337).length < 2 ^ (prefixWord ++ tailWord_1824337).sum := by decide
  have hdescent : baseEnd_1824337 < baseStart_1824337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824343 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 7]
def baseStart_1824343 : Nat := 118140960795 + 1824343 * 2 ^ 59
def prefixEnd_1824343 : Nat := 4983230072969 + 3 ^ 40 * 1824343 * 2
def baseEnd_1824343 : Nat := 104084981962828998146945

theorem tailTrace_1824343 : CollatzResearch.WordTrace tailWord_1824343 prefixEnd_1824343 104084981962828998146945 := by
  unfold tailWord_1824343
  simp only [CollatzResearch.WordTrace]
  refine ⟨66539255629724358823917683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44359503753149572549278455 66539255629724358823917683)
  ·
    refine ⟨99808883444586538235876525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66539255629724358823917683 99808883444586538235876525)
    ·
      refine ⟨37428331291719951838453697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99808883444586538235876525 37428331291719951838453697)
      ·
        refine ⟨28071248468789963878840273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37428331291719951838453697 28071248468789963878840273)
        ·
          refine ⟨21053436351592472909130205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28071248468789963878840273 21053436351592472909130205)
          ·
            refine ⟨7895038631847177340923827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21053436351592472909130205 7895038631847177340923827)
            ·
              refine ⟨11842557947770766011385741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7895038631847177340923827 11842557947770766011385741)
              ·
                refine ⟨4440959230414037254269653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11842557947770766011385741 4440959230414037254269653)
                ·
                  refine ⟨104084981962828998146945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4440959230414037254269653 104084981962828998146945)
                  ·
                    rfl

theorem cell23_1824343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 7].length) (baseStart_1824343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824343 prefixEnd_1824343 := by exact prefixLift 1824343
  have htrace : WordTrace (prefixWord ++ tailWord_1824343) baseStart_1824343 baseEnd_1824343 := by
    simpa [prefixWord, tailWord_1824343, baseEnd_1824343] using wordTrace_append hprefix tailTrace_1824343
  have hstable : (prefixWord ++ tailWord_1824343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824343).length < 2 ^ (prefixWord ++ tailWord_1824343).sum := by decide
  have hdescent : baseEnd_1824343 < baseStart_1824343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824360 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 7]
def baseStart_1824360 : Nat := 118140960795 + 1824360 * 2 ^ 59
def prefixEnd_1824360 : Nat := 4983230072969 + 3 ^ 40 * 1824360 * 2
def baseEnd_1824360 : Nat := 104085951870731935201103

theorem tailTrace_1824360 : CollatzResearch.WordTrace tailWord_1824360 prefixEnd_1824360 104085951870731935201103 := by
  unfold tailWord_1824360
  simp only [CollatzResearch.WordTrace]
  refine ⟨33269937835331385363643267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44359917113775180484857689 33269937835331385363643267)
  ·
    refine ⟨49904906752997078045464901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33269937835331385363643267 49904906752997078045464901)
    ·
      refine ⟨9357170016186952133524669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49904906752997078045464901 9357170016186952133524669)
      ·
        refine ⟨3508938756070107050071751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9357170016186952133524669 3508938756070107050071751)
        ·
          refine ⟨5263408134105160575107627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508938756070107050071751 5263408134105160575107627)
          ·
            refine ⟨7895112201157740862661441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263408134105160575107627 7895112201157740862661441)
            ·
              refine ⟨5921334150868305646996081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895112201157740862661441 5921334150868305646996081)
              ·
                refine ⟨4441000613151229235247061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5921334150868305646996081 4441000613151229235247061)
                ·
                  refine ⟨104085951870731935201103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4441000613151229235247061 104085951870731935201103)
                  ·
                    rfl

theorem cell23_1824360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 7].length) (baseStart_1824360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824360 prefixEnd_1824360 := by exact prefixLift 1824360
  have htrace : WordTrace (prefixWord ++ tailWord_1824360) baseStart_1824360 baseEnd_1824360 := by
    simpa [prefixWord, tailWord_1824360, baseEnd_1824360] using wordTrace_append hprefix tailTrace_1824360
  have hstable : (prefixWord ++ tailWord_1824360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824360).length < 2 ^ (prefixWord ++ tailWord_1824360).sum := by decide
  have hdescent : baseEnd_1824360 < baseStart_1824360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824380 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_1824380 : Nat := 118140960795 + 1824380 * 2 ^ 59
def prefixEnd_1824380 : Nat := 4983230072969 + 3 ^ 40 * 1824380 * 2
def baseEnd_1824380 : Nat := 936783836449677338559835

theorem tailTrace_1824380 : CollatzResearch.WordTrace tailWord_1824380 prefixEnd_1824380 936783836449677338559835 := by
  unfold tailWord_1824380
  simp only [CollatzResearch.WordTrace]
  refine ⟨33270302565295157071507297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44360403420393542762009729 33270302565295157071507297)
  ·
    refine ⟨24952726923971367803630473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33270302565295157071507297 24952726923971367803630473)
    ·
      refine ⟨18714545192978525852722855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24952726923971367803630473 18714545192978525852722855)
      ·
        refine ⟨28071817789467788779084283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18714545192978525852722855 28071817789467788779084283)
        ·
          refine ⟨42107726684201683168626425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28071817789467788779084283 42107726684201683168626425)
          ·
            refine ⟨31580795013151262376469819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42107726684201683168626425 31580795013151262376469819)
            ·
              refine ⟨47371192519726893564704729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31580795013151262376469819 47371192519726893564704729)
              ·
                refine ⟨35528394389795170173528547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47371192519726893564704729 35528394389795170173528547)
                ·
                  refine ⟨53292591584692755260292821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35528394389795170173528547 53292591584692755260292821)
                  ·
                    refine ⟨1249045115266236451413113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53292591584692755260292821 1249045115266236451413113)
                    ·
                      refine ⟨936783836449677338559835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249045115266236451413113 936783836449677338559835)
                      ·
                        rfl

theorem cell23_1824380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_1824380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824380 prefixEnd_1824380 := by exact prefixLift 1824380
  have htrace : WordTrace (prefixWord ++ tailWord_1824380) baseStart_1824380 baseEnd_1824380 := by
    simpa [prefixWord, tailWord_1824380, baseEnd_1824380] using wordTrace_append hprefix tailTrace_1824380
  have hstable : (prefixWord ++ tailWord_1824380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824380).length < 2 ^ (prefixWord ++ tailWord_1824380).sum := by decide
  have hdescent : baseEnd_1824380 < baseStart_1824380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824394 : List Nat := [3, 1, 2, 3, 2, 2, 3, 2, 5]
def baseStart_1824394 : Nat := 118140960795 + 1824394 * 2 ^ 59
def prefixEnd_1824394 : Nat := 4983230072969 + 3 ^ 40 * 1824394 * 2
def baseEnd_1824394 : Nat := 104087891686537809309419

theorem tailTrace_1824394 : CollatzResearch.WordTrace tailWord_1824394 prefixEnd_1824394 104087891686537809309419 := by
  unfold tailWord_1824394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16635278938134898633506059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44360743835026396356016157 16635278938134898633506059)
  ·
    refine ⟨24952918407202347950259089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16635278938134898633506059 24952918407202347950259089)
    ·
      refine ⟨18714688805401760962694317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24952918407202347950259089 18714688805401760962694317)
      ·
        refine ⟨7018008302025660361010369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18714688805401760962694317 7018008302025660361010369)
        ·
          refine ⟨5263506226519245270757777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7018008302025660361010369 5263506226519245270757777)
          ·
            refine ⟨3947629669889433953068333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5263506226519245270757777 3947629669889433953068333)
            ·
              refine ⟨1480361126208537732400625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3947629669889433953068333 1480361126208537732400625)
              ·
                refine ⟨1110270844656403299300469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480361126208537732400625 1110270844656403299300469)
                ·
                  refine ⟨104087891686537809309419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1110270844656403299300469 104087891686537809309419)
                  ·
                    rfl

theorem cell23_1824394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_1824394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824394 prefixEnd_1824394 := by exact prefixLift 1824394
  have htrace : WordTrace (prefixWord ++ tailWord_1824394) baseStart_1824394 baseEnd_1824394 := by
    simpa [prefixWord, tailWord_1824394, baseEnd_1824394] using wordTrace_append hprefix tailTrace_1824394
  have hstable : (prefixWord ++ tailWord_1824394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824394).length < 2 ^ (prefixWord ++ tailWord_1824394).sum := by decide
  have hdescent : baseEnd_1824394 < baseStart_1824394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824453 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_1824453 : Nat := 118140960795 + 1824453 * 2 ^ 59
def prefixEnd_1824453 : Nat := 4983230072969 + 3 ^ 40 * 1824453 * 2
def baseEnd_1824453 : Nat := 936821320537455552946999

theorem tailTrace_1824453 : CollatzResearch.WordTrace tailWord_1824453 prefixEnd_1824453 936821320537455552946999 := by
  unfold tailWord_1824453
  simp only [CollatzResearch.WordTrace]
  refine ⟨66543267659325847610422013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44362178439550565073614675 66543267659325847610422013)
  ·
    refine ⟨24953725372247192853908255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66543267659325847610422013 24953725372247192853908255)
    ·
      refine ⟨37430588058370789280862383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24953725372247192853908255 37430588058370789280862383)
      ·
        refine ⟨56145882087556183921293575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37430588058370789280862383 56145882087556183921293575)
        ·
          refine ⟨84218823131334275881940363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56145882087556183921293575 84218823131334275881940363)
          ·
            refine ⟨126328234697001413822910545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84218823131334275881940363 126328234697001413822910545)
            ·
              refine ⟨94746176022751060367182909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126328234697001413822910545 94746176022751060367182909)
              ·
                refine ⟨35529816008531647637693591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94746176022751060367182909 35529816008531647637693591)
                ·
                  refine ⟨53294724012797471456540387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35529816008531647637693591 53294724012797471456540387)
                  ·
                    refine ⟨79942086019196207184810581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53294724012797471456540387 79942086019196207184810581)
                    ·
                      refine ⟨936821320537455552946999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 79942086019196207184810581 936821320537455552946999)
                      ·
                        rfl

theorem cell23_1824453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_1824453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824453 prefixEnd_1824453 := by exact prefixLift 1824453
  have htrace : WordTrace (prefixWord ++ tailWord_1824453) baseStart_1824453 baseEnd_1824453 := by
    simpa [prefixWord, tailWord_1824453, baseEnd_1824453] using wordTrace_append hprefix tailTrace_1824453
  have hstable : (prefixWord ++ tailWord_1824453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824453).length < 2 ^ (prefixWord ++ tailWord_1824453).sum := by decide
  have hdescent : baseEnd_1824453 < baseStart_1824453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824461 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1824461 : Nat := 118140960795 + 1824461 * 2 ^ 59
def prefixEnd_1824461 : Nat := 4983230072969 + 3 ^ 40 * 1824461 * 2
def baseEnd_1824461 : Nat := 936825428382691521646963

theorem tailTrace_1824461 : CollatzResearch.WordTrace tailWord_1824461 prefixEnd_1824461 936825428382691521646963 := by
  unfold tailWord_1824461
  simp only [CollatzResearch.WordTrace]
  refine ⟨66543559443296864976713237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44362372962197909984475491 66543559443296864976713237)
  ·
    refine ⟨3119229348904540545783433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66543559443296864976713237 3119229348904540545783433)
    ·
      refine ⟨2339422011678405409337575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3119229348904540545783433 2339422011678405409337575)
      ·
        refine ⟨3509133017517608114006363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339422011678405409337575 3509133017517608114006363)
        ·
          refine ⟨5263699526276412171009545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509133017517608114006363 5263699526276412171009545)
          ·
            refine ⟨3947774644707309128257159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5263699526276412171009545 3947774644707309128257159)
            ·
              refine ⟨5921661967060963692385739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947774644707309128257159 5921661967060963692385739)
              ·
                refine ⟨8882492950591445538578609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921661967060963692385739 8882492950591445538578609)
                ·
                  refine ⟨6661869712943584153933957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8882492950591445538578609 6661869712943584153933957)
                  ·
                    refine ⟨1249100571176922028862617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6661869712943584153933957 1249100571176922028862617)
                    ·
                      refine ⟨936825428382691521646963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249100571176922028862617 936825428382691521646963)
                      ·
                        rfl

theorem cell23_1824461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1824461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824461 prefixEnd_1824461 := by exact prefixLift 1824461
  have htrace : WordTrace (prefixWord ++ tailWord_1824461) baseStart_1824461 baseEnd_1824461 := by
    simpa [prefixWord, tailWord_1824461, baseEnd_1824461] using wordTrace_append hprefix tailTrace_1824461
  have hstable : (prefixWord ++ tailWord_1824461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824461).length < 2 ^ (prefixWord ++ tailWord_1824461).sum := by decide
  have hdescent : baseEnd_1824461 < baseStart_1824461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824480 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 3, 5]
def baseStart_1824480 : Nat := 118140960795 + 1824480 * 2 ^ 59
def prefixEnd_1824480 : Nat := 4983230072969 + 3 ^ 40 * 1824480 * 2
def baseEnd_1824480 : Nat := 312278394838375649103125

theorem tailTrace_1824480 : CollatzResearch.WordTrace tailWord_1824480 prefixEnd_1824480 312278394838375649103125 := by
  unfold tailWord_1824480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33272126215114015610827447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44362834953485354147769929 33272126215114015610827447)
  ·
    refine ⟨49908189322671023416241171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33272126215114015610827447 49908189322671023416241171)
    ·
      refine ⟨74862283984006535124361757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49908189322671023416241171 74862283984006535124361757)
      ·
        refine ⟨28073356494002450671635659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74862283984006535124361757 28073356494002450671635659)
        ·
          refine ⟨42110034741003676007453489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28073356494002450671635659 42110034741003676007453489)
          ·
            refine ⟨31582526055752757005590117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42110034741003676007453489 31582526055752757005590117)
            ·
              refine ⟨5921723635453641938548147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31582526055752757005590117 5921723635453641938548147)
              ·
                refine ⟨8882585453180462907822221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921723635453641938548147 8882585453180462907822221)
                ·
                  refine ⟨3330969544942673590433333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8882585453180462907822221 3330969544942673590433333)
                  ·
                    refine ⟨312278394838375649103125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3330969544942673590433333 312278394838375649103125)
                    ·
                      rfl

theorem cell23_1824480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_1824480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824480 prefixEnd_1824480 := by exact prefixLift 1824480
  have htrace : WordTrace (prefixWord ++ tailWord_1824480) baseStart_1824480 baseEnd_1824480 := by
    simpa [prefixWord, tailWord_1824480, baseEnd_1824480] using wordTrace_append hprefix tailTrace_1824480
  have hstable : (prefixWord ++ tailWord_1824480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824480).length < 2 ^ (prefixWord ++ tailWord_1824480).sum := by decide
  have hdescent : baseEnd_1824480 < baseStart_1824480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824481 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_1824481 : Nat := 118140960795 + 1824481 * 2 ^ 59
def prefixEnd_1824481 : Nat := 4983230072969 + 3 ^ 40 * 1824481 * 2
def baseEnd_1824481 : Nat := 936835697995781443396871

theorem tailTrace_1824481 : CollatzResearch.WordTrace tailWord_1824481 prefixEnd_1824481 936835697995781443396871 := by
  unfold tailWord_1824481
  simp only [CollatzResearch.WordTrace]
  refine ⟨66544288903224408392441297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44362859268816272261627531 66544288903224408392441297)
  ·
    refine ⟨49908216677418306294330973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66544288903224408392441297 49908216677418306294330973)
    ·
      refine ⟨18715581254031864860374115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49908216677418306294330973 18715581254031864860374115)
      ·
        refine ⟨28073371881047797290561173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18715581254031864860374115 28073371881047797290561173)
        ·
          refine ⟨1315939306924115497995055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28073371881047797290561173 1315939306924115497995055)
          ·
            refine ⟨1973908960386173246992583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315939306924115497995055 1973908960386173246992583)
            ·
              refine ⟨2960863440579259870488875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973908960386173246992583 2960863440579259870488875)
              ·
                refine ⟨4441295160868889805733313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960863440579259870488875 4441295160868889805733313)
                ·
                  refine ⟨3330971370651667354299985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441295160868889805733313 3330971370651667354299985)
                  ·
                    refine ⟨2498228527988750515724989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3330971370651667354299985 2498228527988750515724989)
                    ·
                      refine ⟨936835697995781443396871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2498228527988750515724989 936835697995781443396871)
                      ·
                        rfl

theorem cell23_1824481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_1824481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824481 prefixEnd_1824481 := by exact prefixLift 1824481
  have htrace : WordTrace (prefixWord ++ tailWord_1824481) baseStart_1824481 baseEnd_1824481 := by
    simpa [prefixWord, tailWord_1824481, baseEnd_1824481] using wordTrace_append hprefix tailTrace_1824481
  have hstable : (prefixWord ++ tailWord_1824481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824481).length < 2 ^ (prefixWord ++ tailWord_1824481).sum := by decide
  have hdescent : baseEnd_1824481 < baseStart_1824481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824497 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 1, 5]
def baseStart_1824497 : Nat := 118140960795 + 1824497 * 2 ^ 59
def prefixEnd_1824497 : Nat := 4983230072969 + 3 ^ 40 * 1824497 * 2
def baseEnd_1824497 : Nat := 312281304562084460265599

theorem tailTrace_1824497 : CollatzResearch.WordTrace tailWord_1824497 prefixEnd_1824497 312281304562084460265599 := by
  unfold tailWord_1824497
  simp only [CollatzResearch.WordTrace]
  refine ⟨66544872471166443125023745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44363248314110962083349163 66544872471166443125023745)
  ·
    refine ⟨49908654353374832343767809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66544872471166443125023745 49908654353374832343767809)
    ·
      refine ⟨37431490765031124257825857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49908654353374832343767809 37431490765031124257825857)
      ·
        refine ⟨28073618073773343193369393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37431490765031124257825857 28073618073773343193369393)
        ·
          refine ⟨21055213555330007395027045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28073618073773343193369393 21055213555330007395027045)
          ·
            refine ⟨3947852541624376386567571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21055213555330007395027045 3947852541624376386567571)
            ·
              refine ⟨5921778812436564579851357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947852541624376386567571 5921778812436564579851357)
              ·
                refine ⟨2220667054663711717444259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5921778812436564579851357 2220667054663711717444259)
                ·
                  refine ⟨3331000581995567576166389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220667054663711717444259 3331000581995567576166389)
                  ·
                    refine ⟨312281304562084460265599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3331000581995567576166389 312281304562084460265599)
                    ·
                      rfl

theorem cell23_1824497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_1824497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824497 prefixEnd_1824497 := by exact prefixLift 1824497
  have htrace : WordTrace (prefixWord ++ tailWord_1824497) baseStart_1824497 baseEnd_1824497 := by
    simpa [prefixWord, tailWord_1824497, baseEnd_1824497] using wordTrace_append hprefix tailTrace_1824497
  have hstable : (prefixWord ++ tailWord_1824497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824497).length < 2 ^ (prefixWord ++ tailWord_1824497).sum := by decide
  have hdescent : baseEnd_1824497 < baseStart_1824497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824540 : List Nat := [2, 2, 3, 1, 1, 2, 3, 9]
def baseStart_1824540 : Nat := 118140960795 + 1824540 * 2 ^ 59
def prefixEnd_1824540 : Nat := 4983230072969 + 3 ^ 40 * 1824540 * 2
def baseEnd_1824540 : Nat := 34698740494607285650337

theorem tailTrace_1824540 : CollatzResearch.WordTrace tailWord_1824540 prefixEnd_1824540 34698740494607285650337 := by
  unfold tailWord_1824540
  simp only [CollatzResearch.WordTrace]
  refine ⟨33273220405005330734419537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44364293873340440979226049 33273220405005330734419537)
  ·
    refine ⟨24954915303753998050814653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33273220405005330734419537 24954915303753998050814653)
    ·
      refine ⟨9358093238907749269055495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24954915303753998050814653 9358093238907749269055495)
      ·
        refine ⟨14037139858361623903583243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9358093238907749269055495 14037139858361623903583243)
        ·
          refine ⟨21055709787542435855374865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14037139858361623903583243 21055709787542435855374865)
          ·
            refine ⟨15791782340656826891531149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21055709787542435855374865 15791782340656826891531149)
            ·
              refine ⟨5921918377746310084324181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15791782340656826891531149 5921918377746310084324181)
              ·
                refine ⟨34698740494607285650337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5921918377746310084324181 34698740494607285650337)
                ·
                  rfl

theorem cell23_1824540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 9].length) (baseStart_1824540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824540 prefixEnd_1824540 := by exact prefixLift 1824540
  have htrace : WordTrace (prefixWord ++ tailWord_1824540) baseStart_1824540 baseEnd_1824540 := by
    simpa [prefixWord, tailWord_1824540, baseEnd_1824540] using wordTrace_append hprefix tailTrace_1824540
  have hstable : (prefixWord ++ tailWord_1824540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824540).length < 2 ^ (prefixWord ++ tailWord_1824540).sum := by decide
  have hdescent : baseEnd_1824540 < baseStart_1824540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824588 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 1, 2, 3]
def baseStart_1824588 : Nat := 118140960795 + 1824588 * 2 ^ 59
def prefixEnd_1824588 : Nat := 4983230072969 + 3 ^ 40 * 1824588 * 2
def baseEnd_1824588 : Nat := 936890640425812524758879

theorem tailTrace_1824588 : CollatzResearch.WordTrace tailWord_1824588 prefixEnd_1824588 936890640425812524758879 := by
  unfold tailWord_1824588
  simp only [CollatzResearch.WordTrace]
  refine ⟨33274095756918382833293209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44365461009224510444390945 33274095756918382833293209)
  ·
    refine ⟨24955571817688787124969907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33274095756918382833293209 24955571817688787124969907)
    ·
      refine ⟨37433357726533180687454861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24955571817688787124969907 37433357726533180687454861)
      ·
        refine ⟨14037509147449942757795573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37433357726533180687454861 14037509147449942757795573)
        ·
          refine ⟨1316016482573432133543335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14037509147449942757795573 1316016482573432133543335)
          ·
            refine ⟨1974024723860148200315003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316016482573432133543335 1974024723860148200315003)
            ·
              refine ⟨2961037085790222300472505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974024723860148200315003 2961037085790222300472505)
              ·
                refine ⟨2220777814342666725354379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961037085790222300472505 2220777814342666725354379)
                ·
                  refine ⟨3331166721514000088031569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220777814342666725354379 3331166721514000088031569)
                  ·
                    refine ⟨2498375041135500066023677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3331166721514000088031569 2498375041135500066023677)
                    ·
                      refine ⟨936890640425812524758879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2498375041135500066023677 936890640425812524758879)
                      ·
                        rfl

theorem cell23_1824588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_1824588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824588 prefixEnd_1824588 := by exact prefixLift 1824588
  have htrace : WordTrace (prefixWord ++ tailWord_1824588) baseStart_1824588 baseEnd_1824588 := by
    simpa [prefixWord, tailWord_1824588, baseEnd_1824588] using wordTrace_append hprefix tailTrace_1824588
  have hstable : (prefixWord ++ tailWord_1824588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824588).length < 2 ^ (prefixWord ++ tailWord_1824588).sum := by decide
  have hdescent : baseEnd_1824588 < baseStart_1824588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824590 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1824590 : Nat := 118140960795 + 1824590 * 2 ^ 59
def prefixEnd_1824590 : Nat := 4983230072969 + 3 ^ 40 * 1824590 * 2
def baseEnd_1824590 : Nat := 936891667387121516933869

theorem tailTrace_1824590 : CollatzResearch.WordTrace tailWord_1824590 prefixEnd_1824590 936891667387121516933869 := by
  unfold tailWord_1824590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8318533057478690001019903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44365509639886346672106149 8318533057478690001019903)
  ·
    refine ⟨12477799586218035001529855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8318533057478690001019903 12477799586218035001529855)
    ·
      refine ⟨18716699379327052502294783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12477799586218035001529855 18716699379327052502294783)
      ·
        refine ⟨28075049068990578753442175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18716699379327052502294783 28075049068990578753442175)
        ·
          refine ⟨42112573603485868130163263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28075049068990578753442175 42112573603485868130163263)
          ·
            refine ⟨63168860405228802195244895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42112573603485868130163263 63168860405228802195244895)
            ·
              refine ⟨94753290607843203292867343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63168860405228802195244895 94753290607843203292867343)
              ·
                refine ⟨142129935911764804939301015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94753290607843203292867343 142129935911764804939301015)
                ·
                  refine ⟨213194903867647207408951523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142129935911764804939301015 213194903867647207408951523)
                  ·
                    refine ⟨319792355801470811113427285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213194903867647207408951523 319792355801470811113427285)
                    ·
                      refine ⟨936891667387121516933869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 319792355801470811113427285 936891667387121516933869)
                      ·
                        rfl

theorem cell23_1824590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1824590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824590 prefixEnd_1824590 := by exact prefixLift 1824590
  have htrace : WordTrace (prefixWord ++ tailWord_1824590) baseStart_1824590 baseEnd_1824590 := by
    simpa [prefixWord, tailWord_1824590, baseEnd_1824590] using wordTrace_append hprefix tailTrace_1824590
  have hstable : (prefixWord ++ tailWord_1824590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824590).length < 2 ^ (prefixWord ++ tailWord_1824590).sum := by decide
  have hdescent : baseEnd_1824590 < baseStart_1824590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824600 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 6, 6]
def baseStart_1824600 : Nat := 118140960795 + 1824600 * 2 ^ 59
def prefixEnd_1824600 : Nat := 4983230072969 + 3 ^ 40 * 1824600 * 2
def baseEnd_1824600 : Nat := 312298934064555492602941

theorem tailTrace_1824600 : CollatzResearch.WordTrace tailWord_1824600 prefixEnd_1824600 312298934064555492602941 := by
  unfold tailWord_1824600
  simp only [CollatzResearch.WordTrace]
  refine ⟨33274314594896645858011627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44365752793195527810682169 33274314594896645858011627)
  ·
    refine ⟨49911471892344968787017441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33274314594896645858011627 49911471892344968787017441)
    ·
      refine ⟨37433603919258726590263081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49911471892344968787017441 37433603919258726590263081)
      ·
        refine ⟨28075202939444044942697311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37433603919258726590263081 28075202939444044942697311)
        ·
          refine ⟨42112804409166067414045967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28075202939444044942697311 42112804409166067414045967)
          ·
            refine ⟨63169206613749101121068951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42112804409166067414045967 63169206613749101121068951)
            ·
              refine ⟨94753809920623651681603427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63169206613749101121068951 94753809920623651681603427)
              ·
                refine ⟨142130714880935477522405141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94753809920623651681603427 142130714880935477522405141)
                ·
                  refine ⟨6662377260043850508862741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142130714880935477522405141 6662377260043850508862741)
                  ·
                    refine ⟨312298934064555492602941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6662377260043850508862741 312298934064555492602941)
                    ·
                      rfl

theorem cell23_1824600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_1824600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824600 prefixEnd_1824600 := by exact prefixLift 1824600
  have htrace : WordTrace (prefixWord ++ tailWord_1824600) baseStart_1824600 baseEnd_1824600 := by
    simpa [prefixWord, tailWord_1824600, baseEnd_1824600] using wordTrace_append hprefix tailTrace_1824600
  have hstable : (prefixWord ++ tailWord_1824600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824600).length < 2 ^ (prefixWord ++ tailWord_1824600).sum := by decide
  have hdescent : baseEnd_1824600 < baseStart_1824600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824662 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1824662 : Nat := 118140960795 + 1824662 * 2 ^ 59
def prefixEnd_1824662 : Nat := 4983230072969 + 3 ^ 40 * 1824662 * 2
def baseEnd_1824662 : Nat := 936928637994245235233539

theorem tailTrace_1824662 : CollatzResearch.WordTrace tailWord_1824662 prefixEnd_1824662 936928637994245235233539 := by
  unfold tailWord_1824662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159430657223042269048765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44367260343712450869853493 4159430657223042269048765)
  ·
    refine ⟨1559786496458640850893287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4159430657223042269048765 1559786496458640850893287)
    ·
      refine ⟨2339679744687961276339931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559786496458640850893287 2339679744687961276339931)
      ·
        refine ⟨3509519617031941914509897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339679744687961276339931 3509519617031941914509897)
        ·
          refine ⟨2632139712773956435882423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3509519617031941914509897 2632139712773956435882423)
          ·
            refine ⟨3948209569160934653823635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632139712773956435882423 3948209569160934653823635)
            ·
              refine ⟨5922314353741401980735453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948209569160934653823635 5922314353741401980735453)
              ·
                refine ⟨2220867882653025742775795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5922314353741401980735453 2220867882653025742775795)
                ·
                  refine ⟨3331301823979538614163693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220867882653025742775795 3331301823979538614163693)
                  ·
                    refine ⟨1249238183992326980311385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331301823979538614163693 1249238183992326980311385)
                    ·
                      refine ⟨936928637994245235233539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249238183992326980311385 936928637994245235233539)
                      ·
                        rfl

theorem cell23_1824662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1824662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824662 prefixEnd_1824662 := by exact prefixLift 1824662
  have htrace : WordTrace (prefixWord ++ tailWord_1824662) baseStart_1824662 baseEnd_1824662 := by
    simpa [prefixWord, tailWord_1824662, baseEnd_1824662] using wordTrace_append hprefix tailTrace_1824662
  have hstable : (prefixWord ++ tailWord_1824662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824662).length < 2 ^ (prefixWord ++ tailWord_1824662).sum := by decide
  have hdescent : baseEnd_1824662 < baseStart_1824662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824677 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_1824677 : Nat := 118140960795 + 1824677 * 2 ^ 59
def prefixEnd_1824677 : Nat := 4983230072969 + 3 ^ 40 * 1824677 * 2
def baseEnd_1824677 : Nat := 312312113401354225515323

theorem tailTrace_1824677 : CollatzResearch.WordTrace tailWord_1824677 prefixEnd_1824677 312312113401354225515323 := by
  unfold tailWord_1824677
  simp only [CollatzResearch.WordTrace]
  refine ⟨66551437610514333866576285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44367625073676222577717523 66551437610514333866576285)
  ·
    refine ⟨24956789103942875199966107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66551437610514333866576285 24956789103942875199966107)
    ·
      refine ⟨37435183655914312799949161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24956789103942875199966107 37435183655914312799949161)
      ·
        refine ⟨28076387741935734599961871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37435183655914312799949161 28076387741935734599961871)
        ·
          refine ⟨42114581612903601899942807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28076387741935734599961871 42114581612903601899942807)
          ·
            refine ⟨63171872419355402849914211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42114581612903601899942807 63171872419355402849914211)
            ·
              refine ⟨94757808629033104274871317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63171872419355402849914211 94757808629033104274871317)
              ·
                refine ⟨4441772279485926762884593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94757808629033104274871317 4441772279485926762884593)
                ·
                  refine ⟨3331329209614445072163445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441772279485926762884593 3331329209614445072163445)
                  ·
                    refine ⟨312312113401354225515323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3331329209614445072163445 312312113401354225515323)
                    ·
                      rfl

theorem cell23_1824677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_1824677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824677 prefixEnd_1824677 := by exact prefixLift 1824677
  have htrace : WordTrace (prefixWord ++ tailWord_1824677) baseStart_1824677 baseEnd_1824677 := by
    simpa [prefixWord, tailWord_1824677, baseEnd_1824677] using wordTrace_append hprefix tailTrace_1824677
  have hstable : (prefixWord ++ tailWord_1824677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824677).length < 2 ^ (prefixWord ++ tailWord_1824677).sum := by decide
  have hdescent : baseEnd_1824677 < baseStart_1824677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824692 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_1824692 : Nat := 118140960795 + 1824692 * 2 ^ 59
def prefixEnd_1824692 : Nat := 4983230072969 + 3 ^ 40 * 1824692 * 2
def baseEnd_1824692 : Nat := 936944042413880117858401

theorem tailTrace_1824692 : CollatzResearch.WordTrace tailWord_1824692 prefixEnd_1824692 936944042413880117858401 := by
  unfold tailWord_1824692
  simp only [CollatzResearch.WordTrace]
  refine ⟨33275992352729995714186165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44367989803639994285581553 33275992352729995714186165)
  ·
    refine ⟨3119624283068437098204953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33275992352729995714186165 3119624283068437098204953)
    ·
      refine ⟨2339718212301327823653715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3119624283068437098204953 2339718212301327823653715)
      ·
        refine ⟨3509577318451991735480573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339718212301327823653715 3509577318451991735480573)
        ·
          refine ⟨1316091494419496900805215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3509577318451991735480573 1316091494419496900805215)
          ·
            refine ⟨1974137241629245351207823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316091494419496900805215 1974137241629245351207823)
            ·
              refine ⟨2961205862443868026811735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974137241629245351207823 2961205862443868026811735)
              ·
                refine ⟨4441808793665802040217603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961205862443868026811735 4441808793665802040217603)
                ·
                  refine ⟨6662713190498703060326405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441808793665802040217603 6662713190498703060326405)
                  ·
                    refine ⟨1249258723218506823811201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6662713190498703060326405 1249258723218506823811201)
                    ·
                      refine ⟨936944042413880117858401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249258723218506823811201 936944042413880117858401)
                      ·
                        rfl

theorem cell23_1824692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_1824692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824692 prefixEnd_1824692 := by exact prefixLift 1824692
  have htrace : WordTrace (prefixWord ++ tailWord_1824692) baseStart_1824692 baseEnd_1824692 := by
    simpa [prefixWord, tailWord_1824692, baseEnd_1824692] using wordTrace_append hprefix tailTrace_1824692
  have hstable : (prefixWord ++ tailWord_1824692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824692).length < 2 ^ (prefixWord ++ tailWord_1824692).sum := by decide
  have hdescent : baseEnd_1824692 < baseStart_1824692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824697 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1824697 : Nat := 118140960795 + 1824697 * 2 ^ 59
def prefixEnd_1824697 : Nat := 4983230072969 + 3 ^ 40 * 1824697 * 2
def baseEnd_1824697 : Nat := 936946609817152598295877

theorem tailTrace_1824697 : CollatzResearch.WordTrace tailWord_1824697 prefixEnd_1824697 936946609817152598295877 := by
  unfold tailWord_1824697
  simp only [CollatzResearch.WordTrace]
  refine ⟨66552167070441877282304345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44368111380294584854869563 66552167070441877282304345)
  ·
    refine ⟨49914125302831407961728259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66552167070441877282304345 49914125302831407961728259)
    ·
      refine ⟨74871187954247111942592389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49914125302831407961728259 74871187954247111942592389)
      ·
        refine ⟨14038347741421333489236073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74871187954247111942592389 14038347741421333489236073)
        ·
          refine ⟨10528760806066000116927055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14038347741421333489236073 10528760806066000116927055)
          ·
            refine ⟨15793141209099000175390583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10528760806066000116927055 15793141209099000175390583)
            ·
              refine ⟨23689711813648500263085875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15793141209099000175390583 23689711813648500263085875)
              ·
                refine ⟨35534567720472750394628813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23689711813648500263085875 35534567720472750394628813)
                ·
                  refine ⟨13325462895177281397985805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35534567720472750394628813 13325462895177281397985805)
                  ·
                    refine ⟨4997048585691480524244677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13325462895177281397985805 4997048585691480524244677)
                    ·
                      refine ⟨936946609817152598295877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4997048585691480524244677 936946609817152598295877)
                      ·
                        rfl

theorem cell23_1824697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1824697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824697 prefixEnd_1824697 := by exact prefixLift 1824697
  have htrace : WordTrace (prefixWord ++ tailWord_1824697) baseStart_1824697 baseEnd_1824697 := by
    simpa [prefixWord, tailWord_1824697, baseEnd_1824697] using wordTrace_append hprefix tailTrace_1824697
  have hstable : (prefixWord ++ tailWord_1824697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824697).length < 2 ^ (prefixWord ++ tailWord_1824697).sum := by decide
  have hdescent : baseEnd_1824697 < baseStart_1824697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824714 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_1824714 : Nat := 118140960795 + 1824714 * 2 ^ 59
def prefixEnd_1824714 : Nat := 4983230072969 + 3 ^ 40 * 1824714 * 2
def baseEnd_1824714 : Nat := 936955338988279031783299

theorem tailTrace_1824714 : CollatzResearch.WordTrace tailWord_1824714 prefixEnd_1824714 936955338988279031783299 := by
  unfold tailWord_1824714
  simp only [CollatzResearch.WordTrace]
  refine ⟨16638196777845072296418299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44368524740920192790448797 16638196777845072296418299)
  ·
    refine ⟨24957295166767608444627449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16638196777845072296418299 24957295166767608444627449)
    ·
      refine ⟨18717971375075706333470587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24957295166767608444627449 18717971375075706333470587)
      ·
        refine ⟨28076957062613559500205881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18717971375075706333470587 28076957062613559500205881)
        ·
          refine ⟨21057717796960169625154411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28076957062613559500205881 21057717796960169625154411)
          ·
            refine ⟨31586576695440254437731617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21057717796960169625154411 31586576695440254437731617)
            ·
              refine ⟨23689932521580190828298713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31586576695440254437731617 23689932521580190828298713)
              ·
                refine ⟨17767449391185143121224035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23689932521580190828298713 17767449391185143121224035)
                ·
                  refine ⟨26651174086777714681836053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17767449391185143121224035 26651174086777714681836053)
                  ·
                    refine ⟨1249273785317705375711065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26651174086777714681836053 1249273785317705375711065)
                    ·
                      refine ⟨936955338988279031783299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249273785317705375711065 936955338988279031783299)
                      ·
                        rfl

theorem cell23_1824714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_1824714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824714 prefixEnd_1824714 := by exact prefixLift 1824714
  have htrace : WordTrace (prefixWord ++ tailWord_1824714) baseStart_1824714 baseEnd_1824714 := by
    simpa [prefixWord, tailWord_1824714, baseEnd_1824714] using wordTrace_append hprefix tailTrace_1824714
  have hstable : (prefixWord ++ tailWord_1824714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824714).length < 2 ^ (prefixWord ++ tailWord_1824714).sum := by decide
  have hdescent : baseEnd_1824714 < baseStart_1824714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824732 : List Nat := [2, 2, 6, 1, 1, 1, 3, 2, 5]
def baseStart_1824732 : Nat := 118140960795 + 1824732 * 2 ^ 59
def prefixEnd_1824732 : Nat := 4983230072969 + 3 ^ 40 * 1824732 * 2
def baseEnd_1824732 : Nat := 104107175737784440150913

theorem tailTrace_1824732 : CollatzResearch.WordTrace tailWord_1824732 prefixEnd_1824732 104107175737784440150913 := by
  unfold tailWord_1824732
  simp only [CollatzResearch.WordTrace]
  refine ⟨33276721812657539129914225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44368962416876718839885633 33276721812657539129914225)
  ·
    refine ⟨24957541359493154347435669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33276721812657539129914225 24957541359493154347435669)
    ·
      refine ⟨1169884751226241610036047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24957541359493154347435669 1169884751226241610036047)
      ·
        refine ⟨1754827126839362415054071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169884751226241610036047 1754827126839362415054071)
        ·
          refine ⟨2632240690259043622581107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754827126839362415054071 2632240690259043622581107)
          ·
            refine ⟨3948361035388565433871661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632240690259043622581107 3948361035388565433871661)
            ·
              refine ⟨1480635388270712037701873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3948361035388565433871661 1480635388270712037701873)
              ·
                refine ⟨1110476541203034028276405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480635388270712037701873 1110476541203034028276405)
                ·
                  refine ⟨104107175737784440150913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1110476541203034028276405 104107175737784440150913)
                  ·
                    rfl

theorem cell23_1824732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_1824732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824732 prefixEnd_1824732 := by exact prefixLift 1824732
  have htrace : WordTrace (prefixWord ++ tailWord_1824732) baseStart_1824732 baseEnd_1824732 := by
    simpa [prefixWord, tailWord_1824732, baseEnd_1824732] using wordTrace_append hprefix tailTrace_1824732
  have hstable : (prefixWord ++ tailWord_1824732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824732).length < 2 ^ (prefixWord ++ tailWord_1824732).sum := by decide
  have hdescent : baseEnd_1824732 < baseStart_1824732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824737 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 8]
def baseStart_1824737 : Nat := 118140960795 + 1824737 * 2 ^ 59
def prefixEnd_1824737 : Nat := 4983230072969 + 3 ^ 40 * 1824737 * 2
def baseEnd_1824737 : Nat := 104107461004814715755077

theorem tailTrace_1824737 : CollatzResearch.WordTrace tailWord_1824737 prefixEnd_1824737 104107461004814715755077 := by
  unfold tailWord_1824737
  simp only [CollatzResearch.WordTrace]
  refine ⟨66553625990296964113760465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44369083993531309409173643 66553625990296964113760465)
  ·
    refine ⟨49915219492722723085320349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66553625990296964113760465 49915219492722723085320349)
    ·
      refine ⟨18718207309771021156995131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49915219492722723085320349 18718207309771021156995131)
      ·
        refine ⟨28077310964656531735492697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18718207309771021156995131 28077310964656531735492697)
        ·
          refine ⟨21057983223492398801619523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28077310964656531735492697 21057983223492398801619523)
          ·
            refine ⟨31586974835238598202429285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21057983223492398801619523 31586974835238598202429285)
            ·
              refine ⟨5922557781607237162955491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31586974835238598202429285 5922557781607237162955491)
              ·
                refine ⟨8883836672410855744433237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922557781607237162955491 8883836672410855744433237)
                ·
                  refine ⟨104107461004814715755077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8883836672410855744433237 104107461004814715755077)
                  ·
                    rfl

theorem cell23_1824737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 8].length) (baseStart_1824737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824737 prefixEnd_1824737 := by exact prefixLift 1824737
  have htrace : WordTrace (prefixWord ++ tailWord_1824737) baseStart_1824737 baseEnd_1824737 := by
    simpa [prefixWord, tailWord_1824737, baseEnd_1824737] using wordTrace_append hprefix tailTrace_1824737
  have hstable : (prefixWord ++ tailWord_1824737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824737).length < 2 ^ (prefixWord ++ tailWord_1824737).sum := by decide
  have hdescent : baseEnd_1824737 < baseStart_1824737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824825 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1824825 : Nat := 118140960795 + 1824825 * 2 ^ 59
def prefixEnd_1824825 : Nat := 4983230072969 + 3 ^ 40 * 1824825 * 2
def baseEnd_1824825 : Nat := 937012335340928097495289

theorem tailTrace_1824825 : CollatzResearch.WordTrace tailWord_1824825 prefixEnd_1824825 937012335340928097495289 := by
  unfold tailWord_1824825
  simp only [CollatzResearch.WordTrace]
  refine ⟨66556835613978155142963929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44371223742652103428642619 66556835613978155142963929)
  ·
    refine ⟨49917626710483616357222947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66556835613978155142963929 49917626710483616357222947)
    ·
      refine ⟨74876440065725424535834421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49917626710483616357222947 74876440065725424535834421)
      ·
        refine ⟨7019666256161758550234477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74876440065725424535834421 7019666256161758550234477)
        ·
          refine ⟨2632374846060659456337929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7019666256161758550234477 2632374846060659456337929)
          ·
            refine ⟨1974281134545494592253447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632374846060659456337929 1974281134545494592253447)
            ·
              refine ⟨2961421701818241888380171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974281134545494592253447 2961421701818241888380171)
              ·
                refine ⟨4442132552727362832570257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961421701818241888380171 4442132552727362832570257)
                ·
                  refine ⟨3331599414545522124427693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4442132552727362832570257 3331599414545522124427693)
                  ·
                    refine ⟨1249349780454570796660385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331599414545522124427693 1249349780454570796660385)
                    ·
                      refine ⟨937012335340928097495289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249349780454570796660385 937012335340928097495289)
                      ·
                        rfl

theorem cell23_1824825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1824825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824825 prefixEnd_1824825 := by exact prefixLift 1824825
  have htrace : WordTrace (prefixWord ++ tailWord_1824825) baseStart_1824825 baseEnd_1824825 := by
    simpa [prefixWord, tailWord_1824825, baseEnd_1824825] using wordTrace_append hprefix tailTrace_1824825
  have hstable : (prefixWord ++ tailWord_1824825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824825).length < 2 ^ (prefixWord ++ tailWord_1824825).sum := by decide
  have hdescent : baseEnd_1824825 < baseStart_1824825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824841 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 3]
def baseStart_1824841 : Nat := 118140960795 + 1824841 * 2 ^ 59
def prefixEnd_1824841 : Nat := 4983230072969 + 3 ^ 40 * 1824841 * 2
def baseEnd_1824841 : Nat := 937020551031400034895215

theorem tailTrace_1824841 : CollatzResearch.WordTrace tailWord_1824841 prefixEnd_1824841 937020551031400034895215 := by
  unfold tailWord_1824841
  simp only [CollatzResearch.WordTrace]
  refine ⟨66557419181920189875546377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44371612787946793250364251 66557419181920189875546377)
  ·
    refine ⟨49918064386440142406659783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66557419181920189875546377 49918064386440142406659783)
    ·
      refine ⟨74877096579660213609989675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49918064386440142406659783 74877096579660213609989675)
      ·
        refine ⟨112315644869490320414984513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74877096579660213609989675 112315644869490320414984513)
        ·
          refine ⟨84236733652117740311238385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112315644869490320414984513 84236733652117740311238385)
          ·
            refine ⟨63177550239088305233428789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84236733652117740311238385 63177550239088305233428789)
            ·
              refine ⟨5922895334914528615633949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63177550239088305233428789 5922895334914528615633949)
              ·
                refine ⟨2221085750592948230862731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5922895334914528615633949 2221085750592948230862731)
                ·
                  refine ⟨3331628625889422346294097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221085750592948230862731 3331628625889422346294097)
                  ·
                    refine ⟨2498721469417066759720573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3331628625889422346294097 2498721469417066759720573)
                    ·
                      refine ⟨937020551031400034895215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2498721469417066759720573 937020551031400034895215)
                      ·
                        rfl

theorem cell23_1824841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_1824841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824841 prefixEnd_1824841 := by exact prefixLift 1824841
  have htrace : WordTrace (prefixWord ++ tailWord_1824841) baseStart_1824841 baseEnd_1824841 := by
    simpa [prefixWord, tailWord_1824841, baseEnd_1824841] using wordTrace_append hprefix tailTrace_1824841
  have hstable : (prefixWord ++ tailWord_1824841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824841).length < 2 ^ (prefixWord ++ tailWord_1824841).sum := by decide
  have hdescent : baseEnd_1824841 < baseStart_1824841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824855 : List Nat := [1, 1, 3, 2, 2, 1, 4, 4, 1, 2, 2]
def baseStart_1824855 : Nat := 118140960795 + 1824855 * 2 ^ 59
def prefixEnd_1824855 : Nat := 4983230072969 + 3 ^ 40 * 1824855 * 2
def baseEnd_1824855 : Nat := 937027739760562980120151

theorem tailTrace_1824855 : CollatzResearch.WordTrace tailWord_1824855 prefixEnd_1824855 937027739760562980120151 := by
  unfold tailWord_1824855
  simp only [CollatzResearch.WordTrace]
  refine ⟨66557929803869470266556019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44371953202579646844370679 66557929803869470266556019)
  ·
    refine ⟨99836894705804205399834029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66557929803869470266556019 99836894705804205399834029)
    ·
      refine ⟨37438835514676577024937761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99836894705804205399834029 37438835514676577024937761)
      ·
        refine ⟨28079126636007432768703321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37438835514676577024937761 28079126636007432768703321)
        ·
          refine ⟨21059344977005574576527491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28079126636007432768703321 21059344977005574576527491)
          ·
            refine ⟨31589017465508361864791237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21059344977005574576527491 31589017465508361864791237)
            ·
              refine ⟨5922940774782817849648357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31589017465508361864791237 5922940774782817849648357)
              ·
                refine ⟨1110551395271778346809067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5922940774782817849648357 1110551395271778346809067)
                ·
                  refine ⟨1665827092907667520213601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110551395271778346809067 1665827092907667520213601)
                  ·
                    refine ⟨1249370319680750640160201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1665827092907667520213601 1249370319680750640160201)
                    ·
                      refine ⟨937027739760562980120151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249370319680750640160201 937027739760562980120151)
                      ·
                        rfl

theorem cell23_1824855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_1824855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824855 prefixEnd_1824855 := by exact prefixLift 1824855
  have htrace : WordTrace (prefixWord ++ tailWord_1824855) baseStart_1824855 baseEnd_1824855 := by
    simpa [prefixWord, tailWord_1824855, baseEnd_1824855] using wordTrace_append hprefix tailTrace_1824855
  have hstable : (prefixWord ++ tailWord_1824855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824855).length < 2 ^ (prefixWord ++ tailWord_1824855).sum := by decide
  have hdescent : baseEnd_1824855 < baseStart_1824855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824932 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_1824932 : Nat := 118140960795 + 1824932 * 2 ^ 59
def prefixEnd_1824932 : Nat := 4983230072969 + 3 ^ 40 * 1824932 * 2
def baseEnd_1824932 : Nat := 937067277770959178857297

theorem tailTrace_1824932 : CollatzResearch.WordTrace tailWord_1824932 prefixEnd_1824932 937067277770959178857297 := by
  unfold tailWord_1824932
  simp only [CollatzResearch.WordTrace]
  refine ⟨33280369112295256208554525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44373825483060341611406033 33280369112295256208554525)
  ·
    refine ⟨12480138417110721078207947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33280369112295256208554525 12480138417110721078207947)
    ·
      refine ⟨18720207625666081617311921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12480138417110721078207947 18720207625666081617311921)
      ·
        refine ⟨14040155719249561212983941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18720207625666081617311921 14040155719249561212983941)
        ·
          refine ⟨2632529197359292727434489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14040155719249561212983941 2632529197359292727434489)
          ·
            refine ⟨1974396898019469545575867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632529197359292727434489 1974396898019469545575867)
            ·
              refine ⟨2961595347029204318363801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974396898019469545575867 2961595347029204318363801)
              ·
                refine ⟨2221196510271903238772851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961595347029204318363801 2221196510271903238772851)
                ·
                  refine ⟨3331794765407854858159277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221196510271903238772851 3331794765407854858159277)
                  ·
                    refine ⟨1249423037027945571809729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331794765407854858159277 1249423037027945571809729)
                    ·
                      refine ⟨937067277770959178857297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249423037027945571809729 937067277770959178857297)
                      ·
                        rfl

theorem cell23_1824932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_1824932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824932 prefixEnd_1824932 := by exact prefixLift 1824932
  have htrace : WordTrace (prefixWord ++ tailWord_1824932) baseStart_1824932 baseEnd_1824932 := by
    simpa [prefixWord, tailWord_1824932, baseEnd_1824932] using wordTrace_append hprefix tailTrace_1824932
  have hstable : (prefixWord ++ tailWord_1824932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824932).length < 2 ^ (prefixWord ++ tailWord_1824932).sum := by decide
  have hdescent : baseEnd_1824932 < baseStart_1824932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824945 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1824945 : Nat := 118140960795 + 1824945 * 2 ^ 59
def prefixEnd_1824945 : Nat := 4983230072969 + 3 ^ 40 * 1824945 * 2
def baseEnd_1824945 : Nat := 937073953019467627994737

theorem tailTrace_1824945 : CollatzResearch.WordTrace tailWord_1824945 prefixEnd_1824945 937073953019467627994737 := by
  unfold tailWord_1824945
  simp only [CollatzResearch.WordTrace]
  refine ⟨66561212373543415637332289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44374141582362277091554859 66561212373543415637332289)
  ·
    refine ⟨49920909280157561727999217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66561212373543415637332289 49920909280157561727999217)
    ·
      refine ⟨37440681960118171295999413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49920909280157561727999217 37440681960118171295999413)
      ·
        refine ⟨3510063933761078558999945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37440681960118171295999413 3510063933761078558999945)
        ·
          refine ⟨2632547950320808919249959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510063933761078558999945 2632547950320808919249959)
          ·
            refine ⟨3948821925481213378874939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632547950320808919249959 3948821925481213378874939)
            ·
              refine ⟨5923232888221820068312409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948821925481213378874939 5923232888221820068312409)
              ·
                refine ⟨4442424666166365051234307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5923232888221820068312409 4442424666166365051234307)
                ·
                  refine ⟨6663636999249547576851461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442424666166365051234307 6663636999249547576851461)
                  ·
                    refine ⟨1249431937359290170659649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663636999249547576851461 1249431937359290170659649)
                    ·
                      refine ⟨937073953019467627994737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249431937359290170659649 937073953019467627994737)
                      ·
                        rfl

theorem cell23_1824945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1824945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824945 prefixEnd_1824945 := by exact prefixLift 1824945
  have htrace : WordTrace (prefixWord ++ tailWord_1824945) baseStart_1824945 baseEnd_1824945 := by
    simpa [prefixWord, tailWord_1824945, baseEnd_1824945] using wordTrace_append hprefix tailTrace_1824945
  have hstable : (prefixWord ++ tailWord_1824945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824945).length < 2 ^ (prefixWord ++ tailWord_1824945).sum := by decide
  have hdescent : baseEnd_1824945 < baseStart_1824945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824949 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1824949 : Nat := 118140960795 + 1824949 * 2 ^ 59
def prefixEnd_1824949 : Nat := 4983230072969 + 3 ^ 40 * 1824949 * 2
def baseEnd_1824949 : Nat := 937076006942085612344719

theorem tailTrace_1824949 : CollatzResearch.WordTrace tailWord_1824949 prefixEnd_1824949 937076006942085612344719 := by
  unfold tailWord_1824949
  simp only [CollatzResearch.WordTrace]
  refine ⟨66561358265528924320477901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44374238843685949546985267 66561358265528924320477901)
  ·
    refine ⟨24960509349573346620179213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66561358265528924320477901 24960509349573346620179213)
    ·
      refine ⟨9360191006090004982567205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24960509349573346620179213 9360191006090004982567205)
      ·
        refine ⟨1755035813641875934231351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9360191006090004982567205 1755035813641875934231351)
        ·
          refine ⟨2632553720462813901347027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755035813641875934231351 2632553720462813901347027)
          ·
            refine ⟨3948830580694220852020541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632553720462813901347027 3948830580694220852020541)
            ·
              refine ⟨1480811467760332819507703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3948830580694220852020541 1480811467760332819507703)
              ·
                refine ⟨2221217201640499229261555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480811467760332819507703 2221217201640499229261555)
                ·
                  refine ⟨3331825802460748843892333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221217201640499229261555 3331825802460748843892333)
                  ·
                    refine ⟨1249434675922780816459625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3331825802460748843892333 1249434675922780816459625)
                    ·
                      refine ⟨937076006942085612344719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249434675922780816459625 937076006942085612344719)
                      ·
                        rfl

theorem cell23_1824949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1824949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824949 prefixEnd_1824949 := by exact prefixLift 1824949
  have htrace : WordTrace (prefixWord ++ tailWord_1824949) baseStart_1824949 baseEnd_1824949 := by
    simpa [prefixWord, tailWord_1824949, baseEnd_1824949] using wordTrace_append hprefix tailTrace_1824949
  have hstable : (prefixWord ++ tailWord_1824949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824949).length < 2 ^ (prefixWord ++ tailWord_1824949).sum := by decide
  have hdescent : baseEnd_1824949 < baseStart_1824949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824971 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 7, 2]
def baseStart_1824971 : Nat := 118140960795 + 1824971 * 2 ^ 59
def prefixEnd_1824971 : Nat := 4983230072969 + 3 ^ 40 * 1824971 * 2
def baseEnd_1824971 : Nat := 937087303516484526269617

theorem tailTrace_1824971 : CollatzResearch.WordTrace tailWord_1824971 prefixEnd_1824971 937087303516484526269617 := by
  unfold tailWord_1824971
  simp only [CollatzResearch.WordTrace]
  refine ⟨66562160671449222077778767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44374773780966148051852511 66562160671449222077778767)
  ·
    refine ⟨99843241007173833116668151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66562160671449222077778767 99843241007173833116668151)
    ·
      refine ⟨149764861510760749675002227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99843241007173833116668151 149764861510760749675002227)
      ·
        refine ⟨224647292266141124512503341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149764861510760749675002227 224647292266141124512503341)
        ·
          refine ⟨84242734599802921692188753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224647292266141124512503341 84242734599802921692188753)
          ·
            refine ⟨63182050949852191269141565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84242734599802921692188753 63182050949852191269141565)
            ·
              refine ⟨23693269106194571725928087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63182050949852191269141565 23693269106194571725928087)
              ·
                refine ⟨35539903659291857588892131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23693269106194571725928087 35539903659291857588892131)
                ·
                  refine ⟨53309855488937786383338197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35539903659291857588892131 53309855488937786383338197)
                  ·
                    refine ⟨1249449738021979368359489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53309855488937786383338197 1249449738021979368359489)
                    ·
                      refine ⟨937087303516484526269617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249449738021979368359489 937087303516484526269617)
                      ·
                        rfl

theorem cell23_1824971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 7, 2].length) (baseStart_1824971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824971 prefixEnd_1824971 := by exact prefixLift 1824971
  have htrace : WordTrace (prefixWord ++ tailWord_1824971) baseStart_1824971 baseEnd_1824971 := by
    simpa [prefixWord, tailWord_1824971, baseEnd_1824971] using wordTrace_append hprefix tailTrace_1824971
  have hstable : (prefixWord ++ tailWord_1824971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824971).length < 2 ^ (prefixWord ++ tailWord_1824971).sum := by decide
  have hdescent : baseEnd_1824971 < baseStart_1824971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824978 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1824978 : Nat := 118140960795 + 1824978 * 2 ^ 59
def prefixEnd_1824978 : Nat := 4983230072969 + 3 ^ 40 * 1824978 * 2
def baseEnd_1824978 : Nat := 937090897881065998882085

theorem tailTrace_1824978 : CollatzResearch.WordTrace tailWord_1824978 prefixEnd_1824978 937090897881065998882085 := by
  unfold tailWord_1824978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16640603995605965568320897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44374943988282574848855725 16640603995605965568320897)
  ·
    refine ⟨12480452996704474176240673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16640603995605965568320897 12480452996704474176240673)
    ·
      refine ⟨9360339747528355632180505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12480452996704474176240673 9360339747528355632180505)
      ·
        refine ⟨7020254810646266724135379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9360339747528355632180505 7020254810646266724135379)
        ·
          refine ⟨10530382215969400086203069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020254810646266724135379 10530382215969400086203069)
          ·
            refine ⟨3948893330988525032326151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10530382215969400086203069 3948893330988525032326151)
            ·
              refine ⟨5923339996482787548489227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948893330988525032326151 5923339996482787548489227)
              ·
                refine ⟨8885009994724181322733841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923339996482787548489227 8885009994724181322733841)
                ·
                  refine ⟨6663757496043135992050381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8885009994724181322733841 6663757496043135992050381)
                  ·
                    refine ⟨2498909061016175997018893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6663757496043135992050381 2498909061016175997018893)
                    ·
                      refine ⟨937090897881065998882085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2498909061016175997018893 937090897881065998882085)
                      ·
                        rfl

theorem cell23_1824978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1824978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1824978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1824978 prefixEnd_1824978 := by exact prefixLift 1824978
  have htrace : WordTrace (prefixWord ++ tailWord_1824978) baseStart_1824978 baseEnd_1824978 := by
    simpa [prefixWord, tailWord_1824978, baseEnd_1824978] using wordTrace_append hprefix tailTrace_1824978
  have hstable : (prefixWord ++ tailWord_1824978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824978).length < 2 ^ (prefixWord ++ tailWord_1824978).sum := by decide
  have hdescent : baseEnd_1824978 < baseStart_1824978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825011 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 5, 4]
def baseStart_1825011 : Nat := 118140960795 + 1825011 * 2 ^ 59
def prefixEnd_1825011 : Nat := 4983230072969 + 3 ^ 40 * 1825011 * 2
def baseEnd_1825011 : Nat := 312369280914221456589811

theorem tailTrace_1825011 : CollatzResearch.WordTrace tailWord_1825011 prefixEnd_1825011 312369280914221456589811 := by
  unfold tailWord_1825011
  simp only [CollatzResearch.WordTrace]
  refine ⟨66563619591304308909234887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44375746394202872606156591 66563619591304308909234887)
  ·
    refine ⟨99845429386956463363852331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66563619591304308909234887 99845429386956463363852331)
    ·
      refine ⟨149768144080434695045778497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99845429386956463363852331 149768144080434695045778497)
      ·
        refine ⟨112326108060326021284333873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149768144080434695045778497 112326108060326021284333873)
        ·
          refine ⟨84244581045244515963250405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112326108060326021284333873 84244581045244515963250405)
          ·
            refine ⟨15795858945983346743109451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84244581045244515963250405 15795858945983346743109451)
            ·
              refine ⟨23693788418975020114664177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15795858945983346743109451 23693788418975020114664177)
              ·
                refine ⟨17770341314231265085998133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23693788418975020114664177 17770341314231265085998133)
                ·
                  refine ⟨1665969498209181101812325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17770341314231265085998133 1665969498209181101812325)
                  ·
                    refine ⟨312369280914221456589811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1665969498209181101812325 312369280914221456589811)
                    ·
                      rfl

theorem cell23_1825011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 4].length) (baseStart_1825011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825011 prefixEnd_1825011 := by exact prefixLift 1825011
  have htrace : WordTrace (prefixWord ++ tailWord_1825011) baseStart_1825011 baseEnd_1825011 := by
    simpa [prefixWord, tailWord_1825011, baseEnd_1825011] using wordTrace_append hprefix tailTrace_1825011
  have hstable : (prefixWord ++ tailWord_1825011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825011).length < 2 ^ (prefixWord ++ tailWord_1825011).sum := by decide
  have hdescent : baseEnd_1825011 < baseStart_1825011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825018 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2]
def baseStart_1825018 : Nat := 118140960795 + 1825018 * 2 ^ 59
def prefixEnd_1825018 : Nat := 4983230072969 + 3 ^ 40 * 1825018 * 2
def baseEnd_1825018 : Nat := 937111437107245842381901

theorem tailTrace_1825018 : CollatzResearch.WordTrace tailWord_1825018 prefixEnd_1825018 937111437107245842381901 := by
  unfold tailWord_1825018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16640968725569737276184927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44375916601519299403159805 16640968725569737276184927)
  ·
    refine ⟨24961453088354605914277391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16640968725569737276184927 24961453088354605914277391)
    ·
      refine ⟨37442179632531908871416087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24961453088354605914277391 37442179632531908871416087)
      ·
        refine ⟨56163269448797863307124131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37442179632531908871416087 56163269448797863307124131)
        ·
          refine ⟨84244904173196794960686197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56163269448797863307124131 84244904173196794960686197)
          ·
            refine ⟨7897959766237199527564331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84244904173196794960686197 7897959766237199527564331)
            ·
              refine ⟨11846939649355799291346497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897959766237199527564331 11846939649355799291346497)
              ·
                refine ⟨8885204737016849468509873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11846939649355799291346497 8885204737016849468509873)
                ·
                  refine ⟨6663903552762637101382405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8885204737016849468509873 6663903552762637101382405)
                  ·
                    refine ⟨1249481916142994456509201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6663903552762637101382405 1249481916142994456509201)
                    ·
                      refine ⟨937111437107245842381901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249481916142994456509201 937111437107245842381901)
                      ·
                        rfl

theorem cell23_1825018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_1825018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825018 prefixEnd_1825018 := by exact prefixLift 1825018
  have htrace : WordTrace (prefixWord ++ tailWord_1825018) baseStart_1825018 baseEnd_1825018 := by
    simpa [prefixWord, tailWord_1825018, baseEnd_1825018] using wordTrace_append hprefix tailTrace_1825018
  have hstable : (prefixWord ++ tailWord_1825018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825018).length < 2 ^ (prefixWord ++ tailWord_1825018).sum := by decide
  have hdescent : baseEnd_1825018 < baseStart_1825018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825068 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_1825068 : Nat := 118140960795 + 1825068 * 2 ^ 59
def prefixEnd_1825068 : Nat := 4983230072969 + 3 ^ 40 * 1825068 * 2
def baseEnd_1825068 : Nat := 937137111139970646756671

theorem tailTrace_1825068 : CollatzResearch.WordTrace tailWord_1825068 prefixEnd_1825068 937137111139970646756671 := by
  unfold tailWord_1825068
  simp only [CollatzResearch.WordTrace]
  refine ⟨33282849276048903822029929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44377132368065205096039905 33282849276048903822029929)
  ·
    refine ⟨24962136957036677866522447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33282849276048903822029929 24962136957036677866522447)
    ·
      refine ⟨37443205435555016799783671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24962136957036677866522447 37443205435555016799783671)
      ·
        refine ⟨56164808153332525199675507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37443205435555016799783671 56164808153332525199675507)
        ·
          refine ⟨84247212229998787799513261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56164808153332525199675507 84247212229998787799513261)
          ·
            refine ⟨31592704586249545424817473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84247212229998787799513261 31592704586249545424817473)
            ·
              refine ⟨23694528439687159068613105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31592704586249545424817473 23694528439687159068613105)
              ·
                refine ⟨17770896329765369301459829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23694528439687159068613105 17770896329765369301459829)
                ·
                  refine ⟨1666021530915503372011859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17770896329765369301459829 1666021530915503372011859)
                  ·
                    refine ⟨2499032296373255058017789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1666021530915503372011859 2499032296373255058017789)
                    ·
                      refine ⟨937137111139970646756671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2499032296373255058017789 937137111139970646756671)
                      ·
                        rfl

theorem cell23_1825068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_1825068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825068 prefixEnd_1825068 := by exact prefixLift 1825068
  have htrace : WordTrace (prefixWord ++ tailWord_1825068) baseStart_1825068 baseEnd_1825068 := by
    simpa [prefixWord, tailWord_1825068, baseEnd_1825068] using wordTrace_append hprefix tailTrace_1825068
  have hstable : (prefixWord ++ tailWord_1825068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825068).length < 2 ^ (prefixWord ++ tailWord_1825068).sum := by decide
  have hdescent : baseEnd_1825068 < baseStart_1825068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825105 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 1, 5]
def baseStart_1825105 : Nat := 118140960795 + 1825105 * 2 ^ 59
def prefixEnd_1825105 : Nat := 4983230072969 + 3 ^ 40 * 1825105 * 2
def baseEnd_1825105 : Nat := 312385369974729000664667

theorem tailTrace_1825105 : CollatzResearch.WordTrace tailWord_1825105 prefixEnd_1825105 312385369974729000664667 := by
  unfold tailWord_1825105
  simp only [CollatzResearch.WordTrace]
  refine ⟨66567048052963762963156769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44378032035309175308771179 66567048052963762963156769)
  ·
    refine ⟨49925286039722822222367577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66567048052963762963156769 49925286039722822222367577)
    ·
      refine ⟨37443964529792116666775683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49925286039722822222367577 37443964529792116666775683)
      ·
        refine ⟨56165946794688175000163525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37443964529792116666775683 56165946794688175000163525)
        ·
          refine ⟨10531115024004032812530661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56165946794688175000163525 10531115024004032812530661)
          ·
            refine ⟨1974584067000756152349499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10531115024004032812530661 1974584067000756152349499)
            ·
              refine ⟨2961876100501134228524249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974584067000756152349499 2961876100501134228524249)
              ·
                refine ⟨2221407075375850671393187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961876100501134228524249 2221407075375850671393187)
                ·
                  refine ⟨3332110613063776007089781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221407075375850671393187 3332110613063776007089781)
                  ·
                    refine ⟨312385369974729000664667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3332110613063776007089781 312385369974729000664667)
                    ·
                      rfl

theorem cell23_1825105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_1825105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825105 prefixEnd_1825105 := by exact prefixLift 1825105
  have htrace : WordTrace (prefixWord ++ tailWord_1825105) baseStart_1825105 baseEnd_1825105 := by
    simpa [prefixWord, tailWord_1825105, baseEnd_1825105] using wordTrace_append hprefix tailTrace_1825105
  have hstable : (prefixWord ++ tailWord_1825105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825105).length < 2 ^ (prefixWord ++ tailWord_1825105).sum := by decide
  have hdescent : baseEnd_1825105 < baseStart_1825105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825122 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1825122 : Nat := 118140960795 + 1825122 * 2 ^ 59
def prefixEnd_1825122 : Nat := 4983230072969 + 3 ^ 40 * 1825122 * 2
def baseEnd_1825122 : Nat := 312388279698437811827141

theorem tailTrace_1825122 : CollatzResearch.WordTrace tailWord_1825122 prefixEnd_1825122 312388279698437811827141 := by
  unfold tailWord_1825122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641917023475543716631405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44378445395934783244350413 16641917023475543716631405)
  ·
    refine ⟨6240718883803328893736777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16641917023475543716631405 6240718883803328893736777)
    ·
      refine ⟨4680539162852496670302583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6240718883803328893736777 4680539162852496670302583)
      ·
        refine ⟨7020808744278745005453875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680539162852496670302583 7020808744278745005453875)
        ·
          refine ⟨10531213116418117508180813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020808744278745005453875 10531213116418117508180813)
          ·
            refine ⟨3949204918656794065567805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10531213116418117508180813 3949204918656794065567805)
            ·
              refine ⟨1480951844496297774587927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3949204918656794065567805 1480951844496297774587927)
              ·
                refine ⟨2221427766744446661881891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480951844496297774587927 2221427766744446661881891)
                ·
                  refine ⟨3332141650116669992822837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221427766744446661881891 3332141650116669992822837)
                  ·
                    refine ⟨312388279698437811827141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3332141650116669992822837 312388279698437811827141)
                    ·
                      rfl

theorem cell23_1825122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1825122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825122 prefixEnd_1825122 := by exact prefixLift 1825122
  have htrace : WordTrace (prefixWord ++ tailWord_1825122) baseStart_1825122 baseEnd_1825122 := by
    simpa [prefixWord, tailWord_1825122, baseEnd_1825122] using wordTrace_append hprefix tailTrace_1825122
  have hstable : (prefixWord ++ tailWord_1825122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825122).length < 2 ^ (prefixWord ++ tailWord_1825122).sum := by decide
  have hdescent : baseEnd_1825122 < baseStart_1825122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825155 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 4]
def baseStart_1825155 : Nat := 118140960795 + 1825155 * 2 ^ 59
def prefixEnd_1825155 : Nat := 4983230072969 + 3 ^ 40 * 1825155 * 2
def baseEnd_1825155 : Nat := 937181783956911806368771

theorem tailTrace_1825155 : CollatzResearch.WordTrace tailWord_1825155 prefixEnd_1825155 937181783956911806368771 := by
  unfold tailWord_1825155
  simp only [CollatzResearch.WordTrace]
  refine ⟨66568871702782621502476919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44379247801855081001651279 66568871702782621502476919)
  ·
    refine ⟨99853307554173932253715379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66568871702782621502476919 99853307554173932253715379)
    ·
      refine ⟨149779961331260898380573069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99853307554173932253715379 149779961331260898380573069)
      ·
        refine ⟨56167485499222836892714901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149779961331260898380573069 56167485499222836892714901)
        ·
          refine ⟨2632850882776070479346011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56167485499222836892714901 2632850882776070479346011)
          ·
            refine ⟨3949276324164105719019017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632850882776070479346011 3949276324164105719019017)
            ·
              refine ⟨2961957243123079289264263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949276324164105719019017 2961957243123079289264263)
              ·
                refine ⟨4442935864684618933896395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961957243123079289264263 4442935864684618933896395)
                ·
                  refine ⟨6664403797026928400844593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442935864684618933896395 6664403797026928400844593)
                  ·
                    refine ⟨4998302847770196300633445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6664403797026928400844593 4998302847770196300633445)
                    ·
                      refine ⟨937181783956911806368771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4998302847770196300633445 937181783956911806368771)
                      ·
                        rfl

theorem cell23_1825155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_1825155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825155 prefixEnd_1825155 := by exact prefixLift 1825155
  have htrace : WordTrace (prefixWord ++ tailWord_1825155) baseStart_1825155 baseEnd_1825155 := by
    simpa [prefixWord, tailWord_1825155, baseEnd_1825155] using wordTrace_append hprefix tailTrace_1825155
  have hstable : (prefixWord ++ tailWord_1825155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825155).length < 2 ^ (prefixWord ++ tailWord_1825155).sum := by decide
  have hdescent : baseEnd_1825155 < baseStart_1825155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825168 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 7, 2]
def baseStart_1825168 : Nat := 118140960795 + 1825168 * 2 ^ 59
def prefixEnd_1825168 : Nat := 4983230072969 + 3 ^ 40 * 1825168 * 2
def baseEnd_1825168 : Nat := 937188459205420255506211

theorem tailTrace_1825168 : CollatzResearch.WordTrace tailWord_1825168 prefixEnd_1825168 937188459205420255506211 := by
  unfold tailWord_1825168
  simp only [CollatzResearch.WordTrace]
  refine ⟨33284672925867762361350079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44379563901157016481800105 33284672925867762361350079)
  ·
    refine ⟨49927009388801643542025119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33284672925867762361350079 49927009388801643542025119)
    ·
      refine ⟨74890514083202465313037679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49927009388801643542025119 74890514083202465313037679)
      ·
        refine ⟨112335771124803697969556519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74890514083202465313037679 112335771124803697969556519)
        ·
          refine ⟨168503656687205546954334779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112335771124803697969556519 168503656687205546954334779)
          ·
            refine ⟨252755485030808320431502169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168503656687205546954334779 252755485030808320431502169)
            ·
              refine ⟨189566613773106240323626627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252755485030808320431502169 189566613773106240323626627)
              ·
                refine ⟨284349920659659360485439941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189566613773106240323626627 284349920659659360485439941)
                ·
                  refine ⟨53315610123686130091019989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284349920659659360485439941 53315610123686130091019989)
                  ·
                    refine ⟨1249584612273893674008281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53315610123686130091019989 1249584612273893674008281)
                    ·
                      refine ⟨937188459205420255506211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249584612273893674008281 937188459205420255506211)
                      ·
                        rfl

theorem cell23_1825168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 7, 2].length) (baseStart_1825168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825168 prefixEnd_1825168 := by exact prefixLift 1825168
  have htrace : WordTrace (prefixWord ++ tailWord_1825168) baseStart_1825168 baseEnd_1825168 := by
    simpa [prefixWord, tailWord_1825168, baseEnd_1825168] using wordTrace_append hprefix tailTrace_1825168
  have hstable : (prefixWord ++ tailWord_1825168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825168).length < 2 ^ (prefixWord ++ tailWord_1825168).sum := by decide
  have hdescent : baseEnd_1825168 < baseStart_1825168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825176 : List Nat := [2, 1, 2, 5, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1825176 : Nat := 118140960795 + 1825176 * 2 ^ 59
def prefixEnd_1825176 : Nat := 4983230072969 + 3 ^ 40 * 1825176 * 2
def baseEnd_1825176 : Nat := 937192567050656224206175

theorem tailTrace_1825176 : CollatzResearch.WordTrace tailWord_1825176 prefixEnd_1825176 937192567050656224206175 := by
  unfold tailWord_1825176
  simp only [CollatzResearch.WordTrace]
  refine ⟨33284818817853271044495691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44379758423804361392660921 33284818817853271044495691)
  ·
    refine ⟨49927228226779906566743537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33284818817853271044495691 49927228226779906566743537)
    ·
      refine ⟨37445421170084929925057653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49927228226779906566743537 37445421170084929925057653)
      ·
        refine ⟨3510508234695462180474155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37445421170084929925057653 3510508234695462180474155)
        ·
          refine ⟨5265762352043193270711233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510508234695462180474155 5265762352043193270711233)
          ·
            refine ⟨3949321764032394953033425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5265762352043193270711233 3949321764032394953033425)
            ·
              refine ⟨2961991323024296214775069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949321764032394953033425 2961991323024296214775069)
              ·
                refine ⟨1110746746134111080540651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2961991323024296214775069 1110746746134111080540651)
                ·
                  refine ⟨1666120119201166620810977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110746746134111080540651 1666120119201166620810977)
                  ·
                    refine ⟨1249590089400874965608233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1666120119201166620810977 1249590089400874965608233)
                    ·
                      refine ⟨937192567050656224206175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249590089400874965608233 937192567050656224206175)
                      ·
                        rfl

theorem cell23_1825176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1825176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825176 prefixEnd_1825176 := by exact prefixLift 1825176
  have htrace : WordTrace (prefixWord ++ tailWord_1825176) baseStart_1825176 baseEnd_1825176 := by
    simpa [prefixWord, tailWord_1825176, baseEnd_1825176] using wordTrace_append hprefix tailTrace_1825176
  have hstable : (prefixWord ++ tailWord_1825176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825176).length < 2 ^ (prefixWord ++ tailWord_1825176).sum := by decide
  have hdescent : baseEnd_1825176 < baseStart_1825176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825209 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 2, 1, 3]
def baseStart_1825209 : Nat := 118140960795 + 1825209 * 2 ^ 59
def prefixEnd_1825209 : Nat := 4983230072969 + 3 ^ 40 * 1825209 * 2
def baseEnd_1825209 : Nat := 937209511912254595093523

theorem tailTrace_1825209 : CollatzResearch.WordTrace tailWord_1825209 prefixEnd_1825209 937209511912254595093523 := by
  unfold tailWord_1825209
  simp only [CollatzResearch.WordTrace]
  refine ⟨66570841244586988724942681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44380560829724659149961787 66570841244586988724942681)
  ·
    refine ⟨49928130933440241543707011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66570841244586988724942681 49928130933440241543707011)
    ·
      refine ⟨74892196400160362315560517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49928130933440241543707011 74892196400160362315560517)
      ·
        refine ⟨14042286825030067934167597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74892196400160362315560517 14042286825030067934167597)
        ·
          refine ⟨5265857559386275475312849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14042286825030067934167597 5265857559386275475312849)
          ·
            refine ⟨3949393169539706606484637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5265857559386275475312849 3949393169539706606484637)
            ·
              refine ⟨1481022438577389977431739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3949393169539706606484637 1481022438577389977431739)
              ·
                refine ⟨2221533657866084966147609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481022438577389977431739 2221533657866084966147609)
                ·
                  refine ⟨1666150243399563724610707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2221533657866084966147609 1666150243399563724610707)
                  ·
                    refine ⟨2499225365099345586916061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1666150243399563724610707 2499225365099345586916061)
                    ·
                      refine ⟨937209511912254595093523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2499225365099345586916061 937209511912254595093523)
                      ·
                        rfl

theorem cell23_1825209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_1825209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825209 prefixEnd_1825209 := by exact prefixLift 1825209
  have htrace : WordTrace (prefixWord ++ tailWord_1825209) baseStart_1825209 baseEnd_1825209 := by
    simpa [prefixWord, tailWord_1825209, baseEnd_1825209] using wordTrace_append hprefix tailTrace_1825209
  have hstable : (prefixWord ++ tailWord_1825209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825209).length < 2 ^ (prefixWord ++ tailWord_1825209).sum := by decide
  have hdescent : baseEnd_1825209 < baseStart_1825209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825211 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6]
def baseStart_1825211 : Nat := 118140960795 + 1825211 * 2 ^ 59
def prefixEnd_1825211 : Nat := 4983230072969 + 3 ^ 40 * 1825211 * 2
def baseEnd_1825211 : Nat := 937210538873563587268513

theorem tailTrace_1825211 : CollatzResearch.WordTrace tailWord_1825211 prefixEnd_1825211 937210538873563587268513 := by
  unfold tailWord_1825211
  simp only [CollatzResearch.WordTrace]
  refine ⟨66570914190579743066515487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44380609460386495377676991 66570914190579743066515487)
  ·
    refine ⟨99856371285869614599773231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66570914190579743066515487 99856371285869614599773231)
    ·
      refine ⟨149784556928804421899659847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99856371285869614599773231 149784556928804421899659847)
      ·
        refine ⟨224676835393206632849489771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149784556928804421899659847 224676835393206632849489771)
        ·
          refine ⟨337015253089809949274234657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224676835393206632849489771 337015253089809949274234657)
          ·
            refine ⟨252761439817357461955675993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337015253089809949274234657 252761439817357461955675993)
            ·
              refine ⟨189571079863018096466756995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252761439817357461955675993 189571079863018096466756995)
              ·
                refine ⟨284356619794527144700135493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189571079863018096466756995 284356619794527144700135493)
                ·
                  refine ⟨53316866211473839631275405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284356619794527144700135493 53316866211473839631275405)
                  ·
                    refine ⟨19993824829302689861728277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53316866211473839631275405 19993824829302689861728277)
                    ·
                      refine ⟨937210538873563587268513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19993824829302689861728277 937210538873563587268513)
                      ·
                        rfl

theorem cell23_1825211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_1825211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825211 prefixEnd_1825211 := by exact prefixLift 1825211
  have htrace : WordTrace (prefixWord ++ tailWord_1825211) baseStart_1825211 baseEnd_1825211 := by
    simpa [prefixWord, tailWord_1825211, baseEnd_1825211] using wordTrace_append hprefix tailTrace_1825211
  have hstable : (prefixWord ++ tailWord_1825211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825211).length < 2 ^ (prefixWord ++ tailWord_1825211).sum := by decide
  have hdescent : baseEnd_1825211 < baseStart_1825211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825266 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1825266 : Nat := 118140960795 + 1825266 * 2 ^ 59
def prefixEnd_1825266 : Nat := 4983230072969 + 3 ^ 40 * 1825266 * 2
def baseEnd_1825266 : Nat := 937238780309560872080761

theorem tailTrace_1825266 : CollatzResearch.WordTrace tailWord_1825266 prefixEnd_1825266 937238780309560872080761 := by
  unfold tailWord_1825266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643230051345121864941913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44381946803586991639845101 16643230051345121864941913)
  ·
    refine ⟨12482422538508841398706435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16643230051345121864941913 12482422538508841398706435)
    ·
      refine ⟨18723633807763262098059653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12482422538508841398706435 18723633807763262098059653)
      ·
        refine ⟨3510681338955611643386185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18723633807763262098059653 3510681338955611643386185)
        ·
          refine ⟨2633011004216708732539639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510681338955611643386185 2633011004216708732539639)
          ·
            refine ⟨3949516506325063098809459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633011004216708732539639 3949516506325063098809459)
            ·
              refine ⟨5924274759487594648214189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949516506325063098809459 5924274759487594648214189)
              ·
                refine ⟨2221603034807847993080321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5924274759487594648214189 2221603034807847993080321)
                ·
                  refine ⟨1666202276105885994810241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2221603034807847993080321 1666202276105885994810241)
                  ·
                    refine ⟨1249651707079414496107681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1666202276105885994810241 1249651707079414496107681)
                    ·
                      refine ⟨937238780309560872080761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249651707079414496107681 937238780309560872080761)
                      ·
                        rfl

theorem cell23_1825266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1825266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825266 prefixEnd_1825266 := by exact prefixLift 1825266
  have htrace : WordTrace (prefixWord ++ tailWord_1825266) baseStart_1825266 baseEnd_1825266 := by
    simpa [prefixWord, tailWord_1825266, baseEnd_1825266] using wordTrace_append hprefix tailTrace_1825266
  have hstable : (prefixWord ++ tailWord_1825266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825266).length < 2 ^ (prefixWord ++ tailWord_1825266).sum := by decide
  have hdescent : baseEnd_1825266 < baseStart_1825266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825305 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 4, 4, 2]
def baseStart_1825305 : Nat := 118140960795 + 1825305 * 2 ^ 59
def prefixEnd_1825305 : Nat := 4983230072969 + 3 ^ 40 * 1825305 * 2
def baseEnd_1825305 : Nat := 937258806055086219493081

theorem tailTrace_1825305 : CollatzResearch.WordTrace tailWord_1825305 prefixEnd_1825305 937258806055086219493081 := by
  unfold tailWord_1825305
  simp only [CollatzResearch.WordTrace]
  refine ⟨66574342652239197120437369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44382895101492798080291579 66574342652239197120437369)
  ·
    refine ⟨49930756989179397840328027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66574342652239197120437369 49930756989179397840328027)
    ·
      refine ⟨74896135483769096760492041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49930756989179397840328027 74896135483769096760492041)
      ·
        refine ⟨56172101612826822570369031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74896135483769096760492041 56172101612826822570369031)
        ·
          refine ⟨84258152419240233855553547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56172101612826822570369031 84258152419240233855553547)
          ·
            refine ⟨126387228628860350783330321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84258152419240233855553547 126387228628860350783330321)
            ·
              refine ⟨94790421471645263087497741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126387228628860350783330321 94790421471645263087497741)
              ·
                refine ⟨35546408051866973657811653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94790421471645263087497741 35546408051866973657811653)
                ·
                  refine ⟨6664951509725057560839685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35546408051866973657811653 6664951509725057560839685)
                  ·
                    refine ⟨1249678408073448292657441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6664951509725057560839685 1249678408073448292657441)
                    ·
                      refine ⟨937258806055086219493081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249678408073448292657441 937258806055086219493081)
                      ·
                        rfl

theorem cell23_1825305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_1825305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825305 prefixEnd_1825305 := by exact prefixLift 1825305
  have htrace : WordTrace (prefixWord ++ tailWord_1825305) baseStart_1825305 baseEnd_1825305 := by
    simpa [prefixWord, tailWord_1825305, baseEnd_1825305] using wordTrace_append hprefix tailTrace_1825305
  have hstable : (prefixWord ++ tailWord_1825305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825305).length < 2 ^ (prefixWord ++ tailWord_1825305).sum := by decide
  have hdescent : baseEnd_1825305 < baseStart_1825305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825322 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1825322 : Nat := 118140960795 + 1825322 * 2 ^ 59
def prefixEnd_1825322 : Nat := 4983230072969 + 3 ^ 40 * 1825322 * 2
def baseEnd_1825322 : Nat := 937267535226212652980503

theorem tailTrace_1825322 : CollatzResearch.WordTrace tailWord_1825322 prefixEnd_1825322 937267535226212652980503 := by
  unfold tailWord_1825322
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643740673294402255951555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44383308462118406015870813 16643740673294402255951555)
  ·
    refine ⟨24965611009941603383927333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16643740673294402255951555 24965611009941603383927333)
    ·
      refine ⟨4681052064364050634486375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24965611009941603383927333 4681052064364050634486375)
      ·
        refine ⟨7021578096546075951729563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681052064364050634486375 7021578096546075951729563)
        ·
          refine ⟨10532367144819113927594345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021578096546075951729563 10532367144819113927594345)
          ·
            refine ⟨7899275358614335445695759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532367144819113927594345 7899275358614335445695759)
            ·
              refine ⟨11848913037921503168543639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899275358614335445695759 11848913037921503168543639)
              ·
                refine ⟨17773369556882254752815459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11848913037921503168543639 17773369556882254752815459)
                ·
                  refine ⟨26660054335323382129223189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17773369556882254752815459 26660054335323382129223189)
                  ·
                    refine ⟨1249690046968283537307337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26660054335323382129223189 1249690046968283537307337)
                    ·
                      refine ⟨937267535226212652980503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249690046968283537307337 937267535226212652980503)
                      ·
                        rfl

theorem cell23_1825322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1825322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825322 prefixEnd_1825322 := by exact prefixLift 1825322
  have htrace : WordTrace (prefixWord ++ tailWord_1825322) baseStart_1825322 baseEnd_1825322 := by
    simpa [prefixWord, tailWord_1825322, baseEnd_1825322] using wordTrace_append hprefix tailTrace_1825322
  have hstable : (prefixWord ++ tailWord_1825322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825322).length < 2 ^ (prefixWord ++ tailWord_1825322).sum := by decide
  have hdescent : baseEnd_1825322 < baseStart_1825322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825349 : List Nat := [1, 3, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_1825349 : Nat := 118140960795 + 1825349 * 2 ^ 59
def prefixEnd_1825349 : Nat := 4983230072969 + 3 ^ 40 * 1825349 * 2
def baseEnd_1825349 : Nat := 312427133067961349114293

theorem tailTrace_1825349 : CollatzResearch.WordTrace tailWord_1825349 prefixEnd_1825349 312427133067961349114293 := by
  unfold tailWord_1825349
  simp only [CollatzResearch.WordTrace]
  refine ⟨66575947464079792635039101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44383964976053195090026067 66575947464079792635039101)
  ·
    refine ⟨24965980299029922238139663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66575947464079792635039101 24965980299029922238139663)
    ·
      refine ⟨37448970448544883357209495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24965980299029922238139663 37448970448544883357209495)
      ·
        refine ⟨56173455672817325035814243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37448970448544883357209495 56173455672817325035814243)
        ·
          refine ⟨84260183509225987553721365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56173455672817325035814243 84260183509225987553721365)
          ·
            refine ⟨3949696101994968166580689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84260183509225987553721365 3949696101994968166580689)
            ·
              refine ⟨2962272076496226124935517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949696101994968166580689 2962272076496226124935517)
              ·
                refine ⟨1110852028686084796850819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962272076496226124935517 1110852028686084796850819)
                ·
                  refine ⟨1666278043029127195276229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110852028686084796850819 1666278043029127195276229)
                  ·
                    refine ⟨312427133067961349114293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1666278043029127195276229 312427133067961349114293)
                    ·
                      rfl

theorem cell23_1825349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_1825349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825349 prefixEnd_1825349 := by exact prefixLift 1825349
  have htrace : WordTrace (prefixWord ++ tailWord_1825349) baseStart_1825349 baseEnd_1825349 := by
    simpa [prefixWord, tailWord_1825349, baseEnd_1825349] using wordTrace_append hprefix tailTrace_1825349
  have hstable : (prefixWord ++ tailWord_1825349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825349).length < 2 ^ (prefixWord ++ tailWord_1825349).sum := by decide
  have hdescent : baseEnd_1825349 < baseStart_1825349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825389 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1825389 : Nat := 118140960795 + 1825389 * 2 ^ 59
def prefixEnd_1825389 : Nat := 4983230072969 + 3 ^ 40 * 1825389 * 2
def baseEnd_1825389 : Nat := 937301938430063890842695

theorem tailTrace_1825389 : CollatzResearch.WordTrace tailWord_1825389 prefixEnd_1825389 937301938430063890842695 := by
  unfold tailWord_1825389
  simp only [CollatzResearch.WordTrace]
  refine ⟨66577406383934879466495221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44384937589289919644330147 66577406383934879466495221)
  ·
    refine ⟨6241631848493894949983927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66577406383934879466495221 6241631848493894949983927)
    ·
      refine ⟨9362447772740842424975891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6241631848493894949983927 9362447772740842424975891)
      ·
        refine ⟨14043671659111263637463837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9362447772740842424975891 14043671659111263637463837)
        ·
          refine ⟨5266376872166723864048939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14043671659111263637463837 5266376872166723864048939)
          ·
            refine ⟨7899565308250085796073409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266376872166723864048939 7899565308250085796073409)
            ·
              refine ⟨5924673981187564347055057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7899565308250085796073409 5924673981187564347055057)
              ·
                refine ⟨4443505485890673260291293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5924673981187564347055057 4443505485890673260291293)
                ·
                  refine ⟨1666314557209002472609235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4443505485890673260291293 1666314557209002472609235)
                  ·
                    refine ⟨2499471835813503708913853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1666314557209002472609235 2499471835813503708913853)
                    ·
                      refine ⟨937301938430063890842695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2499471835813503708913853 937301938430063890842695)
                      ·
                        rfl

theorem cell23_1825389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1825389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825389 prefixEnd_1825389 := by exact prefixLift 1825389
  have htrace : WordTrace (prefixWord ++ tailWord_1825389) baseStart_1825389 baseEnd_1825389 := by
    simpa [prefixWord, tailWord_1825389, baseEnd_1825389] using wordTrace_append hprefix tailTrace_1825389
  have hstable : (prefixWord ++ tailWord_1825389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825389).length < 2 ^ (prefixWord ++ tailWord_1825389).sum := by decide
  have hdescent : baseEnd_1825389 < baseStart_1825389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825422 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_1825422 : Nat := 118140960795 + 1825422 * 2 ^ 59
def prefixEnd_1825422 : Nat := 4983230072969 + 3 ^ 40 * 1825422 * 2
def baseEnd_1825422 : Nat := 312439627763887420576681

theorem tailTrace_1825422 : CollatzResearch.WordTrace tailWord_1825422 prefixEnd_1825422 312439627763887420576681 := by
  unfold tailWord_1825422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322326249101915762805815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44385739995210217401631013 8322326249101915762805815)
  ·
    refine ⟨12483489373652873644208723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8322326249101915762805815 12483489373652873644208723)
    ·
      refine ⟨18725234060479310466313085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12483489373652873644208723 18725234060479310466313085)
      ·
        refine ⟨7021962772679741424867407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18725234060479310466313085 7021962772679741424867407)
        ·
          refine ⟨10532944159019612137301111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021962772679741424867407 10532944159019612137301111)
          ·
            refine ⟨15799416238529418205951667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10532944159019612137301111 15799416238529418205951667)
            ·
              refine ⟨23699124357794127308927501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15799416238529418205951667 23699124357794127308927501)
              ·
                refine ⟨8887171634172797740847813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23699124357794127308927501 8887171634172797740847813)
                ·
                  refine ⟨1666344681407399576408965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8887171634172797740847813 1666344681407399576408965)
                  ·
                    refine ⟨312439627763887420576681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1666344681407399576408965 312439627763887420576681)
                    ·
                      rfl

theorem cell23_1825422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_1825422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825422 prefixEnd_1825422 := by exact prefixLift 1825422
  have htrace : WordTrace (prefixWord ++ tailWord_1825422) baseStart_1825422 baseEnd_1825422 := by
    simpa [prefixWord, tailWord_1825422, baseEnd_1825422] using wordTrace_append hprefix tailTrace_1825422
  have hstable : (prefixWord ++ tailWord_1825422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825422).length < 2 ^ (prefixWord ++ tailWord_1825422).sum := by decide
  have hdescent : baseEnd_1825422 < baseStart_1825422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825432 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1825432 : Nat := 118140960795 + 1825432 * 2 ^ 59
def prefixEnd_1825432 : Nat := 4983230072969 + 3 ^ 40 * 1825432 * 2
def baseEnd_1825432 : Nat := 937324018098207222604997

theorem tailTrace_1825432 : CollatzResearch.WordTrace tailWord_1825432 prefixEnd_1825432 937324018098207222604997 := by
  unfold tailWord_1825432
  simp only [CollatzResearch.WordTrace]
  refine ⟨33289487361389548905155275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44385983148519398540207033 33289487361389548905155275)
  ·
    refine ⟨49934231042084323357732913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33289487361389548905155275 49934231042084323357732913)
    ·
      refine ⟨37450673281563242518299685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49934231042084323357732913 37450673281563242518299685)
      ·
        refine ⟨7022001240293107972181191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37450673281563242518299685 7022001240293107972181191)
        ·
          refine ⟨10533001860439661958271787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022001240293107972181191 10533001860439661958271787)
          ·
            refine ⟨15799502790659492937407681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10533001860439661958271787 15799502790659492937407681)
            ·
              refine ⟨11849627092994619703055761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15799502790659492937407681 11849627092994619703055761)
              ·
                refine ⟨8887220319745964777291821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11849627092994619703055761 8887220319745964777291821)
                ·
                  refine ⟨3332707619904736791484433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8887220319745964777291821 3332707619904736791484433)
                  ·
                    refine ⟨2499530714928552593613325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3332707619904736791484433 2499530714928552593613325)
                    ·
                      refine ⟨937324018098207222604997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2499530714928552593613325 937324018098207222604997)
                      ·
                        rfl

theorem cell23_1825432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1825432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825432 prefixEnd_1825432 := by exact prefixLift 1825432
  have htrace : WordTrace (prefixWord ++ tailWord_1825432) baseStart_1825432 baseEnd_1825432 := by
    simpa [prefixWord, tailWord_1825432, baseEnd_1825432] using wordTrace_append hprefix tailTrace_1825432
  have hstable : (prefixWord ++ tailWord_1825432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825432).length < 2 ^ (prefixWord ++ tailWord_1825432).sum := by decide
  have hdescent : baseEnd_1825432 < baseStart_1825432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825473 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1825473 : Nat := 118140960795 + 1825473 * 2 ^ 59
def prefixEnd_1825473 : Nat := 4983230072969 + 3 ^ 40 * 1825473 * 2
def baseEnd_1825473 : Nat := 312448356935013854064103

theorem tailTrace_1825473 : CollatzResearch.WordTrace tailWord_1825473 prefixEnd_1825473 312448356935013854064103 := by
  unfold tailWord_1825473
  simp only [CollatzResearch.WordTrace]
  refine ⟨66580470115630561812553073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44386980077087041208368715 66580470115630561812553073)
  ·
    refine ⟨49935352586722921359414805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66580470115630561812553073 49935352586722921359414805)
    ·
      refine ⟨2340719652502636938722569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49935352586722921359414805 2340719652502636938722569)
      ·
        refine ⟨1755539739376977704041927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2340719652502636938722569 1755539739376977704041927)
        ·
          refine ⟨2633309609065466556062891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755539739376977704041927 2633309609065466556062891)
          ·
            refine ⟨3949964413598199834094337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633309609065466556062891 3949964413598199834094337)
            ·
              refine ⟨2962473310198649875570753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949964413598199834094337 2962473310198649875570753)
              ·
                refine ⟨2221854982648987406678065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962473310198649875570753 2221854982648987406678065)
                ·
                  refine ⟨1666391236986740555008549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2221854982648987406678065 1666391236986740555008549)
                  ·
                    refine ⟨312448356935013854064103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1666391236986740555008549 312448356935013854064103)
                    ·
                      rfl

theorem cell23_1825473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1825473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825473 prefixEnd_1825473 := by exact prefixLift 1825473
  have htrace : WordTrace (prefixWord ++ tailWord_1825473) baseStart_1825473 baseEnd_1825473 := by
    simpa [prefixWord, tailWord_1825473, baseEnd_1825473] using wordTrace_append hprefix tailTrace_1825473
  have hstable : (prefixWord ++ tailWord_1825473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825473).length < 2 ^ (prefixWord ++ tailWord_1825473).sum := by decide
  have hdescent : baseEnd_1825473 < baseStart_1825473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825480 : List Nat := [2, 1, 3, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_1825480 : Nat := 118140960795 + 1825480 * 2 ^ 59
def prefixEnd_1825480 : Nat := 4983230072969 + 3 ^ 40 * 1825480 * 2
def baseEnd_1825480 : Nat := 937348665169623034804777

theorem tailTrace_1825480 : CollatzResearch.WordTrace tailWord_1825480 prefixEnd_1825480 937348665169623034804777 := by
  unfold tailWord_1825480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33290362713302601004028947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44387150284403468005371929 33290362713302601004028947)
  ·
    refine ⟨49935544069953901506043421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33290362713302601004028947 49935544069953901506043421)
    ·
      refine ⟨18725829026232713064766283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49935544069953901506043421 18725829026232713064766283)
      ·
        refine ⟨28088743539349069597149425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18725829026232713064766283 28088743539349069597149425)
        ·
          refine ⟨21066557654511802197862069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28088743539349069597149425 21066557654511802197862069)
          ·
            refine ⟨1974989780110481456049569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21066557654511802197862069 1974989780110481456049569)
            ·
              refine ⟨1481242335082861092037177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974989780110481456049569 1481242335082861092037177)
              ·
                refine ⟨1110931751312145819027883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481242335082861092037177 1110931751312145819027883)
                ·
                  refine ⟨1666397626968218728541825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110931751312145819027883 1666397626968218728541825)
                  ·
                    refine ⟨1249798220226164046406369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1666397626968218728541825 1249798220226164046406369)
                    ·
                      refine ⟨937348665169623034804777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249798220226164046406369 937348665169623034804777)
                      ·
                        rfl

theorem cell23_1825480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_1825480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825480 prefixEnd_1825480 := by exact prefixLift 1825480
  have htrace : WordTrace (prefixWord ++ tailWord_1825480) baseStart_1825480 baseEnd_1825480 := by
    simpa [prefixWord, tailWord_1825480, baseEnd_1825480] using wordTrace_append hprefix tailTrace_1825480
  have hstable : (prefixWord ++ tailWord_1825480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825480).length < 2 ^ (prefixWord ++ tailWord_1825480).sum := by decide
  have hdescent : baseEnd_1825480 < baseStart_1825480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825495 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 1, 8]
def baseStart_1825495 : Nat := 118140960795 + 1825495 * 2 ^ 59
def prefixEnd_1825495 : Nat := 4983230072969 + 3 ^ 40 * 1825495 * 2
def baseEnd_1825495 : Nat := 312452122459813492039069

theorem tailTrace_1825495 : CollatzResearch.WordTrace tailWord_1825495 prefixEnd_1825495 312452122459813492039069 := by
  unfold tailWord_1825495
  simp only [CollatzResearch.WordTrace]
  refine ⟨66581272521550859569853939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44387515014367239713235959 66581272521550859569853939)
  ·
    refine ⟨99871908782326289354780909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66581272521550859569853939 99871908782326289354780909)
    ·
      refine ⟨37451965793372358508042841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99871908782326289354780909 37451965793372358508042841)
      ·
        refine ⟨28088974345029268881032131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37451965793372358508042841 28088974345029268881032131)
        ·
          refine ⟨42133461517543903321548197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28088974345029268881032131 42133461517543903321548197)
          ·
            refine ⟨7900024034539481872790287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42133461517543903321548197 7900024034539481872790287)
            ·
              refine ⟨11850036051809222809185431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900024034539481872790287 11850036051809222809185431)
              ·
                refine ⟨17775054077713834213778147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11850036051809222809185431 17775054077713834213778147)
                ·
                  refine ⟨26662581116570751320667221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17775054077713834213778147 26662581116570751320667221)
                  ·
                    refine ⟨312452122459813492039069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26662581116570751320667221 312452122459813492039069)
                    ·
                      rfl

theorem cell23_1825495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_1825495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825495 prefixEnd_1825495 := by exact prefixLift 1825495
  have htrace : WordTrace (prefixWord ++ tailWord_1825495) baseStart_1825495 baseEnd_1825495 := by
    simpa [prefixWord, tailWord_1825495, baseEnd_1825495] using wordTrace_append hprefix tailTrace_1825495
  have hstable : (prefixWord ++ tailWord_1825495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825495).length < 2 ^ (prefixWord ++ tailWord_1825495).sum := by decide
  have hdescent : baseEnd_1825495 < baseStart_1825495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825515 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4]
def baseStart_1825515 : Nat := 118140960795 + 1825515 * 2 ^ 59
def prefixEnd_1825515 : Nat := 4983230072969 + 3 ^ 40 * 1825515 * 2
def baseEnd_1825515 : Nat := 937366636992530397867115

theorem tailTrace_1825515 : CollatzResearch.WordTrace tailWord_1825515 prefixEnd_1825515 937366636992530397867115 := by
  unfold tailWord_1825515
  simp only [CollatzResearch.WordTrace]
  refine ⟨66582001981478402985581999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44388001320985601990387999 66582001981478402985581999)
  ·
    refine ⟨99873002972217604478372999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66582001981478402985581999 99873002972217604478372999)
    ·
      refine ⟨149809504458326406717559499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99873002972217604478372999 149809504458326406717559499)
      ·
        refine ⟨224714256687489610076339249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149809504458326406717559499 224714256687489610076339249)
        ·
          refine ⟨168535692515617207557254437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224714256687489610076339249 168535692515617207557254437)
          ·
            refine ⟨31600442346678226416985207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168535692515617207557254437 31600442346678226416985207)
            ·
              refine ⟨47400663520017339625477811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31600442346678226416985207 47400663520017339625477811)
              ·
                refine ⟨71100995280026009438216717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47400663520017339625477811 71100995280026009438216717)
                ·
                  refine ⟨26662873230009753539331269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71100995280026009438216717 26662873230009753539331269)
                  ·
                    refine ⟨4999288730626828788624613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26662873230009753539331269 4999288730626828788624613)
                    ·
                      refine ⟨937366636992530397867115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4999288730626828788624613 937366636992530397867115)
                      ·
                        rfl

theorem cell23_1825515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_1825515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825515 prefixEnd_1825515 := by exact prefixLift 1825515
  have htrace : WordTrace (prefixWord ++ tailWord_1825515) baseStart_1825515 baseEnd_1825515 := by
    simpa [prefixWord, tailWord_1825515, baseEnd_1825515] using wordTrace_append hprefix tailTrace_1825515
  have hstable : (prefixWord ++ tailWord_1825515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825515).length < 2 ^ (prefixWord ++ tailWord_1825515).sum := by decide
  have hdescent : baseEnd_1825515 < baseStart_1825515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825519 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 1, 4, 2]
def baseStart_1825519 : Nat := 118140960795 + 1825519 * 2 ^ 59
def prefixEnd_1825519 : Nat := 4983230072969 + 3 ^ 40 * 1825519 * 2
def baseEnd_1825519 : Nat := 937368690915148382217097

theorem tailTrace_1825519 : CollatzResearch.WordTrace tailWord_1825519 prefixEnd_1825519 937368690915148382217097 := by
  unfold tailWord_1825519
  simp only [CollatzResearch.WordTrace]
  refine ⟨66582147873463911668727611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44388098582309274445818407 66582147873463911668727611)
  ·
    refine ⟨99873221810195867503091417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66582147873463911668727611 99873221810195867503091417)
    ·
      refine ⟨74904916357646900627318563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99873221810195867503091417 74904916357646900627318563)
      ·
        refine ⟨112357374536470350940977845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74904916357646900627318563 112357374536470350940977845)
        ·
          refine ⟨10533503862794095400716673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112357374536470350940977845 10533503862794095400716673)
          ·
            refine ⟨7900127897095571550537505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533503862794095400716673 7900127897095571550537505)
            ·
              refine ⟨5925095922821678662903129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7900127897095571550537505 5925095922821678662903129)
              ·
                refine ⟨4443821942116258997177347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5925095922821678662903129 4443821942116258997177347)
                ·
                  refine ⟨6665732913174388495766021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443821942116258997177347 6665732913174388495766021)
                  ·
                    refine ⟨1249824921220197842956129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6665732913174388495766021 1249824921220197842956129)
                    ·
                      refine ⟨937368690915148382217097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249824921220197842956129 937368690915148382217097)
                      ·
                        rfl

theorem cell23_1825519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4, 2].length) (baseStart_1825519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825519 prefixEnd_1825519 := by exact prefixLift 1825519
  have htrace : WordTrace (prefixWord ++ tailWord_1825519) baseStart_1825519 baseEnd_1825519 := by
    simpa [prefixWord, tailWord_1825519, baseEnd_1825519] using wordTrace_append hprefix tailTrace_1825519
  have hstable : (prefixWord ++ tailWord_1825519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825519).length < 2 ^ (prefixWord ++ tailWord_1825519).sum := by decide
  have hdescent : baseEnd_1825519 < baseStart_1825519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825532 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1825532 : Nat := 118140960795 + 1825532 * 2 ^ 59
def prefixEnd_1825532 : Nat := 4983230072969 + 3 ^ 40 * 1825532 * 2
def baseEnd_1825532 : Nat := 937375366163656831354537

theorem tailTrace_1825532 : CollatzResearch.WordTrace tailWord_1825532 prefixEnd_1825532 937375366163656831354537 := by
  unfold tailWord_1825532
  simp only [CollatzResearch.WordTrace]
  refine ⟨33291311011208407444475425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44388414681611209925967233 33291311011208407444475425)
  ·
    refine ⟨24968483258406305583356569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33291311011208407444475425 24968483258406305583356569)
    ·
      refine ⟨18726362443804729187517427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24968483258406305583356569 18726362443804729187517427)
      ·
        refine ⟨28089543665707093781276141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18726362443804729187517427 28089543665707093781276141)
        ·
          refine ⟨10533578874640160167978553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28089543665707093781276141 10533578874640160167978553)
          ·
            refine ⟨7900184155980120125983915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533578874640160167978553 7900184155980120125983915)
            ·
              refine ⟨11850276233970180188975873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900184155980120125983915 11850276233970180188975873)
              ·
                refine ⟨8887707175477635141731905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11850276233970180188975873 8887707175477635141731905)
                ·
                  refine ⟨6665780381608226356298929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887707175477635141731905 6665780381608226356298929)
                  ·
                    refine ⟨4999335286206169767224197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665780381608226356298929 4999335286206169767224197)
                    ·
                      refine ⟨937375366163656831354537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4999335286206169767224197 937375366163656831354537)
                      ·
                        rfl

theorem cell23_1825532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1825532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825532 prefixEnd_1825532 := by exact prefixLift 1825532
  have htrace : WordTrace (prefixWord ++ tailWord_1825532) baseStart_1825532 baseEnd_1825532 := by
    simpa [prefixWord, tailWord_1825532, baseEnd_1825532] using wordTrace_append hprefix tailTrace_1825532
  have hstable : (prefixWord ++ tailWord_1825532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825532).length < 2 ^ (prefixWord ++ tailWord_1825532).sum := by decide
  have hdescent : baseEnd_1825532 < baseStart_1825532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825555 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 3, 7]
def baseStart_1825555 : Nat := 118140960795 + 1825555 * 2 ^ 59
def prefixEnd_1825555 : Nat := 4983230072969 + 3 ^ 40 * 1825555 * 2
def baseEnd_1825555 : Nat := 312462392072903413788977

theorem tailTrace_1825555 : CollatzResearch.WordTrace tailWord_1825555 prefixEnd_1825555 312462392072903413788977 := by
  unfold tailWord_1825555
  simp only [CollatzResearch.WordTrace]
  refine ⟨66583460901333489817038119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44388973934222326544692079 66583460901333489817038119)
  ·
    refine ⟨99875191352000234725557179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66583460901333489817038119 99875191352000234725557179)
    ·
      refine ⟨149812787028000352088335769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99875191352000234725557179 149812787028000352088335769)
      ·
        refine ⟨112359590271000264066251827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149812787028000352088335769 112359590271000264066251827)
        ·
          refine ⟨168539385406500396099377741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112359590271000264066251827 168539385406500396099377741)
          ·
            refine ⟨63202269527437648537266653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168539385406500396099377741 63202269527437648537266653)
            ·
              refine ⟨23700851072789118201474995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63202269527437648537266653 23700851072789118201474995)
              ·
                refine ⟨35551276609183677302212493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23700851072789118201474995 35551276609183677302212493)
                ·
                  refine ⟨13331728728443878988329685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35551276609183677302212493 13331728728443878988329685)
                  ·
                    refine ⟨312462392072903413788977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13331728728443878988329685 312462392072903413788977)
                    ·
                      rfl

theorem cell23_1825555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 7].length) (baseStart_1825555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825555 prefixEnd_1825555 := by exact prefixLift 1825555
  have htrace : WordTrace (prefixWord ++ tailWord_1825555) baseStart_1825555 baseEnd_1825555 := by
    simpa [prefixWord, tailWord_1825555, baseEnd_1825555] using wordTrace_append hprefix tailTrace_1825555
  have hstable : (prefixWord ++ tailWord_1825555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825555).length < 2 ^ (prefixWord ++ tailWord_1825555).sum := by decide
  have hdescent : baseEnd_1825555 < baseStart_1825555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825589 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1825589 : Nat := 118140960795 + 1825589 * 2 ^ 59
def prefixEnd_1825589 : Nat := 4983230072969 + 3 ^ 40 * 1825589 * 2
def baseEnd_1825589 : Nat := 312468211520321036113925

theorem tailTrace_1825589 : CollatzResearch.WordTrace tailWord_1825589 prefixEnd_1825589 312468211520321036113925 := by
  unfold tailWord_1825589
  simp only [CollatzResearch.WordTrace]
  refine ⟨66584700983210313623775821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44389800655473542415850547 66584700983210313623775821)
  ·
    refine ⟨24969262868703867608915933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66584700983210313623775821 24969262868703867608915933)
    ·
      refine ⟨9363473575763950353343475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24969262868703867608915933 9363473575763950353343475)
      ·
        refine ⟨14045210363645925530015213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9363473575763950353343475 14045210363645925530015213)
        ·
          refine ⟨5266953886367222073755705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14045210363645925530015213 5266953886367222073755705)
          ·
            refine ⟨3950215414775416555316779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5266953886367222073755705 3950215414775416555316779)
            ·
              refine ⟨5925323122163124832975169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950215414775416555316779 5925323122163124832975169)
              ·
                refine ⟨4443992341622343624731377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5925323122163124832975169 4443992341622343624731377)
                ·
                  refine ⟨3332994256216757718548533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4443992341622343624731377 3332994256216757718548533)
                  ·
                    refine ⟨312468211520321036113925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3332994256216757718548533 312468211520321036113925)
                    ·
                      rfl

theorem cell23_1825589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1825589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825589 prefixEnd_1825589 := by exact prefixLift 1825589
  have htrace : WordTrace (prefixWord ++ tailWord_1825589) baseStart_1825589 baseEnd_1825589 := by
    simpa [prefixWord, tailWord_1825589, baseEnd_1825589] using wordTrace_append hprefix tailTrace_1825589
  have hstable : (prefixWord ++ tailWord_1825589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825589).length < 2 ^ (prefixWord ++ tailWord_1825589).sum := by decide
  have hdescent : baseEnd_1825589 < baseStart_1825589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825604 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1825604 : Nat := 118140960795 + 1825604 * 2 ^ 59
def prefixEnd_1825604 : Nat := 4983230072969 + 3 ^ 40 * 1825604 * 2
def baseEnd_1825604 : Nat := 937412336770780549654207

theorem tailTrace_1825604 : CollatzResearch.WordTrace tailWord_1825604 prefixEnd_1825604 937412336770780549654207 := by
  unfold tailWord_1825604
  simp only [CollatzResearch.WordTrace]
  refine ⟨33292624039077985592785933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44390165385437314123714577 33292624039077985592785933)
  ·
    refine ⟨12484734014654244597294725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33292624039077985592785933 12484734014654244597294725)
    ·
      refine ⟨2340887627747670861992761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12484734014654244597294725 2340887627747670861992761)
      ·
        refine ⟨1755665720810753146494571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2340887627747670861992761 1755665720810753146494571)
        ·
          refine ⟨2633498581216129719741857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755665720810753146494571 2633498581216129719741857)
          ·
            refine ⟨1975123935912097289806393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633498581216129719741857 1975123935912097289806393)
            ·
              refine ⟨1481342951934072967354795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975123935912097289806393 1481342951934072967354795)
              ·
                refine ⟨2222014427901109451032193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481342951934072967354795 2222014427901109451032193)
                ·
                  refine ⟨1666510820925832088274145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2222014427901109451032193 1666510820925832088274145)
                  ·
                    refine ⟨1249883115694374066205609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1666510820925832088274145 1249883115694374066205609)
                    ·
                      refine ⟨937412336770780549654207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1249883115694374066205609 937412336770780549654207)
                      ·
                        rfl

theorem cell23_1825604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1825604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825604 prefixEnd_1825604 := by exact prefixLift 1825604
  have htrace : WordTrace (prefixWord ++ tailWord_1825604) baseStart_1825604 baseEnd_1825604 := by
    simpa [prefixWord, tailWord_1825604, baseEnd_1825604] using wordTrace_append hprefix tailTrace_1825604
  have hstable : (prefixWord ++ tailWord_1825604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825604).length < 2 ^ (prefixWord ++ tailWord_1825604).sum := by decide
  have hdescent : baseEnd_1825604 < baseStart_1825604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825649 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 6]
def baseStart_1825649 : Nat := 118140960795 + 1825649 * 2 ^ 59
def prefixEnd_1825649 : Nat := 4983230072969 + 3 ^ 40 * 1825649 * 2
def baseEnd_1825649 : Nat := 104159493711136985954611

theorem tailTrace_1825649 : CollatzResearch.WordTrace tailWord_1825649 prefixEnd_1825649 104159493711136985954611 := by
  unfold tailWord_1825649
  simp only [CollatzResearch.WordTrace]
  refine ⟨66586889362992943870960001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44391259575328629247306667 66586889362992943870960001)
  ·
    refine ⟨49940167022244707903220001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66586889362992943870960001 49940167022244707903220001)
    ·
      refine ⟨37455125266683530927415001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49940167022244707903220001 37455125266683530927415001)
      ·
        refine ⟨28091343950012648195561251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37455125266683530927415001 28091343950012648195561251)
        ·
          refine ⟨42137015925018972293341877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28091343950012648195561251 42137015925018972293341877)
          ·
            refine ⟨3950345242970528652500801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42137015925018972293341877 3950345242970528652500801)
            ·
              refine ⟨2962758932227896489375601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950345242970528652500801 2962758932227896489375601)
              ·
                refine ⟨2222069199170922367031701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962758932227896489375601 2222069199170922367031701)
                ·
                  refine ⟨104159493711136985954611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2222069199170922367031701 104159493711136985954611)
                  ·
                    rfl

theorem cell23_1825649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 6].length) (baseStart_1825649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825649 prefixEnd_1825649 := by exact prefixLift 1825649
  have htrace : WordTrace (prefixWord ++ tailWord_1825649) baseStart_1825649 baseEnd_1825649 := by
    simpa [prefixWord, tailWord_1825649, baseEnd_1825649] using wordTrace_append hprefix tailTrace_1825649
  have hstable : (prefixWord ++ tailWord_1825649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825649).length < 2 ^ (prefixWord ++ tailWord_1825649).sum := by decide
  have hdescent : baseEnd_1825649 < baseStart_1825649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825653 : List Nat := [1, 3, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1825653 : Nat := 118140960795 + 1825653 * 2 ^ 59
def prefixEnd_1825653 : Nat := 4983230072969 + 3 ^ 40 * 1825653 * 2
def baseEnd_1825653 : Nat := 312479165774283619313827

theorem tailTrace_1825653 : CollatzResearch.WordTrace tailWord_1825653 prefixEnd_1825653 312479165774283619313827 := by
  unfold tailWord_1825653
  simp only [CollatzResearch.WordTrace]
  refine ⟨66587035254978452554105613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44391356836652301702737075 66587035254978452554105613)
  ·
    refine ⟨24970138220616919707789605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66587035254978452554105613 24970138220616919707789605)
    ·
      refine ⟨4681900916365672445210551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24970138220616919707789605 4681900916365672445210551)
      ·
        refine ⟨7022851374548508667815827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681900916365672445210551 7022851374548508667815827)
        ·
          refine ⟨10534277061822763001723741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022851374548508667815827 10534277061822763001723741)
          ·
            refine ⟨3950353898183536125646403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10534277061822763001723741 3950353898183536125646403)
            ·
              refine ⟨5925530847275304188469605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950353898183536125646403 5925530847275304188469605)
              ·
                refine ⟨1111037033864119535338051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5925530847275304188469605 1111037033864119535338051)
                ·
                  refine ⟨1666555550796179303007077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111037033864119535338051 1666555550796179303007077)
                  ·
                    refine ⟨312479165774283619313827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1666555550796179303007077 312479165774283619313827)
                    ·
                      rfl

theorem cell23_1825653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1825653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825653 prefixEnd_1825653 := by exact prefixLift 1825653
  have htrace : WordTrace (prefixWord ++ tailWord_1825653) baseStart_1825653 baseEnd_1825653 := by
    simpa [prefixWord, tailWord_1825653, baseEnd_1825653] using wordTrace_append hprefix tailTrace_1825653
  have hstable : (prefixWord ++ tailWord_1825653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825653).length < 2 ^ (prefixWord ++ tailWord_1825653).sum := by decide
  have hdescent : baseEnd_1825653 < baseStart_1825653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825696 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 1, 5]
def baseStart_1825696 : Nat := 118140960795 + 1825696 * 2 ^ 59
def prefixEnd_1825696 : Nat := 4983230072969 + 3 ^ 40 * 1825696 * 2
def baseEnd_1825696 : Nat := 312486525663664729901261

theorem tailTrace_1825696 : CollatzResearch.WordTrace tailWord_1825696 prefixEnd_1825696 312486525663664729901261 := by
  unfold tailWord_1825696
  simp only [CollatzResearch.WordTrace]
  refine ⟨33294301796911335448960471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44392402395881780598613961 33294301796911335448960471)
  ·
    refine ⟨49941452695367003173440707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33294301796911335448960471 49941452695367003173440707)
    ·
      refine ⟨74912179043050504760161061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49941452695367003173440707 74912179043050504760161061)
      ·
        refine ⟨14046033570571969642530199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74912179043050504760161061 14046033570571969642530199)
        ·
          refine ⟨21069050355857954463795299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14046033570571969642530199 21069050355857954463795299)
          ·
            refine ⟨31603575533786931695692949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21069050355857954463795299 31603575533786931695692949)
            ·
              refine ⟨1481417603146262423235607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31603575533786931695692949 1481417603146262423235607)
              ·
                refine ⟨2222126404719393634853411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481417603146262423235607 2222126404719393634853411)
                ·
                  refine ⟨3333189607079090452280117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222126404719393634853411 3333189607079090452280117)
                  ·
                    refine ⟨312486525663664729901261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3333189607079090452280117 312486525663664729901261)
                    ·
                      rfl

theorem cell23_1825696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 5].length) (baseStart_1825696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825696 prefixEnd_1825696 := by exact prefixLift 1825696
  have htrace : WordTrace (prefixWord ++ tailWord_1825696) baseStart_1825696 baseEnd_1825696 := by
    simpa [prefixWord, tailWord_1825696, baseEnd_1825696] using wordTrace_append hprefix tailTrace_1825696
  have hstable : (prefixWord ++ tailWord_1825696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825696).length < 2 ^ (prefixWord ++ tailWord_1825696).sum := by decide
  have hdescent : baseEnd_1825696 < baseStart_1825696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825712 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_1825712 : Nat := 118140960795 + 1825712 * 2 ^ 59
def prefixEnd_1825712 : Nat := 4983230072969 + 3 ^ 40 * 1825712 * 2
def baseEnd_1825712 : Nat := 937467792681466127103709

theorem tailTrace_1825712 : CollatzResearch.WordTrace tailWord_1825712 prefixEnd_1825712 937467792681466127103709 := by
  unfold tailWord_1825712
  simp only [CollatzResearch.WordTrace]
  refine ⟨33294593580882352815251695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44392791441176470420335593 33294593580882352815251695)
  ·
    refine ⟨49941890371323529222877543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33294593580882352815251695 49941890371323529222877543)
    ·
      refine ⟨74912835556985293834316315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49941890371323529222877543 74912835556985293834316315)
      ·
        refine ⟨112369253335477940751474473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74912835556985293834316315 112369253335477940751474473)
        ·
          refine ⟨84276940001608455563605855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112369253335477940751474473 84276940001608455563605855)
          ·
            refine ⟨126415410002412683345408783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84276940001608455563605855 126415410002412683345408783)
            ·
              refine ⟨189623115003619025018113175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126415410002412683345408783 189623115003619025018113175)
              ·
                refine ⟨284434672505428537527169763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189623115003619025018113175 284434672505428537527169763)
                ·
                  refine ⟨426652008758142806290754645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284434672505428537527169763 426652008758142806290754645)
                  ·
                    refine ⟨4999828227634486011219781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 426652008758142806290754645 4999828227634486011219781)
                    ·
                      refine ⟨937467792681466127103709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4999828227634486011219781 937467792681466127103709)
                      ·
                        rfl

theorem cell23_1825712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_1825712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825712 prefixEnd_1825712 := by exact prefixLift 1825712
  have htrace : WordTrace (prefixWord ++ tailWord_1825712) baseStart_1825712 baseEnd_1825712 := by
    simpa [prefixWord, tailWord_1825712, baseEnd_1825712] using wordTrace_append hprefix tailTrace_1825712
  have hstable : (prefixWord ++ tailWord_1825712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825712).length < 2 ^ (prefixWord ++ tailWord_1825712).sum := by decide
  have hdescent : baseEnd_1825712 < baseStart_1825712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825719 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_1825719 : Nat := 118140960795 + 1825719 * 2 ^ 59
def prefixEnd_1825719 : Nat := 4983230072969 + 3 ^ 40 * 1825719 * 2
def baseEnd_1825719 : Nat := 937471387046047599716177

theorem tailTrace_1825719 : CollatzResearch.WordTrace tailWord_1825719 prefixEnd_1825719 937471387046047599716177 := by
  unfold tailWord_1825719
  simp only [CollatzResearch.WordTrace]
  refine ⟨66589442472739345826008211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44392961648492897217338807 66589442472739345826008211)
  ·
    refine ⟨99884163709109018739012317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66589442472739345826008211 99884163709109018739012317)
    ·
      refine ⟨37456561390915882027129619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99884163709109018739012317 37456561390915882027129619)
      ·
        refine ⟨56184842086373823040694429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37456561390915882027129619 56184842086373823040694429)
        ·
          refine ⟨21069315782390183640260411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56184842086373823040694429 21069315782390183640260411)
          ·
            refine ⟨31603973673585275460390617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21069315782390183640260411 31603973673585275460390617)
            ·
              refine ⟨23702980255188956595292963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31603973673585275460390617 23702980255188956595292963)
              ·
                refine ⟨35554470382783434892939445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23702980255188956595292963 35554470382783434892939445)
                ·
                  refine ⟨3333231598385947021213073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35554470382783434892939445 3333231598385947021213073)
                  ·
                    refine ⟨2499923698789460265909805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3333231598385947021213073 2499923698789460265909805)
                    ·
                      refine ⟨937471387046047599716177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2499923698789460265909805 937471387046047599716177)
                      ·
                        rfl

theorem cell23_1825719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_1825719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825719 prefixEnd_1825719 := by exact prefixLift 1825719
  have htrace : WordTrace (prefixWord ++ tailWord_1825719) baseStart_1825719 baseEnd_1825719 := by
    simpa [prefixWord, tailWord_1825719, baseEnd_1825719] using wordTrace_append hprefix tailTrace_1825719
  have hstable : (prefixWord ++ tailWord_1825719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825719).length < 2 ^ (prefixWord ++ tailWord_1825719).sum := by decide
  have hdescent : baseEnd_1825719 < baseStart_1825719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825722 : List Nat := [3, 1, 1, 1, 2, 1, 4, 10]
def baseStart_1825722 : Nat := 118140960795 + 1825722 * 2 ^ 59
def prefixEnd_1825722 : Nat := 4983230072969 + 3 ^ 40 * 1825722 * 2
def baseEnd_1825722 : Nat := 34721219536593003258469

theorem tailTrace_1825722 : CollatzResearch.WordTrace tailWord_1825722 prefixEnd_1825722 34721219536593003258469 := by
  unfold tailWord_1825722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647387972932119334591855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44393034594485651558911613 16647387972932119334591855)
  ·
    refine ⟨24971081959398179001887783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16647387972932119334591855 24971081959398179001887783)
    ·
      refine ⟨37456622939097268502831675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24971081959398179001887783 37456622939097268502831675)
      ·
        refine ⟨56184934408645902754247513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37456622939097268502831675 56184934408645902754247513)
        ·
          refine ⟨42138700806484427065685635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56184934408645902754247513 42138700806484427065685635)
          ·
            refine ⟨63208051209726640598528453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42138700806484427065685635 63208051209726640598528453)
            ·
              refine ⟨11851509601823745112224085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63208051209726640598528453 11851509601823745112224085)
              ·
                refine ⟨34721219536593003258469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11851509601823745112224085 34721219536593003258469)
                ·
                  rfl

theorem cell23_1825722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_1825722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825722 prefixEnd_1825722 := by exact prefixLift 1825722
  have htrace : WordTrace (prefixWord ++ tailWord_1825722) baseStart_1825722 baseEnd_1825722 := by
    simpa [prefixWord, tailWord_1825722, baseEnd_1825722] using wordTrace_append hprefix tailTrace_1825722
  have hstable : (prefixWord ++ tailWord_1825722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825722).length < 2 ^ (prefixWord ++ tailWord_1825722).sum := by decide
  have hdescent : baseEnd_1825722 < baseStart_1825722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825739 : List Nat := [1, 1, 1, 1, 3, 5, 4, 7]
def baseStart_1825739 : Nat := 118140960795 + 1825739 * 2 ^ 59
def prefixEnd_1825739 : Nat := 4983230072969 + 3 ^ 40 * 1825739 * 2
def baseEnd_1825739 : Nat := 34721542839227315609855

theorem tailTrace_1825739 : CollatzResearch.WordTrace tailWord_1825739 prefixEnd_1825739 34721542839227315609855 := by
  unfold tailWord_1825739
  simp only [CollatzResearch.WordTrace]
  refine ⟨66590171932666889241736271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44393447955111259494490847 66590171932666889241736271)
  ·
    refine ⟨99885257899000333862604407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66590171932666889241736271 99885257899000333862604407)
    ·
      refine ⟨149827886848500500793906611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99885257899000333862604407 149827886848500500793906611)
      ·
        refine ⟨224741830272750751190859917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149827886848500500793906611 224741830272750751190859917)
        ·
          refine ⟨84278186352281531696572469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224741830272750751190859917 84278186352281531696572469)
          ·
            refine ⟨7901079970526393596553669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84278186352281531696572469 7901079970526393596553669)
            ·
              refine ⟨1481452494473698799353813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7901079970526393596553669 1481452494473698799353813)
              ·
                refine ⟨34721542839227315609855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1481452494473698799353813 34721542839227315609855)
                ·
                  rfl

theorem cell23_1825739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 7].length) (baseStart_1825739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825739 prefixEnd_1825739 := by exact prefixLift 1825739
  have htrace : WordTrace (prefixWord ++ tailWord_1825739) baseStart_1825739 baseEnd_1825739 := by
    simpa [prefixWord, tailWord_1825739, baseEnd_1825739] using wordTrace_append hprefix tailTrace_1825739
  have hstable : (prefixWord ++ tailWord_1825739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825739).length < 2 ^ (prefixWord ++ tailWord_1825739).sum := by decide
  have hdescent : baseEnd_1825739 < baseStart_1825739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825776 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 3, 3, 2]
def baseStart_1825776 : Nat := 118140960795 + 1825776 * 2 ^ 59
def prefixEnd_1825776 : Nat := 4983230072969 + 3 ^ 40 * 1825776 * 2
def baseEnd_1825776 : Nat := 937500655443353876703415

theorem tailTrace_1825776 : CollatzResearch.WordTrace tailWord_1825776 prefixEnd_1825776 937500655443353876703415 := by
  unfold tailWord_1825776
  simp only [CollatzResearch.WordTrace]
  refine ⟨33295760716766422280416591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44394347622355229707222121 33295760716766422280416591)
  ·
    refine ⟨49943641075149633420624887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33295760716766422280416591 49943641075149633420624887)
    ·
      refine ⟨74915461612724450130937331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49943641075149633420624887 74915461612724450130937331)
      ·
        refine ⟨112373192419086675196405997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74915461612724450130937331 112373192419086675196405997)
        ·
          refine ⟨42139947157157503198652249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112373192419086675196405997 42139947157157503198652249)
          ·
            refine ⟨31604960367868127398989187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42139947157157503198652249 31604960367868127398989187)
            ·
              refine ⟨47407440551802191098483781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31604960367868127398989187 47407440551802191098483781)
              ·
                refine ⟨8888895103462910830965709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47407440551802191098483781 8888895103462910830965709)
                ·
                  refine ⟨3333335663798591561612141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8888895103462910830965709 3333335663798591561612141)
                  ·
                    refine ⟨1250000873924471835604553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333335663798591561612141 1250000873924471835604553)
                    ·
                      refine ⟨937500655443353876703415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250000873924471835604553 937500655443353876703415)
                      ·
                        rfl

theorem cell23_1825776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 3, 2].length) (baseStart_1825776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825776 prefixEnd_1825776 := by exact prefixLift 1825776
  have htrace : WordTrace (prefixWord ++ tailWord_1825776) baseStart_1825776 baseEnd_1825776 := by
    simpa [prefixWord, tailWord_1825776, baseEnd_1825776] using wordTrace_append hprefix tailTrace_1825776
  have hstable : (prefixWord ++ tailWord_1825776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825776).length < 2 ^ (prefixWord ++ tailWord_1825776).sum := by decide
  have hdescent : baseEnd_1825776 < baseStart_1825776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825793 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_1825793 : Nat := 118140960795 + 1825793 * 2 ^ 59
def prefixEnd_1825793 : Nat := 4983230072969 + 3 ^ 40 * 1825793 * 2
def baseEnd_1825793 : Nat := 937509384614480310190837

theorem tailTrace_1825793 : CollatzResearch.WordTrace tailWord_1825793 prefixEnd_1825793 937509384614480310190837 := by
  unfold tailWord_1825793
  simp only [CollatzResearch.WordTrace]
  refine ⟨66592141474471256464202033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44394760982980837642801355 66592141474471256464202033)
  ·
    refine ⟨49944106105853442348151525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66592141474471256464202033 49944106105853442348151525)
    ·
      refine ⟨9364519894847520440278411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49944106105853442348151525 9364519894847520440278411)
      ·
        refine ⟨14046779842271280660417617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364519894847520440278411 14046779842271280660417617)
        ·
          refine ⟨10535084881703460495313213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14046779842271280660417617 10535084881703460495313213)
          ·
            refine ⟨3950656830638797685742455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10535084881703460495313213 3950656830638797685742455)
            ·
              refine ⟨5925985245958196528613683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950656830638797685742455 5925985245958196528613683)
              ·
                refine ⟨8888977868937294792920525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925985245958196528613683 8888977868937294792920525)
                ·
                  refine ⟨3333366700851485547345197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8888977868937294792920525 3333366700851485547345197)
                  ·
                    refine ⟨1250012512819307080254449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333366700851485547345197 1250012512819307080254449)
                    ·
                      refine ⟨937509384614480310190837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250012512819307080254449 937509384614480310190837)
                      ·
                        rfl

theorem cell23_1825793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_1825793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825793 prefixEnd_1825793 := by exact prefixLift 1825793
  have htrace : WordTrace (prefixWord ++ tailWord_1825793) baseStart_1825793 baseEnd_1825793 := by
    simpa [prefixWord, tailWord_1825793, baseEnd_1825793] using wordTrace_append hprefix tailTrace_1825793
  have hstable : (prefixWord ++ tailWord_1825793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825793).length < 2 ^ (prefixWord ++ tailWord_1825793).sum := by decide
  have hdescent : baseEnd_1825793 < baseStart_1825793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825809 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_1825809 : Nat := 118140960795 + 1825809 * 2 ^ 59
def prefixEnd_1825809 : Nat := 4983230072969 + 3 ^ 40 * 1825809 * 2
def baseEnd_1825809 : Nat := 937517600304952247590763

theorem tailTrace_1825809 : CollatzResearch.WordTrace tailWord_1825809 prefixEnd_1825809 937517600304952247590763 := by
  unfold tailWord_1825809
  simp only [CollatzResearch.WordTrace]
  refine ⟨66592725042413291196784481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44395150028275527464522987 66592725042413291196784481)
  ·
    refine ⟨49944543781809968397588361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66592725042413291196784481 49944543781809968397588361)
    ·
      refine ⟨37458407836357476298191271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49944543781809968397588361 37458407836357476298191271)
      ·
        refine ⟨56187611754536214447286907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37458407836357476298191271 56187611754536214447286907)
        ·
          refine ⟨84281417631804321670930361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56187611754536214447286907 84281417631804321670930361)
          ·
            refine ⟨63211063223853241253197771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84281417631804321670930361 63211063223853241253197771)
            ·
              refine ⟨94816594835779861879796657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63211063223853241253197771 94816594835779861879796657)
              ·
                refine ⟨71112446126834896409847493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94816594835779861879796657 71112446126834896409847493)
                ·
                  refine ⟨13333583648781543076846405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71112446126834896409847493 13333583648781543076846405)
                  ·
                    refine ⟨2500046934146539326908701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13333583648781543076846405 2500046934146539326908701)
                    ·
                      refine ⟨937517600304952247590763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500046934146539326908701 937517600304952247590763)
                      ·
                        rfl

theorem cell23_1825809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_1825809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825809 prefixEnd_1825809 := by exact prefixLift 1825809
  have htrace : WordTrace (prefixWord ++ tailWord_1825809) baseStart_1825809 baseEnd_1825809 := by
    simpa [prefixWord, tailWord_1825809, baseEnd_1825809] using wordTrace_append hprefix tailTrace_1825809
  have hstable : (prefixWord ++ tailWord_1825809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825809).length < 2 ^ (prefixWord ++ tailWord_1825809).sum := by decide
  have hdescent : baseEnd_1825809 < baseStart_1825809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825826 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1825826 : Nat := 118140960795 + 1825826 * 2 ^ 59
def prefixEnd_1825826 : Nat := 4983230072969 + 3 ^ 40 * 1825826 * 2
def baseEnd_1825826 : Nat := 937526329476078681078185

theorem tailTrace_1825826 : CollatzResearch.WordTrace tailWord_1825826 prefixEnd_1825826 937526329476078681078185 := by
  unfold tailWord_1825826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16648336270837925775038333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44395563388901135400102221 16648336270837925775038333)
  ·
    refine ⟨6243126101564222165639375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16648336270837925775038333 6243126101564222165639375)
    ·
      refine ⟨9364689152346333248459063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6243126101564222165639375 9364689152346333248459063)
      ·
        refine ⟨14047033728519499872688595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364689152346333248459063 14047033728519499872688595)
        ·
          refine ⟨21070550592779249809032893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14047033728519499872688595 21070550592779249809032893)
          ·
            refine ⟨7901456472292218678387335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21070550592779249809032893 7901456472292218678387335)
            ·
              refine ⟨11852184708438328017581003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901456472292218678387335 11852184708438328017581003)
              ·
                refine ⟨17778277062657492026371505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11852184708438328017581003 17778277062657492026371505)
                ·
                  refine ⟨13333707796993119019778629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17778277062657492026371505 13333707796993119019778629)
                  ·
                    refine ⟨2500070211936209816208493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13333707796993119019778629 2500070211936209816208493)
                    ·
                      refine ⟨937526329476078681078185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500070211936209816208493 937526329476078681078185)
                      ·
                        rfl

theorem cell23_1825826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1825826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825826 prefixEnd_1825826 := by exact prefixLift 1825826
  have htrace : WordTrace (prefixWord ++ tailWord_1825826) baseStart_1825826 baseEnd_1825826 := by
    simpa [prefixWord, tailWord_1825826, baseEnd_1825826] using wordTrace_append hprefix tailTrace_1825826
  have hstable : (prefixWord ++ tailWord_1825826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825826).length < 2 ^ (prefixWord ++ tailWord_1825826).sum := by decide
  have hdescent : baseEnd_1825826 < baseStart_1825826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825829 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 7]
def baseStart_1825829 : Nat := 118140960795 + 1825829 * 2 ^ 59
def prefixEnd_1825829 : Nat := 4983230072969 + 3 ^ 40 * 1825829 * 2
def baseEnd_1825829 : Nat := 104169763324226907704519

theorem tailTrace_1825829 : CollatzResearch.WordTrace tailWord_1825829 prefixEnd_1825829 104169763324226907704519 := by
  unfold tailWord_1825829
  simp only [CollatzResearch.WordTrace]
  refine ⟨66593454502340834612512541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44395636334893889741675027 66593454502340834612512541)
  ·
    refine ⟨24972545438377812979692203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66593454502340834612512541 24972545438377812979692203)
    ·
      refine ⟨37458818157566719469538305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24972545438377812979692203 37458818157566719469538305)
      ·
        refine ⟨28094113618175039602153729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37458818157566719469538305 28094113618175039602153729)
        ·
          refine ⟨21070585213631279701615297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28094113618175039602153729 21070585213631279701615297)
          ·
            refine ⟨15802938910223459776211473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21070585213631279701615297 15802938910223459776211473)
            ·
              refine ⟨11852204182667594832158605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15802938910223459776211473 11852204182667594832158605)
              ·
                refine ⟨4444576568500348062059477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11852204182667594832158605 4444576568500348062059477)
                ·
                  refine ⟨104169763324226907704519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4444576568500348062059477 104169763324226907704519)
                  ·
                    rfl

theorem cell23_1825829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_1825829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825829 prefixEnd_1825829 := by exact prefixLift 1825829
  have htrace : WordTrace (prefixWord ++ tailWord_1825829) baseStart_1825829 baseEnd_1825829 := by
    simpa [prefixWord, tailWord_1825829, baseEnd_1825829] using wordTrace_append hprefix tailTrace_1825829
  have hstable : (prefixWord ++ tailWord_1825829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825829).length < 2 ^ (prefixWord ++ tailWord_1825829).sum := by decide
  have hdescent : baseEnd_1825829 < baseStart_1825829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825846 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_1825846 : Nat := 118140960795 + 1825846 * 2 ^ 59
def prefixEnd_1825846 : Nat := 4983230072969 + 3 ^ 40 * 1825846 * 2
def baseEnd_1825846 : Nat := 104170733232129844758677

theorem tailTrace_1825846 : CollatzResearch.WordTrace tailWord_1825846 prefixEnd_1825846 104170733232129844758677 := by
  unfold tailWord_1825846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162129658954952907242587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44396049695519497677254261 4162129658954952907242587)
  ·
    refine ⟨6243194488432429360863881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4162129658954952907242587 6243194488432429360863881)
    ·
      refine ⟨4682395866324322020647911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6243194488432429360863881 4682395866324322020647911)
      ·
        refine ⟨7023593799486483030971867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682395866324322020647911 7023593799486483030971867)
        ·
          refine ⟨10535390699229724546457801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023593799486483030971867 10535390699229724546457801)
          ·
            refine ⟨7901543024422293409843351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10535390699229724546457801 7901543024422293409843351)
            ·
              refine ⟨11852314536633440114765027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901543024422293409843351 11852314536633440114765027)
              ·
                refine ⟨17778471804950160172147541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11852314536633440114765027 17778471804950160172147541)
                ·
                  refine ⟨104170733232129844758677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17778471804950160172147541 104170733232129844758677)
                  ·
                    rfl

theorem cell23_1825846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_1825846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825846 prefixEnd_1825846 := by exact prefixLift 1825846
  have htrace : WordTrace (prefixWord ++ tailWord_1825846) baseStart_1825846 baseEnd_1825846 := by
    simpa [prefixWord, tailWord_1825846, baseEnd_1825846] using wordTrace_append hprefix tailTrace_1825846
  have hstable : (prefixWord ++ tailWord_1825846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825846).length < 2 ^ (prefixWord ++ tailWord_1825846).sum := by decide
  have hdescent : baseEnd_1825846 < baseStart_1825846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825859 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 1, 7]
def baseStart_1825859 : Nat := 118140960795 + 1825859 * 2 ^ 59
def prefixEnd_1825859 : Nat := 4983230072969 + 3 ^ 40 * 1825859 * 2
def baseEnd_1825859 : Nat := 312514424779225683988511

theorem tailTrace_1825859 : CollatzResearch.WordTrace tailWord_1825859 prefixEnd_1825859 312514424779225683988511 := by
  unfold tailWord_1825859
  simp only [CollatzResearch.WordTrace]
  refine ⟨66594548692232149736104631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44396365794821433157403087 66594548692232149736104631)
  ·
    refine ⟨99891823038348224604156947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66594548692232149736104631 99891823038348224604156947)
    ·
      refine ⟨149837734557522336906235421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99891823038348224604156947 149837734557522336906235421)
      ·
        refine ⟨56189150459070876339838283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149837734557522336906235421 56189150459070876339838283)
        ·
          refine ⟨84283725688606314509757425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56189150459070876339838283 84283725688606314509757425)
          ·
            refine ⟨63212794266454735882318069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84283725688606314509757425 63212794266454735882318069)
            ·
              refine ⟨5926199462480131488967319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63212794266454735882318069 5926199462480131488967319)
              ·
                refine ⟨8889299193720197233450979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926199462480131488967319 8889299193720197233450979)
                ·
                  refine ⟨13333948790580295850176469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889299193720197233450979 13333948790580295850176469)
                  ·
                    refine ⟨312514424779225683988511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13333948790580295850176469 312514424779225683988511)
                    ·
                      rfl

theorem cell23_1825859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 7].length) (baseStart_1825859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825859 prefixEnd_1825859 := by exact prefixLift 1825859
  have htrace : WordTrace (prefixWord ++ tailWord_1825859) baseStart_1825859 baseEnd_1825859 := by
    simpa [prefixWord, tailWord_1825859, baseEnd_1825859] using wordTrace_append hprefix tailTrace_1825859
  have hstable : (prefixWord ++ tailWord_1825859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825859).length < 2 ^ (prefixWord ++ tailWord_1825859).sum := by decide
  have hdescent : baseEnd_1825859 < baseStart_1825859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825863 : List Nat := [1, 1, 4, 1, 3, 3, 2, 3, 5]
def baseStart_1825863 : Nat := 118140960795 + 1825863 * 2 ^ 59
def prefixEnd_1825863 : Nat := 4983230072969 + 3 ^ 40 * 1825863 * 2
def baseEnd_1825863 : Nat := 104171703140032781812835

theorem tailTrace_1825863 : CollatzResearch.WordTrace tailWord_1825863 prefixEnd_1825863 104171703140032781812835 := by
  unfold tailWord_1825863
  simp only [CollatzResearch.WordTrace]
  refine ⟨66594694584217658419250243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44396463056145105612833495 66594694584217658419250243)
  ·
    refine ⟨99892041876326487628875365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66594694584217658419250243 99892041876326487628875365)
    ·
      refine ⟨18729757851811216430414131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99892041876326487628875365 18729757851811216430414131)
      ·
        refine ⟨28094636777716824645621197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18729757851811216430414131 28094636777716824645621197)
        ·
          refine ⟨10535488791643809242107949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28094636777716824645621197 10535488791643809242107949)
          ·
            refine ⟨3950808296866428465790481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10535488791643809242107949 3950808296866428465790481)
            ·
              refine ⟨2963106222649821349342861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950808296866428465790481 2963106222649821349342861)
              ·
                refine ⟨1111164833493683006003573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963106222649821349342861 1111164833493683006003573)
                ·
                  refine ⟨104171703140032781812835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1111164833493683006003573 104171703140032781812835)
                  ·
                    rfl

theorem cell23_1825863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 5].length) (baseStart_1825863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825863 prefixEnd_1825863 := by exact prefixLift 1825863
  have htrace : WordTrace (prefixWord ++ tailWord_1825863) baseStart_1825863 baseEnd_1825863 := by
    simpa [prefixWord, tailWord_1825863, baseEnd_1825863] using wordTrace_append hprefix tailTrace_1825863
  have hstable : (prefixWord ++ tailWord_1825863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825863).length < 2 ^ (prefixWord ++ tailWord_1825863).sum := by decide
  have hdescent : baseEnd_1825863 < baseStart_1825863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825876 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1825876 : Nat := 118140960795 + 1825876 * 2 ^ 59
def prefixEnd_1825876 : Nat := 4983230072969 + 3 ^ 40 * 1825876 * 2
def baseEnd_1825876 : Nat := 312517334502934495150985

theorem tailTrace_1825876 : CollatzResearch.WordTrace tailWord_1825876 prefixEnd_1825876 312517334502934495150985 := by
  unfold tailWord_1825876
  simp only [CollatzResearch.WordTrace]
  refine ⟨33297584366585280819736741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44396779155447041092982321 33297584366585280819736741)
  ·
    refine ⟨6243297068734740153700639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33297584366585280819736741 6243297068734740153700639)
    ·
      refine ⟨9364945603102110230550959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6243297068734740153700639 9364945603102110230550959)
      ·
        refine ⟨14047418404653165345826439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364945603102110230550959 14047418404653165345826439)
        ·
          refine ⟨21071127606979748018739659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14047418404653165345826439 21071127606979748018739659)
          ·
            refine ⟨31606691410469622028109489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21071127606979748018739659 31606691410469622028109489)
            ·
              refine ⟨23705018557852216521082117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31606691410469622028109489 23705018557852216521082117)
              ·
                refine ⟨4444690979597290597702897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23705018557852216521082117 4444690979597290597702897)
                ·
                  refine ⟨3333518234697967948277173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444690979597290597702897 3333518234697967948277173)
                  ·
                    refine ⟨312517334502934495150985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3333518234697967948277173 312517334502934495150985)
                    ·
                      rfl

theorem cell23_1825876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1825876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825876 prefixEnd_1825876 := by exact prefixLift 1825876
  have htrace : WordTrace (prefixWord ++ tailWord_1825876) baseStart_1825876 baseEnd_1825876 := by
    simpa [prefixWord, tailWord_1825876, baseEnd_1825876] using wordTrace_append hprefix tailTrace_1825876
  have hstable : (prefixWord ++ tailWord_1825876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825876).length < 2 ^ (prefixWord ++ tailWord_1825876).sum := by decide
  have hdescent : baseEnd_1825876 < baseStart_1825876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825916 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_1825916 : Nat := 118140960795 + 1825916 * 2 ^ 59
def prefixEnd_1825916 : Nat := 4983230072969 + 3 ^ 40 * 1825916 * 2
def baseEnd_1825916 : Nat := 937572542734983328952771

theorem tailTrace_1825916 : CollatzResearch.WordTrace tailWord_1825916 prefixEnd_1825916 937572542734983328952771 := by
  unfold tailWord_1825916
  simp only [CollatzResearch.WordTrace]
  refine ⟨33298313826512824235464801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44397751768683765647286401 33298313826512824235464801)
  ·
    refine ⟨24973735369884618176598601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33298313826512824235464801 24973735369884618176598601)
    ·
      refine ⟨18730301527413463632448951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24973735369884618176598601 18730301527413463632448951)
      ·
        refine ⟨28095452291120195448673427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18730301527413463632448951 28095452291120195448673427)
        ·
          refine ⟨42143178436680293173010141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28095452291120195448673427 42143178436680293173010141)
          ·
            refine ⟨15803691913755109939878803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42143178436680293173010141 15803691913755109939878803)
            ·
              refine ⟨23705537870632664909818205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15803691913755109939878803 23705537870632664909818205)
              ·
                refine ⟨8889576701487249341181827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23705537870632664909818205 8889576701487249341181827)
                ·
                  refine ⟨13334365052230874011772741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889576701487249341181827 13334365052230874011772741)
                  ·
                    refine ⟨2500193447293288877207389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13334365052230874011772741 2500193447293288877207389)
                    ·
                      refine ⟨937572542734983328952771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500193447293288877207389 937572542734983328952771)
                      ·
                        rfl

theorem cell23_1825916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_1825916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825916 prefixEnd_1825916 := by exact prefixLift 1825916
  have htrace : WordTrace (prefixWord ++ tailWord_1825916) baseStart_1825916 baseEnd_1825916 := by
    simpa [prefixWord, tailWord_1825916, baseEnd_1825916] using wordTrace_append hprefix tailTrace_1825916
  have hstable : (prefixWord ++ tailWord_1825916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825916).length < 2 ^ (prefixWord ++ tailWord_1825916).sum := by decide
  have hdescent : baseEnd_1825916 < baseStart_1825916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825939 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8]
def baseStart_1825939 : Nat := 118140960795 + 1825939 * 2 ^ 59
def prefixEnd_1825939 : Nat := 4983230072969 + 3 ^ 40 * 1825939 * 2
def baseEnd_1825939 : Nat := 937584352790036738965165

theorem tailTrace_1825939 : CollatzResearch.WordTrace tailWord_1825939 prefixEnd_1825939 937584352790036738965165 := by
  unfold tailWord_1825939
  simp only [CollatzResearch.WordTrace]
  refine ⟨66597466531942323399016871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44398311021294882266011247 66597466531942323399016871)
  ·
    refine ⟨99896199797913485098525307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66597466531942323399016871 99896199797913485098525307)
    ·
      refine ⟨149844299696870227647787961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99896199797913485098525307 149844299696870227647787961)
      ·
        refine ⟨112383224772652670735840971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149844299696870227647787961 112383224772652670735840971)
        ·
          refine ⟨168574837158979006103761457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112383224772652670735840971 168574837158979006103761457)
          ·
            refine ⟨126431127869234254577821093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168574837158979006103761457 126431127869234254577821093)
            ·
              refine ⟨23705836475481422733341455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126431127869234254577821093 23705836475481422733341455)
              ·
                refine ⟨35558754713222134100012183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23705836475481422733341455 35558754713222134100012183)
                ·
                  refine ⟨53338132069833201150018275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35558754713222134100012183 53338132069833201150018275)
                  ·
                    refine ⟨80007198104749801725027413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53338132069833201150018275 80007198104749801725027413)
                    ·
                      refine ⟨937584352790036738965165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 80007198104749801725027413 937584352790036738965165)
                      ·
                        rfl

theorem cell23_1825939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_1825939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1825939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1825939 prefixEnd_1825939 := by exact prefixLift 1825939
  have htrace : WordTrace (prefixWord ++ tailWord_1825939) baseStart_1825939 baseEnd_1825939 := by
    simpa [prefixWord, tailWord_1825939, baseEnd_1825939] using wordTrace_append hprefix tailTrace_1825939
  have hstable : (prefixWord ++ tailWord_1825939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825939).length < 2 ^ (prefixWord ++ tailWord_1825939).sum := by decide
  have hdescent : baseEnd_1825939 < baseStart_1825939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826020 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_1826020 : Nat := 118140960795 + 1826020 * 2 ^ 59
def prefixEnd_1826020 : Nat := 4983230072969 + 3 ^ 40 * 1826020 * 2
def baseEnd_1826020 : Nat := 937625944723050922052293

theorem tailTrace_1826020 : CollatzResearch.WordTrace tailWord_1826020 prefixEnd_1826020 937625944723050922052293 := by
  unfold tailWord_1826020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33300210422324437116357757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44400280563099249488477009 33300210422324437116357757)
  ·
    refine ⟨12487578908371663918634159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33300210422324437116357757 12487578908371663918634159)
    ·
      refine ⟨18731368362557495877951239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12487578908371663918634159 18731368362557495877951239)
      ·
        refine ⟨28097052543836243816926859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18731368362557495877951239 28097052543836243816926859)
        ·
          refine ⟨42145578815754365725390289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28097052543836243816926859 42145578815754365725390289)
          ·
            refine ⟨31609184111815774294042717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42145578815754365725390289 31609184111815774294042717)
            ·
              refine ⟨11853444041930915360266019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31609184111815774294042717 11853444041930915360266019)
              ·
                refine ⟨17780166062896373040399029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11853444041930915360266019 17780166062896373040399029)
                ·
                  refine ⟨1666890568396534972537409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17780166062896373040399029 1666890568396534972537409)
                  ·
                    refine ⟨1250167926297401229403057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1666890568396534972537409 1250167926297401229403057)
                    ·
                      refine ⟨937625944723050922052293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250167926297401229403057 937625944723050922052293)
                      ·
                        rfl

theorem cell23_1826020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_1826020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826020 prefixEnd_1826020 := by exact prefixLift 1826020
  have htrace : WordTrace (prefixWord ++ tailWord_1826020) baseStart_1826020 baseEnd_1826020 := by
    simpa [prefixWord, tailWord_1826020, baseEnd_1826020] using wordTrace_append hprefix tailTrace_1826020
  have hstable : (prefixWord ++ tailWord_1826020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826020).length < 2 ^ (prefixWord ++ tailWord_1826020).sum := by decide
  have hdescent : baseEnd_1826020 < baseStart_1826020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826034 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_1826034 : Nat := 118140960795 + 1826034 * 2 ^ 59
def prefixEnd_1826034 : Nat := 4983230072969 + 3 ^ 40 * 1826034 * 2
def baseEnd_1826034 : Nat := 312544377817404622425743

theorem tailTrace_1826034 : CollatzResearch.WordTrace tailWord_1826034 prefixEnd_1826034 312544377817404622425743 := by
  unfold tailWord_1826034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16650232866649538655931289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44400620977732103082483437 16650232866649538655931289)
  ·
    refine ⟨12487674649987153991948467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16650232866649538655931289 12487674649987153991948467)
    ·
      refine ⟨18731511974980730987922701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12487674649987153991948467 18731511974980730987922701)
      ·
        refine ⟨7024316990617774120471013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18731511974980730987922701 7024316990617774120471013)
        ·
          refine ⟨1317059435740832647588315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7024316990617774120471013 1317059435740832647588315)
          ·
            refine ⟨1975589153611248971382473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317059435740832647588315 1975589153611248971382473)
            ·
              refine ⟨1481691865208436728536855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975589153611248971382473 1481691865208436728536855)
              ·
                refine ⟨2222537797812655092805283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481691865208436728536855 2222537797812655092805283)
                ·
                  refine ⟨3333806696718982639207925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222537797812655092805283 3333806696718982639207925)
                  ·
                    refine ⟨312544377817404622425743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3333806696718982639207925 312544377817404622425743)
                    ·
                      rfl

theorem cell23_1826034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_1826034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826034 prefixEnd_1826034 := by exact prefixLift 1826034
  have htrace : WordTrace (prefixWord ++ tailWord_1826034) baseStart_1826034 baseEnd_1826034 := by
    simpa [prefixWord, tailWord_1826034, baseEnd_1826034] using wordTrace_append hprefix tailTrace_1826034
  have hstable : (prefixWord ++ tailWord_1826034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826034).length < 2 ^ (prefixWord ++ tailWord_1826034).sum := by decide
  have hdescent : baseEnd_1826034 < baseStart_1826034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826097 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 1, 3, 2]
def baseStart_1826097 : Nat := 118140960795 + 1826097 * 2 ^ 59
def prefixEnd_1826097 : Nat := 4983230072969 + 3 ^ 40 * 1826097 * 2
def baseEnd_1826097 : Nat := 937665482733447120789439

theorem tailTrace_1826097 : CollatzResearch.WordTrace tailWord_1826097 prefixEnd_1826097 937665482733447120789439 := by
  unfold tailWord_1826097
  simp only [CollatzResearch.WordTrace]
  refine ⟨66603229265369916383268545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44402152843579944255512363 66603229265369916383268545)
  ·
    refine ⟨49952421949027437287451409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66603229265369916383268545 49952421949027437287451409)
    ·
      refine ⟨37464316461770577965588557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49952421949027437287451409 37464316461770577965588557)
      ·
        refine ⟨14049118673163966737095709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37464316461770577965588557 14049118673163966737095709)
        ·
          refine ⟨5268419502436487526410891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14049118673163966737095709 5268419502436487526410891)
          ·
            refine ⟨7902629253654731289616337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268419502436487526410891 7902629253654731289616337)
            ·
              refine ⟨5926971940241048467212253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7902629253654731289616337 5926971940241048467212253)
              ·
                refine ⟨2222614477590393175204595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5926971940241048467212253 2222614477590393175204595)
                ·
                  refine ⟨3333921716385589762806893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222614477590393175204595 3333921716385589762806893)
                  ·
                    refine ⟨1250220643644596161052585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3333921716385589762806893 1250220643644596161052585)
                    ·
                      refine ⟨937665482733447120789439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250220643644596161052585 937665482733447120789439)
                      ·
                        rfl

theorem cell23_1826097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_1826097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826097 prefixEnd_1826097 := by exact prefixLift 1826097
  have htrace : WordTrace (prefixWord ++ tailWord_1826097) baseStart_1826097 baseEnd_1826097 := by
    simpa [prefixWord, tailWord_1826097, baseEnd_1826097] using wordTrace_append hprefix tailTrace_1826097
  have hstable : (prefixWord ++ tailWord_1826097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826097).length < 2 ^ (prefixWord ++ tailWord_1826097).sum := by decide
  have hdescent : baseEnd_1826097 < baseStart_1826097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826143 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 3]
def baseStart_1826143 : Nat := 118140960795 + 1826143 * 2 ^ 59
def prefixEnd_1826143 : Nat := 4983230072969 + 3 ^ 40 * 1826143 * 2
def baseEnd_1826143 : Nat := 937689102843553940814227

theorem tailTrace_1826143 : CollatzResearch.WordTrace tailWord_1826143 prefixEnd_1826143 937689102843553940814227 := by
  unfold tailWord_1826143
  simp only [CollatzResearch.WordTrace]
  refine ⟨66604907023203266239443083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44403271348802177492962055 66604907023203266239443083)
  ·
    refine ⟨99907360534804899359164625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66604907023203266239443083 99907360534804899359164625)
    ·
      refine ⟨74930520401103674519373469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99907360534804899359164625 74930520401103674519373469)
      ·
        refine ⟨28098945150413877944765051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74930520401103674519373469 28098945150413877944765051)
        ·
          refine ⟨42148417725620816917147577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28098945150413877944765051 42148417725620816917147577)
          ·
            refine ⟨31611313294215612687860683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42148417725620816917147577 31611313294215612687860683)
            ·
              refine ⟨47416969941323419031791025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31611313294215612687860683 47416969941323419031791025)
              ·
                refine ⟨35562727455992564273843269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47416969941323419031791025 35562727455992564273843269)
                ·
                  refine ⟨6668011397998605801345613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35562727455992564273843269 6668011397998605801345613)
                  ·
                    refine ⟨2500504274249477175504605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6668011397998605801345613 2500504274249477175504605)
                    ·
                      refine ⟨937689102843553940814227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500504274249477175504605 937689102843553940814227)
                      ·
                        rfl

theorem cell23_1826143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_1826143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826143 prefixEnd_1826143 := by exact prefixLift 1826143
  have htrace : WordTrace (prefixWord ++ tailWord_1826143) baseStart_1826143 baseEnd_1826143 := by
    simpa [prefixWord, tailWord_1826143, baseEnd_1826143] using wordTrace_append hprefix tailTrace_1826143
  have hstable : (prefixWord ++ tailWord_1826143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826143).length < 2 ^ (prefixWord ++ tailWord_1826143).sum := by decide
  have hdescent : baseEnd_1826143 < baseStart_1826143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826173 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1826173 : Nat := 118140960795 + 1826173 * 2 ^ 59
def prefixEnd_1826173 : Nat := 4983230072969 + 3 ^ 40 * 1826173 * 2
def baseEnd_1826173 : Nat := 937704507263188823439089

theorem tailTrace_1826173 : CollatzResearch.WordTrace tailWord_1826173 prefixEnd_1826173 937704507263188823439089 := by
  unfold tailWord_1826173
  simp only [CollatzResearch.WordTrace]
  refine ⟨66606001213094581363035173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44404000808729720908690115 66606001213094581363035173)
  ·
    refine ⟨12488625227455234005569095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66606001213094581363035173 12488625227455234005569095)
    ·
      refine ⟨18732937841182851008353643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12488625227455234005569095 18732937841182851008353643)
      ·
        refine ⟨28099406761774276512530465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18732937841182851008353643 28099406761774276512530465)
        ·
          refine ⟨21074555071330707384397849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28099406761774276512530465 21074555071330707384397849)
          ·
            refine ⟨15805916303498030538298387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21074555071330707384397849 15805916303498030538298387)
            ·
              refine ⟨23708874455247045807447581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15805916303498030538298387 23708874455247045807447581)
              ·
                refine ⟨8890827920717642177792843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23708874455247045807447581 8890827920717642177792843)
                ·
                  refine ⟨13336241881076463266689265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8890827920717642177792843 13336241881076463266689265)
                  ·
                    refine ⟨10002181410807347450016949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13336241881076463266689265 10002181410807347450016949)
                    ·
                      refine ⟨937704507263188823439089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10002181410807347450016949 937704507263188823439089)
                      ·
                        rfl

theorem cell23_1826173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1826173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826173 prefixEnd_1826173 := by exact prefixLift 1826173
  have htrace : WordTrace (prefixWord ++ tailWord_1826173) baseStart_1826173 baseEnd_1826173 := by
    simpa [prefixWord, tailWord_1826173, baseEnd_1826173] using wordTrace_append hprefix tailTrace_1826173
  have hstable : (prefixWord ++ tailWord_1826173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826173).length < 2 ^ (prefixWord ++ tailWord_1826173).sum := by decide
  have hdescent : baseEnd_1826173 < baseStart_1826173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826174 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1826174 : Nat := 118140960795 + 1826174 * 2 ^ 59
def prefixEnd_1826174 : Nat := 4983230072969 + 3 ^ 40 * 1826174 * 2
def baseEnd_1826174 : Nat := 937705020743843319526585

theorem tailTrace_1826174 : CollatzResearch.WordTrace tailWord_1826174 prefixEnd_1826174 937705020743843319526585 := by
  unfold tailWord_1826174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325754710761369816727697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44404025124060639022547717 8325754710761369816727697)
  ·
    refine ⟨6244316033071027362545773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8325754710761369816727697 6244316033071027362545773)
    ·
      refine ⟨2341618512401635260954665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6244316033071027362545773 2341618512401635260954665)
      ·
        refine ⟨1756213884301226445715999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2341618512401635260954665 1756213884301226445715999)
        ·
          refine ⟨2634320826451839668573999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1756213884301226445715999 2634320826451839668573999)
          ·
            refine ⟨3951481239677759502860999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634320826451839668573999 3951481239677759502860999)
            ·
              refine ⟨5927221859516639254291499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951481239677759502860999 5927221859516639254291499)
              ·
                refine ⟨8890832789274958881437249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927221859516639254291499 8890832789274958881437249)
                ·
                  refine ⟨6668124591956219161077937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8890832789274958881437249 6668124591956219161077937)
                  ·
                    refine ⟨5001093443967164370808453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6668124591956219161077937 5001093443967164370808453)
                    ·
                      refine ⟨937705020743843319526585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5001093443967164370808453 937705020743843319526585)
                      ·
                        rfl

theorem cell23_1826174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1826174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826174 prefixEnd_1826174 := by exact prefixLift 1826174
  have htrace : WordTrace (prefixWord ++ tailWord_1826174) baseStart_1826174 baseEnd_1826174 := by
    simpa [prefixWord, tailWord_1826174, baseEnd_1826174] using wordTrace_append hprefix tailTrace_1826174
  have hstable : (prefixWord ++ tailWord_1826174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826174).length < 2 ^ (prefixWord ++ tailWord_1826174).sum := by decide
  have hdescent : baseEnd_1826174 < baseStart_1826174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826177 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1826177 : Nat := 118140960795 + 1826177 * 2 ^ 59
def prefixEnd_1826177 : Nat := 4983230072969 + 3 ^ 40 * 1826177 * 2
def baseEnd_1826177 : Nat := 937706561185806807789071

theorem tailTrace_1826177 : CollatzResearch.WordTrace tailWord_1826177 prefixEnd_1826177 937706561185806807789071 := by
  unfold tailWord_1826177
  simp only [CollatzResearch.WordTrace]
  refine ⟨66606147105080090046180785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44404098070053393364120523 66606147105080090046180785)
  ·
    refine ⟨49954610328810067534635589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66606147105080090046180785 49954610328810067534635589)
    ·
      refine ⟨9366489436651887662744173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49954610328810067534635589 9366489436651887662744173)
      ·
        refine ⟨3512433538744457873529065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9366489436651887662744173 3512433538744457873529065)
        ·
          refine ⟨2634325154058343405146799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512433538744457873529065 2634325154058343405146799)
          ·
            refine ⟨3951487731087515107720199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634325154058343405146799 3951487731087515107720199)
            ·
              refine ⟨5927231596631272661580299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951487731087515107720199 5927231596631272661580299)
              ·
                refine ⟨8890847394946908992370449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927231596631272661580299 8890847394946908992370449)
                ·
                  refine ⟨6668135546210181744277837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8890847394946908992370449 6668135546210181744277837)
                  ·
                    refine ⟨2500550829828818154104189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6668135546210181744277837 2500550829828818154104189)
                    ·
                      refine ⟨937706561185806807789071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500550829828818154104189 937706561185806807789071)
                      ·
                        rfl

theorem cell23_1826177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1826177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826177 prefixEnd_1826177 := by exact prefixLift 1826177
  have htrace : WordTrace (prefixWord ++ tailWord_1826177) baseStart_1826177 baseEnd_1826177 := by
    simpa [prefixWord, tailWord_1826177, baseEnd_1826177] using wordTrace_append hprefix tailTrace_1826177
  have hstable : (prefixWord ++ tailWord_1826177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826177).length < 2 ^ (prefixWord ++ tailWord_1826177).sum := by decide
  have hdescent : baseEnd_1826177 < baseStart_1826177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826203 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 3]
def baseStart_1826203 : Nat := 118140960795 + 1826203 * 2 ^ 59
def prefixEnd_1826203 : Nat := 4983230072969 + 3 ^ 40 * 1826203 * 2
def baseEnd_1826203 : Nat := 937719911682823706063951

theorem tailTrace_1826203 : CollatzResearch.WordTrace tailWord_1826203 prefixEnd_1826203 937719911682823706063951 := by
  unfold tailWord_1826203
  simp only [CollatzResearch.WordTrace]
  refine ⟨66607095402985896486627263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44404730268657264324418175 66607095402985896486627263)
  ·
    refine ⟨99910643104478844729940895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66607095402985896486627263 99910643104478844729940895)
    ·
      refine ⟨149865964656718267094911343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99910643104478844729940895 149865964656718267094911343)
      ·
        refine ⟨224798946985077400642367015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149865964656718267094911343 224798946985077400642367015)
        ·
          refine ⟨337198420477616100963550523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224798946985077400642367015 337198420477616100963550523)
          ·
            refine ⟨505797630716424151445325785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337198420477616100963550523 505797630716424151445325785)
            ·
              refine ⟨379348223037318113583994339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505797630716424151445325785 379348223037318113583994339)
              ·
                refine ⟨569022334555977170375991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379348223037318113583994339 569022334555977170375991509)
                ·
                  refine ⟨13336460966155714930687301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 569022334555977170375991509 13336460966155714930687301)
                  ·
                    refine ⟨2500586431154196549503869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13336460966155714930687301 2500586431154196549503869)
                    ·
                      refine ⟨937719911682823706063951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500586431154196549503869 937719911682823706063951)
                      ·
                        rfl

theorem cell23_1826203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 3].length) (baseStart_1826203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826203 prefixEnd_1826203 := by exact prefixLift 1826203
  have htrace : WordTrace (prefixWord ++ tailWord_1826203) baseStart_1826203 baseEnd_1826203 := by
    simpa [prefixWord, tailWord_1826203, baseEnd_1826203] using wordTrace_append hprefix tailTrace_1826203
  have hstable : (prefixWord ++ tailWord_1826203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826203).length < 2 ^ (prefixWord ++ tailWord_1826203).sum := by decide
  have hdescent : baseEnd_1826203 < baseStart_1826203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826220 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_1826220 : Nat := 118140960795 + 1826220 * 2 ^ 59
def prefixEnd_1826220 : Nat := 4983230072969 + 3 ^ 40 * 1826220 * 2
def baseEnd_1826220 : Nat := 937728640853950139551373

theorem tailTrace_1826220 : CollatzResearch.WordTrace tailWord_1826220 prefixEnd_1826220 937728640853950139551373 := by
  unfold tailWord_1826220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33303857721962154194998057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44405143629282872259997409 33303857721962154194998057)
  ·
    refine ⟨24977893291471615646248543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33303857721962154194998057 24977893291471615646248543)
    ·
      refine ⟨37466839937207423469372815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24977893291471615646248543 37466839937207423469372815)
      ·
        refine ⟨56200259905811135204059223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37466839937207423469372815 56200259905811135204059223)
        ·
          refine ⟨84300389858716702806088835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56200259905811135204059223 84300389858716702806088835)
          ·
            refine ⟨126450584788075054209133253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84300389858716702806088835 126450584788075054209133253)
            ·
              refine ⟨23709484647764072664212485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126450584788075054209133253 23709484647764072664212485)
              ·
                refine ⟨4445528371455763624539841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23709484647764072664212485 4445528371455763624539841)
                ·
                  refine ⟨3334146278591822718404881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4445528371455763624539841 3334146278591822718404881)
                  ·
                    refine ⟨2500609708943867038803661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3334146278591822718404881 2500609708943867038803661)
                    ·
                      refine ⟨937728640853950139551373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500609708943867038803661 937728640853950139551373)
                      ·
                        rfl

theorem cell23_1826220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_1826220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826220 prefixEnd_1826220 := by exact prefixLift 1826220
  have htrace : WordTrace (prefixWord ++ tailWord_1826220) baseStart_1826220 baseEnd_1826220 := by
    simpa [prefixWord, tailWord_1826220, baseEnd_1826220] using wordTrace_append hprefix tailTrace_1826220
  have hstable : (prefixWord ++ tailWord_1826220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826220).length < 2 ^ (prefixWord ++ tailWord_1826220).sum := by decide
  have hdescent : baseEnd_1826220 < baseStart_1826220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826283 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 5, 6]
def baseStart_1826283 : Nat := 118140960795 + 1826283 * 2 ^ 59
def prefixEnd_1826283 : Nat := 4983230072969 + 3 ^ 40 * 1826283 * 2
def baseEnd_1826283 : Nat := 312586996711727797687861

theorem tailTrace_1826283 : CollatzResearch.WordTrace tailWord_1826283 prefixEnd_1826283 312586996711727797687861 := by
  unfold tailWord_1826283
  simp only [CollatzResearch.WordTrace]
  refine ⟨66610013242696070149539503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44406675495130713433026335 66610013242696070149539503)
  ·
    refine ⟨99915019864044105224309255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66610013242696070149539503 99915019864044105224309255)
    ·
      refine ⟨149872529796066157836463883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99915019864044105224309255 149872529796066157836463883)
      ·
        refine ⟨224808794694099236754695825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149872529796066157836463883 224808794694099236754695825)
        ·
          refine ⟨168606596020574427566021869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224808794694099236754695825 168606596020574427566021869)
          ·
            refine ⟨63227473507715410337258201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168606596020574427566021869 63227473507715410337258201)
            ·
              refine ⟨47420605130786557752943651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63227473507715410337258201 47420605130786557752943651)
              ·
                refine ⟨71130907696179836629415477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47420605130786557752943651 71130907696179836629415477)
                ·
                  refine ⟨6668522596516859684007701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71130907696179836629415477 6668522596516859684007701)
                  ·
                    refine ⟨312586996711727797687861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6668522596516859684007701 312586996711727797687861)
                    ·
                      rfl

theorem cell23_1826283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 6].length) (baseStart_1826283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826283 prefixEnd_1826283 := by exact prefixLift 1826283
  have htrace : WordTrace (prefixWord ++ tailWord_1826283) baseStart_1826283 baseEnd_1826283 := by
    simpa [prefixWord, tailWord_1826283, baseEnd_1826283] using wordTrace_append hprefix tailTrace_1826283
  have hstable : (prefixWord ++ tailWord_1826283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826283).length < 2 ^ (prefixWord ++ tailWord_1826283).sum := by decide
  have hdescent : baseEnd_1826283 < baseStart_1826283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826313 : List Nat := [1, 2, 1, 1, 3, 1, 3, 11]
def baseStart_1826313 : Nat := 118140960795 + 1826313 * 2 ^ 59
def prefixEnd_1826313 : Nat := 4983230072969 + 3 ^ 40 * 1826313 * 2
def baseEnd_1826313 : Nat := 34732459057585862062535

theorem tailTrace_1826313 : CollatzResearch.WordTrace tailWord_1826313 prefixEnd_1826313 34732459057585862062535 := by
  unfold tailWord_1826313
  simp only [CollatzResearch.WordTrace]
  refine ⟨66611107432587385273131593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44407404955058256848754395 66611107432587385273131593)
  ·
    refine ⟨49958330574440538954848695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66611107432587385273131593 49958330574440538954848695)
    ·
      refine ⟨74937495861660808432273043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49958330574440538954848695 74937495861660808432273043)
      ·
        refine ⟨112406243792491212648409565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74937495861660808432273043 112406243792491212648409565)
        ·
          refine ⟨42152341422184204743153587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112406243792491212648409565 42152341422184204743153587)
          ·
            refine ⟨63228512133276307114730381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42152341422184204743153587 63228512133276307114730381)
            ·
              refine ⟨23710692049978615168023893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63228512133276307114730381 23710692049978615168023893)
              ·
                refine ⟨34732459057585862062535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 23710692049978615168023893 34732459057585862062535)
                ·
                  rfl

theorem cell23_1826313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 11].length) (baseStart_1826313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826313 prefixEnd_1826313 := by exact prefixLift 1826313
  have htrace : WordTrace (prefixWord ++ tailWord_1826313) baseStart_1826313 baseEnd_1826313 := by
    simpa [prefixWord, tailWord_1826313, baseEnd_1826313] using wordTrace_append hprefix tailTrace_1826313
  have hstable : (prefixWord ++ tailWord_1826313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826313).length < 2 ^ (prefixWord ++ tailWord_1826313).sum := by decide
  have hdescent : baseEnd_1826313 < baseStart_1826313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826357 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1826357 : Nat := 118140960795 + 1826357 * 2 ^ 59
def prefixEnd_1826357 : Nat := 4983230072969 + 3 ^ 40 * 1826357 * 2
def baseEnd_1826357 : Nat := 937798987703616103538243

theorem tailTrace_1826357 : CollatzResearch.WordTrace tailWord_1826357 prefixEnd_1826357 937798987703616103538243 := by
  unfold tailWord_1826357
  simp only [CollatzResearch.WordTrace]
  refine ⟨66612712244427980787733325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44408474829618653858488883 66612712244427980787733325)
  ·
    refine ⟨24979767091660492795399997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66612712244427980787733325 24979767091660492795399997)
    ·
      refine ⟨9367412659372684798274999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24979767091660492795399997 9367412659372684798274999)
      ·
        refine ⟨14051118989059027197412499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9367412659372684798274999 14051118989059027197412499)
        ·
          refine ⟨21076678483588540796118749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14051118989059027197412499 21076678483588540796118749)
          ·
            refine ⟨7903754431345702798544531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21076678483588540796118749 7903754431345702798544531)
            ·
              refine ⟨11855631647018554197816797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903754431345702798544531 11855631647018554197816797)
              ·
                refine ⟨4445861867631957824181299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11855631647018554197816797 4445861867631957824181299)
                ·
                  refine ⟨6668792801447936736271949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445861867631957824181299 6668792801447936736271949)
                  ·
                    refine ⟨2500797300542976276101981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6668792801447936736271949 2500797300542976276101981)
                    ·
                      refine ⟨937798987703616103538243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500797300542976276101981 937798987703616103538243)
                      ·
                        rfl

theorem cell23_1826357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1826357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826357 prefixEnd_1826357 := by exact prefixLift 1826357
  have htrace : WordTrace (prefixWord ++ tailWord_1826357) baseStart_1826357 baseEnd_1826357 := by
    simpa [prefixWord, tailWord_1826357, baseEnd_1826357] using wordTrace_append hprefix tailTrace_1826357
  have hstable : (prefixWord ++ tailWord_1826357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826357).length < 2 ^ (prefixWord ++ tailWord_1826357).sum := by decide
  have hdescent : baseEnd_1826357 < baseStart_1826357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826358 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_1826358 : Nat := 118140960795 + 1826358 * 2 ^ 59
def prefixEnd_1826358 : Nat := 4983230072969 + 3 ^ 40 * 1826358 * 2
def baseEnd_1826358 : Nat := 937799501184270599625739

theorem tailTrace_1826358 : CollatzResearch.WordTrace tailWord_1826358 prefixEnd_1826358 937799501184270599625739 := by
  unfold tailWord_1826358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4163296794839022372407483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44408499144949571972346485 4163296794839022372407483)
  ·
    refine ⟨6244945192258533558611225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4163296794839022372407483 6244945192258533558611225)
    ·
      refine ⟨4683708894193900168958419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6244945192258533558611225 4683708894193900168958419)
      ·
        refine ⟨7025563341290850253437629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683708894193900168958419 7025563341290850253437629)
        ·
          refine ⟨2634586252984068845039111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7025563341290850253437629 2634586252984068845039111)
          ·
            refine ⟨3951879379476103267558667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634586252984068845039111 3951879379476103267558667)
            ·
              refine ⟨5927819069214154901338001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951879379476103267558667 5927819069214154901338001)
              ·
                refine ⟨4445864301910616176003501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5927819069214154901338001 4445864301910616176003501)
                ·
                  refine ⟨1667199113216481066001313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4445864301910616176003501 1667199113216481066001313)
                  ·
                    refine ⟨1250399334912360799500985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1667199113216481066001313 1250399334912360799500985)
                    ·
                      refine ⟨937799501184270599625739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250399334912360799500985 937799501184270599625739)
                      ·
                        rfl

theorem cell23_1826358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_1826358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826358 prefixEnd_1826358 := by exact prefixLift 1826358
  have htrace : WordTrace (prefixWord ++ tailWord_1826358) baseStart_1826358 baseEnd_1826358 := by
    simpa [prefixWord, tailWord_1826358, baseEnd_1826358] using wordTrace_append hprefix tailTrace_1826358
  have hstable : (prefixWord ++ tailWord_1826358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826358).length < 2 ^ (prefixWord ++ tailWord_1826358).sum := by decide
  have hdescent : baseEnd_1826358 < baseStart_1826358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826384 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 1, 3, 2]
def baseStart_1826384 : Nat := 118140960795 + 1826384 * 2 ^ 59
def prefixEnd_1826384 : Nat := 4983230072969 + 3 ^ 40 * 1826384 * 2
def baseEnd_1826384 : Nat := 937812851681287497900619

theorem tailTrace_1826384 : CollatzResearch.WordTrace tailWord_1826384 prefixEnd_1826384 937812851681287497900619 := by
  unfold tailWord_1826384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33306848507665082199483103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44409131343553442932644137 33306848507665082199483103)
  ·
    refine ⟨49960272761497623299224655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33306848507665082199483103 49960272761497623299224655)
    ·
      refine ⟨74940409142246434948836983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49960272761497623299224655 74940409142246434948836983)
      ·
        refine ⟨112410613713369652423255475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74940409142246434948836983 112410613713369652423255475)
        ·
          refine ⟨168615920570054478634883213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112410613713369652423255475 168615920570054478634883213)
          ·
            refine ⟨63230970213770429488081205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168615920570054478634883213 63230970213770429488081205)
            ·
              refine ⟨5927903457540977764507613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63230970213770429488081205 5927903457540977764507613)
              ·
                refine ⟨2222963796577866661690355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5927903457540977764507613 2222963796577866661690355)
                ·
                  refine ⟨3334445694866799992535533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222963796577866661690355 3334445694866799992535533)
                  ·
                    refine ⟨1250417135575049997200825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3334445694866799992535533 1250417135575049997200825)
                    ·
                      refine ⟨937812851681287497900619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250417135575049997200825 937812851681287497900619)
                      ·
                        rfl

theorem cell23_1826384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 3, 2].length) (baseStart_1826384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826384 prefixEnd_1826384 := by exact prefixLift 1826384
  have htrace : WordTrace (prefixWord ++ tailWord_1826384) baseStart_1826384 baseEnd_1826384 := by
    simpa [prefixWord, tailWord_1826384, baseEnd_1826384] using wordTrace_append hprefix tailTrace_1826384
  have hstable : (prefixWord ++ tailWord_1826384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826384).length < 2 ^ (prefixWord ++ tailWord_1826384).sum := by decide
  have hdescent : baseEnd_1826384 < baseStart_1826384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826391 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_1826391 : Nat := 118140960795 + 1826391 * 2 ^ 59
def prefixEnd_1826391 : Nat := 4983230072969 + 3 ^ 40 * 1826391 * 2
def baseEnd_1826391 : Nat := 937816446045868970513087

theorem tailTrace_1826391 : CollatzResearch.WordTrace tailWord_1826391 prefixEnd_1826391 937816446045868970513087 := by
  unfold tailWord_1826391
  simp only [CollatzResearch.WordTrace]
  refine ⟨66613952326304804594471027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44409301550869869729647351 66613952326304804594471027)
  ·
    refine ⟨99920928489457206891706541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66613952326304804594471027 99920928489457206891706541)
    ·
      refine ⟨37470348183546452584389953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99920928489457206891706541 37470348183546452584389953)
      ·
        refine ⟨28102761137659839438292465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37470348183546452584389953 28102761137659839438292465)
        ·
          refine ⟨21077070853244879578719349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28102761137659839438292465 21077070853244879578719349)
          ·
            refine ⟨1975975392491707460504939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21077070853244879578719349 1975975392491707460504939)
            ·
              refine ⟨2963963088737561190757409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975975392491707460504939 2963963088737561190757409)
              ·
                refine ⟨2222972316553170893068057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963963088737561190757409 2222972316553170893068057)
                ·
                  refine ⟨1667229237414878169801043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2222972316553170893068057 1667229237414878169801043)
                  ·
                    refine ⟨2500843856122317254701565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1667229237414878169801043 2500843856122317254701565)
                    ·
                      refine ⟨937816446045868970513087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500843856122317254701565 937816446045868970513087)
                      ·
                        rfl

theorem cell23_1826391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_1826391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826391 prefixEnd_1826391 := by exact prefixLift 1826391
  have htrace : WordTrace (prefixWord ++ tailWord_1826391) baseStart_1826391 baseEnd_1826391 := by
    simpa [prefixWord, tailWord_1826391, baseEnd_1826391] using wordTrace_append hprefix tailTrace_1826391
  have hstable : (prefixWord ++ tailWord_1826391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826391).length < 2 ^ (prefixWord ++ tailWord_1826391).sum := by decide
  have hdescent : baseEnd_1826391 < baseStart_1826391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826400 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1826400 : Nat := 118140960795 + 1826400 * 2 ^ 59
def prefixEnd_1826400 : Nat := 4983230072969 + 3 ^ 40 * 1826400 * 2
def baseEnd_1826400 : Nat := 937821067371759435300545

theorem tailTrace_1826400 : CollatzResearch.WordTrace tailWord_1826400 prefixEnd_1826400 937821067371759435300545 := by
  unfold tailWord_1826400
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307140291636099565774327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44409520388848132754365769 33307140291636099565774327)
  ·
    refine ⟨49960710437454149348661491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33307140291636099565774327 49960710437454149348661491)
    ·
      refine ⟨74941065656181224022992237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49960710437454149348661491 74941065656181224022992237)
      ·
        refine ⟨28102899621067959008622089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74941065656181224022992237 28102899621067959008622089)
        ·
          refine ⟨21077174715800969256466567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28102899621067959008622089 21077174715800969256466567)
          ·
            refine ⟨31615762073701453884699851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21077174715800969256466567 31615762073701453884699851)
            ·
              refine ⟨47423643110552180827049777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31615762073701453884699851 47423643110552180827049777)
              ·
                refine ⟨35567732332914135620287333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47423643110552180827049777 35567732332914135620287333)
                ·
                  refine ⟨6668949812421400428803875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35567732332914135620287333 6668949812421400428803875)
                  ·
                    refine ⟨10003424718632100643205813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6668949812421400428803875 10003424718632100643205813)
                    ·
                      refine ⟨937821067371759435300545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10003424718632100643205813 937821067371759435300545)
                      ·
                        rfl

theorem cell23_1826400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1826400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826400 prefixEnd_1826400 := by exact prefixLift 1826400
  have htrace : WordTrace (prefixWord ++ tailWord_1826400) baseStart_1826400 baseEnd_1826400 := by
    simpa [prefixWord, tailWord_1826400, baseEnd_1826400] using wordTrace_append hprefix tailTrace_1826400
  have hstable : (prefixWord ++ tailWord_1826400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826400).length < 2 ^ (prefixWord ++ tailWord_1826400).sum := by decide
  have hdescent : baseEnd_1826400 < baseStart_1826400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826408 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1826408 : Nat := 118140960795 + 1826408 * 2 ^ 59
def prefixEnd_1826408 : Nat := 4983230072969 + 3 ^ 40 * 1826408 * 2
def baseEnd_1826408 : Nat := 937825175216995404000509

theorem tailTrace_1826408 : CollatzResearch.WordTrace tailWord_1826408 prefixEnd_1826408 937825175216995404000509 := by
  unfold tailWord_1826408
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307286183621608248919939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44409714911495477665226585 33307286183621608248919939)
  ·
    refine ⟨49960929275432412373379909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33307286183621608248919939 49960929275432412373379909)
    ·
      refine ⟨9367674239143577320008733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49960929275432412373379909 9367674239143577320008733)
      ·
        refine ⟨3512877839678841495003275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9367674239143577320008733 3512877839678841495003275)
        ·
          refine ⟨5269316759518262242504913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512877839678841495003275 5269316759518262242504913)
          ·
            refine ⟨3951987569638696681878685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269316759518262242504913 3951987569638696681878685)
            ·
              refine ⟨1481995338614511255704507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3951987569638696681878685 1481995338614511255704507)
              ·
                refine ⟨2222993007921766883556761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481995338614511255704507 2222993007921766883556761)
                ·
                  refine ⟨1667244755941325162667571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2222993007921766883556761 1667244755941325162667571)
                  ·
                    refine ⟨2500867133911987744001357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1667244755941325162667571 2500867133911987744001357)
                    ·
                      refine ⟨937825175216995404000509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2500867133911987744001357 937825175216995404000509)
                      ·
                        rfl

theorem cell23_1826408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1826408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826408 prefixEnd_1826408 := by exact prefixLift 1826408
  have htrace : WordTrace (prefixWord ++ tailWord_1826408) baseStart_1826408 baseEnd_1826408 := by
    simpa [prefixWord, tailWord_1826408, baseEnd_1826408] using wordTrace_append hprefix tailTrace_1826408
  have hstable : (prefixWord ++ tailWord_1826408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826408).length < 2 ^ (prefixWord ++ tailWord_1826408).sum := by decide
  have hdescent : baseEnd_1826408 < baseStart_1826408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826465 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1826465 : Nat := 118140960795 + 1826465 * 2 ^ 59
def prefixEnd_1826465 : Nat := 4983230072969 + 3 ^ 40 * 1826465 * 2
def baseEnd_1826465 : Nat := 937854443614301680987747

theorem tailTrace_1826465 : CollatzResearch.WordTrace tailWord_1826465 prefixEnd_1826465 937854443614301680987747 := by
  unfold tailWord_1826465
  simp only [CollatzResearch.WordTrace]
  refine ⟨66616651328036715232664849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44411100885357810155109899 66616651328036715232664849)
  ·
    refine ⟨49962488496027536424498637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66616651328036715232664849 49962488496027536424498637)
    ·
      refine ⟨18735933186010326159186989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49962488496027536424498637 18735933186010326159186989)
      ·
        refine ⟨7025974944753872309695121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18735933186010326159186989 7025974944753872309695121)
        ·
          refine ⟨5269481208565404232271341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7025974944753872309695121 5269481208565404232271341)
          ·
            refine ⟨1976055453212026587101753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5269481208565404232271341 1976055453212026587101753)
            ·
              refine ⟨1482041589909019940326315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976055453212026587101753 1482041589909019940326315)
              ·
                refine ⟨2223062384863529910489473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482041589909019940326315 2223062384863529910489473)
                ·
                  refine ⟨1667296788647647432867105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2223062384863529910489473 1667296788647647432867105)
                  ·
                    refine ⟨1250472591485735574650329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1667296788647647432867105 1250472591485735574650329)
                    ·
                      refine ⟨937854443614301680987747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250472591485735574650329 937854443614301680987747)
                      ·
                        rfl

theorem cell23_1826465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1826465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826465 prefixEnd_1826465 := by exact prefixLift 1826465
  have htrace : WordTrace (prefixWord ++ tailWord_1826465) baseStart_1826465 baseEnd_1826465 := by
    simpa [prefixWord, tailWord_1826465, baseEnd_1826465] using wordTrace_append hprefix tailTrace_1826465
  have hstable : (prefixWord ++ tailWord_1826465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826465).length < 2 ^ (prefixWord ++ tailWord_1826465).sum := by decide
  have hdescent : baseEnd_1826465 < baseStart_1826465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826477 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1826477 : Nat := 118140960795 + 1826477 * 2 ^ 59
def prefixEnd_1826477 : Nat := 4983230072969 + 3 ^ 40 * 1826477 * 2
def baseEnd_1826477 : Nat := 937860605382155634037691

theorem tailTrace_1826477 : CollatzResearch.WordTrace tailWord_1826477 prefixEnd_1826477 937860605382155634037691 := by
  unfold tailWord_1826477
  simp only [CollatzResearch.WordTrace]
  refine ⟨66617089003993241282101685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44411392669328827521401123 66617089003993241282101685)
  ·
    refine ⟨6245352094124366370197033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66617089003993241282101685 6245352094124366370197033)
    ·
      refine ⟨4684014070593274777647775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6245352094124366370197033 4684014070593274777647775)
      ·
        refine ⟨7026021105889912166471663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4684014070593274777647775 7026021105889912166471663)
        ·
          refine ⟨10539031658834868249707495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026021105889912166471663 10539031658834868249707495)
          ·
            refine ⟨15808547488252302374561243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10539031658834868249707495 15808547488252302374561243)
            ·
              refine ⟨23712821232378453561841865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808547488252302374561243 23712821232378453561841865)
              ·
                refine ⟨17784615924283840171381399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23712821232378453561841865 17784615924283840171381399)
                ·
                  refine ⟨26676923886425760257072099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17784615924283840171381399 26676923886425760257072099)
                  ·
                    refine ⟨40015385829638640385608149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26676923886425760257072099 40015385829638640385608149)
                    ·
                      refine ⟨937860605382155634037691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40015385829638640385608149 937860605382155634037691)
                      ·
                        rfl

theorem cell23_1826477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1826477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826477 prefixEnd_1826477 := by exact prefixLift 1826477
  have htrace : WordTrace (prefixWord ++ tailWord_1826477) baseStart_1826477 baseEnd_1826477 := by
    simpa [prefixWord, tailWord_1826477, baseEnd_1826477] using wordTrace_append hprefix tailTrace_1826477
  have hstable : (prefixWord ++ tailWord_1826477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826477).length < 2 ^ (prefixWord ++ tailWord_1826477).sum := by decide
  have hdescent : baseEnd_1826477 < baseStart_1826477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826480 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 2, 8]
def baseStart_1826480 : Nat := 118140960795 + 1826480 * 2 ^ 59
def prefixEnd_1826480 : Nat := 4983230072969 + 3 ^ 40 * 1826480 * 2
def baseEnd_1826480 : Nat := 312620715274706374100059

theorem tailTrace_1826480 : CollatzResearch.WordTrace tailWord_1826480 prefixEnd_1826480 312620715274706374100059 := by
  unfold tailWord_1826480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33308599211491186397230447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44411465615321581862973929 33308599211491186397230447)
  ·
    refine ⟨49962898817236779595845671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33308599211491186397230447 49962898817236779595845671)
    ·
      refine ⟨74944348225855169393768507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49962898817236779595845671 74944348225855169393768507)
      ·
        refine ⟨112416522338782754090652761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74944348225855169393768507 112416522338782754090652761)
        ·
          refine ⟨84312391754087065567989571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112416522338782754090652761 84312391754087065567989571)
          ·
            refine ⟨126468587631130598351984357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84312391754087065567989571 126468587631130598351984357)
            ·
              refine ⟨23712860180836987190997067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126468587631130598351984357 23712860180836987190997067)
              ·
                refine ⟨35569290271255480786495601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23712860180836987190997067 35569290271255480786495601)
                ·
                  refine ⟨26676967703441610589871701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35569290271255480786495601 26676967703441610589871701)
                  ·
                    refine ⟨312620715274706374100059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26676967703441610589871701 312620715274706374100059)
                    ·
                      rfl

theorem cell23_1826480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_1826480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826480 prefixEnd_1826480 := by exact prefixLift 1826480
  have htrace : WordTrace (prefixWord ++ tailWord_1826480) baseStart_1826480 baseEnd_1826480 := by
    simpa [prefixWord, tailWord_1826480, baseEnd_1826480] using wordTrace_append hprefix tailTrace_1826480
  have hstable : (prefixWord ++ tailWord_1826480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826480).length < 2 ^ (prefixWord ++ tailWord_1826480).sum := by decide
  have hdescent : baseEnd_1826480 < baseStart_1826480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826504 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_1826504 : Nat := 118140960795 + 1826504 * 2 ^ 59
def prefixEnd_1826504 : Nat := 4983230072969 + 3 ^ 40 * 1826504 * 2
def baseEnd_1826504 : Nat := 937874469359827028400067

theorem tailTrace_1826504 : CollatzResearch.WordTrace tailWord_1826504 prefixEnd_1826504 937874469359827028400067 := by
  unfold tailWord_1826504
  simp only [CollatzResearch.WordTrace]
  refine ⟨33309036887447712446667283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44412049183263616595556377 33309036887447712446667283)
  ·
    refine ⟨49963555331171568670000925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33309036887447712446667283 49963555331171568670000925)
    ·
      refine ⟨18736333249189338251250347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49963555331171568670000925 18736333249189338251250347)
      ·
        refine ⟨28104499873784007376875521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736333249189338251250347 28104499873784007376875521)
        ·
          refine ⟨21078374905338005532656641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28104499873784007376875521 21078374905338005532656641)
          ·
            refine ⟨15808781179003504149492481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21078374905338005532656641 15808781179003504149492481)
            ·
              refine ⟨11856585884252628112119361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15808781179003504149492481 11856585884252628112119361)
              ·
                refine ⟨8892439413189471084089521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11856585884252628112119361 8892439413189471084089521)
                ·
                  refine ⟨6669329559892103313067141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8892439413189471084089521 6669329559892103313067141)
                  ·
                    refine ⟨1250499292479769371200089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6669329559892103313067141 1250499292479769371200089)
                    ·
                      refine ⟨937874469359827028400067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250499292479769371200089 937874469359827028400067)
                      ·
                        rfl

theorem cell23_1826504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_1826504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826504 prefixEnd_1826504 := by exact prefixLift 1826504
  have htrace : WordTrace (prefixWord ++ tailWord_1826504) baseStart_1826504 baseEnd_1826504 := by
    simpa [prefixWord, tailWord_1826504, baseEnd_1826504] using wordTrace_append hprefix tailTrace_1826504
  have hstable : (prefixWord ++ tailWord_1826504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826504).length < 2 ^ (prefixWord ++ tailWord_1826504).sum := by decide
  have hdescent : baseEnd_1826504 < baseStart_1826504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826527 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 6]
def baseStart_1826527 : Nat := 118140960795 + 1826527 * 2 ^ 59
def prefixEnd_1826527 : Nat := 4983230072969 + 3 ^ 40 * 1826527 * 2
def baseEnd_1826527 : Nat := 104209586601653382045829

theorem tailTrace_1826527 : CollatzResearch.WordTrace tailWord_1826527 prefixEnd_1826527 104209586601653382045829 := by
  unfold tailWord_1826527
  simp only [CollatzResearch.WordTrace]
  refine ⟨66618912653812099821421835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44412608435874733214281223 66618912653812099821421835)
  ·
    refine ⟨99928368980718149732132753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66618912653812099821421835 99928368980718149732132753)
    ·
      refine ⟨74946276735538612299099565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99928368980718149732132753 74946276735538612299099565)
      ·
        refine ⟨28104853775826979612162337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74946276735538612299099565 28104853775826979612162337)
        ·
          refine ⟨21078640331870234709121753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28104853775826979612162337 21078640331870234709121753)
          ·
            refine ⟨15808980248902676031841315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21078640331870234709121753 15808980248902676031841315)
            ·
              refine ⟨23713470373354014047761973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808980248902676031841315 23713470373354014047761973)
              ·
                refine ⟨2223137847501938816977685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23713470373354014047761973 2223137847501938816977685)
                ·
                  refine ⟨104209586601653382045829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2223137847501938816977685 104209586601653382045829)
                  ·
                    rfl

theorem cell23_1826527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 6].length) (baseStart_1826527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826527 prefixEnd_1826527 := by exact prefixLift 1826527
  have htrace : WordTrace (prefixWord ++ tailWord_1826527) baseStart_1826527 baseEnd_1826527 := by
    simpa [prefixWord, tailWord_1826527, baseEnd_1826527] using wordTrace_append hprefix tailTrace_1826527
  have hstable : (prefixWord ++ tailWord_1826527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826527).length < 2 ^ (prefixWord ++ tailWord_1826527).sum := by decide
  have hdescent : baseEnd_1826527 < baseStart_1826527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826531 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 3, 4]
def baseStart_1826531 : Nat := 118140960795 + 1826531 * 2 ^ 59
def prefixEnd_1826531 : Nat := 4983230072969 + 3 ^ 40 * 1826531 * 2
def baseEnd_1826531 : Nat := 312629444445832807587481

theorem tailTrace_1826531 : CollatzResearch.WordTrace tailWord_1826531 prefixEnd_1826531 312629444445832807587481 := by
  unfold tailWord_1826531
  simp only [CollatzResearch.WordTrace]
  refine ⟨66619058545797608504567447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44412705697198405669711631 66619058545797608504567447)
  ·
    refine ⟨99928587818696412756851171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66619058545797608504567447 99928587818696412756851171)
    ·
      refine ⟨149892881728044619135276757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99928587818696412756851171 149892881728044619135276757)
      ·
        refine ⟨3513114415501045760983049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 149892881728044619135276757 3513114415501045760983049)
        ·
          refine ⟨2634835811625784320737287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3513114415501045760983049 2634835811625784320737287)
          ·
            refine ⟨3952253717438676481105931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634835811625784320737287 3952253717438676481105931)
            ·
              refine ⟨5928380576158014721658897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952253717438676481105931 5928380576158014721658897)
              ·
                refine ⟨4446285432118511041244173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5928380576158014721658897 4446285432118511041244173)
                ·
                  refine ⟨1667357037044441640466565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4446285432118511041244173 1667357037044441640466565)
                  ·
                    refine ⟨312629444445832807587481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667357037044441640466565 312629444445832807587481)
                    ·
                      rfl

theorem cell23_1826531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 4].length) (baseStart_1826531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826531 prefixEnd_1826531 := by exact prefixLift 1826531
  have htrace : WordTrace (prefixWord ++ tailWord_1826531) baseStart_1826531 baseEnd_1826531 := by
    simpa [prefixWord, tailWord_1826531, baseEnd_1826531] using wordTrace_append hprefix tailTrace_1826531
  have hstable : (prefixWord ++ tailWord_1826531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826531).length < 2 ^ (prefixWord ++ tailWord_1826531).sum := by decide
  have hdescent : baseEnd_1826531 < baseStart_1826531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826541 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1826541 : Nat := 118140960795 + 1826541 * 2 ^ 59
def prefixEnd_1826541 : Nat := 4983230072969 + 3 ^ 40 * 1826541 * 2
def baseEnd_1826541 : Nat := 937893468144043383637397

theorem tailTrace_1826541 : CollatzResearch.WordTrace tailWord_1826541 prefixEnd_1826541 937893468144043383637397 := by
  unfold tailWord_1826541
  simp only [CollatzResearch.WordTrace]
  refine ⟨66619423275761380212431477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44412948850507586808287651 66619423275761380212431477)
  ·
    refine ⟨6245570932102629394915451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66619423275761380212431477 6245570932102629394915451)
    ·
      refine ⟨9368356398153944092373177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6245570932102629394915451 9368356398153944092373177)
      ·
        refine ⟨7026267298615458069279883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9368356398153944092373177 7026267298615458069279883)
        ·
          refine ⟨10539400947923187103919825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026267298615458069279883 10539400947923187103919825)
          ·
            refine ⟨7904550710942390327939869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10539400947923187103919825 7904550710942390327939869)
            ·
              refine ⟨2964206516603396372977451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7904550710942390327939869 2964206516603396372977451)
              ·
                refine ⟨4446309774905094559466177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964206516603396372977451 4446309774905094559466177)
                ·
                  refine ⟨3334732331178820919599633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4446309774905094559466177 3334732331178820919599633)
                  ·
                    refine ⟨2501049248384115689699725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3334732331178820919599633 2501049248384115689699725)
                    ·
                      refine ⟨937893468144043383637397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501049248384115689699725 937893468144043383637397)
                      ·
                        rfl

theorem cell23_1826541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1826541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826541 prefixEnd_1826541 := by exact prefixLift 1826541
  have htrace : WordTrace (prefixWord ++ tailWord_1826541) baseStart_1826541 baseEnd_1826541 := by
    simpa [prefixWord, tailWord_1826541, baseEnd_1826541] using wordTrace_append hprefix tailTrace_1826541
  have hstable : (prefixWord ++ tailWord_1826541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826541).length < 2 ^ (prefixWord ++ tailWord_1826541).sum := by decide
  have hdescent : baseEnd_1826541 < baseStart_1826541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826554 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_1826554 : Nat := 118140960795 + 1826554 * 2 ^ 59
def prefixEnd_1826554 : Nat := 4983230072969 + 3 ^ 40 * 1826554 * 2
def baseEnd_1826554 : Nat := 937900143392551832774837

theorem tailTrace_1826554 : CollatzResearch.WordTrace tailWord_1826554 prefixEnd_1826554 937900143392551832774837 := by
  unfold tailWord_1826554
  simp only [CollatzResearch.WordTrace]
  refine ⟨16654974356178570858163679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44413264949809522288436477 16654974356178570858163679)
  ·
    refine ⟨24982461534267856287245519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16654974356178570858163679 24982461534267856287245519)
    ·
      refine ⟨37473692301401784430868279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24982461534267856287245519 37473692301401784430868279)
      ·
        refine ⟨56210538452102676646302419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37473692301401784430868279 56210538452102676646302419)
        ·
          refine ⟨84315807678154014969453629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56210538452102676646302419 84315807678154014969453629)
          ·
            refine ⟨31618427879307755613545111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84315807678154014969453629 31618427879307755613545111)
            ·
              refine ⟨47427641818961633420317667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31618427879307755613545111 47427641818961633420317667)
              ·
                refine ⟨71141462728442450130476501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47427641818961633420317667 71141462728442450130476501)
                ·
                  refine ⟨1667378032697869924933043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 71141462728442450130476501 1667378032697869924933043)
                  ·
                    refine ⟨2501067049046804887399565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1667378032697869924933043 2501067049046804887399565)
                    ·
                      refine ⟨937900143392551832774837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501067049046804887399565 937900143392551832774837)
                      ·
                        rfl

theorem cell23_1826554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_1826554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826554 prefixEnd_1826554 := by exact prefixLift 1826554
  have htrace : WordTrace (prefixWord ++ tailWord_1826554) baseStart_1826554 baseEnd_1826554 := by
    simpa [prefixWord, tailWord_1826554, baseEnd_1826554] using wordTrace_append hprefix tailTrace_1826554
  have hstable : (prefixWord ++ tailWord_1826554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826554).length < 2 ^ (prefixWord ++ tailWord_1826554).sum := by decide
  have hdescent : baseEnd_1826554 < baseStart_1826554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826557 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1826557 : Nat := 118140960795 + 1826557 * 2 ^ 59
def prefixEnd_1826557 : Nat := 4983230072969 + 3 ^ 40 * 1826557 * 2
def baseEnd_1826557 : Nat := 312633894611505107012441

theorem tailTrace_1826557 : CollatzResearch.WordTrace tailWord_1826557 prefixEnd_1826557 312633894611505107012441 := by
  unfold tailWord_1826557
  simp only [CollatzResearch.WordTrace]
  refine ⟨66620006843703414945013925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44413337895802276630009283 66620006843703414945013925)
  ·
    refine ⟨12491251283194390302190111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66620006843703414945013925 12491251283194390302190111)
    ·
      refine ⟨18736876924791585453285167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12491251283194390302190111 18736876924791585453285167)
      ·
        refine ⟨28105315387187378179927751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736876924791585453285167 28105315387187378179927751)
        ·
          refine ⟨42157973080781067269891627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28105315387187378179927751 42157973080781067269891627)
          ·
            refine ⟨63236959621171600904837441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42157973080781067269891627 63236959621171600904837441)
            ·
              refine ⟨47427719715878700678628081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63236959621171600904837441 47427719715878700678628081)
              ·
                refine ⟨35570789786909025508971061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47427719715878700678628081 35570789786909025508971061)
                ·
                  refine ⟨3334761542522721141466037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35570789786909025508971061 3334761542522721141466037)
                  ·
                    refine ⟨312633894611505107012441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3334761542522721141466037 312633894611505107012441)
                    ·
                      rfl

theorem cell23_1826557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1826557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826557 prefixEnd_1826557 := by exact prefixLift 1826557
  have htrace : WordTrace (prefixWord ++ tailWord_1826557) baseStart_1826557 baseEnd_1826557 := by
    simpa [prefixWord, tailWord_1826557, baseEnd_1826557] using wordTrace_append hprefix tailTrace_1826557
  have hstable : (prefixWord ++ tailWord_1826557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826557).length < 2 ^ (prefixWord ++ tailWord_1826557).sum := by decide
  have hdescent : baseEnd_1826557 < baseStart_1826557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826578 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 6]
def baseStart_1826578 : Nat := 118140960795 + 1826578 * 2 ^ 59
def prefixEnd_1826578 : Nat := 4983230072969 + 3 ^ 40 * 1826578 * 2
def baseEnd_1826578 : Nat := 104212496325362193208303

theorem tailTrace_1826578 : CollatzResearch.WordTrace tailWord_1826578 prefixEnd_1826578 104212496325362193208303 := by
  unfold tailWord_1826578
  simp only [CollatzResearch.WordTrace]
  refine ⟨16655193194156833882882097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44413848517751557021018925 16655193194156833882882097)
  ·
    refine ⟨12491394895617625412161573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16655193194156833882882097 12491394895617625412161573)
    ·
      refine ⟨2342136542928304764780295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12491394895617625412161573 2342136542928304764780295)
      ·
        refine ⟨3513204814392457147170443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342136542928304764780295 3513204814392457147170443)
        ·
          refine ⟨5269807221588685720755665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513204814392457147170443 5269807221588685720755665)
          ·
            refine ⟨3952355416191514290566749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269807221588685720755665 3952355416191514290566749)
            ·
              refine ⟨1482133281071817858962531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3952355416191514290566749 1482133281071817858962531)
              ·
                refine ⟨2223199921607726788443797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482133281071817858962531 2223199921607726788443797)
                ·
                  refine ⟨104212496325362193208303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2223199921607726788443797 104212496325362193208303)
                  ·
                    rfl

theorem cell23_1826578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_1826578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826578 prefixEnd_1826578 := by exact prefixLift 1826578
  have htrace : WordTrace (prefixWord ++ tailWord_1826578) baseStart_1826578 baseEnd_1826578 := by
    simpa [prefixWord, tailWord_1826578, baseEnd_1826578] using wordTrace_append hprefix tailTrace_1826578
  have hstable : (prefixWord ++ tailWord_1826578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826578).length < 2 ^ (prefixWord ++ tailWord_1826578).sum := by decide
  have hdescent : baseEnd_1826578 < baseStart_1826578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826604 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_1826604 : Nat := 118140960795 + 1826604 * 2 ^ 59
def prefixEnd_1826604 : Nat := 4983230072969 + 3 ^ 40 * 1826604 * 2
def baseEnd_1826604 : Nat := 312641939141758879049869

theorem tailTrace_1826604 : CollatzResearch.WordTrace tailWord_1826604 prefixEnd_1826604 312641939141758879049869 := by
  unfold tailWord_1826604
  simp only [CollatzResearch.WordTrace]
  refine ⟨33310860537266570985987433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44414480716355427981316577 33310860537266570985987433)
  ·
    refine ⟨24983145402949928239490575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33310860537266570985987433 24983145402949928239490575)
    ·
      refine ⟨37474718104424892359235863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24983145402949928239490575 37474718104424892359235863)
      ·
        refine ⟨56212077156637338538853795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37474718104424892359235863 56212077156637338538853795)
        ·
          refine ⟨84318115734956007808280693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56212077156637338538853795 84318115734956007808280693)
          ·
            refine ⟨7904823350152125732026315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84318115734956007808280693 7904823350152125732026315)
            ·
              refine ⟨11857235025228188598039473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7904823350152125732026315 11857235025228188598039473)
              ·
                refine ⟨8892926268921141448529605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11857235025228188598039473 8892926268921141448529605)
                ·
                  refine ⟨1667423675422714021599301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8892926268921141448529605 1667423675422714021599301)
                  ·
                    refine ⟨312641939141758879049869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667423675422714021599301 312641939141758879049869)
                    ·
                      rfl

theorem cell23_1826604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_1826604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826604 prefixEnd_1826604 := by exact prefixLift 1826604
  have htrace : WordTrace (prefixWord ++ tailWord_1826604) baseStart_1826604 baseEnd_1826604 := by
    simpa [prefixWord, tailWord_1826604, baseEnd_1826604] using wordTrace_append hprefix tailTrace_1826604
  have hstable : (prefixWord ++ tailWord_1826604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826604).length < 2 ^ (prefixWord ++ tailWord_1826604).sum := by decide
  have hdescent : baseEnd_1826604 < baseStart_1826604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826621 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_1826621 : Nat := 118140960795 + 1826621 * 2 ^ 59
def prefixEnd_1826621 : Nat := 4983230072969 + 3 ^ 40 * 1826621 * 2
def baseEnd_1826621 : Nat := 312644848865467690212343

theorem tailTrace_1826621 : CollatzResearch.WordTrace tailWord_1826621 prefixEnd_1826621 312644848865467690212343 := by
  unfold tailWord_1826621
  simp only [CollatzResearch.WordTrace]
  refine ⟨66622341115471553875343717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44414894076981035916895811 66622341115471553875343717)
  ·
    refine ⟨12491688959150916351626947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66622341115471553875343717 12491688959150916351626947)
    ·
      refine ⟨18737533438726374527440421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12491688959150916351626947 18737533438726374527440421)
      ·
        refine ⟨3513287519761195223895079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18737533438726374527440421 3513287519761195223895079)
        ·
          refine ⟨5269931279641792835842619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513287519761195223895079 5269931279641792835842619)
          ·
            refine ⟨7904896919462689253763929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269931279641792835842619 7904896919462689253763929)
            ·
              refine ⟨5928672689597016940322947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904896919462689253763929 5928672689597016940322947)
              ·
                refine ⟨8893009034395525410484421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928672689597016940322947 8893009034395525410484421)
                ·
                  refine ⟨1667439193949161014465829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8893009034395525410484421 1667439193949161014465829)
                  ·
                    refine ⟨312644848865467690212343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667439193949161014465829 312644848865467690212343)
                    ·
                      rfl

theorem cell23_1826621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_1826621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826621 prefixEnd_1826621 := by exact prefixLift 1826621
  have htrace : WordTrace (prefixWord ++ tailWord_1826621) baseStart_1826621 baseEnd_1826621 := by
    simpa [prefixWord, tailWord_1826621, baseEnd_1826621] using wordTrace_append hprefix tailTrace_1826621
  have hstable : (prefixWord ++ tailWord_1826621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826621).length < 2 ^ (prefixWord ++ tailWord_1826621).sum := by decide
  have hdescent : baseEnd_1826621 < baseStart_1826621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826622 : List Nat := [4, 2, 1, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_1826622 : Nat := 118140960795 + 1826622 * 2 ^ 59
def prefixEnd_1826622 : Nat := 4983230072969 + 3 ^ 40 * 1826622 * 2
def baseEnd_1826622 : Nat := 937935060077057566724525

theorem tailTrace_1826622 : CollatzResearch.WordTrace tailWord_1826622 prefixEnd_1826622 937935060077057566724525 := by
  unfold tailWord_1826622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327797198558491380766265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44414918392311954030753413 8327797198558491380766265)
  ·
    refine ⟨6245847898918868535574699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8327797198558491380766265 6245847898918868535574699)
    ·
      refine ⟨9368771848378302803362049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6245847898918868535574699 9368771848378302803362049)
      ·
        refine ⟨7026578886283727102521537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9368771848378302803362049 7026578886283727102521537)
        ·
          refine ⟨5269934164712795326891153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7026578886283727102521537 5269934164712795326891153)
          ·
            refine ⟨3952450623534596495168365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269934164712795326891153 3952450623534596495168365)
            ·
              refine ⟨1482168983825473685688137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3952450623534596495168365 1482168983825473685688137)
              ·
                refine ⟨1111626737869105264266103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482168983825473685688137 1111626737869105264266103)
                ·
                  refine ⟨1667440106803657896399155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111626737869105264266103 1667440106803657896399155)
                  ·
                    refine ⟨2501160160205486844598733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1667440106803657896399155 2501160160205486844598733)
                    ·
                      refine ⟨937935060077057566724525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501160160205486844598733 937935060077057566724525)
                      ·
                        rfl

theorem cell23_1826622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_1826622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826622 prefixEnd_1826622 := by exact prefixLift 1826622
  have htrace : WordTrace (prefixWord ++ tailWord_1826622) baseStart_1826622 baseEnd_1826622 := by
    simpa [prefixWord, tailWord_1826622, baseEnd_1826622] using wordTrace_append hprefix tailTrace_1826622
  have hstable : (prefixWord ++ tailWord_1826622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826622).length < 2 ^ (prefixWord ++ tailWord_1826622).sum := by decide
  have hdescent : baseEnd_1826622 < baseStart_1826622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826741 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 7]
def baseStart_1826741 : Nat := 118140960795 + 1826741 * 2 ^ 59
def prefixEnd_1826741 : Nat := 4983230072969 + 3 ^ 40 * 1826741 * 2
def baseEnd_1826741 : Nat := 104221796030549177904053

theorem tailTrace_1826741 : CollatzResearch.WordTrace tailWord_1826741 prefixEnd_1826741 104221796030549177904053 := by
  unfold tailWord_1826741
  simp only [CollatzResearch.WordTrace]
  refine ⟨66626717875036814369712077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44417811916691209579808051 66626717875036814369712077)
  ·
    refine ⟨24985019203138805388642029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66626717875036814369712077 24985019203138805388642029)
    ·
      refine ⟨9369382201177052020740761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24985019203138805388642029 9369382201177052020740761)
      ·
        refine ⟨7027036650882789015555571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9369382201177052020740761 7027036650882789015555571)
        ·
          refine ⟨10540554976324183523333357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7027036650882789015555571 10540554976324183523333357)
          ·
            refine ⟨3952708116121568821250009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10540554976324183523333357 3952708116121568821250009)
            ·
              refine ⟨2964531087091176615937507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3952708116121568821250009 2964531087091176615937507)
              ·
                refine ⟨4446796630636764923906261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964531087091176615937507 4446796630636764923906261)
                ·
                  refine ⟨104221796030549177904053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4446796630636764923906261 104221796030549177904053)
                  ·
                    rfl

theorem cell23_1826741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_1826741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826741 prefixEnd_1826741 := by exact prefixLift 1826741
  have htrace : WordTrace (prefixWord ++ tailWord_1826741) baseStart_1826741 baseEnd_1826741 := by
    simpa [prefixWord, tailWord_1826741, baseEnd_1826741] using wordTrace_append hprefix tailTrace_1826741
  have hstable : (prefixWord ++ tailWord_1826741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826741).length < 2 ^ (prefixWord ++ tailWord_1826741).sum := by decide
  have hdescent : baseEnd_1826741 < baseStart_1826741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826828 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1826828 : Nat := 118140960795 + 1826828 * 2 ^ 59
def prefixEnd_1826828 : Nat := 4983230072969 + 3 ^ 40 * 1826828 * 2
def baseEnd_1826828 : Nat := 938040837091883760748577

theorem tailTrace_1826828 : CollatzResearch.WordTrace tailWord_1826828 prefixEnd_1826828 938040837091883760748577 := by
  unfold tailWord_1826828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33314945512860814114064569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44419927350481085485419425 33314945512860814114064569)
  ·
    refine ⟨24986209134645610585548427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33314945512860814114064569 24986209134645610585548427)
    ·
      refine ⟨37479313701968415878322641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24986209134645610585548427 37479313701968415878322641)
      ·
        refine ⟨28109485276476311908741981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37479313701968415878322641 28109485276476311908741981)
        ·
          refine ⟨10541056978678616965778243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28109485276476311908741981 10541056978678616965778243)
          ·
            refine ⟨15811585468017925448667365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541056978678616965778243 15811585468017925448667365)
            ·
              refine ⟨2964672275253361021625131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15811585468017925448667365 2964672275253361021625131)
              ·
                refine ⟨4447008412880041532437697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964672275253361021625131 4447008412880041532437697)
                ·
                  refine ⟨3335256309660031149328273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447008412880041532437697 3335256309660031149328273)
                  ·
                    refine ⟨2501442232245023361996205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3335256309660031149328273 2501442232245023361996205)
                    ·
                      refine ⟨938040837091883760748577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501442232245023361996205 938040837091883760748577)
                      ·
                        rfl

theorem cell23_1826828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1826828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826828 prefixEnd_1826828 := by exact prefixLift 1826828
  have htrace : WordTrace (prefixWord ++ tailWord_1826828) baseStart_1826828 baseEnd_1826828 := by
    simpa [prefixWord, tailWord_1826828, baseEnd_1826828] using wordTrace_append hprefix tailTrace_1826828
  have hstable : (prefixWord ++ tailWord_1826828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826828).length < 2 ^ (prefixWord ++ tailWord_1826828).sum := by decide
  have hdescent : baseEnd_1826828 < baseStart_1826828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826852 : List Nat := [2, 3, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_1826852 : Nat := 118140960795 + 1826852 * 2 ^ 59
def prefixEnd_1826852 : Nat := 4983230072969 + 3 ^ 40 * 1826852 * 2
def baseEnd_1826852 : Nat := 312684386875863888949489

theorem tailTrace_1826852 : CollatzResearch.WordTrace tailWord_1826852 prefixEnd_1826852 312684386875863888949489 := by
  unfold tailWord_1826852
  simp only [CollatzResearch.WordTrace]
  refine ⟨33315383188817340163501405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44420510918423120218001873 33315383188817340163501405)
  ·
    refine ⟨12493268695806502561313027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33315383188817340163501405 12493268695806502561313027)
    ·
      refine ⟨18739903043709753841969541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12493268695806502561313027 18739903043709753841969541)
      ·
        refine ⟨3513731820695578845369289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18739903043709753841969541 3513731820695578845369289)
        ·
          refine ⟨2635298865521684134026967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3513731820695578845369289 2635298865521684134026967)
          ·
            refine ⟨3952948298282526201040451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635298865521684134026967 3952948298282526201040451)
            ·
              refine ⟨5929422447423789301560677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952948298282526201040451 5929422447423789301560677)
              ·
                refine ⟨1111766708891960494042627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5929422447423789301560677 1111766708891960494042627)
                ·
                  refine ⟨1667650063337940741063941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111766708891960494042627 1667650063337940741063941)
                  ·
                    refine ⟨312684386875863888949489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667650063337940741063941 312684386875863888949489)
                    ·
                      rfl

theorem cell23_1826852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_1826852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826852 prefixEnd_1826852 := by exact prefixLift 1826852
  have htrace : WordTrace (prefixWord ++ tailWord_1826852) baseStart_1826852 baseEnd_1826852 := by
    simpa [prefixWord, tailWord_1826852, baseEnd_1826852] using wordTrace_append hprefix tailTrace_1826852
  have hstable : (prefixWord ++ tailWord_1826852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826852).length < 2 ^ (prefixWord ++ tailWord_1826852).sum := by decide
  have hdescent : baseEnd_1826852 < baseStart_1826852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826891 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 6, 4]
def baseStart_1826891 : Nat := 118140960795 + 1826891 * 2 ^ 59
def prefixEnd_1826891 : Nat := 4983230072969 + 3 ^ 40 * 1826891 * 2
def baseEnd_1826891 : Nat := 312691062124372338086929

theorem tailTrace_1826891 : CollatzResearch.WordTrace tailWord_1826891 prefixEnd_1826891 312691062124372338086929 := by
  unfold tailWord_1826891
  simp only [CollatzResearch.WordTrace]
  refine ⟨66632188824493389987672527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44421459216328926658448351 66632188824493389987672527)
  ·
    refine ⟨99948283236740084981508791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66632188824493389987672527 99948283236740084981508791)
    ·
      refine ⟨149922424855110127472263187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99948283236740084981508791 149922424855110127472263187)
      ·
        refine ⟨224883637282665191208394781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149922424855110127472263187 224883637282665191208394781)
        ·
          refine ⟨84331363980999446703148043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224883637282665191208394781 84331363980999446703148043)
          ·
            refine ⟨126497045971499170054722065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84331363980999446703148043 126497045971499170054722065)
            ·
              refine ⟨94872784478624377541041549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126497045971499170054722065 94872784478624377541041549)
              ·
                refine ⟨35577294179484141577890581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94872784478624377541041549 35577294179484141577890581)
                ·
                  refine ⟨1667685664663319136463621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35577294179484141577890581 1667685664663319136463621)
                  ·
                    refine ⟨312691062124372338086929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667685664663319136463621 312691062124372338086929)
                    ·
                      rfl

theorem cell23_1826891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 4].length) (baseStart_1826891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826891 prefixEnd_1826891 := by exact prefixLift 1826891
  have htrace : WordTrace (prefixWord ++ tailWord_1826891) baseStart_1826891 baseEnd_1826891 := by
    simpa [prefixWord, tailWord_1826891, baseEnd_1826891] using wordTrace_append hprefix tailTrace_1826891
  have hstable : (prefixWord ++ tailWord_1826891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826891).length < 2 ^ (prefixWord ++ tailWord_1826891).sum := by decide
  have hdescent : baseEnd_1826891 < baseStart_1826891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826909 : List Nat := [1, 4, 4, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1826909 : Nat := 118140960795 + 1826909 * 2 ^ 59
def prefixEnd_1826909 : Nat := 4983230072969 + 3 ^ 40 * 1826909 * 2
def baseEnd_1826909 : Nat := 938082429024897943835705

theorem tailTrace_1826909 : CollatzResearch.WordTrace tailWord_1826909 prefixEnd_1826909 938082429024897943835705 := by
  unfold tailWord_1826909
  simp only [CollatzResearch.WordTrace]
  refine ⟨66632845338428179061827781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44421896892285452707885187 66632845338428179061827781)
  ·
    refine ⟨12493658500955283574092709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66632845338428179061827781 12493658500955283574092709)
    ·
      refine ⟨2342560968929115670142383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12493658500955283574092709 2342560968929115670142383)
      ·
        refine ⟨3513841453393673505213575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342560968929115670142383 3513841453393673505213575)
        ·
          refine ⟨5270762180090510257820363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513841453393673505213575 5270762180090510257820363)
          ·
            refine ⟨7906143270135765386730545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270762180090510257820363 7906143270135765386730545)
            ·
              refine ⟨5929607452601824040047909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7906143270135765386730545 5929607452601824040047909)
              ·
                refine ⟨1111801397362842007508983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5929607452601824040047909 1111801397362842007508983)
                ·
                  refine ⟨1667702096044263011263475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111801397362842007508983 1667702096044263011263475)
                  ·
                    refine ⟨2501553144066394516895213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1667702096044263011263475 2501553144066394516895213)
                    ·
                      refine ⟨938082429024897943835705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501553144066394516895213 938082429024897943835705)
                      ·
                        rfl

theorem cell23_1826909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1826909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826909 prefixEnd_1826909 := by exact prefixLift 1826909
  have htrace : WordTrace (prefixWord ++ tailWord_1826909) baseStart_1826909 baseEnd_1826909 := by
    simpa [prefixWord, tailWord_1826909, baseEnd_1826909] using wordTrace_append hprefix tailTrace_1826909
  have hstable : (prefixWord ++ tailWord_1826909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826909).length < 2 ^ (prefixWord ++ tailWord_1826909).sum := by decide
  have hdescent : baseEnd_1826909 < baseStart_1826909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826915 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 3, 2, 2]
def baseStart_1826915 : Nat := 118140960795 + 1826915 * 2 ^ 59
def prefixEnd_1826915 : Nat := 4983230072969 + 3 ^ 40 * 1826915 * 2
def baseEnd_1826915 : Nat := 938085509908824920360677

theorem tailTrace_1826915 : CollatzResearch.WordTrace tailWord_1826915 prefixEnd_1826915 938085509908824920360677 := by
  unfold tailWord_1826915
  simp only [CollatzResearch.WordTrace]
  refine ⟨66633064176406442086546199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44422042784270961391030799 66633064176406442086546199)
  ·
    refine ⟨99949596264609663129819299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66633064176406442086546199 99949596264609663129819299)
    ·
      refine ⟨149924394396914494694728949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99949596264609663129819299 149924394396914494694728949)
      ·
        refine ⟨14055411974710733877630839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149924394396914494694728949 14055411974710733877630839)
        ·
          refine ⟨21083117962066100816446259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14055411974710733877630839 21083117962066100816446259)
          ·
            refine ⟨31624676943099151224669389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21083117962066100816446259 31624676943099151224669389)
            ·
              refine ⟨11859253853662181709251021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31624676943099151224669389 11859253853662181709251021)
              ·
                refine ⟨4447220195123318140969133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11859253853662181709251021 4447220195123318140969133)
                ·
                  refine ⟨1667707573171244302863425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4447220195123318140969133 1667707573171244302863425)
                  ·
                    refine ⟨1250780679878433227147569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1667707573171244302863425 1250780679878433227147569)
                    ·
                      refine ⟨938085509908824920360677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250780679878433227147569 938085509908824920360677)
                      ·
                        rfl

theorem cell23_1826915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_1826915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826915 prefixEnd_1826915 := by exact prefixLift 1826915
  have htrace : WordTrace (prefixWord ++ tailWord_1826915) baseStart_1826915 baseEnd_1826915 := by
    simpa [prefixWord, tailWord_1826915, baseEnd_1826915] using wordTrace_append hprefix tailTrace_1826915
  have hstable : (prefixWord ++ tailWord_1826915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826915).length < 2 ^ (prefixWord ++ tailWord_1826915).sum := by decide
  have hdescent : baseEnd_1826915 < baseStart_1826915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826928 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4]
def baseStart_1826928 : Nat := 118140960795 + 1826928 * 2 ^ 59
def prefixEnd_1826928 : Nat := 4983230072969 + 3 ^ 40 * 1826928 * 2
def baseEnd_1826928 : Nat := 938092185157333369498117

theorem tailTrace_1826928 : CollatzResearch.WordTrace tailWord_1826928 prefixEnd_1826928 938092185157333369498117 := by
  unfold tailWord_1826928
  simp only [CollatzResearch.WordTrace]
  refine ⟨33316769162679672653384719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44422358883572896871179625 33316769162679672653384719)
  ·
    refine ⟨49975153744019508980077079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33316769162679672653384719 49975153744019508980077079)
    ·
      refine ⟨74962730616029263470115619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49975153744019508980077079 74962730616029263470115619)
      ·
        refine ⟨112444095924043895205173429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74962730616029263470115619 112444095924043895205173429)
        ·
          refine ⟨10541633992879115175485009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112444095924043895205173429 10541633992879115175485009)
          ·
            refine ⟨7906225494659336381613757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10541633992879115175485009 7906225494659336381613757)
            ·
              refine ⟨2964834560497251143105159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7906225494659336381613757 2964834560497251143105159)
              ·
                refine ⟨4447251840745876714657739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964834560497251143105159 4447251840745876714657739)
                ·
                  refine ⟨6670877761118815071986609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447251840745876714657739 6670877761118815071986609)
                  ·
                    refine ⟨5003158320839111303989957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6670877761118815071986609 5003158320839111303989957)
                    ·
                      refine ⟨938092185157333369498117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5003158320839111303989957 938092185157333369498117)
                      ·
                        rfl

theorem cell23_1826928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_1826928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826928 prefixEnd_1826928 := by exact prefixLift 1826928
  have htrace : WordTrace (prefixWord ++ tailWord_1826928) baseStart_1826928 baseEnd_1826928 := by
    simpa [prefixWord, tailWord_1826928, baseEnd_1826928] using wordTrace_append hprefix tailTrace_1826928
  have hstable : (prefixWord ++ tailWord_1826928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826928).length < 2 ^ (prefixWord ++ tailWord_1826928).sum := by decide
  have hdescent : baseEnd_1826928 < baseStart_1826928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826935 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_1826935 : Nat := 118140960795 + 1826935 * 2 ^ 59
def prefixEnd_1826935 : Nat := 4983230072969 + 3 ^ 40 * 1826935 * 2
def baseEnd_1826935 : Nat := 938095779521914842110585

theorem tailTrace_1826935 : CollatzResearch.WordTrace tailWord_1826935 prefixEnd_1826935 938095779521914842110585 := by
  unfold tailWord_1826935
  simp only [CollatzResearch.WordTrace]
  refine ⟨66633793636333985502274259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44422529090889323668182839 66633793636333985502274259)
  ·
    refine ⟨99950690454500978253411389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66633793636333985502274259 99950690454500978253411389)
    ·
      refine ⟨37481508920437866845029271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99950690454500978253411389 37481508920437866845029271)
      ·
        refine ⟨56222263380656800267543907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37481508920437866845029271 56222263380656800267543907)
        ·
          refine ⟨84333395070985200401315861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56222263380656800267543907 84333395070985200401315861)
          ·
            refine ⟨3953127893952431268811681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84333395070985200401315861 3953127893952431268811681)
            ·
              refine ⟨2964845920464323451608761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953127893952431268811681 2964845920464323451608761)
              ·
                refine ⟨2223634440348242588706571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964845920464323451608761 2223634440348242588706571)
                ·
                  refine ⟨3335451660522363883059857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223634440348242588706571 3335451660522363883059857)
                  ·
                    refine ⟨2501588745391772912294893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3335451660522363883059857 2501588745391772912294893)
                    ·
                      refine ⟨938095779521914842110585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501588745391772912294893 938095779521914842110585)
                      ·
                        rfl

theorem cell23_1826935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_1826935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826935 prefixEnd_1826935 := by exact prefixLift 1826935
  have htrace : WordTrace (prefixWord ++ tailWord_1826935) baseStart_1826935 baseEnd_1826935 := by
    simpa [prefixWord, tailWord_1826935, baseEnd_1826935] using wordTrace_append hprefix tailTrace_1826935
  have hstable : (prefixWord ++ tailWord_1826935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826935).length < 2 ^ (prefixWord ++ tailWord_1826935).sum := by decide
  have hdescent : baseEnd_1826935 < baseStart_1826935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826948 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1826948 : Nat := 118140960795 + 1826948 * 2 ^ 59
def prefixEnd_1826948 : Nat := 4983230072969 + 3 ^ 40 * 1826948 * 2
def baseEnd_1826948 : Nat := 938102454770423291248025

theorem tailTrace_1826948 : CollatzResearch.WordTrace tailWord_1826948 prefixEnd_1826948 938102454770423291248025 := by
  unfold tailWord_1826948
  simp only [CollatzResearch.WordTrace]
  refine ⟨33317133892643444361248749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44422845190191259148331665 33317133892643444361248749)
  ·
    refine ⟨12493925209741291635468281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33317133892643444361248749 12493925209741291635468281)
    ·
      refine ⟨9370443907305968726601211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12493925209741291635468281 9370443907305968726601211)
      ·
        refine ⟨14055665860958953089901817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370443907305968726601211 14055665860958953089901817)
        ·
          refine ⟨10541749395719214817426363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14055665860958953089901817 10541749395719214817426363)
          ·
            refine ⟨15812624093578822226139545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541749395719214817426363 15812624093578822226139545)
            ·
              refine ⟨11859468070184116669604659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15812624093578822226139545 11859468070184116669604659)
              ·
                refine ⟨17789202105276175004406989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859468070184116669604659 17789202105276175004406989)
                ·
                  refine ⟨6670950789478565626652621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17789202105276175004406989 6670950789478565626652621)
                  ·
                    refine ⟨2501606546054462109994733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6670950789478565626652621 2501606546054462109994733)
                    ·
                      refine ⟨938102454770423291248025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501606546054462109994733 938102454770423291248025)
                      ·
                        rfl

theorem cell23_1826948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1826948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826948 prefixEnd_1826948 := by exact prefixLift 1826948
  have htrace : WordTrace (prefixWord ++ tailWord_1826948) baseStart_1826948 baseEnd_1826948 := by
    simpa [prefixWord, tailWord_1826948, baseEnd_1826948] using wordTrace_append hprefix tailTrace_1826948
  have hstable : (prefixWord ++ tailWord_1826948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826948).length < 2 ^ (prefixWord ++ tailWord_1826948).sum := by decide
  have hdescent : baseEnd_1826948 < baseStart_1826948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826949 : List Nat := [1, 3, 1, 1, 5, 1, 3, 3, 1, 2, 2]
def baseStart_1826949 : Nat := 118140960795 + 1826949 * 2 ^ 59
def prefixEnd_1826949 : Nat := 4983230072969 + 3 ^ 40 * 1826949 * 2
def baseEnd_1826949 : Nat := 938102968251077787335521

theorem tailTrace_1826949 : CollatzResearch.WordTrace tailWord_1826949 prefixEnd_1826949 938102968251077787335521 := by
  unfold tailWord_1826949
  simp only [CollatzResearch.WordTrace]
  refine ⟨66634304258283265893283901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44422869505522177262189267 66634304258283265893283901)
  ·
    refine ⟨24987864096856224709981463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66634304258283265893283901 24987864096856224709981463)
    ·
      refine ⟨37481796145284337064972195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24987864096856224709981463 37481796145284337064972195)
      ·
        refine ⟨56222694217926505597458293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37481796145284337064972195 56222694217926505597458293)
        ·
          refine ⟨5270877582930609899761715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56222694217926505597458293 5270877582930609899761715)
          ·
            refine ⟨7906316374395914849642573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270877582930609899761715 7906316374395914849642573)
            ·
              refine ⟨2964868640398468068615965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7906316374395914849642573 2964868640398468068615965)
              ·
                refine ⟨1111825740149425525730987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2964868640398468068615965 1111825740149425525730987)
                ·
                  refine ⟨1667738610224138288596481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111825740149425525730987 1667738610224138288596481)
                  ·
                    refine ⟨1250803957668103716447361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1667738610224138288596481 1250803957668103716447361)
                    ·
                      refine ⟨938102968251077787335521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250803957668103716447361 938102968251077787335521)
                      ·
                        rfl

theorem cell23_1826949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_1826949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826949 prefixEnd_1826949 := by exact prefixLift 1826949
  have htrace : WordTrace (prefixWord ++ tailWord_1826949) baseStart_1826949 baseEnd_1826949 := by
    simpa [prefixWord, tailWord_1826949, baseEnd_1826949] using wordTrace_append hprefix tailTrace_1826949
  have hstable : (prefixWord ++ tailWord_1826949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826949).length < 2 ^ (prefixWord ++ tailWord_1826949).sum := by decide
  have hdescent : baseEnd_1826949 < baseStart_1826949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826965 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_1826965 : Nat := 118140960795 + 1826965 * 2 ^ 59
def prefixEnd_1826965 : Nat := 4983230072969 + 3 ^ 40 * 1826965 * 2
def baseEnd_1826965 : Nat := 938111183941549724735447

theorem tailTrace_1826965 : CollatzResearch.WordTrace tailWord_1826965 prefixEnd_1826965 938111183941549724735447 := by
  unfold tailWord_1826965
  simp only [CollatzResearch.WordTrace]
  refine ⟨66634887826225300625866349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44423258550816867083910899 66634887826225300625866349)
  ·
    refine ⟨24988082934834487734699881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66634887826225300625866349 24988082934834487734699881)
    ·
      refine ⟨18741062201125865801024911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24988082934834487734699881 18741062201125865801024911)
      ·
        refine ⟨28111593301688798701537367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18741062201125865801024911 28111593301688798701537367)
        ·
          refine ⟨42167389952533198052306051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28111593301688798701537367 42167389952533198052306051)
          ·
            refine ⟨63251084928799797078459077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42167389952533198052306051 63251084928799797078459077)
            ·
              refine ⟨11859578424149961952211077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63251084928799797078459077 11859578424149961952211077)
              ·
                refine ⟨2223670954528117866039577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11859578424149961952211077 2223670954528117866039577)
                ·
                  refine ⟨1667753215896088399529683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2223670954528117866039577 1667753215896088399529683)
                  ·
                    refine ⟨2501629823844132599294525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1667753215896088399529683 2501629823844132599294525)
                    ·
                      refine ⟨938111183941549724735447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501629823844132599294525 938111183941549724735447)
                      ·
                        rfl

theorem cell23_1826965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_1826965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826965 prefixEnd_1826965 := by exact prefixLift 1826965
  have htrace : WordTrace (prefixWord ++ tailWord_1826965) baseStart_1826965 baseEnd_1826965 := by
    simpa [prefixWord, tailWord_1826965, baseEnd_1826965] using wordTrace_append hprefix tailTrace_1826965
  have hstable : (prefixWord ++ tailWord_1826965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826965).length < 2 ^ (prefixWord ++ tailWord_1826965).sum := by decide
  have hdescent : baseEnd_1826965 < baseStart_1826965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826981 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_1826981 : Nat := 118140960795 + 1826981 * 2 ^ 59
def prefixEnd_1826981 : Nat := 4983230072969 + 3 ^ 40 * 1826981 * 2
def baseEnd_1826981 : Nat := 312706466544007220711791

theorem tailTrace_1826981 : CollatzResearch.WordTrace tailWord_1826981 prefixEnd_1826981 312706466544007220711791 := by
  unfold tailWord_1826981
  simp only [CollatzResearch.WordTrace]
  refine ⟨66635471394167335358448797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44423647596111556905632531 66635471394167335358448797)
  ·
    refine ⟨24988301772812750759418299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66635471394167335358448797 24988301772812750759418299)
    ·
      refine ⟨37482452659219126139127449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24988301772812750759418299 37482452659219126139127449)
      ·
        refine ⟨28111839494414344604345587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37482452659219126139127449 28111839494414344604345587)
        ·
          refine ⟨42167759241621516906518381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28111839494414344604345587 42167759241621516906518381)
          ·
            refine ⟨15812909715608068839944393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42167759241621516906518381 15812909715608068839944393)
            ·
              refine ⟨11859682286706051629958295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15812909715608068839944393 11859682286706051629958295)
              ·
                refine ⟨17789523430059077444937443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859682286706051629958295 17789523430059077444937443)
                ·
                  refine ⟨26684285145088616167406165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17789523430059077444937443 26684285145088616167406165)
                  ·
                    refine ⟨312706466544007220711791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26684285145088616167406165 312706466544007220711791)
                    ·
                      rfl

theorem cell23_1826981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_1826981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826981 prefixEnd_1826981 := by exact prefixLift 1826981
  have htrace : WordTrace (prefixWord ++ tailWord_1826981) baseStart_1826981 baseEnd_1826981 := by
    simpa [prefixWord, tailWord_1826981, baseEnd_1826981] using wordTrace_append hprefix tailTrace_1826981
  have hstable : (prefixWord ++ tailWord_1826981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826981).length < 2 ^ (prefixWord ++ tailWord_1826981).sum := by decide
  have hdescent : baseEnd_1826981 < baseStart_1826981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826986 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1826986 : Nat := 118140960795 + 1826986 * 2 ^ 59
def prefixEnd_1826986 : Nat := 4983230072969 + 3 ^ 40 * 1826986 * 2
def baseEnd_1826986 : Nat := 938121967035294142572851

theorem tailTrace_1826986 : CollatzResearch.WordTrace tailWord_1826986 prefixEnd_1826986 938121967035294142572851 := by
  unfold tailWord_1826986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16658913439787305303095203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44423769172766147474920541 16658913439787305303095203)
  ·
    refine ⟨24988370159680957954642805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16658913439787305303095203 24988370159680957954642805)
    ·
      refine ⟨2342659702470089808247763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24988370159680957954642805 2342659702470089808247763)
      ·
        refine ⟨3513989553705134712371645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342659702470089808247763 3513989553705134712371645)
        ·
          refine ⟨1317746082639425517139367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3513989553705134712371645 1317746082639425517139367)
          ·
            refine ⟨1976619123959138275709051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317746082639425517139367 1976619123959138275709051)
            ·
              refine ⟨2964928685938707413563577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976619123959138275709051 2964928685938707413563577)
              ·
                refine ⟨2223696514454030560172683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964928685938707413563577 2223696514454030560172683)
                ·
                  refine ⟨3335544771681045840259025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223696514454030560172683 3335544771681045840259025)
                  ·
                    refine ⟨2501658578760784380194269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3335544771681045840259025 2501658578760784380194269)
                    ·
                      refine ⟨938121967035294142572851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2501658578760784380194269 938121967035294142572851)
                      ·
                        rfl

theorem cell23_1826986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1826986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1826986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1826986 prefixEnd_1826986 := by exact prefixLift 1826986
  have htrace : WordTrace (prefixWord ++ tailWord_1826986) baseStart_1826986 baseEnd_1826986 := by
    simpa [prefixWord, tailWord_1826986, baseEnd_1826986] using wordTrace_append hprefix tailTrace_1826986
  have hstable : (prefixWord ++ tailWord_1826986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826986).length < 2 ^ (prefixWord ++ tailWord_1826986).sum := by decide
  have hdescent : baseEnd_1826986 < baseStart_1826986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827008 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1827008 : Nat := 118140960795 + 1827008 * 2 ^ 59
def prefixEnd_1827008 : Nat := 4983230072969 + 3 ^ 40 * 1827008 * 2
def baseEnd_1827008 : Nat := 938133263609693056497749

theorem tailTrace_1827008 : CollatzResearch.WordTrace tailWord_1827008 prefixEnd_1827008 938133263609693056497749 := by
  unfold tailWord_1827008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33318228082534759484840839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44424304110046345979787785 33318228082534759484840839)
  ·
    refine ⟨49977342123802139227261259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33318228082534759484840839 49977342123802139227261259)
    ·
      refine ⟨74966013185703208840891889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49977342123802139227261259 74966013185703208840891889)
      ·
        refine ⟨56224509889277406630668917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74966013185703208840891889 56224509889277406630668917)
        ·
          refine ⟨5271047802119756871625211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56224509889277406630668917 5271047802119756871625211)
          ·
            refine ⟨7906571703179635307437817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271047802119756871625211 7906571703179635307437817)
            ·
              refine ⟨5929928777384726480578363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7906571703179635307437817 5929928777384726480578363)
              ·
                refine ⟨8894893166077089720867545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5929928777384726480578363 8894893166077089720867545)
                ·
                  refine ⟨6671169874557817290650659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8894893166077089720867545 6671169874557817290650659)
                  ·
                    refine ⟨10006754811836725935975989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6671169874557817290650659 10006754811836725935975989)
                    ·
                      refine ⟨938133263609693056497749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10006754811836725935975989 938133263609693056497749)
                      ·
                        rfl

theorem cell23_1827008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1827008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827008 prefixEnd_1827008 := by exact prefixLift 1827008
  have htrace : WordTrace (prefixWord ++ tailWord_1827008) baseStart_1827008 baseEnd_1827008 := by
    simpa [prefixWord, tailWord_1827008, baseEnd_1827008] using wordTrace_append hprefix tailTrace_1827008
  have hstable : (prefixWord ++ tailWord_1827008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827008).length < 2 ^ (prefixWord ++ tailWord_1827008).sum := by decide
  have hdescent : baseEnd_1827008 < baseStart_1827008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827018 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_1827018 : Nat := 118140960795 + 1827018 * 2 ^ 59
def prefixEnd_1827018 : Nat := 4983230072969 + 3 ^ 40 * 1827018 * 2
def baseEnd_1827018 : Nat := 938138398416238017372703

theorem tailTrace_1827018 : CollatzResearch.WordTrace tailWord_1827018 prefixEnd_1827018 938138398416238017372703 := by
  unfold tailWord_1827018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659205223758322669386427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44424547263355527118363805 16659205223758322669386427)
  ·
    refine ⟨24988807835637484004079641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16659205223758322669386427 24988807835637484004079641)
    ·
      refine ⟨18741605876728113003059731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24988807835637484004079641 18741605876728113003059731)
      ·
        refine ⟨28112408815092169504589597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18741605876728113003059731 28112408815092169504589597)
        ·
          refine ⟨10542153305659563564221099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28112408815092169504589597 10542153305659563564221099)
          ·
            refine ⟨15813229958489345346331649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10542153305659563564221099 15813229958489345346331649)
            ·
              refine ⟨11859922468867009009748737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15813229958489345346331649 11859922468867009009748737)
              ·
                refine ⟨8894941851650256757311553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11859922468867009009748737 8894941851650256757311553)
                ·
                  refine ⟨6671206388737692567983665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8894941851650256757311553 6671206388737692567983665)
                  ·
                    refine ⟨5003404791553269425987749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6671206388737692567983665 5003404791553269425987749)
                    ·
                      refine ⟨938138398416238017372703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5003404791553269425987749 938138398416238017372703)
                      ·
                        rfl

theorem cell23_1827018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_1827018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827018 prefixEnd_1827018 := by exact prefixLift 1827018
  have htrace : WordTrace (prefixWord ++ tailWord_1827018) baseStart_1827018 baseEnd_1827018 := by
    simpa [prefixWord, tailWord_1827018, baseEnd_1827018] using wordTrace_append hprefix tailTrace_1827018
  have hstable : (prefixWord ++ tailWord_1827018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827018).length < 2 ^ (prefixWord ++ tailWord_1827018).sum := by decide
  have hdescent : baseEnd_1827018 < baseStart_1827018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827031 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1827031 : Nat := 118140960795 + 1827031 * 2 ^ 59
def prefixEnd_1827031 : Nat := 4983230072969 + 3 ^ 40 * 1827031 * 2
def baseEnd_1827031 : Nat := 938145073664746466510143

theorem tailTrace_1827031 : CollatzResearch.WordTrace tailWord_1827031 prefixEnd_1827031 938145073664746466510143 := by
  unfold tailWord_1827031
  simp only [CollatzResearch.WordTrace]
  refine ⟨66637295043986193897768947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44424863362657462598512631 66637295043986193897768947)
  ·
    refine ⟨99955942565979290846653421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66637295043986193897768947 99955942565979290846653421)
    ·
      refine ⟨37483478462242234067495033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99955942565979290846653421 37483478462242234067495033)
      ·
        refine ⟨28112608846681675550621275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37483478462242234067495033 28112608846681675550621275)
        ·
          refine ⟨42168913270022513325931913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28112608846681675550621275 42168913270022513325931913)
          ·
            refine ⟨31626684952516884994448935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42168913270022513325931913 31626684952516884994448935)
            ·
              refine ⟨47440027428775327491673403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31626684952516884994448935 47440027428775327491673403)
              ·
                refine ⟨71160041143162991237510105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47440027428775327491673403 71160041143162991237510105)
                ·
                  refine ⟨53370030857372243428132579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71160041143162991237510105 53370030857372243428132579)
                  ·
                    refine ⟨80055046286058365142198869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53370030857372243428132579 80055046286058365142198869)
                    ·
                      refine ⟨938145073664746466510143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 80055046286058365142198869 938145073664746466510143)
                      ·
                        rfl

theorem cell23_1827031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1827031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827031 prefixEnd_1827031 := by exact prefixLift 1827031
  have htrace : WordTrace (prefixWord ++ tailWord_1827031) baseStart_1827031 baseEnd_1827031 := by
    simpa [prefixWord, tailWord_1827031, baseEnd_1827031] using wordTrace_append hprefix tailTrace_1827031
  have hstable : (prefixWord ++ tailWord_1827031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827031).length < 2 ^ (prefixWord ++ tailWord_1827031).sum := by decide
  have hdescent : baseEnd_1827031 < baseStart_1827031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827105 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 3, 4]
def baseStart_1827105 : Nat := 118140960795 + 1827105 * 2 ^ 59
def prefixEnd_1827105 : Nat := 4983230072969 + 3 ^ 40 * 1827105 * 2
def baseEnd_1827105 : Nat := 312727690411059725661601

theorem tailTrace_1827105 : CollatzResearch.WordTrace tailWord_1827105 prefixEnd_1827105 312727690411059725661601 := by
  unfold tailWord_1827105
  simp only [CollatzResearch.WordTrace]
  refine ⟨66639994045718104535962769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44426662697145403023975179 66639994045718104535962769)
  ·
    refine ⟨49979995534288578401972077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66639994045718104535962769 49979995534288578401972077)
    ·
      refine ⟨18742498325358216900739529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49979995534288578401972077 18742498325358216900739529)
      ·
        refine ⟨14056873744018662675554647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18742498325358216900739529 14056873744018662675554647)
        ·
          refine ⟨21085310616027994013331971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14056873744018662675554647 21085310616027994013331971)
          ·
            refine ⟨31627965924041991019997957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21085310616027994013331971 31627965924041991019997957)
            ·
              refine ⟨5930243610757873316249617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31627965924041991019997957 5930243610757873316249617)
              ·
                refine ⟨4447682708068404987187213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5930243610757873316249617 4447682708068404987187213)
                ·
                  refine ⟨1667881015525651870195205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4447682708068404987187213 1667881015525651870195205)
                  ·
                    refine ⟨312727690411059725661601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667881015525651870195205 312727690411059725661601)
                    ·
                      rfl

theorem cell23_1827105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_1827105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827105 prefixEnd_1827105 := by exact prefixLift 1827105
  have htrace : WordTrace (prefixWord ++ tailWord_1827105) baseStart_1827105 baseEnd_1827105 := by
    simpa [prefixWord, tailWord_1827105, baseEnd_1827105] using wordTrace_append hprefix tailTrace_1827105
  have hstable : (prefixWord ++ tailWord_1827105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827105).length < 2 ^ (prefixWord ++ tailWord_1827105).sum := by decide
  have hdescent : baseEnd_1827105 < baseStart_1827105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827152 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 6]
def baseStart_1827152 : Nat := 118140960795 + 1827152 * 2 ^ 59
def prefixEnd_1827152 : Nat := 4983230072969 + 3 ^ 40 * 1827152 * 2
def baseEnd_1827152 : Nat := 104245244980437832566343

theorem tailTrace_1827152 : CollatzResearch.WordTrace tailWord_1827152 prefixEnd_1827152 104245244980437832566343 := by
  unfold tailWord_1827152
  simp only [CollatzResearch.WordTrace]
  refine ⟨33320854138273915781461855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44427805517698554375282473 33320854138273915781461855)
  ·
    refine ⟨49981281207410873672192783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33320854138273915781461855 49981281207410873672192783)
    ·
      refine ⟨74971921811116310508289175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49981281207410873672192783 74971921811116310508289175)
      ·
        refine ⟨112457882716674465762433763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74971921811116310508289175 112457882716674465762433763)
        ·
          refine ⟨168686824075011698643650645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112457882716674465762433763 168686824075011698643650645)
          ·
            refine ⟨1976798719629043343480281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 168686824075011698643650645 1976798719629043343480281)
            ·
              refine ⟨1482599039721782507610211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976798719629043343480281 1482599039721782507610211)
              ·
                refine ⟨2223898559582673761415317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482599039721782507610211 2223898559582673761415317)
                ·
                  refine ⟨104245244980437832566343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2223898559582673761415317 104245244980437832566343)
                  ·
                    rfl

theorem cell23_1827152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 6].length) (baseStart_1827152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827152 prefixEnd_1827152 := by exact prefixLift 1827152
  have htrace : WordTrace (prefixWord ++ tailWord_1827152) baseStart_1827152 baseEnd_1827152 := by
    simpa [prefixWord, tailWord_1827152, baseEnd_1827152] using wordTrace_append hprefix tailTrace_1827152
  have hstable : (prefixWord ++ tailWord_1827152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827152).length < 2 ^ (prefixWord ++ tailWord_1827152).sum := by decide
  have hdescent : baseEnd_1827152 < baseStart_1827152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827155 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 1, 5, 2]
def baseStart_1827155 : Nat := 118140960795 + 1827155 * 2 ^ 59
def prefixEnd_1827155 : Nat := 4983230072969 + 3 ^ 40 * 1827155 * 2
def baseEnd_1827155 : Nat := 938208745265903981359573

theorem tailTrace_1827155 : CollatzResearch.WordTrace tailWord_1827155 prefixEnd_1827155 938208745265903981359573 := by
  unfold tailWord_1827155
  simp only [CollatzResearch.WordTrace]
  refine ⟨66641817695536963075282919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44427878463691308716855279 66641817695536963075282919)
  ·
    refine ⟨99962726543305444612924379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66641817695536963075282919 99962726543305444612924379)
    ·
      refine ⟨149944089814958166919386569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99962726543305444612924379 149944089814958166919386569)
      ·
        refine ⟨112458067361218625189539927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149944089814958166919386569 112458067361218625189539927)
        ·
          refine ⟨168687101041827937784309891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112458067361218625189539927 168687101041827937784309891)
          ·
            refine ⟨253030651562741906676464837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168687101041827937784309891 253030651562741906676464837)
            ·
              refine ⟨47443247168014107501837157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253030651562741906676464837 47443247168014107501837157)
              ·
                refine ⟨8895608844002645156594467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47443247168014107501837157 8895608844002645156594467)
                ·
                  refine ⟨13343413266003967734891701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8895608844002645156594467 13343413266003967734891701)
                  ·
                    refine ⟨1250944993687871975146097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13343413266003967734891701 1250944993687871975146097)
                    ·
                      refine ⟨938208745265903981359573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250944993687871975146097 938208745265903981359573)
                      ·
                        rfl

theorem cell23_1827155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5, 2].length) (baseStart_1827155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827155 prefixEnd_1827155 := by exact prefixLift 1827155
  have htrace : WordTrace (prefixWord ++ tailWord_1827155) baseStart_1827155 baseEnd_1827155 := by
    simpa [prefixWord, tailWord_1827155, baseEnd_1827155] using wordTrace_append hprefix tailTrace_1827155
  have hstable : (prefixWord ++ tailWord_1827155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827155).length < 2 ^ (prefixWord ++ tailWord_1827155).sum := by decide
  have hdescent : baseEnd_1827155 < baseStart_1827155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827189 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_1827189 : Nat := 118140960795 + 1827189 * 2 ^ 59
def prefixEnd_1827189 : Nat := 4983230072969 + 3 ^ 40 * 1827189 * 2
def baseEnd_1827189 : Nat := 938226203608156848334417

theorem tailTrace_1827189 : CollatzResearch.WordTrace tailWord_1827189 prefixEnd_1827189 938226203608156848334417 := by
  unfold tailWord_1827189
  simp only [CollatzResearch.WordTrace]
  refine ⟨66643057777413786882020621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44428705184942524588013747 66643057777413786882020621)
  ·
    refine ⟨24991146666530170080757733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66643057777413786882020621 24991146666530170080757733)
    ·
      refine ⟨4685839999974406890142075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24991146666530170080757733 4685839999974406890142075)
      ·
        refine ⟨7028759999961610335213113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685839999974406890142075 7028759999961610335213113)
        ·
          refine ⟨5271569999971207751409835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7028759999961610335213113 5271569999971207751409835)
          ·
            refine ⟨7907354999956811627114753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271569999971207751409835 7907354999956811627114753)
            ·
              refine ⟨5930516249967608720336065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7907354999956811627114753 5930516249967608720336065)
              ·
                refine ⟨4447887187475706540252049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5930516249967608720336065 4447887187475706540252049)
                ·
                  refine ⟨3335915390606779905189037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447887187475706540252049 3335915390606779905189037)
                  ·
                    refine ⟨1250968271477542464445889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3335915390606779905189037 1250968271477542464445889)
                    ·
                      refine ⟨938226203608156848334417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1250968271477542464445889 938226203608156848334417)
                      ·
                        rfl

theorem cell23_1827189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_1827189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827189 prefixEnd_1827189 := by exact prefixLift 1827189
  have htrace : WordTrace (prefixWord ++ tailWord_1827189) baseStart_1827189 baseEnd_1827189 := by
    simpa [prefixWord, tailWord_1827189, baseEnd_1827189] using wordTrace_append hprefix tailTrace_1827189
  have hstable : (prefixWord ++ tailWord_1827189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827189).length < 2 ^ (prefixWord ++ tailWord_1827189).sum := by decide
  have hdescent : baseEnd_1827189 < baseStart_1827189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827190 : List Nat := [5, 1, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1827190 : Nat := 118140960795 + 1827190 * 2 ^ 59
def prefixEnd_1827190 : Nat := 4983230072969 + 3 ^ 40 * 1827190 * 2
def baseEnd_1827190 : Nat := 312742239029603781473971

theorem tailTrace_1827190 : CollatzResearch.WordTrace tailWord_1827190 prefixEnd_1827190 312742239029603781473971 := by
  unfold tailWord_1827190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165193390650635253300439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44428729500273442701871349 4165193390650635253300439)
  ·
    refine ⟨6247790085975952879950659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4165193390650635253300439 6247790085975952879950659)
    ·
      refine ⟨9371685128963929319925989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247790085975952879950659 9371685128963929319925989)
      ·
        refine ⟨1757190961680736747486123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9371685128963929319925989 1757190961680736747486123)
        ·
          refine ⟨2635786442521105121229185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757190961680736747486123 2635786442521105121229185)
          ·
            refine ⟨1976839831890828840921889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2635786442521105121229185 1976839831890828840921889)
            ·
              refine ⟨1482629873918121630691417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976839831890828840921889 1482629873918121630691417)
              ·
                refine ⟨1111972405438591223018563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482629873918121630691417 1111972405438591223018563)
                ·
                  refine ⟨1667958608157886834527845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111972405438591223018563 1667958608157886834527845)
                  ·
                    refine ⟨312742239029603781473971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667958608157886834527845 312742239029603781473971)
                    ·
                      rfl

theorem cell23_1827190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1827190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827190 prefixEnd_1827190 := by exact prefixLift 1827190
  have htrace : WordTrace (prefixWord ++ tailWord_1827190) baseStart_1827190 baseEnd_1827190 := by
    simpa [prefixWord, tailWord_1827190, baseEnd_1827190] using wordTrace_append hprefix tailTrace_1827190
  have hstable : (prefixWord ++ tailWord_1827190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827190).length < 2 ^ (prefixWord ++ tailWord_1827190).sum := by decide
  have hdescent : baseEnd_1827190 < baseStart_1827190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827212 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_1827212 : Nat := 118140960795 + 1827212 * 2 ^ 59
def prefixEnd_1827212 : Nat := 4983230072969 + 3 ^ 40 * 1827212 * 2
def baseEnd_1827212 : Nat := 312746004554403419448937

theorem tailTrace_1827212 : CollatzResearch.WordTrace tailWord_1827212 prefixEnd_1827212 312746004554403419448937 := by
  unfold tailWord_1827212
  simp only [CollatzResearch.WordTrace]
  refine ⟨33321948328165230905053945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44429264437553641206738593 33321948328165230905053945)
  ·
    refine ⟨24991461246123923178790459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33321948328165230905053945 24991461246123923178790459)
    ·
      refine ⟨37487191869185884768185689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24991461246123923178790459 37487191869185884768185689)
      ·
        refine ⟨28115393901889413576139267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37487191869185884768185689 28115393901889413576139267)
        ·
          refine ⟨42173090852834120364208901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28115393901889413576139267 42173090852834120364208901)
          ·
            refine ⟨7907454534906397568289169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42173090852834120364208901 7907454534906397568289169)
            ·
              refine ⟨5930590901179798176216877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7907454534906397568289169 5930590901179798176216877)
              ·
                refine ⟨2223971587942424316081329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5930590901179798176216877 2223971587942424316081329)
                ·
                  refine ⟨1667978690956818237060997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2223971587942424316081329 1667978690956818237060997)
                  ·
                    refine ⟨312746004554403419448937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667978690956818237060997 312746004554403419448937)
                    ·
                      rfl

theorem cell23_1827212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_1827212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827212 prefixEnd_1827212 := by exact prefixLift 1827212
  have htrace : WordTrace (prefixWord ++ tailWord_1827212) baseStart_1827212 baseEnd_1827212 := by
    simpa [prefixWord, tailWord_1827212, baseEnd_1827212] using wordTrace_append hprefix tailTrace_1827212
  have hstable : (prefixWord ++ tailWord_1827212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827212).length < 2 ^ (prefixWord ++ tailWord_1827212).sum := by decide
  have hdescent : baseEnd_1827212 < baseStart_1827212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827225 : List Nat := [1, 2, 1, 2, 1, 4, 5, 7]
def baseStart_1827225 : Nat := 118140960795 + 1827225 * 2 ^ 59
def prefixEnd_1827225 : Nat := 4983230072969 + 3 ^ 40 * 1827225 * 2
def baseEnd_1827225 : Nat := 34749803293026618795713

theorem tailTrace_1827225 : CollatzResearch.WordTrace tailWord_1827225 prefixEnd_1827225 34749803293026618795713 := by
  unfold tailWord_1827225
  simp only [CollatzResearch.WordTrace]
  refine ⟨66644370805283365030331129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44429580536855576686887419 66644370805283365030331129)
  ·
    refine ⟨49983278103962523772748347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66644370805283365030331129 49983278103962523772748347)
    ·
      refine ⟨74974917155943785659122521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49983278103962523772748347 74974917155943785659122521)
      ·
        refine ⟨56231187866957839244341891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74974917155943785659122521 56231187866957839244341891)
        ·
          refine ⟨84346781800436758866512837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56231187866957839244341891 84346781800436758866512837)
          ·
            refine ⟨15815021587581892287471157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84346781800436758866512837 15815021587581892287471157)
            ·
              refine ⟨1482658273835802401950421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15815021587581892287471157 1482658273835802401950421)
              ·
                refine ⟨34749803293026618795713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1482658273835802401950421 34749803293026618795713)
                ·
                  rfl

theorem cell23_1827225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 7].length) (baseStart_1827225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827225 prefixEnd_1827225 := by exact prefixLift 1827225
  have htrace : WordTrace (prefixWord ++ tailWord_1827225) baseStart_1827225 baseEnd_1827225 := by
    simpa [prefixWord, tailWord_1827225, baseEnd_1827225] using wordTrace_append hprefix tailTrace_1827225
  have hstable : (prefixWord ++ tailWord_1827225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827225).length < 2 ^ (prefixWord ++ tailWord_1827225).sum := by decide
  have hdescent : baseEnd_1827225 < baseStart_1827225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827233 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 1, 5]
def baseStart_1827233 : Nat := 118140960795 + 1827233 * 2 ^ 59
def prefixEnd_1827233 : Nat := 4983230072969 + 3 ^ 40 * 1827233 * 2
def baseEnd_1827233 : Nat := 312749598918984892061405

theorem tailTrace_1827233 : CollatzResearch.WordTrace tailWord_1827233 prefixEnd_1827233 312749598918984892061405 := by
  unfold tailWord_1827233
  simp only [CollatzResearch.WordTrace]
  refine ⟨66644662589254382396622353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44429775059502921597748235 66644662589254382396622353)
  ·
    refine ⟨49983496941940786797466765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66644662589254382396622353 49983496941940786797466765)
    ·
      refine ⟨18743811353227795049050037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49983496941940786797466765 18743811353227795049050037)
      ·
        refine ⟨1757232314365105785848441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18743811353227795049050037 1757232314365105785848441)
        ·
          refine ⟨1317924235773829339386331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1757232314365105785848441 1317924235773829339386331)
          ·
            refine ⟨1976886353660744009079497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317924235773829339386331 1976886353660744009079497)
            ·
              refine ⟨1482664765245558006809623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1976886353660744009079497 1482664765245558006809623)
              ·
                refine ⟨2223997147868337010214435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482664765245558006809623 2223997147868337010214435)
                ·
                  refine ⟨3335995721802505515321653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223997147868337010214435 3335995721802505515321653)
                  ·
                    refine ⟨312749598918984892061405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3335995721802505515321653 312749598918984892061405)
                    ·
                      rfl

theorem cell23_1827233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_1827233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827233 prefixEnd_1827233 := by exact prefixLift 1827233
  have htrace : WordTrace (prefixWord ++ tailWord_1827233) baseStart_1827233 baseEnd_1827233 := by
    simpa [prefixWord, tailWord_1827233, baseEnd_1827233] using wordTrace_append hprefix tailTrace_1827233
  have hstable : (prefixWord ++ tailWord_1827233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827233).length < 2 ^ (prefixWord ++ tailWord_1827233).sum := by decide
  have hdescent : baseEnd_1827233 < baseStart_1827233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827236 : List Nat := [2, 3, 1, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_1827236 : Nat := 118140960795 + 1827236 * 2 ^ 59
def prefixEnd_1827236 : Nat := 4983230072969 + 3 ^ 40 * 1827236 * 2
def baseEnd_1827236 : Nat := 938250337198918164446701

theorem tailTrace_1827236 : CollatzResearch.WordTrace tailWord_1827236 prefixEnd_1827236 938250337198918164446701 := by
  unfold tailWord_1827236
  simp only [CollatzResearch.WordTrace]
  refine ⟨33322386004121756954490781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44429848005495675939321041 33322386004121756954490781)
  ·
    refine ⟨12495894751545658857934043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33322386004121756954490781 12495894751545658857934043)
    ·
      refine ⟨18743842127318488286901065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12495894751545658857934043 18743842127318488286901065)
      ·
        refine ⟨14057881595488866215175799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18743842127318488286901065 14057881595488866215175799)
        ·
          refine ⟨21086822393233299322763699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14057881595488866215175799 21086822393233299322763699)
          ·
            refine ⟨31630233589849948984145549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21086822393233299322763699 31630233589849948984145549)
            ·
              refine ⟨11861337596193730869054581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31630233589849948984145549 11861337596193730869054581)
              ·
                refine ⟨1112000399643162268973867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11861337596193730869054581 1112000399643162268973867)
                ·
                  refine ⟨1668000599464743403460801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112000399643162268973867 1668000599464743403460801)
                  ·
                    refine ⟨1251000449598557552595601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1668000599464743403460801 1251000449598557552595601)
                    ·
                      refine ⟨938250337198918164446701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251000449598557552595601 938250337198918164446701)
                      ·
                        rfl

theorem cell23_1827236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_1827236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827236 prefixEnd_1827236 := by exact prefixLift 1827236
  have htrace : WordTrace (prefixWord ++ tailWord_1827236) baseStart_1827236 baseEnd_1827236 := by
    simpa [prefixWord, tailWord_1827236, baseEnd_1827236] using wordTrace_append hprefix tailTrace_1827236
  have hstable : (prefixWord ++ tailWord_1827236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827236).length < 2 ^ (prefixWord ++ tailWord_1827236).sum := by decide
  have hdescent : baseEnd_1827236 < baseStart_1827236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827239 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1827239 : Nat := 118140960795 + 1827239 * 2 ^ 59
def prefixEnd_1827239 : Nat := 4983230072969 + 3 ^ 40 * 1827239 * 2
def baseEnd_1827239 : Nat := 938251877640881652709187

theorem tailTrace_1827239 : CollatzResearch.WordTrace tailWord_1827239 prefixEnd_1827239 938251877640881652709187 := by
  unfold tailWord_1827239
  simp only [CollatzResearch.WordTrace]
  refine ⟨66644881427232645421340771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44429920951488430280893847 66644881427232645421340771)
  ·
    refine ⟨99967322140848968132011157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66644881427232645421340771 99967322140848968132011157)
    ·
      refine ⟨4685968225352295381188023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99967322140848968132011157 4685968225352295381188023)
      ·
        refine ⟨7028952338028443071782035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685968225352295381188023 7028952338028443071782035)
        ·
          refine ⟨10543428507042664607673053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028952338028443071782035 10543428507042664607673053)
          ·
            refine ⟨3953785690140999227877395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10543428507042664607673053 3953785690140999227877395)
            ·
              refine ⟨5930678535211498841816093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953785690140999227877395 5930678535211498841816093)
              ·
                refine ⟨2224004450704312065681035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5930678535211498841816093 2224004450704312065681035)
                ·
                  refine ⟨3336006676056468098521553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224004450704312065681035 3336006676056468098521553)
                  ·
                    refine ⟨2502005007042351073891165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3336006676056468098521553 2502005007042351073891165)
                    ·
                      refine ⟨938251877640881652709187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2502005007042351073891165 938251877640881652709187)
                      ·
                        rfl

theorem cell23_1827239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1827239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827239 prefixEnd_1827239 := by exact prefixLift 1827239
  have htrace : WordTrace (prefixWord ++ tailWord_1827239) baseStart_1827239 baseEnd_1827239 := by
    simpa [prefixWord, tailWord_1827239, baseEnd_1827239] using wordTrace_append hprefix tailTrace_1827239
  have hstable : (prefixWord ++ tailWord_1827239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827239).length < 2 ^ (prefixWord ++ tailWord_1827239).sum := by decide
  have hdescent : baseEnd_1827239 < baseStart_1827239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827295 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1827295 : Nat := 118140960795 + 1827295 * 2 ^ 59
def prefixEnd_1827295 : Nat := 4983230072969 + 3 ^ 40 * 1827295 * 2
def baseEnd_1827295 : Nat := 938280632557533433608929

theorem tailTrace_1827295 : CollatzResearch.WordTrace tailWord_1827295 prefixEnd_1827295 938280632557533433608929 := by
  unfold tailWord_1827295
  simp only [CollatzResearch.WordTrace]
  refine ⟨66646923915029766985379339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44431282610019844656919559 66646923915029766985379339)
  ·
    refine ⟨99970385872544650478069009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66646923915029766985379339 99970385872544650478069009)
    ·
      refine ⟨74977789404408487858551757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99970385872544650478069009 74977789404408487858551757)
      ·
        refine ⟨28116671026653182946956909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74977789404408487858551757 28116671026653182946956909)
        ·
          refine ⟨10543751634994943605108841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28116671026653182946956909 10543751634994943605108841)
          ·
            refine ⟨7907813726246207703831631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10543751634994943605108841 7907813726246207703831631)
            ·
              refine ⟨11861720589369311555747447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907813726246207703831631 11861720589369311555747447)
              ·
                refine ⟨17792580884053967333621171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11861720589369311555747447 17792580884053967333621171)
                ·
                  refine ⟨26688871326080951000431757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17792580884053967333621171 26688871326080951000431757)
                  ·
                    refine ⟨10008326747280356625161909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26688871326080951000431757 10008326747280356625161909)
                    ·
                      refine ⟨938280632557533433608929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10008326747280356625161909 938280632557533433608929)
                      ·
                        rfl

theorem cell23_1827295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1827295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827295 prefixEnd_1827295 := by exact prefixLift 1827295
  have htrace : WordTrace (prefixWord ++ tailWord_1827295) baseStart_1827295 baseEnd_1827295 := by
    simpa [prefixWord, tailWord_1827295, baseEnd_1827295] using wordTrace_append hprefix tailTrace_1827295
  have hstable : (prefixWord ++ tailWord_1827295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827295).length < 2 ^ (prefixWord ++ tailWord_1827295).sum := by decide
  have hdescent : baseEnd_1827295 < baseStart_1827295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827305 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_1827305 : Nat := 118140960795 + 1827305 * 2 ^ 59
def prefixEnd_1827305 : Nat := 4983230072969 + 3 ^ 40 * 1827305 * 2
def baseEnd_1827305 : Nat := 938285767364078394483883

theorem tailTrace_1827305 : CollatzResearch.WordTrace tailWord_1827305 prefixEnd_1827305 938285767364078394483883 := by
  unfold tailWord_1827305
  simp only [CollatzResearch.WordTrace]
  refine ⟨66647288644993538693243369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44431525763329025795495579 66647288644993538693243369)
  ·
    refine ⟨49985466483745154019932527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66647288644993538693243369 49985466483745154019932527)
    ·
      refine ⟨74978199725617731029898791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49985466483745154019932527 74978199725617731029898791)
      ·
        refine ⟨112467299588426596544848187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74978199725617731029898791 112467299588426596544848187)
        ·
          refine ⟨168700949382639894817272281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112467299588426596544848187 168700949382639894817272281)
          ·
            refine ⟨126525712036979921112954211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168700949382639894817272281 126525712036979921112954211)
            ·
              refine ⟨189788568055469881669431317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126525712036979921112954211 189788568055469881669431317)
              ·
                refine ⟨8896339127600150703254593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189788568055469881669431317 8896339127600150703254593)
                ·
                  refine ⟨6672254345700113027440945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8896339127600150703254593 6672254345700113027440945)
                  ·
                    refine ⟨5004190759275084770580709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672254345700113027440945 5004190759275084770580709)
                    ·
                      refine ⟨938285767364078394483883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5004190759275084770580709 938285767364078394483883)
                      ·
                        rfl

theorem cell23_1827305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_1827305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827305 prefixEnd_1827305 := by exact prefixLift 1827305
  have htrace : WordTrace (prefixWord ++ tailWord_1827305) baseStart_1827305 baseEnd_1827305 := by
    simpa [prefixWord, tailWord_1827305, baseEnd_1827305] using wordTrace_append hprefix tailTrace_1827305
  have hstable : (prefixWord ++ tailWord_1827305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827305).length < 2 ^ (prefixWord ++ tailWord_1827305).sum := by decide
  have hdescent : baseEnd_1827305 < baseStart_1827305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827330 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1827330 : Nat := 118140960795 + 1827330 * 2 ^ 59
def prefixEnd_1827330 : Nat := 4983230072969 + 3 ^ 40 * 1827330 * 2
def baseEnd_1827330 : Nat := 938298604380440796671269

theorem tailTrace_1827330 : CollatzResearch.WordTrace tailWord_1827330 prefixEnd_1827330 938298604380440796671269 := by
  unfold tailWord_1827330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662050117475741990725861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44432133646601978641935629 16662050117475741990725861)
  ·
    refine ⟨3124134397026701623261099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16662050117475741990725861 3124134397026701623261099)
    ·
      refine ⟨4686201595540052434891649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124134397026701623261099 4686201595540052434891649)
      ·
        refine ⟨3514651196655039326168737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4686201595540052434891649 3514651196655039326168737)
        ·
          refine ⟨2635988397491279494626553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514651196655039326168737 2635988397491279494626553)
          ·
            refine ⟨1976991298118459620969915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2635988397491279494626553 1976991298118459620969915)
            ·
              refine ⟨2965486947177689431454873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976991298118459620969915 2965486947177689431454873)
              ·
                refine ⟨2224115210383267073591155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965486947177689431454873 2224115210383267073591155)
                ·
                  refine ⟨3336172815574900610386733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224115210383267073591155 3336172815574900610386733)
                  ·
                    refine ⟨1251064805840587728895025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3336172815574900610386733 1251064805840587728895025)
                    ·
                      refine ⟨938298604380440796671269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251064805840587728895025 938298604380440796671269)
                      ·
                        rfl

theorem cell23_1827330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1827330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827330 prefixEnd_1827330 := by exact prefixLift 1827330
  have htrace : WordTrace (prefixWord ++ tailWord_1827330) baseStart_1827330 baseEnd_1827330 := by
    simpa [prefixWord, tailWord_1827330, baseEnd_1827330] using wordTrace_append hprefix tailTrace_1827330
  have hstable : (prefixWord ++ tailWord_1827330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827330).length < 2 ^ (prefixWord ++ tailWord_1827330).sum := by decide
  have hdescent : baseEnd_1827330 < baseStart_1827330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827373 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1827373 : Nat := 118140960795 + 1827373 * 2 ^ 59
def prefixEnd_1827373 : Nat := 4983230072969 + 3 ^ 40 * 1827373 * 2
def baseEnd_1827373 : Nat := 938320684048584128433571

theorem tailTrace_1827373 : CollatzResearch.WordTrace tailWord_1827373 prefixEnd_1827373 938320684048584128433571 := by
  unfold tailWord_1827373
  simp only [CollatzResearch.WordTrace]
  refine ⟨66649768808747186306718773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44433179205831457537812515 66649768808747186306718773)
  ·
    refine ⟨6248415825820048716254885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66649768808747186306718773 6248415825820048716254885)
    ·
      refine ⟨1171577967341259134297791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6248415825820048716254885 1171577967341259134297791)
      ·
        refine ⟨1757366951011888701446687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171577967341259134297791 1757366951011888701446687)
        ·
          refine ⟨2636050426517833052170031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757366951011888701446687 2636050426517833052170031)
          ·
            refine ⟨3954075639776749578255047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636050426517833052170031 3954075639776749578255047)
            ·
              refine ⟨5931113459665124367382571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954075639776749578255047 5931113459665124367382571)
              ·
                refine ⟨8896670189497686551073857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931113459665124367382571 8896670189497686551073857)
                ·
                  refine ⟨6672502642123264913305393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8896670189497686551073857 6672502642123264913305393)
                  ·
                    refine ⟨5004376981592448684979045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672502642123264913305393 5004376981592448684979045)
                    ·
                      refine ⟨938320684048584128433571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5004376981592448684979045 938320684048584128433571)
                      ·
                        rfl

theorem cell23_1827373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1827373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827373 prefixEnd_1827373 := by exact prefixLift 1827373
  have htrace : WordTrace (prefixWord ++ tailWord_1827373) baseStart_1827373 baseEnd_1827373 := by
    simpa [prefixWord, tailWord_1827373, baseEnd_1827373] using wordTrace_append hprefix tailTrace_1827373
  have hstable : (prefixWord ++ tailWord_1827373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827373).length < 2 ^ (prefixWord ++ tailWord_1827373).sum := by decide
  have hdescent : baseEnd_1827373 < baseStart_1827373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827392 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 5, 4]
def baseStart_1827392 : Nat := 118140960795 + 1827392 * 2 ^ 59
def prefixEnd_1827392 : Nat := 4983230072969 + 3 ^ 40 * 1827392 * 2
def baseEnd_1827392 : Nat := 312776813393673184698661

theorem tailTrace_1827392 : CollatzResearch.WordTrace tailWord_1827392 prefixEnd_1827392 312776813393673184698661 := by
  unfold tailWord_1827392
  simp only [CollatzResearch.WordTrace]
  refine ⟨33325230897839176275830215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44433641197118901701106953 33325230897839176275830215)
  ·
    refine ⟨49987846346758764413745323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33325230897839176275830215 49987846346758764413745323)
    ·
      refine ⟨74981769520138146620617985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49987846346758764413745323 74981769520138146620617985)
      ·
        refine ⟨56236327140103609965463489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74981769520138146620617985 56236327140103609965463489)
        ·
          refine ⟨42177245355077707474097617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56236327140103609965463489 42177245355077707474097617)
          ·
            refine ⟨31632934016308280605573213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42177245355077707474097617 31632934016308280605573213)
            ·
              refine ⟨11862350256115605227089955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31632934016308280605573213 11862350256115605227089955)
              ·
                refine ⟨17793525384173407840634933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11862350256115605227089955 17793525384173407840634933)
                ·
                  refine ⟨1668143004766256985059525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17793525384173407840634933 1668143004766256985059525)
                  ·
                    refine ⟨312776813393673184698661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668143004766256985059525 312776813393673184698661)
                    ·
                      rfl

theorem cell23_1827392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_1827392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827392 prefixEnd_1827392 := by exact prefixLift 1827392
  have htrace : WordTrace (prefixWord ++ tailWord_1827392) baseStart_1827392 baseEnd_1827392 := by
    simpa [prefixWord, tailWord_1827392, baseEnd_1827392] using wordTrace_append hprefix tailTrace_1827392
  have hstable : (prefixWord ++ tailWord_1827392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827392).length < 2 ^ (prefixWord ++ tailWord_1827392).sum := by decide
  have hdescent : baseEnd_1827392 < baseStart_1827392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827395 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6]
def baseStart_1827395 : Nat := 118140960795 + 1827395 * 2 ^ 59
def prefixEnd_1827395 : Nat := 4983230072969 + 3 ^ 40 * 1827395 * 2
def baseEnd_1827395 : Nat := 938331980622983042358469

theorem tailTrace_1827395 : CollatzResearch.WordTrace tailWord_1827395 prefixEnd_1827395 938331980622983042358469 := by
  unfold tailWord_1827395
  simp only [CollatzResearch.WordTrace]
  refine ⟨66650571214667484064019639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44433714143111656042679759 66650571214667484064019639)
  ·
    refine ⟨99975856822001226096029459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66650571214667484064019639 99975856822001226096029459)
    ·
      refine ⟨149963785233001839144044189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99975856822001226096029459 149963785233001839144044189)
      ·
        refine ⟨56236419462375689679016571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149963785233001839144044189 56236419462375689679016571)
        ·
          refine ⟨84354629193563534518524857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56236419462375689679016571 84354629193563534518524857)
          ·
            refine ⟨63265971895172650888893643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84354629193563534518524857 63265971895172650888893643)
            ·
              refine ⟨94898957842758976333340465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63265971895172650888893643 94898957842758976333340465)
              ·
                refine ⟨71174218382069232250005349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94898957842758976333340465 71174218382069232250005349)
                ·
                  refine ⟨13345165946637981046876003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71174218382069232250005349 13345165946637981046876003)
                  ·
                    refine ⟨20017748919956971570314005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13345165946637981046876003 20017748919956971570314005)
                    ·
                      refine ⟨938331980622983042358469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20017748919956971570314005 938331980622983042358469)
                      ·
                        rfl

theorem cell23_1827395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_1827395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827395 prefixEnd_1827395 := by exact prefixLift 1827395
  have htrace : WordTrace (prefixWord ++ tailWord_1827395) baseStart_1827395 baseEnd_1827395 := by
    simpa [prefixWord, tailWord_1827395, baseEnd_1827395] using wordTrace_append hprefix tailTrace_1827395
  have hstable : (prefixWord ++ tailWord_1827395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827395).length < 2 ^ (prefixWord ++ tailWord_1827395).sum := by decide
  have hdescent : baseEnd_1827395 < baseStart_1827395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827399 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_1827399 : Nat := 118140960795 + 1827399 * 2 ^ 59
def prefixEnd_1827399 : Nat := 4983230072969 + 3 ^ 40 * 1827399 * 2
def baseEnd_1827399 : Nat := 938334034545601026708451

theorem tailTrace_1827399 : CollatzResearch.WordTrace tailWord_1827399 prefixEnd_1827399 938334034545601026708451 := by
  unfold tailWord_1827399
  simp only [CollatzResearch.WordTrace]
  refine ⟨66650717106652992747165251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44433811404435328498110167 66650717106652992747165251)
  ·
    refine ⟨99976075659979489120747877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66650717106652992747165251 99976075659979489120747877)
    ·
      refine ⟨18745514186246154210140227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99976075659979489120747877 18745514186246154210140227)
      ·
        refine ⟨28118271279369231315210341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18745514186246154210140227 28118271279369231315210341)
        ·
          refine ⟨5272175864881730871601939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28118271279369231315210341 5272175864881730871601939)
          ·
            refine ⟨7908263797322596307402909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272175864881730871601939 7908263797322596307402909)
            ·
              refine ⟨2965598923995973615276091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7908263797322596307402909 2965598923995973615276091)
              ·
                refine ⟨4448398385993960422914137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965598923995973615276091 4448398385993960422914137)
                ·
                  refine ⟨3336298789495470317185603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4448398385993960422914137 3336298789495470317185603)
                  ·
                    refine ⟨5004448184243205475778405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3336298789495470317185603 5004448184243205475778405)
                    ·
                      refine ⟨938334034545601026708451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5004448184243205475778405 938334034545601026708451)
                      ·
                        rfl

theorem cell23_1827399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_1827399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827399 prefixEnd_1827399 := by exact prefixLift 1827399
  have htrace : WordTrace (prefixWord ++ tailWord_1827399) baseStart_1827399 baseEnd_1827399 := by
    simpa [prefixWord, tailWord_1827399, baseEnd_1827399] using wordTrace_append hprefix tailTrace_1827399
  have hstable : (prefixWord ++ tailWord_1827399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827399).length < 2 ^ (prefixWord ++ tailWord_1827399).sum := by decide
  have hdescent : baseEnd_1827399 < baseStart_1827399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827412 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1827412 : Nat := 118140960795 + 1827412 * 2 ^ 59
def prefixEnd_1827412 : Nat := 4983230072969 + 3 ^ 40 * 1827412 * 2
def baseEnd_1827412 : Nat := 938340709794109475845891

theorem tailTrace_1827412 : CollatzResearch.WordTrace tailWord_1827412 prefixEnd_1827412 938340709794109475845891 := by
  unfold tailWord_1827412
  simp only [CollatzResearch.WordTrace]
  refine ⟨33325595627802947983694245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44434127503737263978258993 33325595627802947983694245)
  ·
    refine ⟨6248549180213052746942671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33325595627802947983694245 6248549180213052746942671)
    ·
      refine ⟨9372823770319579120414007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6248549180213052746942671 9372823770319579120414007)
      ·
        refine ⟨14059235655479368680621011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9372823770319579120414007 14059235655479368680621011)
        ·
          refine ⟨21088853483219053020931517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059235655479368680621011 21088853483219053020931517)
          ·
            refine ⟨7908320056207144882849319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21088853483219053020931517 7908320056207144882849319)
            ·
              refine ⟨11862480084310717324273979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908320056207144882849319 11862480084310717324273979)
              ·
                refine ⟨17793720126466075986410969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11862480084310717324273979 17793720126466075986410969)
                ·
                  refine ⟨13345290094849556989808227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17793720126466075986410969 13345290094849556989808227)
                  ·
                    refine ⟨20017935142274335484712341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13345290094849556989808227 20017935142274335484712341)
                    ·
                      refine ⟨938340709794109475845891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20017935142274335484712341 938340709794109475845891)
                      ·
                        rfl

theorem cell23_1827412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1827412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827412 prefixEnd_1827412 := by exact prefixLift 1827412
  have htrace : WordTrace (prefixWord ++ tailWord_1827412) baseStart_1827412 baseEnd_1827412 := by
    simpa [prefixWord, tailWord_1827412, baseEnd_1827412] using wordTrace_append hprefix tailTrace_1827412
  have hstable : (prefixWord ++ tailWord_1827412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827412).length < 2 ^ (prefixWord ++ tailWord_1827412).sum := by decide
  have hdescent : baseEnd_1827412 < baseStart_1827412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827435 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 9]
def baseStart_1827435 : Nat := 118140960795 + 1827435 * 2 ^ 59
def prefixEnd_1827435 : Nat := 4983230072969 + 3 ^ 40 * 1827435 * 2
def baseEnd_1827435 : Nat := 312784173283054295286095

theorem tailTrace_1827435 : CollatzResearch.WordTrace tailWord_1827435 prefixEnd_1827435 312784173283054295286095 := by
  unfold tailWord_1827435
  simp only [CollatzResearch.WordTrace]
  refine ⟨66652030134522570895475759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44434686756348380596983839 66652030134522570895475759)
  ·
    refine ⟨99978045201783856343213639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66652030134522570895475759 99978045201783856343213639)
    ·
      refine ⟨149967067802675784514820459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99978045201783856343213639 149967067802675784514820459)
      ·
        refine ⟨224950601704013676772230689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149967067802675784514820459 224950601704013676772230689)
        ·
          refine ⟨168712951278010257579173017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224950601704013676772230689 168712951278010257579173017)
          ·
            refine ⟨126534713458507693184379763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168712951278010257579173017 126534713458507693184379763)
            ·
              refine ⟨189802070187761539776569645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126534713458507693184379763 189802070187761539776569645)
              ·
                refine ⟨71175776320410577416213617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189802070187761539776569645 71175776320410577416213617)
                ·
                  refine ⟨53381832240307933062160213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71175776320410577416213617 53381832240307933062160213)
                  ·
                    refine ⟨312784173283054295286095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 53381832240307933062160213 312784173283054295286095)
                    ·
                      rfl

theorem cell23_1827435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_1827435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827435 prefixEnd_1827435 := by exact prefixLift 1827435
  have htrace : WordTrace (prefixWord ++ tailWord_1827435) baseStart_1827435 baseEnd_1827435 := by
    simpa [prefixWord, tailWord_1827435, baseEnd_1827435] using wordTrace_append hprefix tailTrace_1827435
  have hstable : (prefixWord ++ tailWord_1827435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827435).length < 2 ^ (prefixWord ++ tailWord_1827435).sum := by decide
  have hdescent : baseEnd_1827435 < baseStart_1827435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827452 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_1827452 : Nat := 118140960795 + 1827452 * 2 ^ 59
def prefixEnd_1827452 : Nat := 4983230072969 + 3 ^ 40 * 1827452 * 2
def baseEnd_1827452 : Nat := 312787083006763106448569

theorem tailTrace_1827452 : CollatzResearch.WordTrace tailWord_1827452 prefixEnd_1827452 312787083006763106448569 := by
  unfold tailWord_1827452
  simp only [CollatzResearch.WordTrace]
  refine ⟨33326325087730491399422305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44435100116973988532563073 33326325087730491399422305)
  ·
    refine ⟨24994743815797868549566729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33326325087730491399422305 24994743815797868549566729)
    ·
      refine ⟨18746057861848401412175047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24994743815797868549566729 18746057861848401412175047)
      ·
        refine ⟨28119086792772602118262571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18746057861848401412175047 28119086792772602118262571)
        ·
          refine ⟨42178630189158903177393857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28119086792772602118262571 42178630189158903177393857)
          ·
            refine ⟨31633972641869177383045393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42178630189158903177393857 31633972641869177383045393)
            ·
              refine ⟨23725479481401883037284045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31633972641869177383045393 23725479481401883037284045)
              ·
                refine ⟨8897054805525706138981517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23725479481401883037284045 8897054805525706138981517)
                ·
                  refine ⟨3336395552072139802118069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8897054805525706138981517 3336395552072139802118069)
                  ·
                    refine ⟨312787083006763106448569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3336395552072139802118069 312787083006763106448569)
                    ·
                      rfl

theorem cell23_1827452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_1827452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827452 prefixEnd_1827452 := by exact prefixLift 1827452
  have htrace : WordTrace (prefixWord ++ tailWord_1827452) baseStart_1827452 baseEnd_1827452 := by
    simpa [prefixWord, tailWord_1827452, baseEnd_1827452] using wordTrace_append hprefix tailTrace_1827452
  have hstable : (prefixWord ++ tailWord_1827452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827452).length < 2 ^ (prefixWord ++ tailWord_1827452).sum := by decide
  have hdescent : baseEnd_1827452 < baseStart_1827452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827459 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 1, 5, 2]
def baseStart_1827459 : Nat := 118140960795 + 1827459 * 2 ^ 59
def prefixEnd_1827459 : Nat := 4983230072969 + 3 ^ 40 * 1827459 * 2
def baseEnd_1827459 : Nat := 938364843384870791958175

theorem tailTrace_1827459 : CollatzResearch.WordTrace tailWord_1827459 prefixEnd_1827459 938364843384870791958175 := by
  unfold tailWord_1827459
  simp only [CollatzResearch.WordTrace]
  refine ⟨66652905486435622994349431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44435270324290415329566287 66652905486435622994349431)
  ·
    refine ⟨99979358229653434491524147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66652905486435622994349431 99979358229653434491524147)
    ·
      refine ⟨149969037344480151737286221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99979358229653434491524147 149969037344480151737286221)
      ·
        refine ⟨56238389004180056901482333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149969037344480151737286221 56238389004180056901482333)
        ·
          refine ⟨21089395876567521338055875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56238389004180056901482333 21089395876567521338055875)
          ·
            refine ⟨31634093814851282007083813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21089395876567521338055875 31634093814851282007083813)
            ·
              refine ⟨5931392590284615376328215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31634093814851282007083813 5931392590284615376328215)
              ·
                refine ⟨8897088885426923064492323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931392590284615376328215 8897088885426923064492323)
                ·
                  refine ⟨13345633328140384596738485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8897088885426923064492323 13345633328140384596738485)
                  ·
                    refine ⟨1251153124513161055944233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13345633328140384596738485 1251153124513161055944233)
                    ·
                      refine ⟨938364843384870791958175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251153124513161055944233 938364843384870791958175)
                      ·
                        rfl

theorem cell23_1827459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_1827459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827459 prefixEnd_1827459 := by exact prefixLift 1827459
  have htrace : WordTrace (prefixWord ++ tailWord_1827459) baseStart_1827459 baseEnd_1827459 := by
    simpa [prefixWord, tailWord_1827459, baseEnd_1827459] using wordTrace_append hprefix tailTrace_1827459
  have hstable : (prefixWord ++ tailWord_1827459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827459).length < 2 ^ (prefixWord ++ tailWord_1827459).sum := by decide
  have hdescent : baseEnd_1827459 < baseStart_1827459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827472 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_1827472 : Nat := 118140960795 + 1827472 * 2 ^ 59
def prefixEnd_1827472 : Nat := 4983230072969 + 3 ^ 40 * 1827472 * 2
def baseEnd_1827472 : Nat := 938371518633379241095615

theorem tailTrace_1827472 : CollatzResearch.WordTrace tailWord_1827472 prefixEnd_1827472 938371518633379241095615 := by
  unfold tailWord_1827472
  simp only [CollatzResearch.WordTrace]
  refine ⟨33326689817694263107286335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44435586423592350809715113 33326689817694263107286335)
  ·
    refine ⟨49990034726541394660929503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33326689817694263107286335 49990034726541394660929503)
    ·
      refine ⟨74985052089812091991394255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49990034726541394660929503 74985052089812091991394255)
      ·
        refine ⟨112477578134718137987091383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74985052089812091991394255 112477578134718137987091383)
        ·
          refine ⟨168716367202077206980637075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112477578134718137987091383 168716367202077206980637075)
          ·
            refine ⟨253074550803115810470955613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168716367202077206980637075 253074550803115810470955613)
            ·
              refine ⟨94902956551168428926608355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253074550803115810470955613 94902956551168428926608355)
              ·
                refine ⟨142354434826752643389912533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94902956551168428926608355 142354434826752643389912533)
                ·
                  refine ⟨3336432066252015079451075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142354434826752643389912533 3336432066252015079451075)
                  ·
                    refine ⟨5004648099378022619176613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3336432066252015079451075 5004648099378022619176613)
                    ·
                      refine ⟨938371518633379241095615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5004648099378022619176613 938371518633379241095615)
                      ·
                        rfl

theorem cell23_1827472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_1827472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827472 prefixEnd_1827472 := by exact prefixLift 1827472
  have htrace : WordTrace (prefixWord ++ tailWord_1827472) baseStart_1827472 baseEnd_1827472 := by
    simpa [prefixWord, tailWord_1827472, baseEnd_1827472] using wordTrace_append hprefix tailTrace_1827472
  have hstable : (prefixWord ++ tailWord_1827472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827472).length < 2 ^ (prefixWord ++ tailWord_1827472).sum := by decide
  have hdescent : baseEnd_1827472 < baseStart_1827472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827506 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_1827506 : Nat := 118140960795 + 1827506 * 2 ^ 59
def prefixEnd_1827506 : Nat := 4983230072969 + 3 ^ 40 * 1827506 * 2
def baseEnd_1827506 : Nat := 938388976975632108070459

theorem tailTrace_1827506 : CollatzResearch.WordTrace tailWord_1827506 prefixEnd_1827506 938388976975632108070459 := by
  unfold tailWord_1827506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663654929316337505327593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44436413144843566680873581 16663654929316337505327593)
  ·
    refine ⟨12497741196987253128995695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16663654929316337505327593 12497741196987253128995695)
    ·
      refine ⟨18746611795480879693493543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12497741196987253128995695 18746611795480879693493543)
      ·
        refine ⟨28119917693221319540240315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18746611795480879693493543 28119917693221319540240315)
        ·
          refine ⟨42179876539831979310360473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28119917693221319540240315 42179876539831979310360473)
          ·
            refine ⟨31634907404873984482770355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42179876539831979310360473 31634907404873984482770355)
            ·
              refine ⟨47452361107310976724155533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31634907404873984482770355 47452361107310976724155533)
              ·
                refine ⟨17794635415241616271558325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47452361107310976724155533 17794635415241616271558325)
                ·
                  refine ⟨1668247070178901525458593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17794635415241616271558325 1668247070178901525458593)
                  ·
                    refine ⟨1251185302634176144093945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1668247070178901525458593 1251185302634176144093945)
                    ·
                      refine ⟨938388976975632108070459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251185302634176144093945 938388976975632108070459)
                      ·
                        rfl

theorem cell23_1827506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_1827506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827506 prefixEnd_1827506 := by exact prefixLift 1827506
  have htrace : WordTrace (prefixWord ++ tailWord_1827506) baseStart_1827506 baseEnd_1827506 := by
    simpa [prefixWord, tailWord_1827506, baseEnd_1827506] using wordTrace_append hprefix tailTrace_1827506
  have hstable : (prefixWord ++ tailWord_1827506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827506).length < 2 ^ (prefixWord ++ tailWord_1827506).sum := by decide
  have hdescent : baseEnd_1827506 < baseStart_1827506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827519 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_1827519 : Nat := 118140960795 + 1827519 * 2 ^ 59
def prefixEnd_1827519 : Nat := 4983230072969 + 3 ^ 40 * 1827519 * 2
def baseEnd_1827519 : Nat := 938395652224140557207899

theorem tailTrace_1827519 : CollatzResearch.WordTrace tailWord_1827519 prefixEnd_1827519 938395652224140557207899 := by
  unfold tailWord_1827519
  simp only [CollatzResearch.WordTrace]
  refine ⟨66655093866218253241533611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44436729244145502161022407 66655093866218253241533611)
  ·
    refine ⟨99982640799327379862300417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66655093866218253241533611 99982640799327379862300417)
    ·
      refine ⟨74986980599495534896725313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99982640799327379862300417 74986980599495534896725313)
      ·
        refine ⟨56240235449621651172543985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74986980599495534896725313 56240235449621651172543985)
        ·
          refine ⟨42180176587216238379407989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56240235449621651172543985 42180176587216238379407989)
          ·
            refine ⟨3954391555051522348069499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42180176587216238379407989 3954391555051522348069499)
            ·
              refine ⟨5931587332577283522104249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954391555051522348069499 5931587332577283522104249)
              ·
                refine ⟨4448690499432962641578187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931587332577283522104249 4448690499432962641578187)
                ·
                  refine ⟨6673035749149443962367281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448690499432962641578187 6673035749149443962367281)
                  ·
                    refine ⟨5004776811862082971775461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6673035749149443962367281 5004776811862082971775461)
                    ·
                      refine ⟨938395652224140557207899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5004776811862082971775461 938395652224140557207899)
                      ·
                        rfl

theorem cell23_1827519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_1827519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827519 prefixEnd_1827519 := by exact prefixLift 1827519
  have htrace : WordTrace (prefixWord ++ tailWord_1827519) baseStart_1827519 baseEnd_1827519 := by
    simpa [prefixWord, tailWord_1827519, baseEnd_1827519] using wordTrace_append hprefix tailTrace_1827519
  have hstable : (prefixWord ++ tailWord_1827519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827519).length < 2 ^ (prefixWord ++ tailWord_1827519).sum := by decide
  have hdescent : baseEnd_1827519 < baseStart_1827519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827552 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1827552 : Nat := 118140960795 + 1827552 * 2 ^ 59
def prefixEnd_1827552 : Nat := 4983230072969 + 3 ^ 40 * 1827552 * 2
def baseEnd_1827552 : Nat := 938412597085738928095247

theorem tailTrace_1827552 : CollatzResearch.WordTrace tailWord_1827552 prefixEnd_1827552 938412597085738928095247 := by
  unfold tailWord_1827552
  simp only [CollatzResearch.WordTrace]
  refine ⟨33328148737549349938742455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44437531650065799918323273 33328148737549349938742455)
  ·
    refine ⟨49992223106324024908113683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33328148737549349938742455 49992223106324024908113683)
    ·
      refine ⟨74988334659486037362170525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49992223106324024908113683 74988334659486037362170525)
      ·
        refine ⟨28120625497307264010813947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74988334659486037362170525 28120625497307264010813947)
        ·
          refine ⟨42180938245960896016220921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28120625497307264010813947 42180938245960896016220921)
          ·
            refine ⟨31635703684470672012165691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42180938245960896016220921 31635703684470672012165691)
            ·
              refine ⟨47453555526706008018248537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31635703684470672012165691 47453555526706008018248537)
              ·
                refine ⟨35590166645029506013686403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47453555526706008018248537 35590166645029506013686403)
                ·
                  refine ⟨53385249967544259020529605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35590166645029506013686403 53385249967544259020529605)
                  ·
                    refine ⟨10009734368914548566349301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53385249967544259020529605 10009734368914548566349301)
                    ·
                      refine ⟨938412597085738928095247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10009734368914548566349301 938412597085738928095247)
                      ·
                        rfl

theorem cell23_1827552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1827552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827552 prefixEnd_1827552 := by exact prefixLift 1827552
  have htrace : WordTrace (prefixWord ++ tailWord_1827552) baseStart_1827552 baseEnd_1827552 := by
    simpa [prefixWord, tailWord_1827552, baseEnd_1827552] using wordTrace_append hprefix tailTrace_1827552
  have hstable : (prefixWord ++ tailWord_1827552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827552).length < 2 ^ (prefixWord ++ tailWord_1827552).sum := by decide
  have hdescent : baseEnd_1827552 < baseStart_1827552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827556 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_1827556 : Nat := 118140960795 + 1827556 * 2 ^ 59
def prefixEnd_1827556 : Nat := 4983230072969 + 3 ^ 40 * 1827556 * 2
def baseEnd_1827556 : Nat := 938414651008356912445229

theorem tailTrace_1827556 : CollatzResearch.WordTrace tailWord_1827556 prefixEnd_1827556 938414651008356912445229 := by
  unfold tailWord_1827556
  simp only [CollatzResearch.WordTrace]
  refine ⟨33328221683542104280315261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44437628911389472373753681 33328221683542104280315261)
  ·
    refine ⟨12498083131328289105118223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33328221683542104280315261 12498083131328289105118223)
    ·
      refine ⟨18747124696992433657677335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12498083131328289105118223 18747124696992433657677335)
      ·
        refine ⟨28120687045488650486516003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18747124696992433657677335 28120687045488650486516003)
        ·
          refine ⟨42181030568232975729774005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28120687045488650486516003 42181030568232975729774005)
          ·
            refine ⟨3954471615771841474666313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42181030568232975729774005 3954471615771841474666313)
            ·
              refine ⟨2965853711828881105999735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954471615771841474666313 2965853711828881105999735)
              ·
                refine ⟨4448780567743321658999603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965853711828881105999735 4448780567743321658999603)
                ·
                  refine ⟨6673170851614982488499405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448780567743321658999603 6673170851614982488499405)
                  ·
                    refine ⟨2502439069355618433187277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6673170851614982488499405 2502439069355618433187277)
                    ·
                      refine ⟨938414651008356912445229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2502439069355618433187277 938414651008356912445229)
                      ·
                        rfl

theorem cell23_1827556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_1827556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827556 prefixEnd_1827556 := by exact prefixLift 1827556
  have htrace : WordTrace (prefixWord ++ tailWord_1827556) baseStart_1827556 baseEnd_1827556 := by
    simpa [prefixWord, tailWord_1827556, baseEnd_1827556] using wordTrace_append hprefix tailTrace_1827556
  have hstable : (prefixWord ++ tailWord_1827556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827556).length < 2 ^ (prefixWord ++ tailWord_1827556).sum := by decide
  have hdescent : baseEnd_1827556 < baseStart_1827556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827579 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 8, 2]
def baseStart_1827579 : Nat := 118140960795 + 1827579 * 2 ^ 59
def prefixEnd_1827579 : Nat := 4983230072969 + 3 ^ 40 * 1827579 * 2
def baseEnd_1827579 : Nat := 938426461063410322457623

theorem tailTrace_1827579 : CollatzResearch.WordTrace tailWord_1827579 prefixEnd_1827579 938426461063410322457623 := by
  unfold tailWord_1827579
  simp only [CollatzResearch.WordTrace]
  refine ⟨66657282246000883488717791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44438188164000588992478527 66657282246000883488717791)
  ·
    refine ⟨99985923369001325233076687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66657282246000883488717791 99985923369001325233076687)
    ·
      refine ⟨149978885053501987849615031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99985923369001325233076687 149978885053501987849615031)
      ·
        refine ⟨224968327580252981774422547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149978885053501987849615031 224968327580252981774422547)
        ·
          refine ⟨337452491370379472661633821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224968327580252981774422547 337452491370379472661633821)
          ·
            refine ⟨126544684263892302248112683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337452491370379472661633821 126544684263892302248112683)
            ·
              refine ⟨189817026395838453372169025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126544684263892302248112683 189817026395838453372169025)
              ·
                refine ⟨142362769796878840029126769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189817026395838453372169025 142362769796878840029126769)
                ·
                  refine ⟨106772077347659130021845077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142362769796878840029126769 106772077347659130021845077)
                  ·
                    refine ⟨1251235281417880429943497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106772077347659130021845077 1251235281417880429943497)
                    ·
                      refine ⟨938426461063410322457623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251235281417880429943497 938426461063410322457623)
                      ·
                        rfl

theorem cell23_1827579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8, 2].length) (baseStart_1827579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827579 prefixEnd_1827579 := by exact prefixLift 1827579
  have htrace : WordTrace (prefixWord ++ tailWord_1827579) baseStart_1827579 baseEnd_1827579 := by
    simpa [prefixWord, tailWord_1827579, baseEnd_1827579] using wordTrace_append hprefix tailTrace_1827579
  have hstable : (prefixWord ++ tailWord_1827579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827579).length < 2 ^ (prefixWord ++ tailWord_1827579).sum := by decide
  have hdescent : baseEnd_1827579 < baseStart_1827579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827630 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1827630 : Nat := 118140960795 + 1827630 * 2 ^ 59
def prefixEnd_1827630 : Nat := 4983230072969 + 3 ^ 40 * 1827630 * 2
def baseEnd_1827630 : Nat := 938452648576789622919889

theorem tailTrace_1827630 : CollatzResearch.WordTrace tailWord_1827630 prefixEnd_1827630 938452648576789622919889 := by
  unfold tailWord_1827630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332392796102014899853043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44439428245877412799216229 8332392796102014899853043)
  ·
    refine ⟨12498589194153022349779565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8332392796102014899853043 12498589194153022349779565)
    ·
      refine ⟨4686970947807383381167337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12498589194153022349779565 4686970947807383381167337)
      ·
        refine ⟨3515228210855537535875503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4686970947807383381167337 3515228210855537535875503)
        ·
          refine ⟨5272842316283306303813255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515228210855537535875503 5272842316283306303813255)
          ·
            refine ⟨7909263474424959455719883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272842316283306303813255 7909263474424959455719883)
            ·
              refine ⟨11863895211637439183579825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909263474424959455719883 11863895211637439183579825)
              ·
                refine ⟨8897921408728079387684869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11863895211637439183579825 8897921408728079387684869)
                ·
                  refine ⟨1668360264136514885190913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8897921408728079387684869 1668360264136514885190913)
                  ·
                    refine ⟨1251270198102386163893185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1668360264136514885190913 1251270198102386163893185)
                    ·
                      refine ⟨938452648576789622919889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251270198102386163893185 938452648576789622919889)
                      ·
                        rfl

theorem cell23_1827630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1827630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827630 prefixEnd_1827630 := by exact prefixLift 1827630
  have htrace : WordTrace (prefixWord ++ tailWord_1827630) baseStart_1827630 baseEnd_1827630 := by
    simpa [prefixWord, tailWord_1827630, baseEnd_1827630] using wordTrace_append hprefix tailTrace_1827630
  have hstable : (prefixWord ++ tailWord_1827630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827630).length < 2 ^ (prefixWord ++ tailWord_1827630).sum := by decide
  have hdescent : baseEnd_1827630 < baseStart_1827630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827656 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_1827656 : Nat := 118140960795 + 1827656 * 2 ^ 59
def prefixEnd_1827656 : Nat := 4983230072969 + 3 ^ 40 * 1827656 * 2
def baseEnd_1827656 : Nat := 938465999073806521194769

theorem tailTrace_1827656 : CollatzResearch.WordTrace tailWord_1827656 prefixEnd_1827656 938465999073806521194769 := by
  unfold tailWord_1827656
  simp only [CollatzResearch.WordTrace]
  refine ⟨33330045333360962819635411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44440060444481283759513881 33330045333360962819635411)
  ·
    refine ⟨49995068000041444229453117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33330045333360962819635411 49995068000041444229453117)
    ·
      refine ⟨18748150500015541586044919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49995068000041444229453117 18748150500015541586044919)
      ·
        refine ⟨28122225750023312379067379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18748150500015541586044919 28122225750023312379067379)
        ·
          refine ⟨42183338625034968568601069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28122225750023312379067379 42183338625034968568601069)
          ·
            refine ⟨15818751984388113213225401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42183338625034968568601069 15818751984388113213225401)
            ·
              refine ⟨11864063988291084909919051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15818751984388113213225401 11864063988291084909919051)
              ·
                refine ⟨17796095982436627364878577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864063988291084909919051 17796095982436627364878577)
                ·
                  refine ⟨13347071986827470523658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17796095982436627364878577 13347071986827470523658933)
                  ·
                    refine ⟨1251287998765075361593025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13347071986827470523658933 1251287998765075361593025)
                    ·
                      refine ⟨938465999073806521194769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251287998765075361593025 938465999073806521194769)
                      ·
                        rfl

theorem cell23_1827656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_1827656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827656 prefixEnd_1827656 := by exact prefixLift 1827656
  have htrace : WordTrace (prefixWord ++ tailWord_1827656) baseStart_1827656 baseEnd_1827656 := by
    simpa [prefixWord, tailWord_1827656, baseEnd_1827656] using wordTrace_append hprefix tailTrace_1827656
  have hstable : (prefixWord ++ tailWord_1827656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827656).length < 2 ^ (prefixWord ++ tailWord_1827656).sum := by decide
  have hdescent : baseEnd_1827656 < baseStart_1827656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827709 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 8]
def baseStart_1827709 : Nat := 118140960795 + 1827709 * 2 ^ 59
def prefixEnd_1827709 : Nat := 4983230072969 + 3 ^ 40 * 1827709 * 2
def baseEnd_1827709 : Nat := 104277023727610534870225

theorem tailTrace_1827709 : CollatzResearch.WordTrace tailWord_1827709 prefixEnd_1827709 104277023727610534870225 := by
  unfold tailWord_1827709
  simp only [CollatzResearch.WordTrace]
  refine ⟨66662023735529915690950181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44441349157019943793966787 66662023735529915690950181)
  ·
    refine ⟨12499129450411859192053159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66662023735529915690950181 12499129450411859192053159)
    ·
      refine ⟨18748694175617788788079739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12499129450411859192053159 18748694175617788788079739)
      ·
        refine ⟨28123041263426683182119609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18748694175617788788079739 28123041263426683182119609)
        ·
          refine ⟨21092280947570012386589707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28123041263426683182119609 21092280947570012386589707)
          ·
            refine ⟨31638421421355018579884561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21092280947570012386589707 31638421421355018579884561)
            ·
              refine ⟨23728816066016263934913421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31638421421355018579884561 23728816066016263934913421)
              ·
                refine ⟨8898306024756098975592533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23728816066016263934913421 8898306024756098975592533)
                ·
                  refine ⟨104277023727610534870225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8898306024756098975592533 104277023727610534870225)
                  ·
                    rfl

theorem cell23_1827709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_1827709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827709 prefixEnd_1827709 := by exact prefixLift 1827709
  have htrace : WordTrace (prefixWord ++ tailWord_1827709) baseStart_1827709 baseEnd_1827709 := by
    simpa [prefixWord, tailWord_1827709, baseEnd_1827709] using wordTrace_append hprefix tailTrace_1827709
  have hstable : (prefixWord ++ tailWord_1827709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827709).length < 2 ^ (prefixWord ++ tailWord_1827709).sum := by decide
  have hdescent : baseEnd_1827709 < baseStart_1827709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827730 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1827730 : Nat := 118140960795 + 1827730 * 2 ^ 59
def prefixEnd_1827730 : Nat := 4983230072969 + 3 ^ 40 * 1827730 * 2
def baseEnd_1827730 : Nat := 312834665547413077223143

theorem tailTrace_1827730 : CollatzResearch.WordTrace tailWord_1827730 prefixEnd_1827730 312834665547413077223143 := by
  unfold tailWord_1827730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16665697417113459069366161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44441859778969224184976429 16665697417113459069366161)
  ·
    refine ⟨12499273062835094302024621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16665697417113459069366161 12499273062835094302024621)
    ·
      refine ⟨4687227398563160363259233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12499273062835094302024621 4687227398563160363259233)
      ·
        refine ⟨3515420548922370272444425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4687227398563160363259233 3515420548922370272444425)
        ·
          refine ⟨2636565411691777704333319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3515420548922370272444425 2636565411691777704333319)
          ·
            refine ⟨3954848117537666556499979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636565411691777704333319 3954848117537666556499979)
            ·
              refine ⟨5932272176306499834749969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954848117537666556499979 5932272176306499834749969)
              ·
                refine ⟨4449204132229874876062477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932272176306499834749969 4449204132229874876062477)
                ·
                  refine ⟨1668451549586203078523429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4449204132229874876062477 1668451549586203078523429)
                  ·
                    refine ⟨312834665547413077223143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668451549586203078523429 312834665547413077223143)
                    ·
                      rfl

theorem cell23_1827730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1827730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827730 prefixEnd_1827730 := by exact prefixLift 1827730
  have htrace : WordTrace (prefixWord ++ tailWord_1827730) baseStart_1827730 baseEnd_1827730 := by
    simpa [prefixWord, tailWord_1827730, baseEnd_1827730] using wordTrace_append hprefix tailTrace_1827730
  have hstable : (prefixWord ++ tailWord_1827730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827730).length < 2 ^ (prefixWord ++ tailWord_1827730).sum := by decide
  have hdescent : baseEnd_1827730 < baseStart_1827730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827749 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_1827749 : Nat := 118140960795 + 1827749 * 2 ^ 59
def prefixEnd_1827749 : Nat := 4983230072969 + 3 ^ 40 * 1827749 * 2
def baseEnd_1827749 : Nat := 938513752774674657331841

theorem tailTrace_1827749 : CollatzResearch.WordTrace tailWord_1827749 prefixEnd_1827749 938513752774674657331841 := by
  unfold tailWord_1827749
  simp only [CollatzResearch.WordTrace]
  refine ⟨66663482655385002522406301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44442321770256668348270867 66663482655385002522406301)
  ·
    refine ⟨24998805995769375945902363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66663482655385002522406301 24998805995769375945902363)
    ·
      refine ⟨37498208993654063918853545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24998805995769375945902363 37498208993654063918853545)
      ·
        refine ⟨28123656745240547939140159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37498208993654063918853545 28123656745240547939140159)
        ·
          refine ⟨42185485117860821908710239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28123656745240547939140159 42185485117860821908710239)
          ·
            refine ⟨63278227676791232863065359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42185485117860821908710239 63278227676791232863065359)
            ·
              refine ⟨94917341515186849294598039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63278227676791232863065359 94917341515186849294598039)
              ·
                refine ⟨142376012272780273941897059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94917341515186849294598039 142376012272780273941897059)
                ·
                  refine ⟨213564018409170410912845589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142376012272780273941897059 213564018409170410912845589)
                  ·
                    refine ⟨10010813362929863011539637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213564018409170410912845589 10010813362929863011539637)
                    ·
                      refine ⟨938513752774674657331841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10010813362929863011539637 938513752774674657331841)
                      ·
                        rfl

theorem cell23_1827749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_1827749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827749 prefixEnd_1827749 := by exact prefixLift 1827749
  have htrace : WordTrace (prefixWord ++ tailWord_1827749) baseStart_1827749 baseEnd_1827749 := by
    simpa [prefixWord, tailWord_1827749, baseEnd_1827749] using wordTrace_append hprefix tailTrace_1827749
  have hstable : (prefixWord ++ tailWord_1827749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827749).length < 2 ^ (prefixWord ++ tailWord_1827749).sum := by decide
  have hdescent : baseEnd_1827749 < baseStart_1827749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827756 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_1827756 : Nat := 118140960795 + 1827756 * 2 ^ 59
def prefixEnd_1827756 : Nat := 4983230072969 + 3 ^ 40 * 1827756 * 2
def baseEnd_1827756 : Nat := 312839115713085376648103

theorem tailTrace_1827756 : CollatzResearch.WordTrace tailWord_1827756 prefixEnd_1827756 312839115713085376648103 := by
  unfold tailWord_1827756
  simp only [CollatzResearch.WordTrace]
  refine ⟨33331868983179821358955561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44442491977573095145274081 33331868983179821358955561)
  ·
    refine ⟨24998901737384866019216671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33331868983179821358955561 24998901737384866019216671)
    ·
      refine ⟨37498352606077299028825007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24998901737384866019216671 37498352606077299028825007)
      ·
        refine ⟨56247528909115948543237511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37498352606077299028825007 56247528909115948543237511)
        ·
          refine ⟨84371293363673922814856267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56247528909115948543237511 84371293363673922814856267)
          ·
            refine ⟨126556940045510884222284401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84371293363673922814856267 126556940045510884222284401)
            ·
              refine ⟨94917705034133163166713301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126556940045510884222284401 94917705034133163166713301)
              ·
                refine ⟨2224633711737496011719843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94917705034133163166713301 2224633711737496011719843)
                ·
                  refine ⟨3336950567606244017579765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224633711737496011719843 3336950567606244017579765)
                  ·
                    refine ⟨312839115713085376648103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3336950567606244017579765 312839115713085376648103)
                    ·
                      rfl

theorem cell23_1827756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_1827756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827756 prefixEnd_1827756 := by exact prefixLift 1827756
  have htrace : WordTrace (prefixWord ++ tailWord_1827756) baseStart_1827756 baseEnd_1827756 := by
    simpa [prefixWord, tailWord_1827756, baseEnd_1827756] using wordTrace_append hprefix tailTrace_1827756
  have hstable : (prefixWord ++ tailWord_1827756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827756).length < 2 ^ (prefixWord ++ tailWord_1827756).sum := by decide
  have hdescent : baseEnd_1827756 < baseStart_1827756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827770 : List Nat := [3, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3]
def baseStart_1827770 : Nat := 118140960795 + 1827770 * 2 ^ 59
def prefixEnd_1827770 : Nat := 4983230072969 + 3 ^ 40 * 1827770 * 2
def baseEnd_1827770 : Nat := 938524535868419075169245

theorem tailTrace_1827770 : CollatzResearch.WordTrace tailWord_1827770 prefixEnd_1827770 938524535868419075169245 := by
  unfold tailWord_1827770
  simp only [CollatzResearch.WordTrace]
  refine ⟨16666062147077230777230191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44442832392205948739280509 16666062147077230777230191)
  ·
    refine ⟨24999093220615846165845287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16666062147077230777230191 24999093220615846165845287)
    ·
      refine ⟨37498639830923769248767931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24999093220615846165845287 37498639830923769248767931)
      ·
        refine ⟨56247959746385653873151897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37498639830923769248767931 56247959746385653873151897)
        ·
          refine ⟨42185969809789240404863923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56247959746385653873151897 42185969809789240404863923)
          ·
            refine ⟨63278954714683860607295885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42185969809789240404863923 63278954714683860607295885)
            ·
              refine ⟨23729608018006447727735957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63278954714683860607295885 23729608018006447727735957)
              ·
                refine ⟨1112325375844052237237623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23729608018006447727735957 1112325375844052237237623)
                ·
                  refine ⟨1668488063766078355856435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112325375844052237237623 1668488063766078355856435)
                  ·
                    refine ⟨2502732095649117533784653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1668488063766078355856435 2502732095649117533784653)
                    ·
                      refine ⟨938524535868419075169245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2502732095649117533784653 938524535868419075169245)
                      ·
                        rfl

theorem cell23_1827770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_1827770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827770 prefixEnd_1827770 := by exact prefixLift 1827770
  have htrace : WordTrace (prefixWord ++ tailWord_1827770) baseStart_1827770 baseEnd_1827770 := by
    simpa [prefixWord, tailWord_1827770, baseEnd_1827770] using wordTrace_append hprefix tailTrace_1827770
  have hstable : (prefixWord ++ tailWord_1827770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827770).length < 2 ^ (prefixWord ++ tailWord_1827770).sum := by decide
  have hdescent : baseEnd_1827770 < baseStart_1827770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827793 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_1827793 : Nat := 118140960795 + 1827793 * 2 ^ 59
def prefixEnd_1827793 : Nat := 4983230072969 + 3 ^ 40 * 1827793 * 2
def baseEnd_1827793 : Nat := 938536345923472485181639

theorem tailTrace_1827793 : CollatzResearch.WordTrace tailWord_1827793 prefixEnd_1827793 938536345923472485181639 := by
  unfold tailWord_1827793
  simp only [CollatzResearch.WordTrace]
  refine ⟨66665087467225598037008033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44443391644817065358005355 66665087467225598037008033)
  ·
    refine ⟨49998815600419198527756025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66665087467225598037008033 49998815600419198527756025)
    ·
      refine ⟨37499111700314398895817019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49998815600419198527756025 37499111700314398895817019)
      ·
        refine ⟨56248667550471598343725529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37499111700314398895817019 56248667550471598343725529)
        ·
          refine ⟨42186500662853698757794147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56248667550471598343725529 42186500662853698757794147)
          ·
            refine ⟨63279750994280548136691221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42186500662853698757794147 63279750994280548136691221)
            ·
              refine ⟨2966238327856900693907401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63279750994280548136691221 2966238327856900693907401)
              ·
                refine ⟨2224678745892675520430551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966238327856900693907401 2224678745892675520430551)
                ·
                  refine ⟨3337018118839013280645827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224678745892675520430551 3337018118839013280645827)
                  ·
                    refine ⟨5005527178258519920968741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337018118839013280645827 5005527178258519920968741)
                    ·
                      refine ⟨938536345923472485181639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5005527178258519920968741 938536345923472485181639)
                      ·
                        rfl

theorem cell23_1827793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_1827793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827793 prefixEnd_1827793 := by exact prefixLift 1827793
  have htrace : WordTrace (prefixWord ++ tailWord_1827793) baseStart_1827793 baseEnd_1827793 := by
    simpa [prefixWord, tailWord_1827793, baseEnd_1827793] using wordTrace_append hprefix tailTrace_1827793
  have hstable : (prefixWord ++ tailWord_1827793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827793).length < 2 ^ (prefixWord ++ tailWord_1827793).sum := by decide
  have hdescent : baseEnd_1827793 < baseStart_1827793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827828 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1827828 : Nat := 118140960795 + 1827828 * 2 ^ 59
def prefixEnd_1827828 : Nat := 4983230072969 + 3 ^ 40 * 1827828 * 2
def baseEnd_1827828 : Nat := 104283813082931094249331

theorem tailTrace_1827828 : CollatzResearch.WordTrace tailWord_1827828 prefixEnd_1827828 104283813082931094249331 := by
  unfold tailWord_1827828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33333182011049399507266069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44444242681399199343021425 33333182011049399507266069)
  ·
    refine ⟨1562492906767940601903097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33333182011049399507266069 1562492906767940601903097)
    ·
      refine ⟨1171869680075955451427323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1562492906767940601903097 1171869680075955451427323)
      ·
        refine ⟨1757804520113933177140985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171869680075955451427323 1757804520113933177140985)
        ·
          refine ⟨1318353390085449882855739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1757804520113933177140985 1318353390085449882855739)
          ·
            refine ⟨1977530085128174824283609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318353390085449882855739 1977530085128174824283609)
            ·
              refine ⟨1483147563846131118212707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977530085128174824283609 1483147563846131118212707)
              ·
                refine ⟨2224721345769196677319061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483147563846131118212707 2224721345769196677319061)
                ·
                  refine ⟨104283813082931094249331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2224721345769196677319061 104283813082931094249331)
                  ·
                    rfl

theorem cell23_1827828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1827828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827828 prefixEnd_1827828 := by exact prefixLift 1827828
  have htrace : WordTrace (prefixWord ++ tailWord_1827828) baseStart_1827828 baseEnd_1827828 := by
    simpa [prefixWord, tailWord_1827828, baseEnd_1827828] using wordTrace_append hprefix tailTrace_1827828
  have hstable : (prefixWord ++ tailWord_1827828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827828).length < 2 ^ (prefixWord ++ tailWord_1827828).sum := by decide
  have hdescent : baseEnd_1827828 < baseStart_1827828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827883 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 3, 4, 2]
def baseStart_1827883 : Nat := 118140960795 + 1827883 * 2 ^ 59
def prefixEnd_1827883 : Nat := 4983230072969 + 3 ^ 40 * 1827883 * 2
def baseEnd_1827883 : Nat := 938582559182377133056225

theorem tailTrace_1827883 : CollatzResearch.WordTrace tailWord_1827883 prefixEnd_1827883 938582559182377133056225 := by
  unfold tailWord_1827883
  simp only [CollatzResearch.WordTrace]
  refine ⟨66668370036899543407784303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44445580024599695605189535 66668370036899543407784303)
  ·
    refine ⟨100002555055349315111676455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66668370036899543407784303 100002555055349315111676455)
    ·
      refine ⟨150003832583023972667514683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100002555055349315111676455 150003832583023972667514683)
      ·
        refine ⟨225005748874535959001272025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150003832583023972667514683 225005748874535959001272025)
        ·
          refine ⟨168754311655901969250954019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225005748874535959001272025 168754311655901969250954019)
          ·
            refine ⟨253131467483852953876431029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168754311655901969250954019 253131467483852953876431029)
            ·
              refine ⟨23731075076611214425915409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253131467483852953876431029 23731075076611214425915409)
              ·
                refine ⟨17798306307458410819436557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23731075076611214425915409 17798306307458410819436557)
                ·
                  refine ⟨6674364865296904057288709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17798306307458410819436557 6674364865296904057288709)
                  ·
                    refine ⟨1251443412243169510741633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674364865296904057288709 1251443412243169510741633)
                    ·
                      refine ⟨938582559182377133056225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251443412243169510741633 938582559182377133056225)
                      ·
                        rfl

theorem cell23_1827883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4, 2].length) (baseStart_1827883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827883 prefixEnd_1827883 := by exact prefixLift 1827883
  have htrace : WordTrace (prefixWord ++ tailWord_1827883) baseStart_1827883 baseEnd_1827883 := by
    simpa [prefixWord, tailWord_1827883, baseEnd_1827883] using wordTrace_append hprefix tailTrace_1827883
  have hstable : (prefixWord ++ tailWord_1827883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827883).length < 2 ^ (prefixWord ++ tailWord_1827883).sum := by decide
  have hdescent : baseEnd_1827883 < baseStart_1827883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827900 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_1827900 : Nat := 118140960795 + 1827900 * 2 ^ 59
def prefixEnd_1827900 : Nat := 4983230072969 + 3 ^ 40 * 1827900 * 2
def baseEnd_1827900 : Nat := 938591288353503566543647

theorem tailTrace_1827900 : CollatzResearch.WordTrace tailWord_1827900 prefixEnd_1827900 938591288353503566543647 := by
  unfold tailWord_1827900
  simp only [CollatzResearch.WordTrace]
  refine ⟨33334495038918977655576577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44445993385225303540768769 33334495038918977655576577)
  ·
    refine ⟨25000871279189233241682433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33334495038918977655576577 25000871279189233241682433)
    ·
      refine ⟨18750653459391924931261825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25000871279189233241682433 18750653459391924931261825)
      ·
        refine ⟨14062990094543943698446369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18750653459391924931261825 14062990094543943698446369)
        ·
          refine ⟨10547242570907957773834777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14062990094543943698446369 10547242570907957773834777)
          ·
            refine ⟨7910431928180968330376083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10547242570907957773834777 7910431928180968330376083)
            ·
              refine ⟨11865647892271452495564125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7910431928180968330376083 11865647892271452495564125)
              ·
                refine ⟨4449617959601794685836547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11865647892271452495564125 4449617959601794685836547)
                ·
                  refine ⟨6674426939402692028754821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449617959601794685836547 6674426939402692028754821)
                  ·
                    refine ⟨1251455051138004755391529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674426939402692028754821 1251455051138004755391529)
                    ·
                      refine ⟨938591288353503566543647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251455051138004755391529 938591288353503566543647)
                      ·
                        rfl

theorem cell23_1827900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_1827900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827900 prefixEnd_1827900 := by exact prefixLift 1827900
  have htrace : WordTrace (prefixWord ++ tailWord_1827900) baseStart_1827900 baseEnd_1827900 := by
    simpa [prefixWord, tailWord_1827900, baseEnd_1827900] using wordTrace_append hprefix tailTrace_1827900
  have hstable : (prefixWord ++ tailWord_1827900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827900).length < 2 ^ (prefixWord ++ tailWord_1827900).sum := by decide
  have hdescent : baseEnd_1827900 < baseStart_1827900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827916 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1827916 : Nat := 118140960795 + 1827916 * 2 ^ 59
def prefixEnd_1827916 : Nat := 4983230072969 + 3 ^ 40 * 1827916 * 2
def baseEnd_1827916 : Nat := 938599504043975503943573

theorem tailTrace_1827916 : CollatzResearch.WordTrace tailWord_1827916 prefixEnd_1827916 938599504043975503943573 := by
  unfold tailWord_1827916
  simp only [CollatzResearch.WordTrace]
  refine ⟨33334786822889995021867801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44446382430519993362490401 33334786822889995021867801)
  ·
    refine ⟨25001090117167496266400851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33334786822889995021867801 25001090117167496266400851)
    ·
      refine ⟨37501635175751244399601277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25001090117167496266400851 37501635175751244399601277)
      ·
        refine ⟨14063113190906716649850479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37501635175751244399601277 14063113190906716649850479)
        ·
          refine ⟨21094669786360074974775719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063113190906716649850479 21094669786360074974775719)
          ·
            refine ⟨31642004679540112462163579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21094669786360074974775719 31642004679540112462163579)
            ·
              refine ⟨47463007019310168693245369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31642004679540112462163579 47463007019310168693245369)
              ·
                refine ⟨35597255264482626519934027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47463007019310168693245369 35597255264482626519934027)
                ·
                  refine ⟨53395882896723939779901041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35597255264482626519934027 53395882896723939779901041)
                  ·
                    refine ⟨40046912172542954834925781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53395882896723939779901041 40046912172542954834925781)
                    ·
                      refine ⟨938599504043975503943573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40046912172542954834925781 938599504043975503943573)
                      ·
                        rfl

theorem cell23_1827916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1827916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827916 prefixEnd_1827916 := by exact prefixLift 1827916
  have htrace : WordTrace (prefixWord ++ tailWord_1827916) baseStart_1827916 baseEnd_1827916 := by
    simpa [prefixWord, tailWord_1827916, baseEnd_1827916] using wordTrace_append hprefix tailTrace_1827916
  have hstable : (prefixWord ++ tailWord_1827916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827916).length < 2 ^ (prefixWord ++ tailWord_1827916).sum := by decide
  have hdescent : baseEnd_1827916 < baseStart_1827916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827917 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_1827917 : Nat := 118140960795 + 1827917 * 2 ^ 59
def prefixEnd_1827917 : Nat := 4983230072969 + 3 ^ 40 * 1827917 * 2
def baseEnd_1827917 : Nat := 938600017524630000031069

theorem tailTrace_1827917 : CollatzResearch.WordTrace tailWord_1827917 prefixEnd_1827917 938600017524630000031069 := by
  unfold tailWord_1827917
  simp only [CollatzResearch.WordTrace]
  refine ⟨66669610118776367214522005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44446406745850911476348003 66669610118776367214522005)
  ·
    refine ⟨3125137974317642213180719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66669610118776367214522005 3125137974317642213180719)
    ·
      refine ⟨4687706961476463319771079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3125137974317642213180719 4687706961476463319771079)
      ·
        refine ⟨7031560442214694979656619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4687706961476463319771079 7031560442214694979656619)
        ·
          refine ⟨10547340663322042469484929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031560442214694979656619 10547340663322042469484929)
          ·
            refine ⟨7910505497491531852113697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10547340663322042469484929 7910505497491531852113697)
            ·
              refine ⟨5932879123118648889085273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910505497491531852113697 5932879123118648889085273)
              ·
                refine ⟨4449659342338986666813955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932879123118648889085273 4449659342338986666813955)
                ·
                  refine ⟨6674489013508480000220933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449659342338986666813955 6674489013508480000220933)
                  ·
                    refine ⟨1251466690032840000041425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674489013508480000220933 1251466690032840000041425)
                    ·
                      refine ⟨938600017524630000031069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1251466690032840000041425 938600017524630000031069)
                      ·
                        rfl

theorem cell23_1827917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_1827917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827917 prefixEnd_1827917 := by exact prefixLift 1827917
  have htrace : WordTrace (prefixWord ++ tailWord_1827917) baseStart_1827917 baseEnd_1827917 := by
    simpa [prefixWord, tailWord_1827917, baseEnd_1827917] using wordTrace_append hprefix tailTrace_1827917
  have hstable : (prefixWord ++ tailWord_1827917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827917).length < 2 ^ (prefixWord ++ tailWord_1827917).sum := by decide
  have hdescent : baseEnd_1827917 < baseStart_1827917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827923 : List Nat := [1, 1, 1, 2, 1, 1, 2, 9, 5]
def baseStart_1827923 : Nat := 118140960795 + 1827923 * 2 ^ 59
def prefixEnd_1827923 : Nat := 4983230072969 + 3 ^ 40 * 1827923 * 2
def baseEnd_1827923 : Nat := 104289233156506330728449

theorem tailTrace_1827923 : CollatzResearch.WordTrace tailWord_1827923 prefixEnd_1827923 104289233156506330728449 := by
  unfold tailWord_1827923
  simp only [CollatzResearch.WordTrace]
  refine ⟨66669828956754630239240423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44446552637836420159493615 66669828956754630239240423)
  ·
    refine ⟨100004743435131945358860635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66669828956754630239240423 100004743435131945358860635)
    ·
      refine ⟨150007115152697918038290953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100004743435131945358860635 150007115152697918038290953)
      ·
        refine ⟨112505336364523438528718215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150007115152697918038290953 112505336364523438528718215)
        ·
          refine ⟨168758004546785157793077323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112505336364523438528718215 168758004546785157793077323)
          ·
            refine ⟨253137006820177736689615985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168758004546785157793077323 253137006820177736689615985)
            ·
              refine ⟨189852755115133302517211989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253137006820177736689615985 189852755115133302517211989)
              ·
                refine ⟨1112418487002734194436789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 189852755115133302517211989 1112418487002734194436789)
                ·
                  refine ⟨104289233156506330728449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1112418487002734194436789 104289233156506330728449)
                  ·
                    rfl

theorem cell23_1827923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 5].length) (baseStart_1827923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1827923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1827923 prefixEnd_1827923 := by exact prefixLift 1827923
  have htrace : WordTrace (prefixWord ++ tailWord_1827923) baseStart_1827923 baseEnd_1827923 := by
    simpa [prefixWord, tailWord_1827923, baseEnd_1827923] using wordTrace_append hprefix tailTrace_1827923
  have hstable : (prefixWord ++ tailWord_1827923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827923).length < 2 ^ (prefixWord ++ tailWord_1827923).sum := by decide
  have hdescent : baseEnd_1827923 < baseStart_1827923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
