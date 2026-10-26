import V185TrunkScan22Chunk001

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_18120 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 5, 3]
def baseStart_18120 : Nat := 118140960795 + 18120 * 2 ^ 59
def prefixEnd_18120 : Nat := 4983230072969 + 3 ^ 40 * 18120 * 2
def baseEnd_18120 : Nat := 6202846306382892744449

theorem tailTrace_18120 : CollatzResearch.WordTrace tailWord_18120 prefixEnd_18120 6202846306382892744449 := by
  unfold tailWord_18120
  simp only [CollatzResearch.WordTrace]
  refine ⟨330445347180904747365907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 440593796241206329821209 330445347180904747365907)
  ·
    refine ⟨495668020771357121048861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 330445347180904747365907 495668020771357121048861)
    ·
      refine ⟨185875507789258920393323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 495668020771357121048861 185875507789258920393323)
      ·
        refine ⟨278813261683888380589985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185875507789258920393323 278813261683888380589985)
        ·
          refine ⟨209109946262916285442489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278813261683888380589985 209109946262916285442489)
          ·
            refine ⟨156832459697187214081867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209109946262916285442489 156832459697187214081867)
            ·
              refine ⟨235248689545780821122801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156832459697187214081867 235248689545780821122801)
              ·
                refine ⟨176436517159335615842101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235248689545780821122801 176436517159335615842101)
                ·
                  refine ⟨16540923483687713985197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176436517159335615842101 16540923483687713985197)
                  ·
                    refine ⟨6202846306382892744449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16540923483687713985197 6202846306382892744449)
                    ·
                      rfl

theorem cell22_18120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_18120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18120 prefixEnd_18120 := by exact prefixLift 18120
  have htrace : WordTrace (prefixWord ++ tailWord_18120) baseStart_18120 baseEnd_18120 := by
    simpa [prefixWord, tailWord_18120, baseEnd_18120] using wordTrace_append hprefix tailTrace_18120
  have hstable : (prefixWord ++ tailWord_18120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18120).length < 2 ^ (prefixWord ++ tailWord_18120).sum := by decide
  have hdescent : baseEnd_18120 < baseStart_18120 := by decide
  rcases family_descends (prefixWord ++ tailWord_18120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18137 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 3, 3]
def baseStart_18137 : Nat := 118140960795 + 18137 * 2 ^ 59
def prefixEnd_18137 : Nat := 4983230072969 + 3 ^ 40 * 18137 * 2
def baseEnd_18137 : Nat := 6208665753800515069397

theorem tailTrace_18137 : CollatzResearch.WordTrace tailWord_18137 prefixEnd_18137 6208665753800515069397 := by
  unfold tailWord_18137
  simp only [CollatzResearch.WordTrace]
  refine ⟨661510735300221398100665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 441007156866814265400443 661510735300221398100665)
  ·
    refine ⟨496133051475166048575499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 661510735300221398100665 496133051475166048575499)
    ·
      refine ⟨744199577212749072863249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496133051475166048575499 744199577212749072863249)
      ·
        refine ⟨558149682909561804647437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 744199577212749072863249 558149682909561804647437)
        ·
          refine ⟨209306131091085676742789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 558149682909561804647437 209306131091085676742789)
          ·
            refine ⟨39244899579578564389273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209306131091085676742789 39244899579578564389273)
            ·
              refine ⟨29433674684683923291955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39244899579578564389273 29433674684683923291955)
              ·
                refine ⟨44150512027025884937933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29433674684683923291955 44150512027025884937933)
                ·
                  refine ⟨16556442010134706851725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44150512027025884937933 16556442010134706851725)
                  ·
                    refine ⟨6208665753800515069397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16556442010134706851725 6208665753800515069397)
                    ·
                      rfl

theorem cell22_18137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_18137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18137 prefixEnd_18137 := by exact prefixLift 18137
  have htrace : WordTrace (prefixWord ++ tailWord_18137) baseStart_18137 baseEnd_18137 := by
    simpa [prefixWord, tailWord_18137, baseEnd_18137] using wordTrace_append hprefix tailTrace_18137
  have hstable : (prefixWord ++ tailWord_18137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18137).length < 2 ^ (prefixWord ++ tailWord_18137).sum := by decide
  have hdescent : baseEnd_18137 < baseStart_18137 := by decide
  rcases family_descends (prefixWord ++ tailWord_18137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18227 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 1, 5]
def baseStart_18227 : Nat := 118140960795 + 18227 * 2 ^ 59
def prefixEnd_18227 : Nat := 4983230072969 + 3 ^ 40 * 18227 * 2
def baseEnd_18227 : Nat := 6239474593070280319121

theorem tailTrace_18227 : CollatzResearch.WordTrace tailWord_18227 prefixEnd_18227 6239474593070280319121 := by
  unfold tailWord_18227
  simp only [CollatzResearch.WordTrace]
  refine ⟨664793304974166768876935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 443195536649444512584623 664793304974166768876935)
  ·
    refine ⟨997189957461250153315403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664793304974166768876935 997189957461250153315403)
    ·
      refine ⟨1495784936191875229973105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997189957461250153315403 1495784936191875229973105)
      ·
        refine ⟨1121838702143906422479829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1495784936191875229973105 1121838702143906422479829)
        ·
          refine ⟨26293094581497806776871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1121838702143906422479829 26293094581497806776871)
          ·
            refine ⟨39439641872246710165307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26293094581497806776871 39439641872246710165307)
            ·
              refine ⟨59159462808370065247961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39439641872246710165307 59159462808370065247961)
              ·
                refine ⟨44369597106277548935971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59159462808370065247961 44369597106277548935971)
                ·
                  refine ⟨66554395659416323403957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44369597106277548935971 66554395659416323403957)
                  ·
                    refine ⟨6239474593070280319121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66554395659416323403957 6239474593070280319121)
                    ·
                      rfl

theorem cell22_18227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5].length) (baseStart_18227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18227 prefixEnd_18227 := by exact prefixLift 18227
  have htrace : WordTrace (prefixWord ++ tailWord_18227) baseStart_18227 baseEnd_18227 := by
    simpa [prefixWord, tailWord_18227, baseEnd_18227] using wordTrace_append hprefix tailTrace_18227
  have hstable : (prefixWord ++ tailWord_18227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18227).length < 2 ^ (prefixWord ++ tailWord_18227).sum := by decide
  have hdescent : baseEnd_18227 < baseStart_18227 := by decide
  rcases family_descends (prefixWord ++ tailWord_18227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18257 : List Nat := [1, 2, 2, 1, 5, 3, 1, 7]
def baseStart_18257 : Nat := 118140960795 + 18257 * 2 ^ 59
def prefixEnd_18257 : Nat := 4983230072969 + 3 ^ 40 * 18257 * 2
def baseEnd_18257 : Nat := 694416022906689118781

theorem tailTrace_18257 : CollatzResearch.WordTrace tailWord_18257 prefixEnd_18257 694416022906689118781 := by
  unfold tailWord_18257
  simp only [CollatzResearch.WordTrace]
  refine ⟨665887494865481892469025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 443924996576987928312683 665887494865481892469025)
  ·
    refine ⟨499415621149111419351769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 665887494865481892469025 499415621149111419351769)
    ·
      refine ⟨374561715861833564513827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 499415621149111419351769 374561715861833564513827)
      ·
        refine ⟨561842573792750346770741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374561715861833564513827 561842573792750346770741)
        ·
          refine ⟨52672741293070345009757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 561842573792750346770741 52672741293070345009757)
          ·
            refine ⟨19752277984901379378659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52672741293070345009757 19752277984901379378659)
            ·
              refine ⟨29628416977352069067989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19752277984901379378659 29628416977352069067989)
              ·
                refine ⟨694416022906689118781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29628416977352069067989 694416022906689118781)
                ·
                  rfl

theorem cell22_18257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 7].length) (baseStart_18257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18257 prefixEnd_18257 := by exact prefixLift 18257
  have htrace : WordTrace (prefixWord ++ tailWord_18257) baseStart_18257 baseEnd_18257 := by
    simpa [prefixWord, tailWord_18257, baseEnd_18257] using wordTrace_append hprefix tailTrace_18257
  have hstable : (prefixWord ++ tailWord_18257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18257).length < 2 ^ (prefixWord ++ tailWord_18257).sum := by decide
  have hdescent : baseEnd_18257 < baseStart_18257 := by decide
  rcases family_descends (prefixWord ++ tailWord_18257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18272 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 5, 3]
def baseStart_18272 : Nat := 118140960795 + 18272 * 2 ^ 59
def prefixEnd_18272 : Nat := 4983230072969 + 3 ^ 40 * 18272 * 2
def baseEnd_18272 : Nat := 6254879012705162943983

theorem tailTrace_18272 : CollatzResearch.WordTrace tailWord_18272 prefixEnd_18272 6254879012705162943983 := by
  unfold tailWord_18272
  simp only [CollatzResearch.WordTrace]
  refine ⟨333217294905569727132535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 444289726540759636176713 333217294905569727132535)
  ·
    refine ⟨499825942358354590698803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 333217294905569727132535 499825942358354590698803)
    ·
      refine ⟨749738913537531886048205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499825942358354590698803 749738913537531886048205)
      ·
        refine ⟨281152092576574457268077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 749738913537531886048205 281152092576574457268077)
        ·
          refine ⟨105432034716215421475529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281152092576574457268077 105432034716215421475529)
          ·
            refine ⟨79074026037161566106647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105432034716215421475529 79074026037161566106647)
            ·
              refine ⟨118611039055742349159971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79074026037161566106647 118611039055742349159971)
              ·
                refine ⟨177916558583613523739957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118611039055742349159971 177916558583613523739957)
                ·
                  refine ⟨16679677367213767850621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177916558583613523739957 16679677367213767850621)
                  ·
                    refine ⟨6254879012705162943983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16679677367213767850621 6254879012705162943983)
                    ·
                      rfl

theorem cell22_18272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_18272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18272 prefixEnd_18272 := by exact prefixLift 18272
  have htrace : WordTrace (prefixWord ++ tailWord_18272) baseStart_18272 baseEnd_18272 := by
    simpa [prefixWord, tailWord_18272, baseEnd_18272] using wordTrace_append hprefix tailTrace_18272
  have hstable : (prefixWord ++ tailWord_18272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18272).length < 2 ^ (prefixWord ++ tailWord_18272).sum := by decide
  have hdescent : baseEnd_18272 < baseStart_18272 := by decide
  rcases family_descends (prefixWord ++ tailWord_18272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18274 : List Nat := [3, 3, 2, 1, 2, 2, 3, 6]
def baseStart_18274 : Nat := 118140960795 + 18274 * 2 ^ 59
def prefixEnd_18274 : Nat := 4983230072969 + 3 ^ 40 * 18274 * 2
def baseEnd_18274 : Nat := 695062628175313821553

theorem tailTrace_18274 : CollatzResearch.WordTrace tailWord_18274 prefixEnd_18274 695062628175313821553 := by
  unfold tailWord_18274
  simp only [CollatzResearch.WordTrace]
  refine ⟨166626883950973448959469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 444338357202595863891917 166626883950973448959469)
  ·
    refine ⟨62485081481615043359801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166626883950973448959469 62485081481615043359801)
    ·
      refine ⟨46863811111211282519851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62485081481615043359801 46863811111211282519851)
      ·
        refine ⟨70295716666816923779777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46863811111211282519851 70295716666816923779777)
        ·
          refine ⟨52721787500112692834833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70295716666816923779777 52721787500112692834833)
          ·
            refine ⟨39541340625084519626125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52721787500112692834833 39541340625084519626125)
            ·
              refine ⟨14828002734406694859797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39541340625084519626125 14828002734406694859797)
              ·
                refine ⟨695062628175313821553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14828002734406694859797 695062628175313821553)
                ·
                  rfl

theorem cell22_18274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_18274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18274 prefixEnd_18274 := by exact prefixLift 18274
  have htrace : WordTrace (prefixWord ++ tailWord_18274) baseStart_18274 baseEnd_18274 := by
    simpa [prefixWord, tailWord_18274, baseEnd_18274] using wordTrace_append hprefix tailTrace_18274
  have hstable : (prefixWord ++ tailWord_18274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18274).length < 2 ^ (prefixWord ++ tailWord_18274).sum := by decide
  have hdescent : baseEnd_18274 < baseStart_18274 := by decide
  rcases family_descends (prefixWord ++ tailWord_18274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18276 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_18276 : Nat := 118140960795 + 18276 * 2 ^ 59
def prefixEnd_18276 : Nat := 4983230072969 + 3 ^ 40 * 18276 * 2
def baseEnd_18276 : Nat := 6256248294450485843971

theorem tailTrace_18276 : CollatzResearch.WordTrace tailWord_18276 prefixEnd_18276 6256248294450485843971 := by
  unfold tailWord_18276
  simp only [CollatzResearch.WordTrace]
  refine ⟨333290240898324068705341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 444386987864432091607121 333290240898324068705341)
  ·
    refine ⟨124983840336871525764503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 333290240898324068705341 124983840336871525764503)
    ·
      refine ⟨187475760505307288646755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124983840336871525764503 187475760505307288646755)
      ·
        refine ⟨281213640757960932970133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187475760505307288646755 281213640757960932970133)
        ·
          refine ⟨13181889410529418732975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 281213640757960932970133 13181889410529418732975)
          ·
            refine ⟨19772834115794128099463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13181889410529418732975 19772834115794128099463)
            ·
              refine ⟨29659251173691192149195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19772834115794128099463 29659251173691192149195)
              ·
                refine ⟨44488876760536788223793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29659251173691192149195 44488876760536788223793)
                ·
                  refine ⟨33366657570402591167845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44488876760536788223793 33366657570402591167845)
                  ·
                    refine ⟨6256248294450485843971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33366657570402591167845 6256248294450485843971)
                    ·
                      rfl

theorem cell22_18276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_18276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18276 prefixEnd_18276 := by exact prefixLift 18276
  have htrace : WordTrace (prefixWord ++ tailWord_18276) baseStart_18276 baseEnd_18276 := by
    simpa [prefixWord, tailWord_18276, baseEnd_18276] using wordTrace_append hprefix tailTrace_18276
  have hstable : (prefixWord ++ tailWord_18276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18276).length < 2 ^ (prefixWord ++ tailWord_18276).sum := by decide
  have hdescent : baseEnd_18276 < baseStart_18276 := by decide
  rcases family_descends (prefixWord ++ tailWord_18276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18379 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 2, 3]
def baseStart_18379 : Nat := 118140960795 + 18379 * 2 ^ 59
def prefixEnd_18379 : Nat := 4983230072969 + 3 ^ 40 * 18379 * 2
def baseEnd_18379 : Nat := 6291507299392550518655

theorem tailTrace_18379 : CollatzResearch.WordTrace tailWord_18379 prefixEnd_18379 6291507299392550518655 := by
  unfold tailWord_18379
  simp only [CollatzResearch.WordTrace]
  refine ⟨670337200423496728410191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 446891466948997818940127 670337200423496728410191)
  ·
    refine ⟨1005505800635245092615287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670337200423496728410191 1005505800635245092615287)
    ·
      refine ⟨1508258700952867638922931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005505800635245092615287 1508258700952867638922931)
      ·
        refine ⟨2262388051429301458384397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508258700952867638922931 2262388051429301458384397)
        ·
          refine ⟨848395519285988046894149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2262388051429301458384397 848395519285988046894149)
          ·
            refine ⟨159074159866122758792653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 848395519285988046894149 159074159866122758792653)
            ·
              refine ⟨59652809949796034547245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159074159866122758792653 59652809949796034547245)
              ·
                refine ⟨22369803731173512955217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59652809949796034547245 22369803731173512955217)
                ·
                  refine ⟨16777352798380134716413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22369803731173512955217 16777352798380134716413)
                  ·
                    refine ⟨6291507299392550518655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16777352798380134716413 6291507299392550518655)
                    ·
                      rfl

theorem cell22_18379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 3].length) (baseStart_18379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18379 prefixEnd_18379 := by exact prefixLift 18379
  have htrace : WordTrace (prefixWord ++ tailWord_18379) baseStart_18379 baseEnd_18379 := by
    simpa [prefixWord, tailWord_18379, baseEnd_18379] using wordTrace_append hprefix tailTrace_18379
  have hstable : (prefixWord ++ tailWord_18379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18379).length < 2 ^ (prefixWord ++ tailWord_18379).sum := by decide
  have hdescent : baseEnd_18379 < baseStart_18379 := by decide
  rcases family_descends (prefixWord ++ tailWord_18379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18458 : List Nat := [3, 1, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_18458 : Nat := 118140960795 + 18458 * 2 ^ 59
def prefixEnd_18458 : Nat := 4983230072969 + 3 ^ 40 * 18458 * 2
def baseEnd_18458 : Nat := 6318550613862677793413

theorem tailTrace_18458 : CollatzResearch.WordTrace tailWord_18458 prefixEnd_18458 6318550613862677793413 := by
  unfold tailWord_18458
  simp only [CollatzResearch.WordTrace]
  refine ⟨168304641784323305134007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 448812378091528813690685 168304641784323305134007)
  ·
    refine ⟨252456962676484957701011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168304641784323305134007 252456962676484957701011)
    ·
      refine ⟨378685444014727436551517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252456962676484957701011 378685444014727436551517)
      ·
        refine ⟨142007041505522788706819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 378685444014727436551517 142007041505522788706819)
        ·
          refine ⟨213010562258284183060229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142007041505522788706819 213010562258284183060229)
          ·
            refine ⟨39939480423428284323793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213010562258284183060229 39939480423428284323793)
            ·
              refine ⟨29954610317571213242845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39939480423428284323793 29954610317571213242845)
              ·
                refine ⟨11232978869089204966067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29954610317571213242845 11232978869089204966067)
                ·
                  refine ⟨16849468303633807449101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11232978869089204966067 16849468303633807449101)
                  ·
                    refine ⟨6318550613862677793413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16849468303633807449101 6318550613862677793413)
                    ·
                      rfl

theorem cell22_18458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_18458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18458 prefixEnd_18458 := by exact prefixLift 18458
  have htrace : WordTrace (prefixWord ++ tailWord_18458) baseStart_18458 baseEnd_18458 := by
    simpa [prefixWord, tailWord_18458, baseEnd_18458] using wordTrace_append hprefix tailTrace_18458
  have hstable : (prefixWord ++ tailWord_18458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18458).length < 2 ^ (prefixWord ++ tailWord_18458).sum := by decide
  have hdescent : baseEnd_18458 < baseStart_18458 := by decide
  rcases family_descends (prefixWord ++ tailWord_18458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18471 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 7]
def baseStart_18471 : Nat := 118140960795 + 18471 * 2 ^ 59
def prefixEnd_18471 : Nat := 4983230072969 + 3 ^ 40 * 18471 * 2
def baseEnd_18471 : Nat := 2107666926511659072791

theorem tailTrace_18471 : CollatzResearch.WordTrace tailWord_18471 prefixEnd_18471 2107666926511659072791 := by
  unfold tailWord_18471
  simp only [CollatzResearch.WordTrace]
  refine ⟨673692716090196440759267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 449128477393464293839511 673692716090196440759267)
  ·
    refine ⟨1010539074135294661138901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673692716090196440759267 1010539074135294661138901)
    ·
      refine ⟨23684509550045968620443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1010539074135294661138901 23684509550045968620443)
      ·
        refine ⟨35526764325068952930665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23684509550045968620443 35526764325068952930665)
        ·
          refine ⟨26645073243801714697999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35526764325068952930665 26645073243801714697999)
          ·
            refine ⟨39967609865702572046999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26645073243801714697999 39967609865702572046999)
            ·
              refine ⟨59951414798553858070499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39967609865702572046999 59951414798553858070499)
              ·
                refine ⟨89927122197830787105749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59951414798553858070499 89927122197830787105749)
                ·
                  refine ⟨2107666926511659072791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 89927122197830787105749 2107666926511659072791)
                  ·
                    rfl

theorem cell22_18471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 7].length) (baseStart_18471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18471 prefixEnd_18471 := by exact prefixLift 18471
  have htrace : WordTrace (prefixWord ++ tailWord_18471) baseStart_18471 baseEnd_18471 := by
    simpa [prefixWord, tailWord_18471, baseEnd_18471] using wordTrace_append hprefix tailTrace_18471
  have hstable : (prefixWord ++ tailWord_18471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18471).length < 2 ^ (prefixWord ++ tailWord_18471).sum := by decide
  have hdescent : baseEnd_18471 < baseStart_18471 := by decide
  rcases family_descends (prefixWord ++ tailWord_18471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18533 : List Nat := [1, 3, 1, 3, 2, 3, 3, 2, 4]
def baseStart_18533 : Nat := 118140960795 + 18533 * 2 ^ 59
def prefixEnd_18533 : Nat := 4983230072969 + 3 ^ 40 * 18533 * 2
def baseEnd_18533 : Nat := 2114741548862494056061

theorem tailTrace_18533 : CollatzResearch.WordTrace tailWord_18533 prefixEnd_18533 2114741548862494056061 := by
  unfold tailWord_18533
  simp only [CollatzResearch.WordTrace]
  refine ⟨675954041865581029516253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 450636027910387353010835 675954041865581029516253)
  ·
    refine ⟨253482765699592886068595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 675954041865581029516253 253482765699592886068595)
    ·
      refine ⟨380224148549389329102893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253482765699592886068595 380224148549389329102893)
      ·
        refine ⟨142584055706020998413585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380224148549389329102893 142584055706020998413585)
        ·
          refine ⟨106938041779515748810189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142584055706020998413585 106938041779515748810189)
          ·
            refine ⟨40101765667318405803821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106938041779515748810189 40101765667318405803821)
            ·
              refine ⟨15038162125244402176433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40101765667318405803821 15038162125244402176433)
              ·
                refine ⟨11278621593933301632325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15038162125244402176433 11278621593933301632325)
                ·
                  refine ⟨2114741548862494056061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11278621593933301632325 2114741548862494056061)
                  ·
                    rfl

theorem cell22_18533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_18533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18533 prefixEnd_18533 := by exact prefixLift 18533
  have htrace : WordTrace (prefixWord ++ tailWord_18533) baseStart_18533 baseEnd_18533 := by
    simpa [prefixWord, tailWord_18533, baseEnd_18533] using wordTrace_append hprefix tailTrace_18533
  have hstable : (prefixWord ++ tailWord_18533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18533).length < 2 ^ (prefixWord ++ tailWord_18533).sum := by decide
  have hdescent : baseEnd_18533 < baseStart_18533 := by decide
  rcases family_descends (prefixWord ++ tailWord_18533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18544 : List Nat := [2, 1, 1, 1, 5, 3, 2, 7]
def baseStart_18544 : Nat := 118140960795 + 18544 * 2 ^ 59
def prefixEnd_18544 : Nat := 4983230072969 + 3 ^ 40 * 18544 * 2
def baseEnd_18544 : Nat := 705332241265235571461

theorem tailTrace_18544 : CollatzResearch.WordTrace tailWord_18544 prefixEnd_18544 705332241265235571461 := by
  unfold tailWord_18544
  simp only [CollatzResearch.WordTrace]
  refine ⟨338177622412864954083343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 450903496550486605444457 338177622412864954083343)
  ·
    refine ⟨507266433619297431125015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 338177622412864954083343 507266433619297431125015)
    ·
      refine ⟨760899650428946146687523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507266433619297431125015 760899650428946146687523)
      ·
        refine ⟨1141349475643419220031285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760899650428946146687523 1141349475643419220031285)
        ·
          refine ⟨107001513341570551877933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1141349475643419220031285 107001513341570551877933)
          ·
            refine ⟨40125567503088956954225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107001513341570551877933 40125567503088956954225)
            ·
              refine ⟨30094175627316717715669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40125567503088956954225 30094175627316717715669)
              ·
                refine ⟨705332241265235571461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30094175627316717715669 705332241265235571461)
                ·
                  rfl

theorem cell22_18544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_18544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18544 prefixEnd_18544 := by exact prefixLift 18544
  have htrace : WordTrace (prefixWord ++ tailWord_18544) baseStart_18544 baseEnd_18544 := by
    simpa [prefixWord, tailWord_18544, baseEnd_18544] using wordTrace_append hprefix tailTrace_18544
  have hstable : (prefixWord ++ tailWord_18544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18544).length < 2 ^ (prefixWord ++ tailWord_18544).sum := by decide
  have hdescent : baseEnd_18544 < baseStart_18544 := by decide
  rcases family_descends (prefixWord ++ tailWord_18544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18612 : List Nat := [2, 5, 3, 1, 1, 1, 3, 6]
def baseStart_18612 : Nat := 118140960795 + 18612 * 2 ^ 59
def prefixEnd_18612 : Nat := 4983230072969 + 3 ^ 40 * 18612 * 2
def baseEnd_18612 : Nat := 707918662339734382549

theorem tailTrace_18612 : CollatzResearch.WordTrace tailWord_18612 prefixEnd_18612 707918662339734382549 := by
  unfold tailWord_18612
  simp only [CollatzResearch.WordTrace]
  refine ⟨339417704289688760821045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 452556939052918347761393 339417704289688760821045)
  ·
    refine ⟨31820409777158321326973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 339417704289688760821045 31820409777158321326973)
    ·
      refine ⟨11932653666434370497615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31820409777158321326973 11932653666434370497615)
      ·
        refine ⟨17898980499651555746423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11932653666434370497615 17898980499651555746423)
        ·
          refine ⟨26848470749477333619635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17898980499651555746423 26848470749477333619635)
          ·
            refine ⟨40272706124216000429453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26848470749477333619635 40272706124216000429453)
            ·
              refine ⟨15102264796581000161045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40272706124216000429453 15102264796581000161045)
              ·
                refine ⟨707918662339734382549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15102264796581000161045 707918662339734382549)
                ·
                  rfl

theorem cell22_18612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 6].length) (baseStart_18612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18612 prefixEnd_18612 := by exact prefixLift 18612
  have htrace : WordTrace (prefixWord ++ tailWord_18612) baseStart_18612 baseEnd_18612 := by
    simpa [prefixWord, tailWord_18612, baseEnd_18612] using wordTrace_append hprefix tailTrace_18612
  have hstable : (prefixWord ++ tailWord_18612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18612).length < 2 ^ (prefixWord ++ tailWord_18612).sum := by decide
  have hdescent : baseEnd_18612 < baseStart_18612 := by decide
  rcases family_descends (prefixWord ++ tailWord_18612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18619 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 3, 4]
def baseStart_18619 : Nat := 118140960795 + 18619 * 2 ^ 59
def prefixEnd_18619 : Nat := 4983230072969 + 3 ^ 40 * 18619 * 2
def baseEnd_18619 : Nat := 6373664204111924517919

theorem tailTrace_18619 : CollatzResearch.WordTrace tailWord_18619 prefixEnd_18619 6373664204111924517919 := by
  unfold tailWord_18619
  simp only [CollatzResearch.WordTrace]
  refine ⟨679090719554017717146911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 452727146369345144764607 679090719554017717146911)
  ·
    refine ⟨1018636079331026575720367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 679090719554017717146911 1018636079331026575720367)
    ·
      refine ⟨1527954118996539863580551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018636079331026575720367 1527954118996539863580551)
      ·
        refine ⟨2291931178494809795370827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527954118996539863580551 2291931178494809795370827)
        ·
          refine ⟨3437896767742214693056241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291931178494809795370827 3437896767742214693056241)
          ·
            refine ⟨2578422575806661019792181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3437896767742214693056241 2578422575806661019792181)
            ·
              refine ⟨241727116481874470605517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2578422575806661019792181 241727116481874470605517)
              ·
                refine ⟨90647668680702926477069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241727116481874470605517 90647668680702926477069)
                ·
                  refine ⟨33992875755263597428901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90647668680702926477069 33992875755263597428901)
                  ·
                    refine ⟨6373664204111924517919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33992875755263597428901 6373664204111924517919)
                    ·
                      rfl

theorem cell22_18619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_18619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18619 prefixEnd_18619 := by exact prefixLift 18619
  have htrace : WordTrace (prefixWord ++ tailWord_18619) baseStart_18619 baseEnd_18619 := by
    simpa [prefixWord, tailWord_18619, baseEnd_18619] using wordTrace_append hprefix tailTrace_18619
  have hstable : (prefixWord ++ tailWord_18619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18619).length < 2 ^ (prefixWord ++ tailWord_18619).sum := by decide
  have hdescent : baseEnd_18619 < baseStart_18619 := by decide
  rcases family_descends (prefixWord ++ tailWord_18619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18634 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_18634 : Nat := 118140960795 + 18634 * 2 ^ 59
def prefixEnd_18634 : Nat := 4983230072969 + 3 ^ 40 * 18634 * 2
def baseEnd_18634 : Nat := 2126266336885628464291

theorem tailTrace_18634 : CollatzResearch.WordTrace tailWord_18634 prefixEnd_18634 2126266336885628464291 := by
  unfold tailWord_18634
  simp only [CollatzResearch.WordTrace]
  refine ⟨169909453624918819735739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 453091876333116852628637 169909453624918819735739)
  ·
    refine ⟨254864180437378229603609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169909453624918819735739 254864180437378229603609)
    ·
      refine ⟨191148135328033672202707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254864180437378229603609 191148135328033672202707)
      ·
        refine ⟨286722202992050508304061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191148135328033672202707 286722202992050508304061)
        ·
          refine ⟨107520826122018940614023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286722202992050508304061 107520826122018940614023)
          ·
            refine ⟨161281239183028410921035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107520826122018940614023 161281239183028410921035)
            ·
              refine ⟨241921858774542616381553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161281239183028410921035 241921858774542616381553)
              ·
                refine ⟨181441394080906962286165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241921858774542616381553 181441394080906962286165)
                ·
                  refine ⟨2126266336885628464291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 181441394080906962286165 2126266336885628464291)
                  ·
                    rfl

theorem cell22_18634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_18634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18634 prefixEnd_18634 := by exact prefixLift 18634
  have htrace : WordTrace (prefixWord ++ tailWord_18634) baseStart_18634 baseEnd_18634 := by
    simpa [prefixWord, tailWord_18634, baseEnd_18634] using wordTrace_append hprefix tailTrace_18634
  have hstable : (prefixWord ++ tailWord_18634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18634).length < 2 ^ (prefixWord ++ tailWord_18634).sum := by decide
  have hdescent : baseEnd_18634 < baseStart_18634 := by decide
  rcases family_descends (prefixWord ++ tailWord_18634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18649 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_18649 : Nat := 118140960795 + 18649 * 2 ^ 59
def prefixEnd_18649 : Nat := 4983230072969 + 3 ^ 40 * 18649 * 2
def baseEnd_18649 : Nat := 6383933817201846267827

theorem tailTrace_18649 : CollatzResearch.WordTrace tailWord_18649 prefixEnd_18649 6383933817201846267827 := by
  unfold tailWord_18649
  simp only [CollatzResearch.WordTrace]
  refine ⟨680184909445332840739001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 453456606296888560492667 680184909445332840739001)
  ·
    refine ⟨510138682083999630554251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 680184909445332840739001 510138682083999630554251)
    ·
      refine ⟨765208023125999445831377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510138682083999630554251 765208023125999445831377)
      ·
        refine ⟨573906017344499584373533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 765208023125999445831377 573906017344499584373533)
        ·
          refine ⟨215214756504187344140075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 573906017344499584373533 215214756504187344140075)
          ·
            refine ⟨322822134756281016210113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215214756504187344140075 322822134756281016210113)
            ·
              refine ⟨242116601067210762157585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322822134756281016210113 242116601067210762157585)
              ·
                refine ⟨181587450800408071618189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242116601067210762157585 181587450800408071618189)
                ·
                  refine ⟨68095294050153026856821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181587450800408071618189 68095294050153026856821)
                  ·
                    refine ⟨6383933817201846267827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68095294050153026856821 6383933817201846267827)
                    ·
                      rfl

theorem cell22_18649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_18649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18649 prefixEnd_18649 := by exact prefixLift 18649
  have htrace : WordTrace (prefixWord ++ tailWord_18649) baseStart_18649 baseEnd_18649 := by
    simpa [prefixWord, tailWord_18649, baseEnd_18649] using wordTrace_append hprefix tailTrace_18649
  have hstable : (prefixWord ++ tailWord_18649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18649).length < 2 ^ (prefixWord ++ tailWord_18649).sum := by decide
  have hdescent : baseEnd_18649 < baseStart_18649 := by decide
  rcases family_descends (prefixWord ++ tailWord_18649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18696 : List Nat := [2, 1, 3, 2, 3, 3, 8]
def baseStart_18696 : Nat := 118140960795 + 18696 * 2 ^ 59
def prefixEnd_18696 : Nat := 4983230072969 + 3 ^ 40 * 18696 * 2
def baseEnd_18696 : Nat := 237037884359607049729

theorem tailTrace_18696 : CollatzResearch.WordTrace tailWord_18696 prefixEnd_18696 237037884359607049729 := by
  unfold tailWord_18696
  simp only [CollatzResearch.WordTrace]
  refine ⟨340949570137529933849971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 454599426850039911799961 340949570137529933849971)
  ·
    refine ⟨511424355206294900774957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 340949570137529933849971 511424355206294900774957)
    ·
      refine ⟨191784133202360587790609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 511424355206294900774957 191784133202360587790609)
      ·
        refine ⟨143838099901770440842957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191784133202360587790609 143838099901770440842957)
        ·
          refine ⟨53939287463163915316109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143838099901770440842957 53939287463163915316109)
          ·
            refine ⟨20227232798686468243541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53939287463163915316109 20227232798686468243541)
            ·
              refine ⟨237037884359607049729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 20227232798686468243541 237037884359607049729)
              ·
                rfl

theorem cell22_18696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 8].length) (baseStart_18696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18696 prefixEnd_18696 := by exact prefixLift 18696
  have htrace : WordTrace (prefixWord ++ tailWord_18696) baseStart_18696 baseEnd_18696 := by
    simpa [prefixWord, tailWord_18696, baseEnd_18696] using wordTrace_append hprefix tailTrace_18696
  have hstable : (prefixWord ++ tailWord_18696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18696).length < 2 ^ (prefixWord ++ tailWord_18696).sum := by decide
  have hdescent : baseEnd_18696 < baseStart_18696 := by decide
  rcases family_descends (prefixWord ++ tailWord_18696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18773 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_18773 : Nat := 118140960795 + 18773 * 2 ^ 59
def prefixEnd_18773 : Nat := 4983230072969 + 3 ^ 40 * 18773 * 2
def baseEnd_18773 : Nat := 6426381551306856167447

theorem tailTrace_18773 : CollatzResearch.WordTrace tailWord_18773 prefixEnd_18773 6426381551306856167447 := by
  unfold tailWord_18773
  simp only [CollatzResearch.WordTrace]
  refine ⟨684707560996102018252973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 456471707330734678835315 684707560996102018252973)
  ·
    refine ⟨256765335373538256844865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 684707560996102018252973 256765335373538256844865)
    ·
      refine ⟨192574001530153692633649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256765335373538256844865 192574001530153692633649)
      ·
        refine ⟨144430501147615269475237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192574001530153692633649 144430501147615269475237)
        ·
          refine ⟨27080718965177863026607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144430501147615269475237 27080718965177863026607)
          ·
            refine ⟨40621078447766794539911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27080718965177863026607 40621078447766794539911)
            ·
              refine ⟨60931617671650191809867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40621078447766794539911 60931617671650191809867)
              ·
                refine ⟨91397426507475287714801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60931617671650191809867 91397426507475287714801)
                ·
                  refine ⟨68548069880606465786101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91397426507475287714801 68548069880606465786101)
                  ·
                    refine ⟨6426381551306856167447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68548069880606465786101 6426381551306856167447)
                    ·
                      rfl

theorem cell22_18773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_18773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18773 prefixEnd_18773 := by exact prefixLift 18773
  have htrace : WordTrace (prefixWord ++ tailWord_18773) baseStart_18773 baseEnd_18773 := by
    simpa [prefixWord, tailWord_18773, baseEnd_18773] using wordTrace_append hprefix tailTrace_18773
  have hstable : (prefixWord ++ tailWord_18773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18773).length < 2 ^ (prefixWord ++ tailWord_18773).sum := by decide
  have hdescent : baseEnd_18773 < baseStart_18773 := by decide
  rcases family_descends (prefixWord ++ tailWord_18773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18788 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_18788 : Nat := 118140960795 + 18788 * 2 ^ 59
def prefixEnd_18788 : Nat := 4983230072969 + 3 ^ 40 * 18788 * 2
def baseEnd_18788 : Nat := 6431516357851817042401

theorem tailTrace_18788 : CollatzResearch.WordTrace tailWord_18788 prefixEnd_18788 6431516357851817042401 := by
  unfold tailWord_18788
  simp only [CollatzResearch.WordTrace]
  refine ⟨342627327970879790024509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 456836437294506386699345 342627327970879790024509)
  ·
    refine ⟨128485247989079921259191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 342627327970879790024509 128485247989079921259191)
    ·
      refine ⟨192727871983619881888787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128485247989079921259191 192727871983619881888787)
      ·
        refine ⟨289091807975429822833181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192727871983619881888787 289091807975429822833181)
        ·
          refine ⟨108409427990786183562443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 289091807975429822833181 108409427990786183562443)
          ·
            refine ⟨162614141986179275343665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108409427990786183562443 162614141986179275343665)
            ·
              refine ⟨121960606489634456507749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162614141986179275343665 121960606489634456507749)
              ·
                refine ⟨22867613716806460595203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121960606489634456507749 22867613716806460595203)
                ·
                  refine ⟨34301420575209690892805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22867613716806460595203 34301420575209690892805)
                  ·
                    refine ⟨6431516357851817042401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34301420575209690892805 6431516357851817042401)
                    ·
                      rfl

theorem cell22_18788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_18788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18788 prefixEnd_18788 := by exact prefixLift 18788
  have htrace : WordTrace (prefixWord ++ tailWord_18788) baseStart_18788 baseEnd_18788 := by
    simpa [prefixWord, tailWord_18788, baseEnd_18788] using wordTrace_append hprefix tailTrace_18788
  have hstable : (prefixWord ++ tailWord_18788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18788).length < 2 ^ (prefixWord ++ tailWord_18788).sum := by decide
  have hdescent : baseEnd_18788 < baseStart_18788 := by decide
  rcases family_descends (prefixWord ++ tailWord_18788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18805 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_18805 : Nat := 118140960795 + 18805 * 2 ^ 59
def prefixEnd_18805 : Nat := 4983230072969 + 3 ^ 40 * 18805 * 2
def baseEnd_18805 : Nat := 6437335805269439367349

theorem tailTrace_18805 : CollatzResearch.WordTrace tailWord_18805 prefixEnd_18805 6437335805269439367349 := by
  unfold tailWord_18805
  simp only [CollatzResearch.WordTrace]
  refine ⟨685874696880171483417869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 457249797920114322278579 685874696880171483417869)
  ·
    refine ⟨257203011330064306281701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 685874696880171483417869 257203011330064306281701)
    ·
      refine ⟨48225564624387057427819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257203011330064306281701 48225564624387057427819)
      ·
        refine ⟨72338346936580586141729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48225564624387057427819 72338346936580586141729)
        ·
          refine ⟨54253760202435439606297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72338346936580586141729 54253760202435439606297)
          ·
            refine ⟨40690320151826579704723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54253760202435439606297 40690320151826579704723)
            ·
              refine ⟨61035480227739869557085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40690320151826579704723 61035480227739869557085)
              ·
                refine ⟨22888305085402451083907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61035480227739869557085 22888305085402451083907)
                ·
                  refine ⟨34332457628103676625861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22888305085402451083907 34332457628103676625861)
                  ·
                    refine ⟨6437335805269439367349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34332457628103676625861 6437335805269439367349)
                    ·
                      rfl

theorem cell22_18805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_18805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18805 prefixEnd_18805 := by exact prefixLift 18805
  have htrace : WordTrace (prefixWord ++ tailWord_18805) baseStart_18805 baseEnd_18805 := by
    simpa [prefixWord, tailWord_18805, baseEnd_18805] using wordTrace_append hprefix tailTrace_18805
  have hstable : (prefixWord ++ tailWord_18805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18805).length < 2 ^ (prefixWord ++ tailWord_18805).sum := by decide
  have hdescent : baseEnd_18805 < baseStart_18805 := by decide
  rcases family_descends (prefixWord ++ tailWord_18805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18848 : List Nat := [2, 1, 1, 4, 1, 3, 4, 6]
def baseStart_18848 : Nat := 118140960795 + 18848 * 2 ^ 59
def prefixEnd_18848 : Nat := 4983230072969 + 3 ^ 40 * 18848 * 2
def baseEnd_18848 : Nat := 716895064892406726913

theorem tailTrace_18848 : CollatzResearch.WordTrace tailWord_18848 prefixEnd_18848 716895064892406726913 := by
  unfold tailWord_18848
  simp only [CollatzResearch.WordTrace]
  refine ⟨343721517862194913616599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 458295357149593218155465 343721517862194913616599)
  ·
    refine ⟨515582276793292370424899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 343721517862194913616599 515582276793292370424899)
    ·
      refine ⟨773373415189938555637349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515582276793292370424899 773373415189938555637349)
      ·
        refine ⟨145007515348113479182003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 773373415189938555637349 145007515348113479182003)
        ·
          refine ⟨217511273022170218773005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145007515348113479182003 217511273022170218773005)
          ·
            refine ⟨81566727383313832039877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217511273022170218773005 81566727383313832039877)
            ·
              refine ⟨15293761384371343507477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81566727383313832039877 15293761384371343507477)
              ·
                refine ⟨716895064892406726913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15293761384371343507477 716895064892406726913)
                ·
                  rfl

theorem cell22_18848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 6].length) (baseStart_18848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18848 prefixEnd_18848 := by exact prefixLift 18848
  have htrace : WordTrace (prefixWord ++ tailWord_18848) baseStart_18848 baseEnd_18848 := by
    simpa [prefixWord, tailWord_18848, baseEnd_18848] using wordTrace_append hprefix tailTrace_18848
  have hstable : (prefixWord ++ tailWord_18848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18848).length < 2 ^ (prefixWord ++ tailWord_18848).sum := by decide
  have hdescent : baseEnd_18848 < baseStart_18848 := by decide
  rcases family_descends (prefixWord ++ tailWord_18848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18891 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 1, 7]
def baseStart_18891 : Nat := 118140960795 + 18891 * 2 ^ 59
def prefixEnd_18891 : Nat := 4983230072969 + 3 ^ 40 * 18891 * 2
def baseEnd_18891 : Nat := 6466775362793881717085

theorem tailTrace_18891 : CollatzResearch.WordTrace tailWord_18891 prefixEnd_18891 6466775362793881717085 := by
  unfold tailWord_18891
  simp only [CollatzResearch.WordTrace]
  refine ⟨689011374568608171048527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 459340916379072114032351 689011374568608171048527)
  ·
    refine ⟨1033517061852912256572791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 689011374568608171048527 1033517061852912256572791)
    ·
      refine ⟨1550275592779368384859187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033517061852912256572791 1550275592779368384859187)
      ·
        refine ⟨2325413389169052577288781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550275592779368384859187 2325413389169052577288781)
        ·
          refine ⟨872030020938394716483293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2325413389169052577288781 872030020938394716483293)
          ·
            refine ⟨327011257851898018681235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 872030020938394716483293 327011257851898018681235)
            ·
              refine ⟨490516886777847028021853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327011257851898018681235 490516886777847028021853)
              ·
                refine ⟨183943832541692635508195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 490516886777847028021853 183943832541692635508195)
                ·
                  refine ⟨275915748812538953262293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183943832541692635508195 275915748812538953262293)
                  ·
                    refine ⟨6466775362793881717085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 275915748812538953262293 6466775362793881717085)
                    ·
                      rfl

theorem cell22_18891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_18891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18891 prefixEnd_18891 := by exact prefixLift 18891
  have htrace : WordTrace (prefixWord ++ tailWord_18891) baseStart_18891 baseEnd_18891 := by
    simpa [prefixWord, tailWord_18891, baseEnd_18891] using wordTrace_append hprefix tailTrace_18891
  have hstable : (prefixWord ++ tailWord_18891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18891).length < 2 ^ (prefixWord ++ tailWord_18891).sum := by decide
  have hdescent : baseEnd_18891 < baseStart_18891 := by decide
  rcases family_descends (prefixWord ++ tailWord_18891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18921 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 10]
def baseStart_18921 : Nat := 118140960795 + 18921 * 2 ^ 59
def prefixEnd_18921 : Nat := 4983230072969 + 3 ^ 40 * 18921 * 2
def baseEnd_18921 : Nat := 2159014991961267822331

theorem tailTrace_18921 : CollatzResearch.WordTrace tailWord_18921 prefixEnd_18921 2159014991961267822331 := by
  unfold tailWord_18921
  simp only [CollatzResearch.WordTrace]
  refine ⟨690105564459923294640617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 460070376306615529760411 690105564459923294640617)
  ·
    refine ⟨517579173344942470980463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 690105564459923294640617 517579173344942470980463)
    ·
      refine ⟨776368760017413706470695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517579173344942470980463 776368760017413706470695)
      ·
        refine ⟨1164553140026120559706043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776368760017413706470695 1164553140026120559706043)
        ·
          refine ⟨1746829710039180839559065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164553140026120559706043 1746829710039180839559065)
          ·
            refine ⟨1310122282529385629669299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1746829710039180839559065 1310122282529385629669299)
            ·
              refine ⟨1965183423794078444503949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310122282529385629669299 1965183423794078444503949)
              ·
                refine ⟨736943783922779416688981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1965183423794078444503949 736943783922779416688981)
                ·
                  refine ⟨2159014991961267822331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 736943783922779416688981 2159014991961267822331)
                  ·
                    rfl

theorem cell22_18921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_18921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18921 prefixEnd_18921 := by exact prefixLift 18921
  have htrace : WordTrace (prefixWord ++ tailWord_18921) baseStart_18921 baseEnd_18921 := by
    simpa [prefixWord, tailWord_18921, baseEnd_18921] using wordTrace_append hprefix tailTrace_18921
  have hstable : (prefixWord ++ tailWord_18921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18921).length < 2 ^ (prefixWord ++ tailWord_18921).sum := by decide
  have hdescent : baseEnd_18921 < baseStart_18921 := by decide
  rcases family_descends (prefixWord ++ tailWord_18921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18972 : List Nat := [2, 2, 3, 1, 2, 3, 2, 3, 4]
def baseStart_18972 : Nat := 118140960795 + 18972 * 2 ^ 59
def prefixEnd_18972 : Nat := 4983230072969 + 3 ^ 40 * 18972 * 2
def baseEnd_18972 : Nat := 2164834439378890147279

theorem tailTrace_18972 : CollatzResearch.WordTrace tailWord_18972 prefixEnd_18972 2164834439378890147279 := by
  unfold tailWord_18972
  simp only [CollatzResearch.WordTrace]
  refine ⟨345982843637579502373585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 461310458183439336498113 345982843637579502373585)
  ·
    refine ⟨259487132728184626780189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 345982843637579502373585 259487132728184626780189)
    ·
      refine ⟨97307674773069235042571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259487132728184626780189 97307674773069235042571)
      ·
        refine ⟨145961512159603852563857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97307674773069235042571 145961512159603852563857)
        ·
          refine ⟨109471134119702889422893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145961512159603852563857 109471134119702889422893)
          ·
            refine ⟨41051675294888583533585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109471134119702889422893 41051675294888583533585)
            ·
              refine ⟨30788756471166437650189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41051675294888583533585 30788756471166437650189)
              ·
                refine ⟨11545783676687414118821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30788756471166437650189 11545783676687414118821)
                ·
                  refine ⟨2164834439378890147279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11545783676687414118821 2164834439378890147279)
                  ·
                    rfl

theorem cell22_18972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_18972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18972 prefixEnd_18972 := by exact prefixLift 18972
  have htrace : WordTrace (prefixWord ++ tailWord_18972) baseStart_18972 baseEnd_18972 := by
    simpa [prefixWord, tailWord_18972, baseEnd_18972] using wordTrace_append hprefix tailTrace_18972
  have hstable : (prefixWord ++ tailWord_18972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18972).length < 2 ^ (prefixWord ++ tailWord_18972).sum := by decide
  have hdescent : baseEnd_18972 < baseStart_18972 := by decide
  rcases family_descends (prefixWord ++ tailWord_18972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19004 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_19004 : Nat := 118140960795 + 19004 * 2 ^ 59
def prefixEnd_19004 : Nat := 4983230072969 + 3 ^ 40 * 19004 * 2
def baseEnd_19004 : Nat := 6505457572099253641739

theorem tailTrace_19004 : CollatzResearch.WordTrace tailWord_19004 prefixEnd_19004 6505457572099253641739 := by
  unfold tailWord_19004
  simp only [CollatzResearch.WordTrace]
  refine ⟨346566411579614234956033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 462088548772818979941377 346566411579614234956033)
  ·
    refine ⟨259924808684710676217025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 346566411579614234956033 259924808684710676217025)
    ·
      refine ⟨194943606513533007162769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259924808684710676217025 194943606513533007162769)
      ·
        refine ⟨146207704885149755372077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194943606513533007162769 146207704885149755372077)
        ·
          refine ⟨54827889331931158264529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146207704885149755372077 54827889331931158264529)
          ·
            refine ⟨41120916998948368698397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54827889331931158264529 41120916998948368698397)
            ·
              refine ⟨15420343874605638261899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41120916998948368698397 15420343874605638261899)
              ·
                refine ⟨23130515811908457392849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15420343874605638261899 23130515811908457392849)
                ·
                  refine ⟨17347886858931343044637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23130515811908457392849 17347886858931343044637)
                  ·
                    refine ⟨6505457572099253641739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17347886858931343044637 6505457572099253641739)
                    ·
                      rfl

theorem cell22_19004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_19004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19004 prefixEnd_19004 := by exact prefixLift 19004
  have htrace : WordTrace (prefixWord ++ tailWord_19004) baseStart_19004 baseEnd_19004 := by
    simpa [prefixWord, tailWord_19004, baseEnd_19004] using wordTrace_append hprefix tailTrace_19004
  have hstable : (prefixWord ++ tailWord_19004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19004).length < 2 ^ (prefixWord ++ tailWord_19004).sum := by decide
  have hdescent : baseEnd_19004 < baseStart_19004 := by decide
  rcases family_descends (prefixWord ++ tailWord_19004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19167 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 3, 3]
def baseStart_19167 : Nat := 118140960795 + 19167 * 2 ^ 59
def prefixEnd_19167 : Nat := 4983230072969 + 3 ^ 40 * 19167 * 2
def baseEnd_19167 : Nat := 6561255803221161816239

theorem tailTrace_19167 : CollatzResearch.WordTrace tailWord_19167 prefixEnd_19167 6561255803221161816239 := by
  unfold tailWord_19167
  simp only [CollatzResearch.WordTrace]
  refine ⟨699077921568707308095755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 466051947712471538730503 699077921568707308095755)
  ·
    refine ⟨1048616882353060962143633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699077921568707308095755 1048616882353060962143633)
    ·
      refine ⟨786462661764795721607725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1048616882353060962143633 786462661764795721607725)
      ·
        refine ⟨294923498161798395602897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 786462661764795721607725 294923498161798395602897)
        ·
          refine ⟨221192623621348796702173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294923498161798395602897 221192623621348796702173)
          ·
            refine ⟨82947233858005798763315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221192623621348796702173 82947233858005798763315)
            ·
              refine ⟨124420850787008698144973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82947233858005798763315 124420850787008698144973)
              ·
                refine ⟨46657819045128261804365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124420850787008698144973 46657819045128261804365)
                ·
                  refine ⟨17496682141923098176637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46657819045128261804365 17496682141923098176637)
                  ·
                    refine ⟨6561255803221161816239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17496682141923098176637 6561255803221161816239)
                    ·
                      rfl

theorem cell22_19167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_19167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19167 prefixEnd_19167 := by exact prefixLift 19167
  have htrace : WordTrace (prefixWord ++ tailWord_19167) baseStart_19167 baseEnd_19167 := by
    simpa [prefixWord, tailWord_19167, baseEnd_19167] using wordTrace_append hprefix tailTrace_19167
  have hstable : (prefixWord ++ tailWord_19167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19167).length < 2 ^ (prefixWord ++ tailWord_19167).sum := by decide
  have hdescent : baseEnd_19167 < baseStart_19167 := by decide
  rcases family_descends (prefixWord ++ tailWord_19167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19218 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_19218 : Nat := 118140960795 + 19218 * 2 ^ 59
def prefixEnd_19218 : Nat := 4983230072969 + 3 ^ 40 * 19218 * 2
def baseEnd_19218 : Nat := 6578714145474028791083

theorem tailTrace_19218 : CollatzResearch.WordTrace tailWord_19218 prefixEnd_19218 6578714145474028791083 := by
  unfold tailWord_19218
  simp only [CollatzResearch.WordTrace]
  refine ⟨175234511095985754550577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 467292029589295345468205 175234511095985754550577)
  ·
    refine ⟨131425883321989315912933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175234511095985754550577 131425883321989315912933)
    ·
      refine ⟨24642353122872996733675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131425883321989315912933 24642353122872996733675)
      ·
        refine ⟨36963529684309495100513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24642353122872996733675 36963529684309495100513)
        ·
          refine ⟨27722647263232121325385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36963529684309495100513 27722647263232121325385)
          ·
            refine ⟨20791985447424090994039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27722647263232121325385 20791985447424090994039)
            ·
              refine ⟨31187978171136136491059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20791985447424090994039 31187978171136136491059)
              ·
                refine ⟨46781967256704204736589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31187978171136136491059 46781967256704204736589)
                ·
                  refine ⟨17543237721264076776221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46781967256704204736589 17543237721264076776221)
                  ·
                    refine ⟨6578714145474028791083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17543237721264076776221 6578714145474028791083)
                    ·
                      rfl

theorem cell22_19218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_19218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19218 prefixEnd_19218 := by exact prefixLift 19218
  have htrace : WordTrace (prefixWord ++ tailWord_19218) baseStart_19218 baseEnd_19218 := by
    simpa [prefixWord, tailWord_19218, baseEnd_19218] using wordTrace_append hprefix tailTrace_19218
  have hstable : (prefixWord ++ tailWord_19218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19218).length < 2 ^ (prefixWord ++ tailWord_19218).sum := by decide
  have hdescent : baseEnd_19218 < baseStart_19218 := by decide
  rcases family_descends (prefixWord ++ tailWord_19218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19225 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 6]
def baseStart_19225 : Nat := 118140960795 + 19225 * 2 ^ 59
def prefixEnd_19225 : Nat := 4983230072969 + 3 ^ 40 * 19225 * 2
def baseEnd_19225 : Nat := 2193703462842781288687

theorem tailTrace_19225 : CollatzResearch.WordTrace tailWord_19225 prefixEnd_19225 2193703462842781288687 := by
  unfold tailWord_19225
  simp only [CollatzResearch.WordTrace]
  refine ⟨701193355358583213707129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 467462236905722142471419 701193355358583213707129)
  ·
    refine ⟨525895016518937410280347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 701193355358583213707129 525895016518937410280347)
    ·
      refine ⟨788842524778406115420521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525895016518937410280347 788842524778406115420521)
      ·
        refine ⟨591631893583804586565391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788842524778406115420521 591631893583804586565391)
        ·
          refine ⟨887447840375706879848087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591631893583804586565391 887447840375706879848087)
          ·
            refine ⟨1331171760563560319772131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887447840375706879848087 1331171760563560319772131)
            ·
              refine ⟨1996757640845340479658197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331171760563560319772131 1996757640845340479658197)
              ·
                refine ⟨46799007207312667491989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1996757640845340479658197 46799007207312667491989)
                ·
                  refine ⟨2193703462842781288687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46799007207312667491989 2193703462842781288687)
                  ·
                    rfl

theorem cell22_19225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_19225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19225 prefixEnd_19225 := by exact prefixLift 19225
  have htrace : WordTrace (prefixWord ++ tailWord_19225) baseStart_19225 baseEnd_19225 := by
    simpa [prefixWord, tailWord_19225, baseEnd_19225] using wordTrace_append hprefix tailTrace_19225
  have hstable : (prefixWord ++ tailWord_19225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19225).length < 2 ^ (prefixWord ++ tailWord_19225).sum := by decide
  have hdescent : baseEnd_19225 < baseStart_19225 := by decide
  rcases family_descends (prefixWord ++ tailWord_19225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19272 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_19272 : Nat := 118140960795 + 19272 * 2 ^ 59
def prefixEnd_19272 : Nat := 4983230072969 + 3 ^ 40 * 19272 * 2
def baseEnd_19272 : Nat := 6597199449035887940917

theorem tailTrace_19272 : CollatzResearch.WordTrace tailWord_19272 prefixEnd_19272 6597199449035887940917 := by
  unfold tailWord_19272
  simp only [CollatzResearch.WordTrace]
  refine ⟨351453793094155120334035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 468605057458873493778713 351453793094155120334035)
  ·
    refine ⟨527180689641232680501053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351453793094155120334035 527180689641232680501053)
    ·
      refine ⟨197692758615462255187895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 527180689641232680501053 197692758615462255187895)
      ·
        refine ⟨296539137923193382781843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197692758615462255187895 296539137923193382781843)
        ·
          refine ⟨444808706884790074172765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296539137923193382781843 444808706884790074172765)
          ·
            refine ⟨166803265081796277814787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 444808706884790074172765 166803265081796277814787)
            ·
              refine ⟨250204897622694416722181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166803265081796277814787 250204897622694416722181)
              ·
                refine ⟨46913418304255203135409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250204897622694416722181 46913418304255203135409)
                ·
                  refine ⟨35185063728191402351557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46913418304255203135409 35185063728191402351557)
                  ·
                    refine ⟨6597199449035887940917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35185063728191402351557 6597199449035887940917)
                    ·
                      rfl

theorem cell22_19272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_19272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19272 prefixEnd_19272 := by exact prefixLift 19272
  have htrace : WordTrace (prefixWord ++ tailWord_19272) baseStart_19272 baseEnd_19272 := by
    simpa [prefixWord, tailWord_19272, baseEnd_19272] using wordTrace_append hprefix tailTrace_19272
  have hstable : (prefixWord ++ tailWord_19272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19272).length < 2 ^ (prefixWord ++ tailWord_19272).sum := by decide
  have hdescent : baseEnd_19272 < baseStart_19272 := by decide
  rcases family_descends (prefixWord ++ tailWord_19272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19276 : List Nat := [2, 2, 1, 3, 3, 1, 4, 2, 4]
def baseStart_19276 : Nat := 118140960795 + 19276 * 2 ^ 59
def prefixEnd_19276 : Nat := 4983230072969 + 3 ^ 40 * 19276 * 2
def baseEnd_19276 : Nat := 2199522910260403613635

theorem tailTrace_19276 : CollatzResearch.WordTrace tailWord_19276 prefixEnd_19276 2199522910260403613635 := by
  unfold tailWord_19276
  simp only [CollatzResearch.WordTrace]
  refine ⟨351526739086909461906841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 468702318782545949209121 351526739086909461906841)
  ·
    refine ⟨263645054315182096430131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 351526739086909461906841 263645054315182096430131)
    ·
      refine ⟨395467581472773144645197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263645054315182096430131 395467581472773144645197)
      ·
        refine ⟨148300343052289929241949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395467581472773144645197 148300343052289929241949)
        ·
          refine ⟨55612628644608723465731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148300343052289929241949 55612628644608723465731)
          ·
            refine ⟨83418942966913085198597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55612628644608723465731 83418942966913085198597)
            ·
              refine ⟨15641051806296203474737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83418942966913085198597 15641051806296203474737)
              ·
                refine ⟨11730788854722152606053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15641051806296203474737 11730788854722152606053)
                ·
                  refine ⟨2199522910260403613635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11730788854722152606053 2199522910260403613635)
                  ·
                    rfl

theorem cell22_19276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_19276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19276 prefixEnd_19276 := by exact prefixLift 19276
  have htrace : WordTrace (prefixWord ++ tailWord_19276) baseStart_19276 baseEnd_19276 := by
    simpa [prefixWord, tailWord_19276, baseEnd_19276] using wordTrace_append hprefix tailTrace_19276
  have hstable : (prefixWord ++ tailWord_19276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19276).length < 2 ^ (prefixWord ++ tailWord_19276).sum := by decide
  have hdescent : baseEnd_19276 < baseStart_19276 := by decide
  rcases family_descends (prefixWord ++ tailWord_19276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19287 : List Nat := [1, 1, 3, 2, 4, 1, 3, 7]
def baseStart_19287 : Nat := 118140960795 + 19287 * 2 ^ 59
def prefixEnd_19287 : Nat := 4983230072969 + 3 ^ 40 * 19287 * 2
def baseEnd_19287 : Nat := 733592695064538757319

theorem tailTrace_19287 : CollatzResearch.WordTrace tailWord_19287 prefixEnd_19287 733592695064538757319 := by
  unfold tailWord_19287
  simp only [CollatzResearch.WordTrace]
  refine ⟨703454681133967802464115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 468969787422645201642743 703454681133967802464115)
  ·
    refine ⟨1055182021700951703696173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703454681133967802464115 1055182021700951703696173)
    ·
      refine ⟨395693258137856888886065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1055182021700951703696173 395693258137856888886065)
      ·
        refine ⟨296769943603392666664549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395693258137856888886065 296769943603392666664549)
        ·
          refine ⟨55644364425636124999603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296769943603392666664549 55644364425636124999603)
          ·
            refine ⟨83466546638454187499405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55644364425636124999603 83466546638454187499405)
            ·
              refine ⟨31299954989420320312277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83466546638454187499405 31299954989420320312277)
              ·
                refine ⟨733592695064538757319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31299954989420320312277 733592695064538757319)
                ·
                  rfl

theorem cell22_19287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 7].length) (baseStart_19287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19287 prefixEnd_19287 := by exact prefixLift 19287
  have htrace : WordTrace (prefixWord ++ tailWord_19287) baseStart_19287 baseEnd_19287 := by
    simpa [prefixWord, tailWord_19287, baseEnd_19287] using wordTrace_append hprefix tailTrace_19287
  have hstable : (prefixWord ++ tailWord_19287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19287).length < 2 ^ (prefixWord ++ tailWord_19287).sum := by decide
  have hdescent : baseEnd_19287 < baseStart_19287 := by decide
  rcases family_descends (prefixWord ++ tailWord_19287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19304 : List Nat := [2, 1, 4, 2, 1, 3, 3, 6]
def baseStart_19304 : Nat := 118140960795 + 19304 * 2 ^ 59
def prefixEnd_19304 : Nat := 4983230072969 + 3 ^ 40 * 19304 * 2
def baseEnd_19304 : Nat := 734239300333163460091

theorem tailTrace_19304 : CollatzResearch.WordTrace tailWord_19304 prefixEnd_19304 734239300333163460091 := by
  unfold tailWord_19304
  simp only [CollatzResearch.WordTrace]
  refine ⟨352037361036189852916483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 469383148048253137221977 352037361036189852916483)
  ·
    refine ⟨528056041554284779374725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 352037361036189852916483 528056041554284779374725)
    ·
      refine ⟨99010507791428396132761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 528056041554284779374725 99010507791428396132761)
      ·
        refine ⟨74257880843571297099571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99010507791428396132761 74257880843571297099571)
        ·
          refine ⟨111386821265356945649357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74257880843571297099571 111386821265356945649357)
          ·
            refine ⟨41770057974508854618509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111386821265356945649357 41770057974508854618509)
            ·
              refine ⟨15663771740440820481941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41770057974508854618509 15663771740440820481941)
              ·
                refine ⟨734239300333163460091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15663771740440820481941 734239300333163460091)
                ·
                  rfl

theorem cell22_19304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 6].length) (baseStart_19304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19304 prefixEnd_19304 := by exact prefixLift 19304
  have htrace : WordTrace (prefixWord ++ tailWord_19304) baseStart_19304 baseEnd_19304 := by
    simpa [prefixWord, tailWord_19304, baseEnd_19304] using wordTrace_append hprefix tailTrace_19304
  have hstable : (prefixWord ++ tailWord_19304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19304).length < 2 ^ (prefixWord ++ tailWord_19304).sum := by decide
  have hdescent : baseEnd_19304 < baseStart_19304 := by decide
  rcases family_descends (prefixWord ++ tailWord_19304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19336 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 3, 3]
def baseStart_19336 : Nat := 118140960795 + 19336 * 2 ^ 59
def prefixEnd_19336 : Nat := 4983230072969 + 3 ^ 40 * 19336 * 2
def baseEnd_19336 : Nat := 6619107956961054340721

theorem tailTrace_19336 : CollatzResearch.WordTrace tailWord_19336 prefixEnd_19336 6619107956961054340721 := by
  unfold tailWord_19336
  simp only [CollatzResearch.WordTrace]
  refine ⟨352620928978224585498931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 470161238637632780665241 352620928978224585498931)
  ·
    refine ⟨528931393467336878248397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 352620928978224585498931 528931393467336878248397)
    ·
      refine ⟨198349272550251329343149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 528931393467336878248397 198349272550251329343149)
      ·
        refine ⟨74380977206344248503681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198349272550251329343149 74380977206344248503681)
        ·
          refine ⟨55785732904758186377761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74380977206344248503681 55785732904758186377761)
          ·
            refine ⟨41839299678568639783321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55785732904758186377761 41839299678568639783321)
            ·
              refine ⟨31379474758926479837491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41839299678568639783321 31379474758926479837491)
              ·
                refine ⟨47069212138389719756237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31379474758926479837491 47069212138389719756237)
                ·
                  refine ⟨17650954551896144908589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47069212138389719756237 17650954551896144908589)
                  ·
                    refine ⟨6619107956961054340721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17650954551896144908589 6619107956961054340721)
                    ·
                      rfl

theorem cell22_19336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_19336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19336 prefixEnd_19336 := by exact prefixLift 19336
  have htrace : WordTrace (prefixWord ++ tailWord_19336) baseStart_19336 baseEnd_19336 := by
    simpa [prefixWord, tailWord_19336, baseEnd_19336] using wordTrace_append hprefix tailTrace_19336
  have hstable : (prefixWord ++ tailWord_19336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19336).length < 2 ^ (prefixWord ++ tailWord_19336).sum := by decide
  have hdescent : baseEnd_19336 < baseStart_19336 := by decide
  rcases family_descends (prefixWord ++ tailWord_19336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19413 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_19413 : Nat := 118140960795 + 19413 * 2 ^ 59
def prefixEnd_19413 : Nat := 4983230072969 + 3 ^ 40 * 19413 * 2
def baseEnd_19413 : Nat := 6645466630558520165485

theorem tailTrace_19413 : CollatzResearch.WordTrace tailWord_19413 prefixEnd_19413 6645466630558520165485 := by
  unfold tailWord_19413
  simp only [CollatzResearch.WordTrace]
  refine ⟨708050278677491321550893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 472033519118327547700595 708050278677491321550893)
  ·
    refine ⟨265518854504059245581585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 708050278677491321550893 265518854504059245581585)
    ·
      refine ⟨199139140878044434186189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265518854504059245581585 199139140878044434186189)
      ·
        refine ⟨74677177829266662819821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199139140878044434186189 74677177829266662819821)
        ·
          refine ⟨28003941685974998557433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74677177829266662819821 28003941685974998557433)
          ·
            refine ⟨21002956264481248918075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28003941685974998557433 21002956264481248918075)
            ·
              refine ⟨31504434396721873377113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21002956264481248918075 31504434396721873377113)
              ·
                refine ⟨23628325797541405032835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31504434396721873377113 23628325797541405032835)
                ·
                  refine ⟨35442488696312107549253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23628325797541405032835 35442488696312107549253)
                  ·
                    refine ⟨6645466630558520165485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35442488696312107549253 6645466630558520165485)
                    ·
                      rfl

theorem cell22_19413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_19413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19413 prefixEnd_19413 := by exact prefixLift 19413
  have htrace : WordTrace (prefixWord ++ tailWord_19413) baseStart_19413 baseEnd_19413 := by
    simpa [prefixWord, tailWord_19413, baseEnd_19413] using wordTrace_append hprefix tailTrace_19413
  have hstable : (prefixWord ++ tailWord_19413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19413).length < 2 ^ (prefixWord ++ tailWord_19413).sum := by decide
  have hdescent : baseEnd_19413 < baseStart_19413 := by decide
  rcases family_descends (prefixWord ++ tailWord_19413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19426 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_19426 : Nat := 118140960795 + 19426 * 2 ^ 59
def prefixEnd_19426 : Nat := 4983230072969 + 3 ^ 40 * 19426 * 2
def baseEnd_19426 : Nat := 6649916796230819590445

theorem tailTrace_19426 : CollatzResearch.WordTrace tailWord_19426 prefixEnd_19426 6649916796230819590445 := by
  unfold tailWord_19426
  simp only [CollatzResearch.WordTrace]
  refine ⟨177131106907598635443533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 472349618420263027849421 177131106907598635443533)
  ·
    refine ⟨66424165090349488291325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177131106907598635443533 66424165090349488291325)
    ·
      refine ⟨24909061908881058109247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66424165090349488291325 24909061908881058109247)
      ·
        refine ⟨37363592863321587163871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24909061908881058109247 37363592863321587163871)
        ·
          refine ⟨56045389294982380745807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37363592863321587163871 56045389294982380745807)
          ·
            refine ⟨84068083942473571118711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56045389294982380745807 84068083942473571118711)
            ·
              refine ⟨126102125913710356678067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84068083942473571118711 126102125913710356678067)
              ·
                refine ⟨189153188870565535017101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126102125913710356678067 189153188870565535017101)
                ·
                  refine ⟨70932445826462075631413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189153188870565535017101 70932445826462075631413)
                  ·
                    refine ⟨6649916796230819590445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70932445826462075631413 6649916796230819590445)
                    ·
                      rfl

theorem cell22_19426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_19426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19426 prefixEnd_19426 := by exact prefixLift 19426
  have htrace : WordTrace (prefixWord ++ tailWord_19426) baseStart_19426 baseEnd_19426 := by
    simpa [prefixWord, tailWord_19426, baseEnd_19426] using wordTrace_append hprefix tailTrace_19426
  have hstable : (prefixWord ++ tailWord_19426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19426).length < 2 ^ (prefixWord ++ tailWord_19426).sum := by decide
  have hdescent : baseEnd_19426 < baseStart_19426 := by decide
  rcases family_descends (prefixWord ++ tailWord_19426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19445 : List Nat := [1, 3, 5, 2, 1, 1, 1, 4, 4]
def baseStart_19445 : Nat := 118140960795 + 19445 * 2 ^ 59
def prefixEnd_19445 : Nat := 4983230072969 + 3 ^ 40 * 19445 * 2
def baseEnd_19445 : Nat := 2218806961507034455129

theorem tailTrace_19445 : CollatzResearch.WordTrace tailWord_19445 prefixEnd_19445 2218806961507034455129 := by
  unfold tailWord_19445
  simp only [CollatzResearch.WordTrace]
  refine ⟨709217414561560786715789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 472811609707707191143859 709217414561560786715789)
  ·
    refine ⟨265956530460585295018421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 709217414561560786715789 265956530460585295018421)
    ·
      refine ⟨24933424730679871407977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265956530460585295018421 24933424730679871407977)
      ·
        refine ⟨18700068548009903555983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24933424730679871407977 18700068548009903555983)
        ·
          refine ⟨28050102822014855333975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18700068548009903555983 28050102822014855333975)
          ·
            refine ⟨42075154233022283000963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28050102822014855333975 42075154233022283000963)
            ·
              refine ⟨63112731349533424501445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42075154233022283000963 63112731349533424501445)
              ·
                refine ⟨11833637128037517094021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63112731349533424501445 11833637128037517094021)
                ·
                  refine ⟨2218806961507034455129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11833637128037517094021 2218806961507034455129)
                  ·
                    rfl

theorem cell22_19445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_19445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19445 prefixEnd_19445 := by exact prefixLift 19445
  have htrace : WordTrace (prefixWord ++ tailWord_19445) baseStart_19445 baseEnd_19445 := by
    simpa [prefixWord, tailWord_19445, baseEnd_19445] using wordTrace_append hprefix tailTrace_19445
  have hstable : (prefixWord ++ tailWord_19445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19445).length < 2 ^ (prefixWord ++ tailWord_19445).sum := by decide
  have hdescent : baseEnd_19445 < baseStart_19445 := by decide
  rcases family_descends (prefixWord ++ tailWord_19445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19514 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_19514 : Nat := 118140960795 + 19514 * 2 ^ 59
def prefixEnd_19514 : Nat := 4983230072969 + 3 ^ 40 * 19514 * 2
def baseEnd_19514 : Nat := 6680040994627923390175

theorem tailTrace_19514 : CollatzResearch.WordTrace tailWord_19514 prefixEnd_19514 6680040994627923390175 := by
  unfold tailWord_19514
  simp only [CollatzResearch.WordTrace]
  refine ⟨177933512827896392744399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 474489367541057047318397 177933512827896392744399)
  ·
    refine ⟨266900269241844589116599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177933512827896392744399 266900269241844589116599)
    ·
      refine ⟨400350403862766883674899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266900269241844589116599 400350403862766883674899)
      ·
        refine ⟨600525605794150325512349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400350403862766883674899 600525605794150325512349)
        ·
          refine ⟨225197102172806372067131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 600525605794150325512349 225197102172806372067131)
          ·
            refine ⟨337795653259209558100697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225197102172806372067131 337795653259209558100697)
            ·
              refine ⟨253346739944407168575523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337795653259209558100697 253346739944407168575523)
              ·
                refine ⟨380020109916610752863285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253346739944407168575523 380020109916610752863285)
                ·
                  refine ⟨35626885304682258080933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 380020109916610752863285 35626885304682258080933)
                  ·
                    refine ⟨6680040994627923390175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35626885304682258080933 6680040994627923390175)
                    ·
                      rfl

theorem cell22_19514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_19514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19514 prefixEnd_19514 := by exact prefixLift 19514
  have htrace : WordTrace (prefixWord ++ tailWord_19514) baseStart_19514 baseEnd_19514 := by
    simpa [prefixWord, tailWord_19514, baseEnd_19514] using wordTrace_append hprefix tailTrace_19514
  have hstable : (prefixWord ++ tailWord_19514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19514).length < 2 ^ (prefixWord ++ tailWord_19514).sum := by decide
  have hdescent : baseEnd_19514 < baseStart_19514 := by decide
  rcases family_descends (prefixWord ++ tailWord_19514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19544 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_19544 : Nat := 118140960795 + 19544 * 2 ^ 59
def prefixEnd_19544 : Nat := 4983230072969 + 3 ^ 40 * 19544 * 2
def baseEnd_19544 : Nat := 6690310607717845140083

theorem tailTrace_19544 : CollatzResearch.WordTrace tailWord_19544 prefixEnd_19544 6690310607717845140083 := by
  unfold tailWord_19544
  simp only [CollatzResearch.WordTrace]
  refine ⟨356414120601450347284843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 475218827468600463046457 356414120601450347284843)
  ·
    refine ⟨534621180902175520927265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356414120601450347284843 534621180902175520927265)
    ·
      refine ⟨400965885676631640695449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 534621180902175520927265 400965885676631640695449)
      ·
        refine ⟨300724414257473730521587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400965885676631640695449 300724414257473730521587)
        ·
          refine ⟨451086621386210595782381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300724414257473730521587 451086621386210595782381)
          ·
            refine ⟨169157483019828973418393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 451086621386210595782381 169157483019828973418393)
            ·
              refine ⟨126868112264871730063795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169157483019828973418393 126868112264871730063795)
              ·
                refine ⟨190302168397307595095693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126868112264871730063795 190302168397307595095693)
                ·
                  refine ⟨71363313148990348160885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190302168397307595095693 71363313148990348160885)
                  ·
                    refine ⟨6690310607717845140083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71363313148990348160885 6690310607717845140083)
                    ·
                      rfl

theorem cell22_19544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_19544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19544 prefixEnd_19544 := by exact prefixLift 19544
  have htrace : WordTrace (prefixWord ++ tailWord_19544) baseStart_19544 baseEnd_19544 := by
    simpa [prefixWord, tailWord_19544, baseEnd_19544] using wordTrace_append hprefix tailTrace_19544
  have hstable : (prefixWord ++ tailWord_19544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19544).length < 2 ^ (prefixWord ++ tailWord_19544).sum := by decide
  have hdescent : baseEnd_19544 < baseStart_19544 := by decide
  rcases family_descends (prefixWord ++ tailWord_19544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19546 : List Nat := [3, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_19546 : Nat := 118140960795 + 19546 * 2 ^ 59
def prefixEnd_19546 : Nat := 4983230072969 + 3 ^ 40 * 19546 * 2
def baseEnd_19546 : Nat := 2230331749530168863359

theorem tailTrace_19546 : CollatzResearch.WordTrace tailWord_19546 prefixEnd_19546 2230331749530168863359 := by
  unfold tailWord_19546
  simp only [CollatzResearch.WordTrace]
  refine ⟨178225296798913759035623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 475267458130436690761661 178225296798913759035623)
  ·
    refine ⟨267337945198370638553435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178225296798913759035623 267337945198370638553435)
    ·
      refine ⟨401006917797555957830153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267337945198370638553435 401006917797555957830153)
      ·
        refine ⟨300755188348166968372615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401006917797555957830153 300755188348166968372615)
        ·
          refine ⟨451132782522250452558923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300755188348166968372615 451132782522250452558923)
          ·
            refine ⟨676699173783375678838385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451132782522250452558923 676699173783375678838385)
            ·
              refine ⟨507524380337531759128789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676699173783375678838385 507524380337531759128789)
              ·
                refine ⟨11895102664160900604581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 507524380337531759128789 11895102664160900604581)
                ·
                  refine ⟨2230331749530168863359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11895102664160900604581 2230331749530168863359)
                  ·
                    rfl

theorem cell22_19546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_19546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19546 prefixEnd_19546 := by exact prefixLift 19546
  have htrace : WordTrace (prefixWord ++ tailWord_19546) baseStart_19546 baseEnd_19546 := by
    simpa [prefixWord, tailWord_19546, baseEnd_19546] using wordTrace_append hprefix tailTrace_19546
  have hstable : (prefixWord ++ tailWord_19546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19546).length < 2 ^ (prefixWord ++ tailWord_19546).sum := by decide
  have hdescent : baseEnd_19546 < baseStart_19546 := by decide
  rcases family_descends (prefixWord ++ tailWord_19546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19561 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 4, 3]
def baseStart_19561 : Nat := 118140960795 + 19561 * 2 ^ 59
def prefixEnd_19561 : Nat := 4983230072969 + 3 ^ 40 * 19561 * 2
def baseEnd_19561 : Nat := 6696130055135467465031

theorem tailTrace_19561 : CollatzResearch.WordTrace tailWord_19561 prefixEnd_19561 6696130055135467465031 := by
  unfold tailWord_19561
  simp only [CollatzResearch.WordTrace]
  refine ⟨713448282141312597938537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 475632188094208398625691 713448282141312597938537)
  ·
    refine ⟨535086211605984448453903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 713448282141312597938537 535086211605984448453903)
    ·
      refine ⟨802629317408976672680855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535086211605984448453903 802629317408976672680855)
      ·
        refine ⟨1203943976113465009021283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802629317408976672680855 1203943976113465009021283)
        ·
          refine ⟨1805915964170197513531925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203943976113465009021283 1805915964170197513531925)
          ·
            refine ⟨84652310820478008446809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1805915964170197513531925 84652310820478008446809)
            ·
              refine ⟨63489233115358506335107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84652310820478008446809 63489233115358506335107)
              ·
                refine ⟨95233849673037759502661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63489233115358506335107 95233849673037759502661)
                ·
                  refine ⟨17856346813694579906749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95233849673037759502661 17856346813694579906749)
                  ·
                    refine ⟨6696130055135467465031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17856346813694579906749 6696130055135467465031)
                    ·
                      rfl

theorem cell22_19561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_19561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19561 prefixEnd_19561 := by exact prefixLift 19561
  have htrace : WordTrace (prefixWord ++ tailWord_19561) baseStart_19561 baseEnd_19561 := by
    simpa [prefixWord, tailWord_19561, baseEnd_19561] using wordTrace_append hprefix tailTrace_19561
  have hstable : (prefixWord ++ tailWord_19561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19561).length < 2 ^ (prefixWord ++ tailWord_19561).sum := by decide
  have hdescent : baseEnd_19561 < baseStart_19561 := by decide
  rcases family_descends (prefixWord ++ tailWord_19561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19582 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_19582 : Nat := 118140960795 + 19582 * 2 ^ 59
def prefixEnd_19582 : Nat := 4983230072969 + 3 ^ 40 * 19582 * 2
def baseEnd_19582 : Nat := 6703318784298412689967

theorem tailTrace_19582 : CollatzResearch.WordTrace tailWord_19582 prefixEnd_19582 6703318784298412689967 := by
  unfold tailWord_19582
  simp only [CollatzResearch.WordTrace]
  refine ⟨89276776883154148056625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 476142810043488789635333 89276776883154148056625)
  ·
    refine ⟨66957582662365611042469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89276776883154148056625 66957582662365611042469)
    ·
      refine ⟨12554546749193552070463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66957582662365611042469 12554546749193552070463)
      ·
        refine ⟨18831820123790328105695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12554546749193552070463 18831820123790328105695)
        ·
          refine ⟨28247730185685492158543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18831820123790328105695 28247730185685492158543)
          ·
            refine ⟨42371595278528238237815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28247730185685492158543 42371595278528238237815)
            ·
              refine ⟨63557392917792357356723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42371595278528238237815 63557392917792357356723)
              ·
                refine ⟨95336089376688536035085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63557392917792357356723 95336089376688536035085)
                ·
                  refine ⟨35751033516258201013157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95336089376688536035085 35751033516258201013157)
                  ·
                    refine ⟨6703318784298412689967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35751033516258201013157 6703318784298412689967)
                    ·
                      rfl

theorem cell22_19582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_19582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19582 prefixEnd_19582 := by exact prefixLift 19582
  have htrace : WordTrace (prefixWord ++ tailWord_19582) baseStart_19582 baseEnd_19582 := by
    simpa [prefixWord, tailWord_19582, baseEnd_19582] using wordTrace_append hprefix tailTrace_19582
  have hstable : (prefixWord ++ tailWord_19582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19582).length < 2 ^ (prefixWord ++ tailWord_19582).sum := by decide
  have hdescent : baseEnd_19582 < baseStart_19582 := by decide
  rcases family_descends (prefixWord ++ tailWord_19582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19619 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 7]
def baseStart_19619 : Nat := 118140960795 + 19619 * 2 ^ 59
def prefixEnd_19619 : Nat := 4983230072969 + 3 ^ 40 * 19619 * 2
def baseEnd_19619 : Nat := 2238661546814216504951

theorem tailTrace_19619 : CollatzResearch.WordTrace tailWord_19619 prefixEnd_19619 2238661546814216504951 := by
  unfold tailWord_19619
  simp only [CollatzResearch.WordTrace]
  refine ⟨715563715931188503549911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 477042477287459002366607 715563715931188503549911)
  ·
    refine ⟨1073345573896782755324867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 715563715931188503549911 1073345573896782755324867)
    ·
      refine ⟨1610018360845174132987301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073345573896782755324867 1610018360845174132987301)
      ·
        refine ⟨301878442658470149935119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1610018360845174132987301 301878442658470149935119)
        ·
          refine ⟨452817663987705224902679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301878442658470149935119 452817663987705224902679)
          ·
            refine ⟨679226495981557837354019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452817663987705224902679 679226495981557837354019)
            ·
              refine ⟨1018839743972336756031029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679226495981557837354019 1018839743972336756031029)
              ·
                refine ⟨95516225997406570877909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1018839743972336756031029 95516225997406570877909)
                ·
                  refine ⟨2238661546814216504951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 95516225997406570877909 2238661546814216504951)
                  ·
                    rfl

theorem cell22_19619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_19619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19619 prefixEnd_19619 := by exact prefixLift 19619
  have htrace : WordTrace (prefixWord ++ tailWord_19619) baseStart_19619 baseEnd_19619 := by
    simpa [prefixWord, tailWord_19619, baseEnd_19619] using wordTrace_append hprefix tailTrace_19619
  have hstable : (prefixWord ++ tailWord_19619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19619).length < 2 ^ (prefixWord ++ tailWord_19619).sum := by decide
  have hdescent : baseEnd_19619 < baseStart_19619 := by decide
  rcases family_descends (prefixWord ++ tailWord_19619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19670 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_19670 : Nat := 118140960795 + 19670 * 2 ^ 59
def prefixEnd_19670 : Nat := 4983230072969 + 3 ^ 40 * 19670 * 2
def baseEnd_19670 : Nat := 2244480994231838829899

theorem tailTrace_19670 : CollatzResearch.WordTrace tailWord_19670 prefixEnd_19670 2244480994231838829899 := by
  unfold tailWord_19670
  simp only [CollatzResearch.WordTrace]
  refine ⟨44838989921651513353529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 478282559164282809104309 44838989921651513353529)
  ·
    refine ⟨33629242441238635015147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44838989921651513353529 33629242441238635015147)
    ·
      refine ⟨50443863661857952522721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33629242441238635015147 50443863661857952522721)
      ·
        refine ⟨37832897746393464392041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50443863661857952522721 37832897746393464392041)
        ·
          refine ⟨28374673309795098294031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37832897746393464392041 28374673309795098294031)
          ·
            refine ⟨42562009964692647441047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28374673309795098294031 42562009964692647441047)
            ·
              refine ⟨63843014947038971161571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42562009964692647441047 63843014947038971161571)
              ·
                refine ⟨95764522420558456742357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63843014947038971161571 95764522420558456742357)
                ·
                  refine ⟨2244480994231838829899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 95764522420558456742357 2244480994231838829899)
                  ·
                    rfl

theorem cell22_19670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_19670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19670 prefixEnd_19670 := by exact prefixLift 19670
  have htrace : WordTrace (prefixWord ++ tailWord_19670) baseStart_19670 baseEnd_19670 := by
    simpa [prefixWord, tailWord_19670, baseEnd_19670] using wordTrace_append hprefix tailTrace_19670
  have hstable : (prefixWord ++ tailWord_19670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19670).length < 2 ^ (prefixWord ++ tailWord_19670).sum := by decide
  have hdescent : baseEnd_19670 < baseStart_19670 := by decide
  rcases family_descends (prefixWord ++ tailWord_19670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19681 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 6]
def baseStart_19681 : Nat := 118140960795 + 19681 * 2 ^ 59
def prefixEnd_19681 : Nat := 4983230072969 + 3 ^ 40 * 19681 * 2
def baseEnd_19681 : Nat := 2245736169165051488221

theorem tailTrace_19681 : CollatzResearch.WordTrace tailWord_19681 prefixEnd_19681 2245736169165051488221 := by
  unfold tailWord_19681
  simp only [CollatzResearch.WordTrace]
  refine ⟨717825041706573092306897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 478550027804382061537931 717825041706573092306897)
  ·
    refine ⟨538368781279929819230173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 717825041706573092306897 538368781279929819230173)
    ·
      refine ⟨201888292979973682211315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 538368781279929819230173 201888292979973682211315)
      ·
        refine ⟨302832439469960523316973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201888292979973682211315 302832439469960523316973)
        ·
          refine ⟨113562164801235196243865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302832439469960523316973 113562164801235196243865)
          ·
            refine ⟨85171623600926397182899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113562164801235196243865 85171623600926397182899)
            ·
              refine ⟨127757435401389595774349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85171623600926397182899 127757435401389595774349)
              ·
                refine ⟨47909038275521098415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127757435401389595774349 47909038275521098415381)
                ·
                  refine ⟨2245736169165051488221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47909038275521098415381 2245736169165051488221)
                  ·
                    rfl

theorem cell22_19681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_19681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19681 prefixEnd_19681 := by exact prefixLift 19681
  have htrace : WordTrace (prefixWord ++ tailWord_19681) baseStart_19681 baseEnd_19681 := by
    simpa [prefixWord, tailWord_19681, baseEnd_19681] using wordTrace_append hprefix tailTrace_19681
  have hstable : (prefixWord ++ tailWord_19681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19681).length < 2 ^ (prefixWord ++ tailWord_19681).sum := by decide
  have hdescent : baseEnd_19681 < baseStart_19681 := by decide
  rcases family_descends (prefixWord ++ tailWord_19681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19711 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 1, 6]
def baseStart_19711 : Nat := 118140960795 + 19711 * 2 ^ 59
def prefixEnd_19711 : Nat := 4983230072969 + 3 ^ 40 * 19711 * 2
def baseEnd_19711 : Nat := 6747478120585076214571

theorem tailTrace_19711 : CollatzResearch.WordTrace tailWord_19711 prefixEnd_19711 6747478120585076214571 := by
  unfold tailWord_19711
  simp only [CollatzResearch.WordTrace]
  refine ⟨718919231597888215898987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 479279487731925477265991 718919231597888215898987)
  ·
    refine ⟨1078378847396832323848481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 718919231597888215898987 1078378847396832323848481)
    ·
      refine ⟨808784135547624242886361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1078378847396832323848481 808784135547624242886361)
      ·
        refine ⟨606588101660718182164771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 808784135547624242886361 606588101660718182164771)
        ·
          refine ⟨909882152491077273247157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606588101660718182164771 909882152491077273247157)
          ·
            refine ⟨85301451796038494366921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 909882152491077273247157 85301451796038494366921)
            ·
              refine ⟨63976088847028870775191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85301451796038494366921 63976088847028870775191)
              ·
                refine ⟨95964133270543306162787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63976088847028870775191 95964133270543306162787)
                ·
                  refine ⟨143946199905814959244181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95964133270543306162787 143946199905814959244181)
                  ·
                    refine ⟨6747478120585076214571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 143946199905814959244181 6747478120585076214571)
                    ·
                      rfl

theorem cell22_19711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_19711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19711 prefixEnd_19711 := by exact prefixLift 19711
  have htrace : WordTrace (prefixWord ++ tailWord_19711) baseStart_19711 baseEnd_19711 := by
    simpa [prefixWord, tailWord_19711, baseEnd_19711] using wordTrace_append hprefix tailTrace_19711
  have hstable : (prefixWord ++ tailWord_19711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19711).length < 2 ^ (prefixWord ++ tailWord_19711).sum := by decide
  have hdescent : baseEnd_19711 < baseStart_19711 := by decide
  rcases family_descends (prefixWord ++ tailWord_19711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19713 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 4, 3]
def baseStart_19713 : Nat := 118140960795 + 19713 * 2 ^ 59
def prefixEnd_19713 : Nat := 4983230072969 + 3 ^ 40 * 19713 * 2
def baseEnd_19713 : Nat := 6748162761457737664565

theorem tailTrace_19713 : CollatzResearch.WordTrace tailWord_19713 prefixEnd_19713 6748162761457737664565 := by
  unfold tailWord_19713
  simp only [CollatzResearch.WordTrace]
  refine ⟨718992177590642557471793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 479328118393761704981195 718992177590642557471793)
  ·
    refine ⟨539244133192981918103845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 718992177590642557471793 539244133192981918103845)
    ·
      refine ⟨101108274973684109644471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 539244133192981918103845 101108274973684109644471)
      ·
        refine ⟨151662412460526164466707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101108274973684109644471 151662412460526164466707)
        ·
          refine ⟨227493618690789246700061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151662412460526164466707 227493618690789246700061)
          ·
            refine ⟨85310107009045967512523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227493618690789246700061 85310107009045967512523)
            ·
              refine ⟨127965160513568951268785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85310107009045967512523 127965160513568951268785)
              ·
                refine ⟨95973870385176713451589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127965160513568951268785 95973870385176713451589)
                ·
                  refine ⟨17995100697220633772173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95973870385176713451589 17995100697220633772173)
                  ·
                    refine ⟨6748162761457737664565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17995100697220633772173 6748162761457737664565)
                    ·
                      rfl

theorem cell22_19713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_19713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19713 prefixEnd_19713 := by exact prefixLift 19713
  have htrace : WordTrace (prefixWord ++ tailWord_19713) baseStart_19713 baseEnd_19713 := by
    simpa [prefixWord, tailWord_19713, baseEnd_19713] using wordTrace_append hprefix tailTrace_19713
  have hstable : (prefixWord ++ tailWord_19713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19713).length < 2 ^ (prefixWord ++ tailWord_19713).sum := by decide
  have hdescent : baseEnd_19713 < baseStart_19713 := by decide
  rcases family_descends (prefixWord ++ tailWord_19713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19715 : List Nat := [1, 1, 1, 3, 2, 6, 1, 3, 4]
def baseStart_19715 : Nat := 118140960795 + 19715 * 2 ^ 59
def prefixEnd_19715 : Nat := 4983230072969 + 3 ^ 40 * 19715 * 2
def baseEnd_19715 : Nat := 2249615800776799704853

theorem tailTrace_19715 : CollatzResearch.WordTrace tailWord_19715 prefixEnd_19715 2249615800776799704853 := by
  unfold tailWord_19715
  simp only [CollatzResearch.WordTrace]
  refine ⟨719065123583396899044599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 479376749055597932696399 719065123583396899044599)
  ·
    refine ⟨1078597685375095348566899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 719065123583396899044599 1078597685375095348566899)
    ·
      refine ⟨1617896528062643022850349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078597685375095348566899 1617896528062643022850349)
      ·
        refine ⟨606711198023491133568881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1617896528062643022850349 606711198023491133568881)
        ·
          refine ⟨455033398517618350176661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606711198023491133568881 455033398517618350176661)
          ·
            refine ⟨21329690555513360164531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 455033398517618350176661 21329690555513360164531)
            ·
              refine ⟨31994535833270040246797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21329690555513360164531 31994535833270040246797)
              ·
                refine ⟨11997950937476265092549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31994535833270040246797 11997950937476265092549)
                ·
                  refine ⟨2249615800776799704853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11997950937476265092549 2249615800776799704853)
                  ·
                    rfl

theorem cell22_19715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 4].length) (baseStart_19715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19715 prefixEnd_19715 := by exact prefixLift 19715
  have htrace : WordTrace (prefixWord ++ tailWord_19715) baseStart_19715 baseEnd_19715 := by
    simpa [prefixWord, tailWord_19715, baseEnd_19715] using wordTrace_append hprefix tailTrace_19715
  have hstable : (prefixWord ++ tailWord_19715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19715).length < 2 ^ (prefixWord ++ tailWord_19715).sum := by decide
  have hdescent : baseEnd_19715 < baseStart_19715 := by decide
  rcases family_descends (prefixWord ++ tailWord_19715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19726 : List Nat := [4, 1, 1, 2, 1, 3, 10]
def baseStart_19726 : Nat := 118140960795 + 19726 * 2 ^ 59
def prefixEnd_19726 : Nat := 4983230072969 + 3 ^ 40 * 19726 * 2
def baseEnd_19726 : Nat := 250096775078890262575

theorem tailTrace_19726 : CollatzResearch.WordTrace tailWord_19726 prefixEnd_19726 250096775078890262575 := by
  unfold tailWord_19726
  simp only [CollatzResearch.WordTrace]
  refine ⟨89933290817943222211879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 479644217695697185130021 89933290817943222211879)
  ·
    refine ⟨134899936226914833317819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89933290817943222211879 134899936226914833317819)
    ·
      refine ⟨202349904340372249976729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134899936226914833317819 202349904340372249976729)
      ·
        refine ⟨151762428255279187482547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202349904340372249976729 151762428255279187482547)
        ·
          refine ⟨227643642382918781223821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151762428255279187482547 227643642382918781223821)
          ·
            refine ⟨85366365893594542958933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227643642382918781223821 85366365893594542958933)
            ·
              refine ⟨250096775078890262575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 85366365893594542958933 250096775078890262575)
              ·
                rfl

theorem cell22_19726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 10].length) (baseStart_19726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19726 prefixEnd_19726 := by exact prefixLift 19726
  have htrace : WordTrace (prefixWord ++ tailWord_19726) baseStart_19726 baseEnd_19726 := by
    simpa [prefixWord, tailWord_19726, baseEnd_19726] using wordTrace_append hprefix tailTrace_19726
  have hstable : (prefixWord ++ tailWord_19726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19726).length < 2 ^ (prefixWord ++ tailWord_19726).sum := by decide
  have hdescent : baseEnd_19726 < baseStart_19726 := by decide
  rcases family_descends (prefixWord ++ tailWord_19726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19743 : List Nat := [1, 1, 2, 4, 4, 1, 2, 7]
def baseStart_19743 : Nat := 118140960795 + 19743 * 2 ^ 59
def prefixEnd_19743 : Nat := 4983230072969 + 3 ^ 40 * 19743 * 2
def baseEnd_19743 : Nat := 750936930505295490497

theorem tailTrace_19743 : CollatzResearch.WordTrace tailWord_19743 prefixEnd_19743 750936930505295490497 := by
  unfold tailWord_19743
  simp only [CollatzResearch.WordTrace]
  refine ⟨720086367481957681063883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 480057578321305120709255 720086367481957681063883)
  ·
    refine ⟨1080129551222936521595825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720086367481957681063883 1080129551222936521595825)
    ·
      refine ⟨810097163417202391196869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1080129551222936521595825 810097163417202391196869)
      ·
        refine ⟨151893218140725448349413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 810097163417202391196869 151893218140725448349413)
        ·
          refine ⟨28479978401386021565515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151893218140725448349413 28479978401386021565515)
          ·
            refine ⟨42719967602079032348273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28479978401386021565515 42719967602079032348273)
            ·
              refine ⟨32039975701559274261205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42719967602079032348273 32039975701559274261205)
              ·
                refine ⟨750936930505295490497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32039975701559274261205 750936930505295490497)
                ·
                  rfl

theorem cell22_19743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 7].length) (baseStart_19743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19743 prefixEnd_19743 := by exact prefixLift 19743
  have htrace : WordTrace (prefixWord ++ tailWord_19743) baseStart_19743 baseEnd_19743 := by
    simpa [prefixWord, tailWord_19743, baseEnd_19743] using wordTrace_append hprefix tailTrace_19743
  have hstable : (prefixWord ++ tailWord_19743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19743).length < 2 ^ (prefixWord ++ tailWord_19743).sum := by decide
  have hdescent : baseEnd_19743 < baseStart_19743 := by decide
  rcases family_descends (prefixWord ++ tailWord_19743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19747 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 2, 3]
def baseStart_19747 : Nat := 118140960795 + 19747 * 2 ^ 59
def prefixEnd_19747 : Nat := 4983230072969 + 3 ^ 40 * 19747 * 2
def baseEnd_19747 : Nat := 6759801656292982314461

theorem tailTrace_19747 : CollatzResearch.WordTrace tailWord_19747 prefixEnd_19747 6759801656292982314461 := by
  unfold tailWord_19747
  simp only [CollatzResearch.WordTrace]
  refine ⟨720232259467466364209495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 480154839644977576139663 720232259467466364209495)
  ·
    refine ⟨1080348389201199546314243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720232259467466364209495 1080348389201199546314243)
    ·
      refine ⟨1620522583801799319471365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080348389201199546314243 1620522583801799319471365)
      ·
        refine ⟨303847984462837372400881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1620522583801799319471365 303847984462837372400881)
        ·
          refine ⟨227885988347128029300661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303847984462837372400881 227885988347128029300661)
          ·
            refine ⟨21364311407543252746937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227885988347128029300661 21364311407543252746937)
            ·
              refine ⟨16023233555657439560203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21364311407543252746937 16023233555657439560203)
              ·
                refine ⟨24034850333486159340305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16023233555657439560203 24034850333486159340305)
                ·
                  refine ⟨18026137750114619505229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24034850333486159340305 18026137750114619505229)
                  ·
                    refine ⟨6759801656292982314461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18026137750114619505229 6759801656292982314461)
                    ·
                      rfl

theorem cell22_19747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 2, 3].length) (baseStart_19747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19747 prefixEnd_19747 := by exact prefixLift 19747
  have htrace : WordTrace (prefixWord ++ tailWord_19747) baseStart_19747 baseEnd_19747 := by
    simpa [prefixWord, tailWord_19747, baseEnd_19747] using wordTrace_append hprefix tailTrace_19747
  have hstable : (prefixWord ++ tailWord_19747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19747).length < 2 ^ (prefixWord ++ tailWord_19747).sum := by decide
  have hdescent : baseEnd_19747 < baseStart_19747 := by decide
  rcases family_descends (prefixWord ++ tailWord_19747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19786 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_19786 : Nat := 118140960795 + 19786 * 2 ^ 59
def prefixEnd_19786 : Nat := 4983230072969 + 3 ^ 40 * 19786 * 2
def baseEnd_19786 : Nat := 6773152153309880589341

theorem tailTrace_19786 : CollatzResearch.WordTrace tailWord_19786 prefixEnd_19786 6773152153309880589341 := by
  unfold tailWord_19786
  simp only [CollatzResearch.WordTrace]
  refine ⟨180413676581544006219803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 481103137550784016586141 180413676581544006219803)
  ·
    refine ⟨270620514872316009329705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180413676581544006219803 270620514872316009329705)
    ·
      refine ⟨202965386154237006997279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270620514872316009329705 202965386154237006997279)
      ·
        refine ⟨304448079231355510495919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202965386154237006997279 304448079231355510495919)
        ·
          refine ⟨456672118847033265743879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304448079231355510495919 456672118847033265743879)
          ·
            refine ⟨685008178270549898615819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456672118847033265743879 685008178270549898615819)
            ·
              refine ⟨1027512267405824847923729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685008178270549898615819 1027512267405824847923729)
              ·
                refine ⟨770634200554368635942797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027512267405824847923729 770634200554368635942797)
                ·
                  refine ⟨288987825207888238478549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770634200554368635942797 288987825207888238478549)
                  ·
                    refine ⟨6773152153309880589341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 288987825207888238478549 6773152153309880589341)
                    ·
                      rfl

theorem cell22_19786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_19786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19786 prefixEnd_19786 := by exact prefixLift 19786
  have htrace : WordTrace (prefixWord ++ tailWord_19786) baseStart_19786 baseEnd_19786 := by
    simpa [prefixWord, tailWord_19786, baseEnd_19786] using wordTrace_append hprefix tailTrace_19786
  have hstable : (prefixWord ++ tailWord_19786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19786).length < 2 ^ (prefixWord ++ tailWord_19786).sum := by decide
  have hdescent : baseEnd_19786 < baseStart_19786 := by decide
  rcases family_descends (prefixWord ++ tailWord_19786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19788 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 5]
def baseStart_19788 : Nat := 118140960795 + 19788 * 2 ^ 59
def prefixEnd_19788 : Nat := 4983230072969 + 3 ^ 40 * 19788 * 2
def baseEnd_19788 : Nat := 2257945598060847346445

theorem tailTrace_19788 : CollatzResearch.WordTrace tailWord_19788 prefixEnd_19788 2257945598060847346445 := by
  unfold tailWord_19788
  simp only [CollatzResearch.WordTrace]
  refine ⟨360863826159465183226009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 481151768212620244301345 360863826159465183226009)
  ·
    refine ⟨270647869619598887419507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 360863826159465183226009 270647869619598887419507)
    ·
      refine ⟨405971804429398331129261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270647869619598887419507 405971804429398331129261)
      ·
        refine ⟨152239426661024374173473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 405971804429398331129261 152239426661024374173473)
        ·
          refine ⟨114179569995768280630105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152239426661024374173473 114179569995768280630105)
          ·
            refine ⟨85634677496826210472579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114179569995768280630105 85634677496826210472579)
            ·
              refine ⟨128452016245239315708869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85634677496826210472579 128452016245239315708869)
              ·
                refine ⟨24084753045982371695413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128452016245239315708869 24084753045982371695413)
                ·
                  refine ⟨2257945598060847346445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24084753045982371695413 2257945598060847346445)
                  ·
                    rfl

theorem cell22_19788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_19788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19788 prefixEnd_19788 := by exact prefixLift 19788
  have htrace : WordTrace (prefixWord ++ tailWord_19788) baseStart_19788 baseEnd_19788 := by
    simpa [prefixWord, tailWord_19788, baseEnd_19788] using wordTrace_append hprefix tailTrace_19788
  have hstable : (prefixWord ++ tailWord_19788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19788).length < 2 ^ (prefixWord ++ tailWord_19788).sum := by decide
  have hdescent : baseEnd_19788 < baseStart_19788 := by decide
  rcases family_descends (prefixWord ++ tailWord_19788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19865 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 1, 5]
def baseStart_19865 : Nat := 118140960795 + 19865 * 2 ^ 59
def prefixEnd_19865 : Nat := 4983230072969 + 3 ^ 40 * 19865 * 2
def baseEnd_19865 : Nat := 6800195467780007864099

theorem tailTrace_19865 : CollatzResearch.WordTrace tailWord_19865 prefixEnd_19865 6800195467780007864099 := by
  unfold tailWord_19865
  simp only [CollatzResearch.WordTrace]
  refine ⟨724536073039972517005049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 483024048693315011336699 724536073039972517005049)
  ·
    refine ⟨543402054779979387753787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 724536073039972517005049 543402054779979387753787)
    ·
      refine ⟨815103082169969081630681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543402054779979387753787 815103082169969081630681)
      ·
        refine ⟨611327311627476811223011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 815103082169969081630681 611327311627476811223011)
        ·
          refine ⟨916990967441215216834517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611327311627476811223011 916990967441215216834517)
          ·
            refine ⟨21491975799403481644559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 916990967441215216834517 21491975799403481644559)
            ·
              refine ⟨32237963699105222466839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21491975799403481644559 32237963699105222466839)
              ·
                refine ⟨48356945548657833700259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32237963699105222466839 48356945548657833700259)
                ·
                  refine ⟨72535418322986750550389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48356945548657833700259 72535418322986750550389)
                  ·
                    refine ⟨6800195467780007864099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72535418322986750550389 6800195467780007864099)
                    ·
                      rfl

theorem cell22_19865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_19865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19865 prefixEnd_19865 := by exact prefixLift 19865
  have htrace : WordTrace (prefixWord ++ tailWord_19865) baseStart_19865 baseEnd_19865 := by
    simpa [prefixWord, tailWord_19865, baseEnd_19865] using wordTrace_append hprefix tailTrace_19865
  have hstable : (prefixWord ++ tailWord_19865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19865).length < 2 ^ (prefixWord ++ tailWord_19865).sum := by decide
  have hdescent : baseEnd_19865 < baseStart_19865 := by decide
  rcases family_descends (prefixWord ++ tailWord_19865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19957 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 5]
def baseStart_19957 : Nat := 118140960795 + 19957 * 2 ^ 59
def prefixEnd_19957 : Nat := 4983230072969 + 3 ^ 40 * 19957 * 2
def baseEnd_19957 : Nat := 2277229649307478187939

theorem tailTrace_19957 : CollatzResearch.WordTrace tailWord_19957 prefixEnd_19957 2277229649307478187939 := by
  unfold tailWord_19957
  simp only [CollatzResearch.WordTrace]
  refine ⟨727891588706672229354125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 485261059137781486236083 727891588706672229354125)
  ·
    refine ⟨272959345765002086007797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 727891588706672229354125 272959345765002086007797)
    ·
      refine ⟨25589938665468945563231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 272959345765002086007797 25589938665468945563231)
      ·
        refine ⟨38384907998203418344847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25589938665468945563231 38384907998203418344847)
        ·
          refine ⟨57577361997305127517271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38384907998203418344847 57577361997305127517271)
          ·
            refine ⟨86366042995957691275907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57577361997305127517271 86366042995957691275907)
            ·
              refine ⟨129549064493936536913861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86366042995957691275907 129549064493936536913861)
              ·
                refine ⟨24290449592613100671349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129549064493936536913861 24290449592613100671349)
                ·
                  refine ⟨2277229649307478187939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24290449592613100671349 2277229649307478187939)
                  ·
                    rfl

theorem cell22_19957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_19957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19957 prefixEnd_19957 := by exact prefixLift 19957
  have htrace : WordTrace (prefixWord ++ tailWord_19957) baseStart_19957 baseEnd_19957 := by
    simpa [prefixWord, tailWord_19957, baseEnd_19957] using wordTrace_append hprefix tailTrace_19957
  have hstable : (prefixWord ++ tailWord_19957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19957).length < 2 ^ (prefixWord ++ tailWord_19957).sum := by decide
  have hdescent : baseEnd_19957 < baseStart_19957 := by decide
  rcases family_descends (prefixWord ++ tailWord_19957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19972 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_19972 : Nat := 118140960795 + 19972 * 2 ^ 59
def prefixEnd_19972 : Nat := 4983230072969 + 3 ^ 40 * 19972 * 2
def baseEnd_19972 : Nat := 6836823754467395438771

theorem tailTrace_19972 : CollatzResearch.WordTrace tailWord_19972 prefixEnd_19972 6836823754467395438771 := by
  unfold tailWord_19972
  simp only [CollatzResearch.WordTrace]
  refine ⟨364219341826164895575085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 485625789101553194100113 364219341826164895575085)
  ·
    refine ⟨136582253184811835840657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 364219341826164895575085 136582253184811835840657)
    ·
      refine ⟨102436689888608876880493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136582253184811835840657 102436689888608876880493)
      ·
        refine ⟨38413758708228328830185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102436689888608876880493 38413758708228328830185)
        ·
          refine ⟨28810319031171246622639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38413758708228328830185 28810319031171246622639)
          ·
            refine ⟨43215478546756869933959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28810319031171246622639 43215478546756869933959)
            ·
              refine ⟨64823217820135304900939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43215478546756869933959 64823217820135304900939)
              ·
                refine ⟨97234826730202957351409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64823217820135304900939 97234826730202957351409)
                ·
                  refine ⟨72926120047652218013557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97234826730202957351409 72926120047652218013557)
                  ·
                    refine ⟨6836823754467395438771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72926120047652218013557 6836823754467395438771)
                    ·
                      rfl

theorem cell22_19972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_19972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_19972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_19972 prefixEnd_19972 := by exact prefixLift 19972
  have htrace : WordTrace (prefixWord ++ tailWord_19972) baseStart_19972 baseEnd_19972 := by
    simpa [prefixWord, tailWord_19972, baseEnd_19972] using wordTrace_append hprefix tailTrace_19972
  have hstable : (prefixWord ++ tailWord_19972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19972).length < 2 ^ (prefixWord ++ tailWord_19972).sum := by decide
  have hdescent : baseEnd_19972 < baseStart_19972 := by decide
  rcases family_descends (prefixWord ++ tailWord_19972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20002 : List Nat := [3, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_20002 : Nat := 118140960795 + 20002 * 2 ^ 59
def prefixEnd_20002 : Nat := 4983230072969 + 3 ^ 40 * 20002 * 2
def baseEnd_20002 : Nat := 2282364455852439062893

theorem tailTrace_20002 : CollatzResearch.WordTrace tailWord_20002 prefixEnd_20002 2282364455852439062893 := by
  unfold tailWord_20002
  simp only [CollatzResearch.WordTrace]
  refine ⟨182383218385911228685565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 486355249029096609828173 182383218385911228685565)
  ·
    refine ⟨68393706894716710757087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182383218385911228685565 68393706894716710757087)
    ·
      refine ⟨102590560342075066135631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68393706894716710757087 102590560342075066135631)
      ·
        refine ⟨153885840513112599203447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102590560342075066135631 153885840513112599203447)
        ·
          refine ⟨230828760769668898805171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153885840513112599203447 230828760769668898805171)
          ·
            refine ⟨346243141154503348207757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230828760769668898805171 346243141154503348207757)
            ·
              refine ⟨129841177932938755577909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346243141154503348207757 129841177932938755577909)
              ·
                refine ⟨12172610431213008335429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129841177932938755577909 12172610431213008335429)
                ·
                  refine ⟨2282364455852439062893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12172610431213008335429 2282364455852439062893)
                  ·
                    rfl

theorem cell22_20002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_20002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20002 prefixEnd_20002 := by exact prefixLift 20002
  have htrace : WordTrace (prefixWord ++ tailWord_20002) baseStart_20002 baseEnd_20002 := by
    simpa [prefixWord, tailWord_20002, baseEnd_20002] using wordTrace_append hprefix tailTrace_20002
  have hstable : (prefixWord ++ tailWord_20002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20002).length < 2 ^ (prefixWord ++ tailWord_20002).sum := by decide
  have hdescent : baseEnd_20002 < baseStart_20002 := by decide
  rcases family_descends (prefixWord ++ tailWord_20002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20173 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_20173 : Nat := 118140960795 + 20173 * 2 ^ 59
def prefixEnd_20173 : Nat := 4983230072969 + 3 ^ 40 * 20173 * 2
def baseEnd_20173 : Nat := 6905630162169871163155

theorem tailTrace_20173 : CollatzResearch.WordTrace tailWord_20173 prefixEnd_20173 6905630162169871163155 := by
  unfold tailWord_20173
  simp only [CollatzResearch.WordTrace]
  refine ⟨735769755924141119217173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 490513170616094079478115 735769755924141119217173)
  ·
    refine ⟨34489207308944114963305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 735769755924141119217173 34489207308944114963305)
    ·
      refine ⟨25866905481708086222479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34489207308944114963305 25866905481708086222479)
      ·
        refine ⟨38800358222562129333719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25866905481708086222479 38800358222562129333719)
        ·
          refine ⟨58200537333843194000579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38800358222562129333719 58200537333843194000579)
          ·
            refine ⟨87300806000764791000869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58200537333843194000579 87300806000764791000869)
            ·
              refine ⟨16368901125143398312663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87300806000764791000869 16368901125143398312663)
              ·
                refine ⟨24553351687715097468995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16368901125143398312663 24553351687715097468995)
                ·
                  refine ⟨36830027531572646203493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24553351687715097468995 36830027531572646203493)
                  ·
                    refine ⟨6905630162169871163155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36830027531572646203493 6905630162169871163155)
                    ·
                      rfl

theorem cell22_20173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_20173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20173 prefixEnd_20173 := by exact prefixLift 20173
  have htrace : WordTrace (prefixWord ++ tailWord_20173) baseStart_20173 baseEnd_20173 := by
    simpa [prefixWord, tailWord_20173, baseEnd_20173] using wordTrace_append hprefix tailTrace_20173
  have hstable : (prefixWord ++ tailWord_20173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20173).length < 2 ^ (prefixWord ++ tailWord_20173).sum := by decide
  have hdescent : baseEnd_20173 < baseStart_20173 := by decide
  rcases family_descends (prefixWord ++ tailWord_20173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20186 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_20186 : Nat := 118140960795 + 20186 * 2 ^ 59
def prefixEnd_20186 : Nat := 4983230072969 + 3 ^ 40 * 20186 * 2
def baseEnd_20186 : Nat := 6910080327842170588115

theorem tailTrace_20186 : CollatzResearch.WordTrace tailWord_20186 prefixEnd_20186 6910080327842170588115 := by
  unfold tailWord_20186
  simp only [CollatzResearch.WordTrace]
  refine ⟨184060976219261084860103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 490829269918029559626941 184060976219261084860103)
  ·
    refine ⟨276091464328891627290155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184060976219261084860103 276091464328891627290155)
    ·
      refine ⟨414137196493337440935233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276091464328891627290155 414137196493337440935233)
      ·
        refine ⟨310602897370003080701425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414137196493337440935233 310602897370003080701425)
        ·
          refine ⟨232952173027502310526069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310602897370003080701425 232952173027502310526069)
          ·
            refine ⟨21839266221328341611819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232952173027502310526069 21839266221328341611819)
            ·
              refine ⟨32758899331992512417729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21839266221328341611819 32758899331992512417729)
              ·
                refine ⟨24569174498994384313297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32758899331992512417729 24569174498994384313297)
                ·
                  refine ⟨18426880874245788234973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24569174498994384313297 18426880874245788234973)
                  ·
                    refine ⟨6910080327842170588115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18426880874245788234973 6910080327842170588115)
                    ·
                      rfl

theorem cell22_20186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_20186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20186 prefixEnd_20186 := by exact prefixLift 20186
  have htrace : WordTrace (prefixWord ++ tailWord_20186) baseStart_20186 baseEnd_20186 := by
    simpa [prefixWord, tailWord_20186, baseEnd_20186] using wordTrace_append hprefix tailTrace_20186
  have hstable : (prefixWord ++ tailWord_20186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20186).length < 2 ^ (prefixWord ++ tailWord_20186).sum := by decide
  have hdescent : baseEnd_20186 < baseStart_20186 := by decide
  rcases family_descends (prefixWord ++ tailWord_20186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20254 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_20254 : Nat := 118140960795 + 20254 * 2 ^ 59
def prefixEnd_20254 : Nat := 4983230072969 + 3 ^ 40 * 20254 * 2
def baseEnd_20254 : Nat := 6933358117512659887907

theorem tailTrace_20254 : CollatzResearch.WordTrace tailWord_20254 prefixEnd_20254 6933358117512659887907 := by
  unfold tailWord_20254
  simp only [CollatzResearch.WordTrace]
  refine ⟨92340508578836494114477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 492482712420461301943877 92340508578836494114477)
  ·
    refine ⟨34627690717063685292929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92340508578836494114477 34627690717063685292929)
    ·
      refine ⟨25970768037797763969697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34627690717063685292929 25970768037797763969697)
      ·
        refine ⟨19478076028348322977273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25970768037797763969697 19478076028348322977273)
        ·
          refine ⟨14608557021261242232955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19478076028348322977273 14608557021261242232955)
          ·
            refine ⟨21912835531891863349433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14608557021261242232955 21912835531891863349433)
            ·
              refine ⟨16434626648918897512075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21912835531891863349433 16434626648918897512075)
              ·
                refine ⟨24651939973378346268113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16434626648918897512075 24651939973378346268113)
                ·
                  refine ⟨18488954980033759701085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24651939973378346268113 18488954980033759701085)
                  ·
                    refine ⟨6933358117512659887907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18488954980033759701085 6933358117512659887907)
                    ·
                      rfl

theorem cell22_20254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_20254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20254 prefixEnd_20254 := by exact prefixLift 20254
  have htrace : WordTrace (prefixWord ++ tailWord_20254) baseStart_20254 baseEnd_20254 := by
    simpa [prefixWord, tailWord_20254, baseEnd_20254] using wordTrace_append hprefix tailTrace_20254
  have hstable : (prefixWord ++ tailWord_20254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20254).length < 2 ^ (prefixWord ++ tailWord_20254).sum := by decide
  have hdescent : baseEnd_20254 < baseStart_20254 := by decide
  rcases family_descends (prefixWord ++ tailWord_20254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20261 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 5]
def baseStart_20261 : Nat := 118140960795 + 20261 * 2 ^ 59
def prefixEnd_20261 : Nat := 4983230072969 + 3 ^ 40 * 20261 * 2
def baseEnd_20261 : Nat := 2311918120188991654295

theorem tailTrace_20261 : CollatzResearch.WordTrace tailWord_20261 prefixEnd_20261 2311918120188991654295 := by
  unfold tailWord_20261
  simp only [CollatzResearch.WordTrace]
  refine ⟨738979379605332148420637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 492652919736888098947091 738979379605332148420637)
  ·
    refine ⟨277117267351999555657739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 738979379605332148420637 277117267351999555657739)
    ·
      refine ⟨415675901027999333486609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277117267351999555657739 415675901027999333486609)
      ·
        refine ⟨311756925770999500114957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415675901027999333486609 311756925770999500114957)
        ·
          refine ⟨116908847164124812543109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311756925770999500114957 116908847164124812543109)
          ·
            refine ⟨21920408843273402351833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116908847164124812543109 21920408843273402351833)
            ·
              refine ⟨16440306632455051763875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21920408843273402351833 16440306632455051763875)
              ·
                refine ⟨24660459948682577645813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16440306632455051763875 24660459948682577645813)
                ·
                  refine ⟨2311918120188991654295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24660459948682577645813 2311918120188991654295)
                  ·
                    rfl

theorem cell22_20261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_20261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20261 prefixEnd_20261 := by exact prefixLift 20261
  have htrace : WordTrace (prefixWord ++ tailWord_20261) baseStart_20261 baseEnd_20261 := by
    simpa [prefixWord, tailWord_20261, baseEnd_20261] using wordTrace_append hprefix tailTrace_20261
  have hstable : (prefixWord ++ tailWord_20261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20261).length < 2 ^ (prefixWord ++ tailWord_20261).sum := by decide
  have hdescent : baseEnd_20261 < baseStart_20261 := by decide
  rcases family_descends (prefixWord ++ tailWord_20261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20274 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_20274 : Nat := 118140960795 + 20274 * 2 ^ 59
def prefixEnd_20274 : Nat := 4983230072969 + 3 ^ 40 * 20274 * 2
def baseEnd_20274 : Nat := 6940204526239274387845

theorem tailTrace_20274 : CollatzResearch.WordTrace tailWord_20274 prefixEnd_20274 6940204526239274387845 := by
  unfold tailWord_20274
  simp only [CollatzResearch.WordTrace]
  refine ⟨184863382139558842160969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 492969019038823579095917 184863382139558842160969)
  ·
    refine ⟨138647536604669131620727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184863382139558842160969 138647536604669131620727)
    ·
      refine ⟨207971304907003697431091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138647536604669131620727 207971304907003697431091)
      ·
        refine ⟨311956957360505546146637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207971304907003697431091 311956957360505546146637)
        ·
          refine ⟨116983859010189579804989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311956957360505546146637 116983859010189579804989)
          ·
            refine ⟨43868947128821092426871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116983859010189579804989 43868947128821092426871)
            ·
              refine ⟨65803420693231638640307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43868947128821092426871 65803420693231638640307)
              ·
                refine ⟨98705131039847457960461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65803420693231638640307 98705131039847457960461)
                ·
                  refine ⟨37014424139942796735173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98705131039847457960461 37014424139942796735173)
                  ·
                    refine ⟨6940204526239274387845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37014424139942796735173 6940204526239274387845)
                    ·
                      rfl

theorem cell22_20274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_20274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20274 prefixEnd_20274 := by exact prefixLift 20274
  have htrace : WordTrace (prefixWord ++ tailWord_20274) baseStart_20274 baseEnd_20274 := by
    simpa [prefixWord, tailWord_20274, baseEnd_20274] using wordTrace_append hprefix tailTrace_20274
  have hstable : (prefixWord ++ tailWord_20274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20274).length < 2 ^ (prefixWord ++ tailWord_20274).sum := by decide
  have hdescent : baseEnd_20274 < baseStart_20274 := by decide
  rcases family_descends (prefixWord ++ tailWord_20274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20291 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 1, 4]
def baseStart_20291 : Nat := 118140960795 + 20291 * 2 ^ 59
def prefixEnd_20291 : Nat := 4983230072969 + 3 ^ 40 * 20291 * 2
def baseEnd_20291 : Nat := 6946023973656896712793

theorem tailTrace_20291 : CollatzResearch.WordTrace tailWord_20291 prefixEnd_20291 6946023973656896712793 := by
  unfold tailWord_20291
  simp only [CollatzResearch.WordTrace]
  refine ⟨740073569496647272012727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 493382379664431514675151 740073569496647272012727)
  ·
    refine ⟨1110110354244970908019091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 740073569496647272012727 1110110354244970908019091)
    ·
      refine ⟨1665165531367456362028637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110110354244970908019091 1665165531367456362028637)
      ·
        refine ⟨624437074262796135760739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1665165531367456362028637 624437074262796135760739)
        ·
          refine ⟨936655611394194203641109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624437074262796135760739 936655611394194203641109)
          ·
            refine ⟨43905731784102853295677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 936655611394194203641109 43905731784102853295677)
            ·
              refine ⟨16464649419038569985879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43905731784102853295677 16464649419038569985879)
              ·
                refine ⟨24696974128557854978819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16464649419038569985879 24696974128557854978819)
                ·
                  refine ⟨37045461192836782468229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24696974128557854978819 37045461192836782468229)
                  ·
                    refine ⟨6946023973656896712793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37045461192836782468229 6946023973656896712793)
                    ·
                      rfl

theorem cell22_20291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 4].length) (baseStart_20291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20291 prefixEnd_20291 := by exact prefixLift 20291
  have htrace : WordTrace (prefixWord ++ tailWord_20291) baseStart_20291 baseEnd_20291 := by
    simpa [prefixWord, tailWord_20291, baseEnd_20291] using wordTrace_append hprefix tailTrace_20291
  have hstable : (prefixWord ++ tailWord_20291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20291).length < 2 ^ (prefixWord ++ tailWord_20291).sum := by decide
  have hdescent : baseEnd_20291 < baseStart_20291 := by decide
  rcases family_descends (prefixWord ++ tailWord_20291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20302 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_20302 : Nat := 118140960795 + 20302 * 2 ^ 59
def prefixEnd_20302 : Nat := 4983230072969 + 3 ^ 40 * 20302 * 2
def baseEnd_20302 : Nat := 6949789498456534687759

theorem tailTrace_20302 : CollatzResearch.WordTrace tailWord_20302 prefixEnd_20302 6949789498456534687759 := by
  unfold tailWord_20302
  simp only [CollatzResearch.WordTrace]
  refine ⟨92559346557099518832895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 493649848304530767108773 92559346557099518832895)
  ·
    refine ⟨138839019835649278249343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92559346557099518832895 138839019835649278249343)
    ·
      refine ⟨208258529753473917374015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138839019835649278249343 208258529753473917374015)
      ·
        refine ⟨312387794630210876061023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208258529753473917374015 312387794630210876061023)
        ·
          refine ⟨468581691945316314091535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312387794630210876061023 468581691945316314091535)
          ·
            refine ⟨702872537917974471137303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468581691945316314091535 702872537917974471137303)
            ·
              refine ⟨1054308806876961706705955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702872537917974471137303 1054308806876961706705955)
              ·
                refine ⟨1581463210315442560058933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054308806876961706705955 1581463210315442560058933)
                ·
                  refine ⟨148262175967072740005525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1581463210315442560058933 148262175967072740005525)
                  ·
                    refine ⟨6949789498456534687759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148262175967072740005525 6949789498456534687759)
                    ·
                      rfl

theorem cell22_20302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_20302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20302 prefixEnd_20302 := by exact prefixLift 20302
  have htrace : WordTrace (prefixWord ++ tailWord_20302) baseStart_20302 baseEnd_20302 := by
    simpa [prefixWord, tailWord_20302, baseEnd_20302] using wordTrace_append hprefix tailTrace_20302
  have hstable : (prefixWord ++ tailWord_20302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20302).length < 2 ^ (prefixWord ++ tailWord_20302).sum := by decide
  have hdescent : baseEnd_20302 < baseStart_20302 := by decide
  rcases family_descends (prefixWord ++ tailWord_20302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20306 : List Nat := [3, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_20306 : Nat := 118140960795 + 20306 * 2 ^ 59
def prefixEnd_20306 : Nat := 4983230072969 + 3 ^ 40 * 20306 * 2
def baseEnd_20306 : Nat := 2317052926733952529249

theorem tailTrace_20306 : CollatzResearch.WordTrace tailWord_20306 prefixEnd_20306 2317052926733952529249 := by
  unfold tailWord_20306
  simp only [CollatzResearch.WordTrace]
  refine ⟨185155166110576208452193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 493747109628203222539181 185155166110576208452193)
  ·
    refine ⟨138866374582932156339145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185155166110576208452193 138866374582932156339145)
    ·
      refine ⟨104149780937199117254359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138866374582932156339145 104149780937199117254359)
      ·
        refine ⟨156224671405798675881539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104149780937199117254359 156224671405798675881539)
        ·
          refine ⟨234337007108698013822309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156224671405798675881539 234337007108698013822309)
          ·
            refine ⟨43938188832880877591683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234337007108698013822309 43938188832880877591683)
            ·
              refine ⟨65907283249321316387525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43938188832880877591683 65907283249321316387525)
              ·
                refine ⟨12357615609247746822661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65907283249321316387525 12357615609247746822661)
                ·
                  refine ⟨2317052926733952529249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12357615609247746822661 2317052926733952529249)
                  ·
                    rfl

theorem cell22_20306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_20306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20306 prefixEnd_20306 := by exact prefixLift 20306
  have htrace : WordTrace (prefixWord ++ tailWord_20306) baseStart_20306 baseEnd_20306 := by
    simpa [prefixWord, tailWord_20306, baseEnd_20306] using wordTrace_append hprefix tailTrace_20306
  have hstable : (prefixWord ++ tailWord_20306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20306).length < 2 ^ (prefixWord ++ tailWord_20306).sum := by decide
  have hdescent : baseEnd_20306 < baseStart_20306 := by decide
  rcases family_descends (prefixWord ++ tailWord_20306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20342 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_20342 : Nat := 118140960795 + 20342 * 2 ^ 59
def prefixEnd_20342 : Nat := 4983230072969 + 3 ^ 40 * 20342 * 2
def baseEnd_20342 : Nat := 6963482315909763687637

theorem tailTrace_20342 : CollatzResearch.WordTrace tailWord_20342 prefixEnd_20342 6963482315909763687637 := by
  unfold tailWord_20342
  simp only [CollatzResearch.WordTrace]
  refine ⟨46370855769492686382455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 494622461541255321412853 46370855769492686382455)
  ·
    refine ⟨69556283654239029573683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46370855769492686382455 69556283654239029573683)
    ·
      refine ⟨104334425481358544360525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69556283654239029573683 104334425481358544360525)
      ·
        refine ⟨39125409555509454135197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104334425481358544360525 39125409555509454135197)
        ·
          refine ⟨14672028583316045300699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39125409555509454135197 14672028583316045300699)
          ·
            refine ⟨22008042874974067951049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14672028583316045300699 22008042874974067951049)
            ·
              refine ⟨16506032156230550963287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22008042874974067951049 16506032156230550963287)
              ·
                refine ⟨24759048234345826444931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16506032156230550963287 24759048234345826444931)
                ·
                  refine ⟨37138572351518739667397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24759048234345826444931 37138572351518739667397)
                  ·
                    refine ⟨6963482315909763687637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37138572351518739667397 6963482315909763687637)
                    ·
                      rfl

theorem cell22_20342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_20342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20342 prefixEnd_20342 := by exact prefixLift 20342
  have htrace : WordTrace (prefixWord ++ tailWord_20342) baseStart_20342 baseEnd_20342 := by
    simpa [prefixWord, tailWord_20342, baseEnd_20342] using wordTrace_append hprefix tailTrace_20342
  have hstable : (prefixWord ++ tailWord_20342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20342).length < 2 ^ (prefixWord ++ tailWord_20342).sum := by decide
  have hdescent : baseEnd_20342 < baseStart_20342 := by decide
  rcases family_descends (prefixWord ++ tailWord_20342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20349 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_20349 : Nat := 118140960795 + 20349 * 2 ^ 59
def prefixEnd_20349 : Nat := 4983230072969 + 3 ^ 40 * 20349 * 2
def baseEnd_20349 : Nat := 6965878558964078762615

theorem tailTrace_20349 : CollatzResearch.WordTrace tailWord_20349 prefixEnd_20349 6965878558964078762615 := by
  unfold tailWord_20349
  simp only [CollatzResearch.WordTrace]
  refine ⟨742189003286523177624101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 494792668857682118416067 742189003286523177624101)
  ·
    refine ⟨139160438116223095804519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 742189003286523177624101 139160438116223095804519)
    ·
      refine ⟨208740657174334643706779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139160438116223095804519 208740657174334643706779)
      ·
        refine ⟨313110985761501965560169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208740657174334643706779 313110985761501965560169)
        ·
          refine ⟨234833239321126474170127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313110985761501965560169 234833239321126474170127)
          ·
            refine ⟨352249858981689711255191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234833239321126474170127 352249858981689711255191)
            ·
              refine ⟨528374788472534566882787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352249858981689711255191 528374788472534566882787)
              ·
                refine ⟨792562182708801850324181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528374788472534566882787 792562182708801850324181)
                ·
                  refine ⟨18575676157237543366973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 792562182708801850324181 18575676157237543366973)
                  ·
                    refine ⟨6965878558964078762615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18575676157237543366973 6965878558964078762615)
                    ·
                      rfl

theorem cell22_20349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_20349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20349 prefixEnd_20349 := by exact prefixLift 20349
  have htrace : WordTrace (prefixWord ++ tailWord_20349) baseStart_20349 baseEnd_20349 := by
    simpa [prefixWord, tailWord_20349, baseEnd_20349] using wordTrace_append hprefix tailTrace_20349
  have hstable : (prefixWord ++ tailWord_20349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20349).length < 2 ^ (prefixWord ++ tailWord_20349).sum := by decide
  have hdescent : baseEnd_20349 < baseStart_20349 := by decide
  rcases family_descends (prefixWord ++ tailWord_20349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20439 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 1, 5]
def baseStart_20439 : Nat := 118140960795 + 20439 * 2 ^ 59
def prefixEnd_20439 : Nat := 4983230072969 + 3 ^ 40 * 20439 * 2
def baseEnd_20439 : Nat := 6996687398233844012339

theorem tailTrace_20439 : CollatzResearch.WordTrace tailWord_20439 prefixEnd_20439 6996687398233844012339 := by
  unfold tailWord_20439
  simp only [CollatzResearch.WordTrace]
  refine ⟨745471572960468548400371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 496981048640312365600247 745471572960468548400371)
  ·
    refine ⟨1118207359440702822600557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745471572960468548400371 1118207359440702822600557)
    ·
      refine ⟨419327759790263558475209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1118207359440702822600557 419327759790263558475209)
      ·
        refine ⟨314495819842697668856407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419327759790263558475209 314495819842697668856407)
        ·
          refine ⟨471743729764046503284611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314495819842697668856407 471743729764046503284611)
          ·
            refine ⟨707615594646069754926917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471743729764046503284611 707615594646069754926917)
            ·
              refine ⟨132677923996138079048797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 707615594646069754926917 132677923996138079048797)
              ·
                refine ⟨49754221498551779643299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132677923996138079048797 49754221498551779643299)
                ·
                  refine ⟨74631332247827669464949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49754221498551779643299 74631332247827669464949)
                  ·
                    refine ⟨6996687398233844012339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74631332247827669464949 6996687398233844012339)
                    ·
                      rfl

theorem cell22_20439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_20439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20439 prefixEnd_20439 := by exact prefixLift 20439
  have htrace : WordTrace (prefixWord ++ tailWord_20439) baseStart_20439 baseEnd_20439 := by
    simpa [prefixWord, tailWord_20439, baseEnd_20439] using wordTrace_append hprefix tailTrace_20439
  have hstable : (prefixWord ++ tailWord_20439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20439).length < 2 ^ (prefixWord ++ tailWord_20439).sum := by decide
  have hdescent : baseEnd_20439 < baseStart_20439 := by decide
  rcases family_descends (prefixWord ++ tailWord_20439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20469 : List Nat := [1, 3, 5, 13]
def baseStart_20469 : Nat := 118140960795 + 20469 * 2 ^ 59
def prefixEnd_20469 : Nat := 4983230072969 + 3 ^ 40 * 20469 * 2
def baseEnd_20469 : Nat := 9611738012789802143

theorem tailTrace_20469 : CollatzResearch.WordTrace tailWord_20469 prefixEnd_20469 9611738012789802143 := by
  unfold tailWord_20469
  simp only [CollatzResearch.WordTrace]
  refine ⟨746565762851783671992461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 497710508567855781328307 746565762851783671992461)
  ·
    refine ⟨279962161069418876997173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 746565762851783671992461 279962161069418876997173)
    ·
      refine ⟨26246452600258019718485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279962161069418876997173 26246452600258019718485)
      ·
        refine ⟨9611738012789802143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 26246452600258019718485 9611738012789802143)
        ·
          rfl

theorem cell22_20469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 13].length) (baseStart_20469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20469 prefixEnd_20469 := by exact prefixLift 20469
  have htrace : WordTrace (prefixWord ++ tailWord_20469) baseStart_20469 baseEnd_20469 := by
    simpa [prefixWord, tailWord_20469, baseEnd_20469] using wordTrace_append hprefix tailTrace_20469
  have hstable : (prefixWord ++ tailWord_20469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20469).length < 2 ^ (prefixWord ++ tailWord_20469).sum := by decide
  have hdescent : baseEnd_20469 < baseStart_20469 := by decide
  rcases family_descends (prefixWord ++ tailWord_20469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20473 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 2, 3]
def baseStart_20473 : Nat := 118140960795 + 20473 * 2 ^ 59
def prefixEnd_20473 : Nat := 4983230072969 + 3 ^ 40 * 20473 * 2
def baseEnd_20473 : Nat := 7008326293069088662235

theorem tailTrace_20473 : CollatzResearch.WordTrace tailWord_20473 prefixEnd_20473 7008326293069088662235 := by
  unfold tailWord_20473
  simp only [CollatzResearch.WordTrace]
  refine ⟨746711654837292355138073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 497807769891528236758715 746711654837292355138073)
  ·
    refine ⟨560033741127969266353555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 746711654837292355138073 560033741127969266353555)
    ·
      refine ⟨840050611691953899530333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560033741127969266353555 840050611691953899530333)
      ·
        refine ⟨315018979384482712323875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 840050611691953899530333 315018979384482712323875)
        ·
          refine ⟨472528469076724068485813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315018979384482712323875 472528469076724068485813)
          ·
            refine ⟨44299543975942881420545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 472528469076724068485813 44299543975942881420545)
            ·
              refine ⟨33224657981957161065409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44299543975942881420545 33224657981957161065409)
              ·
                refine ⟨24918493486467870799057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33224657981957161065409 24918493486467870799057)
                ·
                  refine ⟨18688870114850903099293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24918493486467870799057 18688870114850903099293)
                  ·
                    refine ⟨7008326293069088662235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18688870114850903099293 7008326293069088662235)
                    ·
                      rfl

theorem cell22_20473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_20473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20473 prefixEnd_20473 := by exact prefixLift 20473
  have htrace : WordTrace (prefixWord ++ tailWord_20473) baseStart_20473 baseEnd_20473 := by
    simpa [prefixWord, tailWord_20473, baseEnd_20473] using wordTrace_append hprefix tailTrace_20473
  have hstable : (prefixWord ++ tailWord_20473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20473).length < 2 ^ (prefixWord ++ tailWord_20473).sum := by decide
  have hdescent : baseEnd_20473 < baseStart_20473 := by decide
  rcases family_descends (prefixWord ++ tailWord_20473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20503 : List Nat := [1, 1, 3, 5, 2, 1, 3, 6]
def baseStart_20503 : Nat := 118140960795 + 20503 * 2 ^ 59
def prefixEnd_20503 : Nat := 4983230072969 + 3 ^ 40 * 20503 * 2
def baseEnd_20503 : Nat := 779843989573223379127

theorem tailTrace_20503 : CollatzResearch.WordTrace tailWord_20503 prefixEnd_20503 779843989573223379127 := by
  unfold tailWord_20503
  simp only [CollatzResearch.WordTrace]
  refine ⟨747805844728607478730163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 498537229819071652486775 747805844728607478730163)
  ·
    refine ⟨1121708767092911218095245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 747805844728607478730163 1121708767092911218095245)
    ·
      refine ⟨420640787659841706785717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1121708767092911218095245 420640787659841706785717)
      ·
        refine ⟨39435073843110160011161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 420640787659841706785717 39435073843110160011161)
        ·
          refine ⟨29576305382332620008371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39435073843110160011161 29576305382332620008371)
          ·
            refine ⟨44364458073498930012557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29576305382332620008371 44364458073498930012557)
            ·
              refine ⟨16636671777562098754709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44364458073498930012557 16636671777562098754709)
              ·
                refine ⟨779843989573223379127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16636671777562098754709 779843989573223379127)
                ·
                  rfl

theorem cell22_20503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 6].length) (baseStart_20503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20503 prefixEnd_20503 := by exact prefixLift 20503
  have htrace : WordTrace (prefixWord ++ tailWord_20503) baseStart_20503 baseEnd_20503 := by
    simpa [prefixWord, tailWord_20503, baseEnd_20503] using wordTrace_append hprefix tailTrace_20503
  have hstable : (prefixWord ++ tailWord_20503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20503).length < 2 ^ (prefixWord ++ tailWord_20503).sum := by decide
  have hdescent : baseEnd_20503 < baseStart_20503 := by decide
  rcases family_descends (prefixWord ++ tailWord_20503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20531 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 5]
def baseStart_20531 : Nat := 118140960795 + 20531 * 2 ^ 59
def prefixEnd_20531 : Nat := 4983230072969 + 3 ^ 40 * 20531 * 2
def baseEnd_20531 : Nat := 2342726959458756904019

theorem tailTrace_20531 : CollatzResearch.WordTrace tailWord_20531 prefixEnd_20531 2342726959458756904019 := by
  unfold tailWord_20531
  simp only [CollatzResearch.WordTrace]
  refine ⟨748827088627168260749447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 499218059084778840499631 748827088627168260749447)
  ·
    refine ⟨1123240632940752391124171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748827088627168260749447 1123240632940752391124171)
    ·
      refine ⟨1684860949411128586686257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123240632940752391124171 1684860949411128586686257)
      ·
        refine ⟨1263645712058346440014693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684860949411128586686257 1263645712058346440014693)
        ·
          refine ⟨236933571010939957502755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1263645712058346440014693 236933571010939957502755)
          ·
            refine ⟨355400356516409936254133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236933571010939957502755 355400356516409936254133)
            ·
              refine ⟨33318783423413431523825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 355400356516409936254133 33318783423413431523825)
              ·
                refine ⟨24989087567560073642869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33318783423413431523825 24989087567560073642869)
                ·
                  refine ⟨2342726959458756904019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24989087567560073642869 2342726959458756904019)
                  ·
                    rfl

theorem cell22_20531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 5].length) (baseStart_20531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20531 prefixEnd_20531 := by exact prefixLift 20531
  have htrace : WordTrace (prefixWord ++ tailWord_20531) baseStart_20531 baseEnd_20531 := by
    simpa [prefixWord, tailWord_20531, baseEnd_20531] using wordTrace_append hprefix tailTrace_20531
  have hstable : (prefixWord ++ tailWord_20531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20531).length < 2 ^ (prefixWord ++ tailWord_20531).sum := by decide
  have hdescent : baseEnd_20531 < baseStart_20531 := by decide
  rcases family_descends (prefixWord ++ tailWord_20531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20638 : List Nat := [4, 3, 1, 1, 3, 10]
def baseStart_20638 : Nat := 118140960795 + 20638 * 2 ^ 59
def prefixEnd_20638 : Nat := 4983230072969 + 3 ^ 40 * 20638 * 2
def baseEnd_20638 : Nat := 87219866235353806009

theorem tailTrace_20638 : CollatzResearch.WordTrace tailWord_20638 prefixEnd_20638 87219866235353806009 := by
  unfold tailWord_20638
  simp only [CollatzResearch.WordTrace]
  refine ⟨94091212404940691861821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 501819799493017023263045 94091212404940691861821)
  ·
    refine ⟨35284204651852759448183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94091212404940691861821 35284204651852759448183)
    ·
      refine ⟨52926306977779139172275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35284204651852759448183 52926306977779139172275)
      ·
        refine ⟨79389460466668708758413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52926306977779139172275 79389460466668708758413)
        ·
          refine ⟨29771047675000765784405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79389460466668708758413 29771047675000765784405)
          ·
            refine ⟨87219866235353806009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 29771047675000765784405 87219866235353806009)
            ·
              rfl

theorem cell22_20638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 10].length) (baseStart_20638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20638 prefixEnd_20638 := by exact prefixLift 20638
  have htrace : WordTrace (prefixWord ++ tailWord_20638) baseStart_20638 baseEnd_20638 := by
    simpa [prefixWord, tailWord_20638, baseEnd_20638] using wordTrace_append hprefix tailTrace_20638
  have hstable : (prefixWord ++ tailWord_20638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20638).length < 2 ^ (prefixWord ++ tailWord_20638).sum := by decide
  have hdescent : baseEnd_20638 < baseStart_20638 := by decide
  rcases family_descends (prefixWord ++ tailWord_20638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20642 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_20642 : Nat := 118140960795 + 20642 * 2 ^ 59
def prefixEnd_20642 : Nat := 4983230072969 + 3 ^ 40 * 20642 * 2
def baseEnd_20642 : Nat := 7066178446808981186717

theorem tailTrace_20642 : CollatzResearch.WordTrace tailWord_20642 prefixEnd_20642 7066178446808981186717 := by
  unfold tailWord_20642
  simp only [CollatzResearch.WordTrace]
  refine ⟨188218897806258554510045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 501917060816689478693453 188218897806258554510045)
  ·
    refine ⟨70582086677346957941267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188218897806258554510045 70582086677346957941267)
    ·
      refine ⟨105873130016020436911901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70582086677346957941267 105873130016020436911901)
      ·
        refine ⟨39702423756007663841963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105873130016020436911901 39702423756007663841963)
        ·
          refine ⟨59553635634011495762945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39702423756007663841963 59553635634011495762945)
          ·
            refine ⟨44665226725508621822209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59553635634011495762945 44665226725508621822209)
            ·
              refine ⟨33498920044131466366657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44665226725508621822209 33498920044131466366657)
              ·
                refine ⟨25124190033098599774993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33498920044131466366657 25124190033098599774993)
                ·
                  refine ⟨18843142524823949831245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25124190033098599774993 18843142524823949831245)
                  ·
                    refine ⟨7066178446808981186717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18843142524823949831245 7066178446808981186717)
                    ·
                      rfl

theorem cell22_20642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_20642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20642 prefixEnd_20642 := by exact prefixLift 20642
  have htrace : WordTrace (prefixWord ++ tailWord_20642) baseStart_20642 baseEnd_20642 := by
    simpa [prefixWord, tailWord_20642, baseEnd_20642] using wordTrace_append hprefix tailTrace_20642
  have hstable : (prefixWord ++ tailWord_20642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20642).length < 2 ^ (prefixWord ++ tailWord_20642).sum := by decide
  have hdescent : baseEnd_20642 < baseStart_20642 := by decide
  rcases family_descends (prefixWord ++ tailWord_20642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20644 : List Nat := [2, 3, 1, 2, 5, 1, 2, 2, 4]
def baseStart_20644 : Nat := 118140960795 + 20644 * 2 ^ 59
def prefixEnd_20644 : Nat := 4983230072969 + 3 ^ 40 * 20644 * 2
def baseEnd_20644 : Nat := 2355621029227214212237

theorem tailTrace_20644 : CollatzResearch.WordTrace tailWord_20644 prefixEnd_20644 2355621029227214212237 := by
  unfold tailWord_20644
  simp only [CollatzResearch.WordTrace]
  refine ⟨376474268608894279806493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 501965691478525706408657 376474268608894279806493)
  ·
    refine ⟨141177850728335354927435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 376474268608894279806493 141177850728335354927435)
    ·
      refine ⟨211766776092503032391153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141177850728335354927435 211766776092503032391153)
      ·
        refine ⟨158825082069377274293365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211766776092503032391153 158825082069377274293365)
        ·
          refine ⟨14889851444004119465003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158825082069377274293365 14889851444004119465003)
          ·
            refine ⟨22334777166006179197505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14889851444004119465003 22334777166006179197505)
            ·
              refine ⟨16751082874504634398129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22334777166006179197505 16751082874504634398129)
              ·
                refine ⟨12563312155878475798597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16751082874504634398129 12563312155878475798597)
                ·
                  refine ⟨2355621029227214212237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12563312155878475798597 2355621029227214212237)
                  ·
                    rfl

theorem cell22_20644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_20644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20644 prefixEnd_20644 := by exact prefixLift 20644
  have htrace : WordTrace (prefixWord ++ tailWord_20644) baseStart_20644 baseEnd_20644 := by
    simpa [prefixWord, tailWord_20644, baseEnd_20644] using wordTrace_append hprefix tailTrace_20644
  have hstable : (prefixWord ++ tailWord_20644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20644).length < 2 ^ (prefixWord ++ tailWord_20644).sum := by decide
  have hdescent : baseEnd_20644 < baseStart_20644 := by decide
  rcases family_descends (prefixWord ++ tailWord_20644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20674 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_20674 : Nat := 118140960795 + 20674 * 2 ^ 59
def prefixEnd_20674 : Nat := 4983230072969 + 3 ^ 40 * 20674 * 2
def baseEnd_20674 : Nat := 7077132700771564386619

theorem tailTrace_20674 : CollatzResearch.WordTrace tailWord_20674 prefixEnd_20674 7077132700771564386619 := by
  unfold tailWord_20674
  simp only [CollatzResearch.WordTrace]
  refine ⟨188510681777275920801269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 502695151406069122136717 188510681777275920801269)
  ·
    refine ⟨17672876416619617575119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188510681777275920801269 17672876416619617575119)
    ·
      refine ⟨26509314624929426362679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17672876416619617575119 26509314624929426362679)
      ·
        refine ⟨39763971937394139544019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26509314624929426362679 39763971937394139544019)
        ·
          refine ⟨59645957906091209316029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39763971937394139544019 59645957906091209316029)
          ·
            refine ⟨22367234214784203493511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59645957906091209316029 22367234214784203493511)
            ·
              refine ⟨33550851322176305240267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22367234214784203493511 33550851322176305240267)
              ·
                refine ⟨50326276983264457860401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33550851322176305240267 50326276983264457860401)
                ·
                  refine ⟨37744707737448343395301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50326276983264457860401 37744707737448343395301)
                  ·
                    refine ⟨7077132700771564386619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37744707737448343395301 7077132700771564386619)
                    ·
                      rfl

theorem cell22_20674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_20674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20674 prefixEnd_20674 := by exact prefixLift 20674
  have htrace : WordTrace (prefixWord ++ tailWord_20674) baseStart_20674 baseEnd_20674 := by
    simpa [prefixWord, tailWord_20674, baseEnd_20674] using wordTrace_append hprefix tailTrace_20674
  have hstable : (prefixWord ++ tailWord_20674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20674).length < 2 ^ (prefixWord ++ tailWord_20674).sum := by decide
  have hdescent : baseEnd_20674 < baseStart_20674 := by decide
  rcases family_descends (prefixWord ++ tailWord_20674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20717 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 5]
def baseStart_20717 : Nat := 118140960795 + 20717 * 2 ^ 59
def prefixEnd_20717 : Nat := 4983230072969 + 3 ^ 40 * 20717 * 2
def baseEnd_20717 : Nat := 2363950826511261853829

theorem tailTrace_20717 : CollatzResearch.WordTrace tailWord_20717 prefixEnd_20717 2363950826511261853829 := by
  unfold tailWord_20717
  simp only [CollatzResearch.WordTrace]
  refine ⟨755611065953322027020405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 503740710635548018013603 755611065953322027020405)
  ·
    refine ⟨70838537433123940033163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 755611065953322027020405 70838537433123940033163)
    ·
      refine ⟨106257806149685910049745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70838537433123940033163 106257806149685910049745)
      ·
        refine ⟨79693354612264432537309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106257806149685910049745 79693354612264432537309)
        ·
          refine ⟨29885007979599162201491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79693354612264432537309 29885007979599162201491)
          ·
            refine ⟨44827511969398743302237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29885007979599162201491 44827511969398743302237)
            ·
              refine ⟨16810316988524528738339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44827511969398743302237 16810316988524528738339)
              ·
                refine ⟨25215475482786793107509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16810316988524528738339 25215475482786793107509)
                ·
                  refine ⟨2363950826511261853829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25215475482786793107509 2363950826511261853829)
                  ·
                    rfl

theorem cell22_20717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_20717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20717 prefixEnd_20717 := by exact prefixLift 20717
  have htrace : WordTrace (prefixWord ++ tailWord_20717) baseStart_20717 baseEnd_20717 := by
    simpa [prefixWord, tailWord_20717, baseEnd_20717] using wordTrace_append hprefix tailTrace_20717
  have hstable : (prefixWord ++ tailWord_20717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20717).length < 2 ^ (prefixWord ++ tailWord_20717).sum := by decide
  have hdescent : baseEnd_20717 < baseStart_20717 := by decide
  rcases family_descends (prefixWord ++ tailWord_20717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20730 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_20730 : Nat := 118140960795 + 20730 * 2 ^ 59
def prefixEnd_20730 : Nat := 4983230072969 + 3 ^ 40 * 20730 * 2
def baseEnd_20730 : Nat := 7096302645206084986447

theorem tailTrace_20730 : CollatzResearch.WordTrace tailWord_20730 prefixEnd_20730 7096302645206084986447 := by
  unfold tailWord_20730
  simp only [CollatzResearch.WordTrace]
  refine ⟨189021303726556311810911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 504056809937483498162429 189021303726556311810911)
  ·
    refine ⟨283531955589834467716367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189021303726556311810911 283531955589834467716367)
    ·
      refine ⟨425297933384751701574551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283531955589834467716367 425297933384751701574551)
      ·
        refine ⟨637946900077127552361827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425297933384751701574551 637946900077127552361827)
        ·
          refine ⟨956920350115691328542741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637946900077127552361827 956920350115691328542741)
          ·
            refine ⟨44855641411673031025441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 956920350115691328542741 44855641411673031025441)
            ·
              refine ⟨33641731058754773269081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44855641411673031025441 33641731058754773269081)
              ·
                refine ⟨25231298294066079951811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33641731058754773269081 25231298294066079951811)
                ·
                  refine ⟨37846947441099119927717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25231298294066079951811 37846947441099119927717)
                  ·
                    refine ⟨7096302645206084986447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37846947441099119927717 7096302645206084986447)
                    ·
                      rfl

theorem cell22_20730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_20730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20730 prefixEnd_20730 := by exact prefixLift 20730
  have htrace : WordTrace (prefixWord ++ tailWord_20730) baseStart_20730 baseEnd_20730 := by
    simpa [prefixWord, tailWord_20730, baseEnd_20730] using wordTrace_append hprefix tailTrace_20730
  have hstable : (prefixWord ++ tailWord_20730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20730).length < 2 ^ (prefixWord ++ tailWord_20730).sum := by decide
  have hdescent : baseEnd_20730 < baseStart_20730 := by decide
  rcases family_descends (prefixWord ++ tailWord_20730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20745 : List Nat := [1, 2, 1, 1, 3, 4, 3, 3, 4]
def baseStart_20745 : Nat := 118140960795 + 20745 * 2 ^ 59
def prefixEnd_20745 : Nat := 4983230072969 + 3 ^ 40 * 20745 * 2
def baseEnd_20745 : Nat := 2367145817250348620467

theorem tailTrace_20745 : CollatzResearch.WordTrace tailWord_20745 prefixEnd_20745 2367145817250348620467 := by
  unfold tailWord_20745
  simp only [CollatzResearch.WordTrace]
  refine ⟨756632309851882809039689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 504421539901255206026459 756632309851882809039689)
  ·
    refine ⟨567474232388912106779767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 756632309851882809039689 567474232388912106779767)
    ·
      refine ⟨851211348583368160169651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567474232388912106779767 851211348583368160169651)
      ·
        refine ⟨1276817022875052240254477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851211348583368160169651 1276817022875052240254477)
        ·
          refine ⟨478806383578144590095429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1276817022875052240254477 478806383578144590095429)
          ·
            refine ⟨89776196920902110642893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 478806383578144590095429 89776196920902110642893)
            ·
              refine ⟨33666073845338291491085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89776196920902110642893 33666073845338291491085)
              ·
                refine ⟨12624777692001859309157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33666073845338291491085 12624777692001859309157)
                ·
                  refine ⟨2367145817250348620467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12624777692001859309157 2367145817250348620467)
                  ·
                    rfl

theorem cell22_20745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_20745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20745 prefixEnd_20745 := by exact prefixLift 20745
  have htrace : WordTrace (prefixWord ++ tailWord_20745) baseStart_20745 baseEnd_20745 := by
    simpa [prefixWord, tailWord_20745, baseEnd_20745] using wordTrace_append hprefix tailTrace_20745
  have hstable : (prefixWord ++ tailWord_20745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20745).length < 2 ^ (prefixWord ++ tailWord_20745).sum := by decide
  have hdescent : baseEnd_20745 < baseStart_20745 := by decide
  rcases family_descends (prefixWord ++ tailWord_20745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20760 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 2, 3]
def baseStart_20760 : Nat := 118140960795 + 20760 * 2 ^ 59
def prefixEnd_20760 : Nat := 4983230072969 + 3 ^ 40 * 20760 * 2
def baseEnd_20760 : Nat := 7106572258296006736355

theorem tailTrace_20760 : CollatzResearch.WordTrace tailWord_20760 prefixEnd_20760 7106572258296006736355 := by
  unfold tailWord_20760
  simp only [CollatzResearch.WordTrace]
  refine ⟨378589702398770185417867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 504786269865026913890489 378589702398770185417867)
  ·
    refine ⟨567884553598155278126801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 378589702398770185417867 567884553598155278126801)
    ·
      refine ⟨425913415198616458595101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 567884553598155278126801 425913415198616458595101)
      ·
        refine ⟨159717530699481171973163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425913415198616458595101 159717530699481171973163)
        ·
          refine ⟨239576296049221757959745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159717530699481171973163 239576296049221757959745)
          ·
            refine ⟨179682222036916318469809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239576296049221757959745 179682222036916318469809)
            ·
              refine ⟨134761666527687238852357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179682222036916318469809 134761666527687238852357)
              ·
                refine ⟨25267812473941357284817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134761666527687238852357 25267812473941357284817)
                ·
                  refine ⟨18950859355456017963613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25267812473941357284817 18950859355456017963613)
                  ·
                    refine ⟨7106572258296006736355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18950859355456017963613 7106572258296006736355)
                    ·
                      rfl

theorem cell22_20760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_20760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20760 prefixEnd_20760 := by exact prefixLift 20760
  have htrace : WordTrace (prefixWord ++ tailWord_20760) baseStart_20760 baseEnd_20760 := by
    simpa [prefixWord, tailWord_20760, baseEnd_20760] using wordTrace_append hprefix tailTrace_20760
  have hstable : (prefixWord ++ tailWord_20760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20760).length < 2 ^ (prefixWord ++ tailWord_20760).sum := by decide
  have hdescent : baseEnd_20760 < baseStart_20760 := by decide
  rcases family_descends (prefixWord ++ tailWord_20760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20762 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_20762 : Nat := 118140960795 + 20762 * 2 ^ 59
def prefixEnd_20762 : Nat := 4983230072969 + 3 ^ 40 * 20762 * 2
def baseEnd_20762 : Nat := 2369085633056222728783

theorem tailTrace_20762 : CollatzResearch.WordTrace tailWord_20762 prefixEnd_20762 2369085633056222728783 := by
  unfold tailWord_20762
  simp only [CollatzResearch.WordTrace]
  refine ⟨189313087697573678102135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 504834900526863141605693 189313087697573678102135)
  ·
    refine ⟨283969631546360517153203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189313087697573678102135 283969631546360517153203)
    ·
      refine ⟨425954447319540775729805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283969631546360517153203 425954447319540775729805)
      ·
        refine ⟨159732917744827790898677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425954447319540775729805 159732917744827790898677)
        ·
          refine ⟨14974961038577605396751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159732917744827790898677 14974961038577605396751)
          ·
            refine ⟨22462441557866408095127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14974961038577605396751 22462441557866408095127)
            ·
              refine ⟨33693662336799612142691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22462441557866408095127 33693662336799612142691)
              ·
                refine ⟨50540493505199418214037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33693662336799612142691 50540493505199418214037)
                ·
                  refine ⟨2369085633056222728783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50540493505199418214037 2369085633056222728783)
                  ·
                    rfl

theorem cell22_20762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_20762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20762 prefixEnd_20762 := by exact prefixLift 20762
  have htrace : WordTrace (prefixWord ++ tailWord_20762) baseStart_20762 baseEnd_20762 := by
    simpa [prefixWord, tailWord_20762, baseEnd_20762] using wordTrace_append hprefix tailTrace_20762
  have hstable : (prefixWord ++ tailWord_20762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20762).length < 2 ^ (prefixWord ++ tailWord_20762).sum := by decide
  have hdescent : baseEnd_20762 < baseStart_20762 := by decide
  rcases family_descends (prefixWord ++ tailWord_20762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20781 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_20781 : Nat := 118140960795 + 20781 * 2 ^ 59
def prefixEnd_20781 : Nat := 4983230072969 + 3 ^ 40 * 20781 * 2
def baseEnd_20781 : Nat := 7113760987458951961291

theorem tailTrace_20781 : CollatzResearch.WordTrace tailWord_20781 prefixEnd_20781 7113760987458951961291 := by
  unfold tailWord_20781
  simp only [CollatzResearch.WordTrace]
  refine ⟨757945337721460957350197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 505296891814307304900131 757945337721460957350197)
  ·
    refine ⟨71057375411386964751581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 757945337721460957350197 71057375411386964751581)
    ·
      refine ⟨26646515779270111781843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71057375411386964751581 26646515779270111781843)
      ·
        refine ⟨39969773668905167672765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26646515779270111781843 39969773668905167672765)
        ·
          refine ⟨14988665125839437877287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39969773668905167672765 14988665125839437877287)
          ·
            refine ⟨22482997688759156815931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14988665125839437877287 22482997688759156815931)
            ·
              refine ⟨33724496533138735223897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22482997688759156815931 33724496533138735223897)
              ·
                refine ⟨25293372399854051417923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33724496533138735223897 25293372399854051417923)
                ·
                  refine ⟨37940058599781077126885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25293372399854051417923 37940058599781077126885)
                  ·
                    refine ⟨7113760987458951961291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37940058599781077126885 7113760987458951961291)
                    ·
                      rfl

theorem cell22_20781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_20781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20781 prefixEnd_20781 := by exact prefixLift 20781
  have htrace : WordTrace (prefixWord ++ tailWord_20781) baseStart_20781 baseEnd_20781 := by
    simpa [prefixWord, tailWord_20781, baseEnd_20781] using wordTrace_append hprefix tailTrace_20781
  have hstable : (prefixWord ++ tailWord_20781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20781).length < 2 ^ (prefixWord ++ tailWord_20781).sum := by decide
  have hdescent : baseEnd_20781 < baseStart_20781 := by decide
  rcases family_descends (prefixWord ++ tailWord_20781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20818 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_20818 : Nat := 118140960795 + 20818 * 2 ^ 59
def prefixEnd_20818 : Nat := 4983230072969 + 3 ^ 40 * 20818 * 2
def baseEnd_20818 : Nat := 2375475614534396262059

theorem tailTrace_20818 : CollatzResearch.WordTrace tailWord_20818 prefixEnd_20818 2375475614534396262059 := by
  unfold tailWord_20818
  simp only [CollatzResearch.WordTrace]
  refine ⟨189823709646854069111777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 506196559058277517631405 189823709646854069111777)
  ·
    refine ⟨142367782235140551833833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189823709646854069111777 142367782235140551833833)
    ·
      refine ⟨106775836676355413875375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142367782235140551833833 106775836676355413875375)
      ·
        refine ⟨160163755014533120813063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106775836676355413875375 160163755014533120813063)
        ·
          refine ⟨240245632521799681219595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160163755014533120813063 240245632521799681219595)
          ·
            refine ⟨360368448782699521829393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240245632521799681219595 360368448782699521829393)
            ·
              refine ⟨270276336587024641372045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360368448782699521829393 270276336587024641372045)
              ·
                refine ⟨101353626220134240514517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270276336587024641372045 101353626220134240514517)
                ·
                  refine ⟨2375475614534396262059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101353626220134240514517 2375475614534396262059)
                  ·
                    rfl

theorem cell22_20818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_20818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20818 prefixEnd_20818 := by exact prefixLift 20818
  have htrace : WordTrace (prefixWord ++ tailWord_20818) baseStart_20818 baseEnd_20818 := by
    simpa [prefixWord, tailWord_20818, baseEnd_20818] using wordTrace_append hprefix tailTrace_20818
  have hstable : (prefixWord ++ tailWord_20818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20818).length < 2 ^ (prefixWord ++ tailWord_20818).sum := by decide
  have hdescent : baseEnd_20818 < baseStart_20818 := by decide
  rcases family_descends (prefixWord ++ tailWord_20818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20925 : List Nat := [1, 4, 1, 2, 2, 4, 8]
def baseStart_20925 : Nat := 118140960795 + 20925 * 2 ^ 59
def prefixEnd_20925 : Nat := 4983230072969 + 3 ^ 40 * 20925 * 2
def baseEnd_20925 : Nat := 265298338158910235587

theorem tailTrace_20925 : CollatzResearch.WordTrace tailWord_20925 prefixEnd_20925 265298338158910235587 := by
  unfold tailWord_20925
  simp only [CollatzResearch.WordTrace]
  refine ⟨763197449199773550592229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 508798299466515700394819 763197449199773550592229)
  ·
    refine ⟨143099521724957540736043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 763197449199773550592229 143099521724957540736043)
    ·
      refine ⟨214649282587436311104065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143099521724957540736043 214649282587436311104065)
      ·
        refine ⟨160986961940577233328049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214649282587436311104065 160986961940577233328049)
        ·
          refine ⟨120740221455432924996037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160986961940577233328049 120740221455432924996037)
          ·
            refine ⟨22638791522893673436757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120740221455432924996037 22638791522893673436757)
            ·
              refine ⟨265298338158910235587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 22638791522893673436757 265298338158910235587)
              ·
                rfl

theorem cell22_20925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 8].length) (baseStart_20925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20925 prefixEnd_20925 := by exact prefixLift 20925
  have htrace : WordTrace (prefixWord ++ tailWord_20925) baseStart_20925 baseEnd_20925 := by
    simpa [prefixWord, tailWord_20925, baseEnd_20925] using wordTrace_append hprefix tailTrace_20925
  have hstable : (prefixWord ++ tailWord_20925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20925).length < 2 ^ (prefixWord ++ tailWord_20925).sum := by decide
  have hdescent : baseEnd_20925 < baseStart_20925 := by decide
  rcases family_descends (prefixWord ++ tailWord_20925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20946 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_20946 : Nat := 118140960795 + 20946 * 2 ^ 59
def prefixEnd_20946 : Nat := 4983230072969 + 3 ^ 40 * 20946 * 2
def baseEnd_20946 : Nat := 7170243859453521585785

theorem tailTrace_20946 : CollatzResearch.WordTrace tailWord_20946 prefixEnd_20946 7170243859453521585785 := by
  unfold tailWord_20946
  simp only [CollatzResearch.WordTrace]
  refine ⟨190990845530923534276673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 509308921415796091404461 190990845530923534276673)
  ·
    refine ⟨143243134148192650707505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190990845530923534276673 143243134148192650707505)
    ·
      refine ⟨107432350611144488030629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143243134148192650707505 107432350611144488030629)
      ·
        refine ⟨20143565739589591505743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107432350611144488030629 20143565739589591505743)
        ·
          refine ⟨30215348609384387258615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20143565739589591505743 30215348609384387258615)
          ·
            refine ⟨45323022914076580887923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30215348609384387258615 45323022914076580887923)
            ·
              refine ⟨67984534371114871331885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45323022914076580887923 67984534371114871331885)
              ·
                refine ⟨25494200389168076749457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67984534371114871331885 25494200389168076749457)
                ·
                  refine ⟨19120650291876057562093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25494200389168076749457 19120650291876057562093)
                  ·
                    refine ⟨7170243859453521585785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19120650291876057562093 7170243859453521585785)
                    ·
                      rfl

theorem cell22_20946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_20946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20946 prefixEnd_20946 := by exact prefixLift 20946
  have htrace : WordTrace (prefixWord ++ tailWord_20946) baseStart_20946 baseEnd_20946 := by
    simpa [prefixWord, tailWord_20946, baseEnd_20946] using wordTrace_append hprefix tailTrace_20946
  have hstable : (prefixWord ++ tailWord_20946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20946).length < 2 ^ (prefixWord ++ tailWord_20946).sum := by decide
  have hdescent : baseEnd_20946 < baseStart_20946 := by decide
  rcases family_descends (prefixWord ++ tailWord_20946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20957 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_20957 : Nat := 118140960795 + 20957 * 2 ^ 59
def prefixEnd_20957 : Nat := 4983230072969 + 3 ^ 40 * 20957 * 2
def baseEnd_20957 : Nat := 7174009384253159560751

theorem tailTrace_20957 : CollatzResearch.WordTrace tailWord_20957 prefixEnd_20957 7174009384253159560751 := by
  unfold tailWord_20957
  simp only [CollatzResearch.WordTrace]
  refine ⟨764364585083843015757125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 509576390055895343838083 764364585083843015757125)
  ·
    refine ⟨143318359703220565454461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 764364585083843015757125 143318359703220565454461)
    ·
      refine ⟨53744384888707712045423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143318359703220565454461 53744384888707712045423)
      ·
        refine ⟨80616577333061568068135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53744384888707712045423 80616577333061568068135)
        ·
          refine ⟨120924865999592352102203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80616577333061568068135 120924865999592352102203)
          ·
            refine ⟨181387298999388528153305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120924865999592352102203 181387298999388528153305)
            ·
              refine ⟨136040474249541396114979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181387298999388528153305 136040474249541396114979)
              ·
                refine ⟨204060711374312094172469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136040474249541396114979 204060711374312094172469)
                ·
                  refine ⟨19130691691341758828669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204060711374312094172469 19130691691341758828669)
                  ·
                    refine ⟨7174009384253159560751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19130691691341758828669 7174009384253159560751)
                    ·
                      rfl

theorem cell22_20957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_20957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_20957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_20957 prefixEnd_20957 := by exact prefixLift 20957
  have htrace : WordTrace (prefixWord ++ tailWord_20957) baseStart_20957 baseEnd_20957 := by
    simpa [prefixWord, tailWord_20957, baseEnd_20957] using wordTrace_append hprefix tailTrace_20957
  have hstable : (prefixWord ++ tailWord_20957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20957).length < 2 ^ (prefixWord ++ tailWord_20957).sum := by decide
  have hdescent : baseEnd_20957 < baseStart_20957 := by decide
  rcases family_descends (prefixWord ++ tailWord_20957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21034 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_21034 : Nat := 118140960795 + 21034 * 2 ^ 59
def prefixEnd_21034 : Nat := 4983230072969 + 3 ^ 40 * 21034 * 2
def baseEnd_21034 : Nat := 7200368057850625385515

theorem tailTrace_21034 : CollatzResearch.WordTrace tailWord_21034 prefixEnd_21034 7200368057850625385515 := by
  unfold tailWord_21034
  simp only [CollatzResearch.WordTrace]
  refine ⟨191793251451221291577539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 511448670536590110873437 191793251451221291577539)
  ·
    refine ⟨287689877176831937366309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191793251451221291577539 287689877176831937366309)
    ·
      refine ⟨53941851970655988256183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287689877176831937366309 53941851970655988256183)
      ·
        refine ⟨80912777955983982384275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53941851970655988256183 80912777955983982384275)
        ·
          refine ⟨121369166933975973576413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80912777955983982384275 121369166933975973576413)
          ·
            refine ⟨45513437600240990091155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121369166933975973576413 45513437600240990091155)
            ·
              refine ⟨68270156400361485136733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45513437600240990091155 68270156400361485136733)
              ·
                refine ⟨25601308650135556926275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68270156400361485136733 25601308650135556926275)
                ·
                  refine ⟨38401962975203335389413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25601308650135556926275 38401962975203335389413)
                  ·
                    refine ⟨7200368057850625385515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38401962975203335389413 7200368057850625385515)
                    ·
                      rfl

theorem cell22_21034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_21034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21034 prefixEnd_21034 := by exact prefixLift 21034
  have htrace : WordTrace (prefixWord ++ tailWord_21034) baseStart_21034 baseEnd_21034 := by
    simpa [prefixWord, tailWord_21034, baseEnd_21034] using wordTrace_append hprefix tailTrace_21034
  have hstable : (prefixWord ++ tailWord_21034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21034).length < 2 ^ (prefixWord ++ tailWord_21034).sum := by decide
  have hdescent : baseEnd_21034 < baseStart_21034 := by decide
  rcases family_descends (prefixWord ++ tailWord_21034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21047 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 4, 3]
def baseStart_21047 : Nat := 118140960795 + 21047 * 2 ^ 59
def prefixEnd_21047 : Nat := 4983230072969 + 3 ^ 40 * 21047 * 2
def baseEnd_21047 : Nat := 7204818223522924810475

theorem tailTrace_21047 : CollatzResearch.WordTrace tailWord_21047 prefixEnd_21047 7204818223522924810475 := by
  unfold tailWord_21047
  simp only [CollatzResearch.WordTrace]
  refine ⟨767647154757788386533395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 511764769838525591022263 767647154757788386533395)
  ·
    refine ⟨1151470732136682579800093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767647154757788386533395 1151470732136682579800093)
    ·
      refine ⟨431801524551255967425035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1151470732136682579800093 431801524551255967425035)
      ·
        refine ⟨647702286826883951137553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431801524551255967425035 647702286826883951137553)
        ·
          refine ⟨485776715120162963353165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 647702286826883951137553 485776715120162963353165)
          ·
            refine ⟨182166268170061111257437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 485776715120162963353165 182166268170061111257437)
            ·
              refine ⟨68312350563772916721539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182166268170061111257437 68312350563772916721539)
              ·
                refine ⟨102468525845659375082309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68312350563772916721539 102468525845659375082309)
                ·
                  refine ⟨19212848596061132827933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102468525845659375082309 19212848596061132827933)
                  ·
                    refine ⟨7204818223522924810475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19212848596061132827933 7204818223522924810475)
                    ·
                      rfl

theorem cell22_21047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_21047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21047 prefixEnd_21047 := by exact prefixLift 21047
  have htrace : WordTrace (prefixWord ++ tailWord_21047) baseStart_21047 baseEnd_21047 := by
    simpa [prefixWord, tailWord_21047, baseEnd_21047] using wordTrace_append hprefix tailTrace_21047
  have hstable : (prefixWord ++ tailWord_21047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21047).length < 2 ^ (prefixWord ++ tailWord_21047).sum := by decide
  have hdescent : baseEnd_21047 < baseStart_21047 := by decide
  rcases family_descends (prefixWord ++ tailWord_21047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21077 : List Nat := [1, 3, 2, 2, 1, 1, 6, 6]
def baseStart_21077 : Nat := 118140960795 + 21077 * 2 ^ 59
def prefixEnd_21077 : Nat := 4983230072969 + 3 ^ 40 * 21077 * 2
def baseEnd_21077 : Nat := 801676426290316284487

theorem tailTrace_21077 : CollatzResearch.WordTrace tailWord_21077 prefixEnd_21077 801676426290316284487 := by
  unfold tailWord_21077
  simp only [CollatzResearch.WordTrace]
  refine ⟨768741344649103510125485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 512494229766069006750323 768741344649103510125485)
  ·
    refine ⟨288278004243413816297057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 768741344649103510125485 288278004243413816297057)
    ·
      refine ⟨216208503182560362222793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288278004243413816297057 216208503182560362222793)
      ·
        refine ⟨162156377386920271667095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216208503182560362222793 162156377386920271667095)
        ·
          refine ⟨243234566080380407500643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162156377386920271667095 243234566080380407500643)
          ·
            refine ⟨364851849120570611250965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243234566080380407500643 364851849120570611250965)
            ·
              refine ⟨17102430427526747402389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 364851849120570611250965 17102430427526747402389)
              ·
                refine ⟨801676426290316284487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17102430427526747402389 801676426290316284487)
                ·
                  rfl

theorem cell22_21077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 6].length) (baseStart_21077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21077 prefixEnd_21077 := by exact prefixLift 21077
  have htrace : WordTrace (prefixWord ++ tailWord_21077) baseStart_21077 baseEnd_21077 := by
    simpa [prefixWord, tailWord_21077, baseEnd_21077] using wordTrace_append hprefix tailTrace_21077
  have hstable : (prefixWord ++ tailWord_21077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21077).length < 2 ^ (prefixWord ++ tailWord_21077).sum := by decide
  have hdescent : baseEnd_21077 < baseStart_21077 := by decide
  rcases family_descends (prefixWord ++ tailWord_21077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21135 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 8]
def baseStart_21135 : Nat := 118140960795 + 21135 * 2 ^ 59
def prefixEnd_21135 : Nat := 4983230072969 + 3 ^ 40 * 21135 * 2
def baseEnd_21135 : Nat := 7234942421920028610205

theorem tailTrace_21135 : CollatzResearch.WordTrace tailWord_21135 prefixEnd_21135 7234942421920028610205 := by
  unfold tailWord_21135
  simp only [CollatzResearch.WordTrace]
  refine ⟨770856778438979415736859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 513904518959319610491239 770856778438979415736859)
  ·
    refine ⟨1156285167658469123605289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770856778438979415736859 1156285167658469123605289)
    ·
      refine ⟨867213875743851842703967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1156285167658469123605289 867213875743851842703967)
      ·
        refine ⟨1300820813615777764055951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867213875743851842703967 1300820813615777764055951)
        ·
          refine ⟨1951231220423666646083927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300820813615777764055951 1951231220423666646083927)
          ·
            refine ⟨2926846830635499969125891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951231220423666646083927 2926846830635499969125891)
            ·
              refine ⟨4390270245953249953688837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926846830635499969125891 4390270245953249953688837)
              ·
                refine ⟨823175671116234366316657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4390270245953249953688837 823175671116234366316657)
                ·
                  refine ⟨617381753337175774737493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823175671116234366316657 617381753337175774737493)
                  ·
                    refine ⟨7234942421920028610205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 617381753337175774737493 7234942421920028610205)
                    ·
                      rfl

theorem cell22_21135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_21135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21135 prefixEnd_21135 := by exact prefixLift 21135
  have htrace : WordTrace (prefixWord ++ tailWord_21135) baseStart_21135 baseEnd_21135 := by
    simpa [prefixWord, tailWord_21135, baseEnd_21135] using wordTrace_append hprefix tailTrace_21135
  have hstable : (prefixWord ++ tailWord_21135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21135).length < 2 ^ (prefixWord ++ tailWord_21135).sum := by decide
  have hdescent : baseEnd_21135 < baseStart_21135 := by decide
  rcases family_descends (prefixWord ++ tailWord_21135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21242 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_21242 : Nat := 118140960795 + 21242 * 2 ^ 59
def prefixEnd_21242 : Nat := 4983230072969 + 3 ^ 40 * 21242 * 2
def baseEnd_21242 : Nat := 7271570708607416184877

theorem tailTrace_21242 : CollatzResearch.WordTrace tailWord_21242 prefixEnd_21242 7271570708607416184877 := by
  unfold tailWord_21242
  simp only [CollatzResearch.WordTrace]
  refine ⟨193689847262834172470495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 516506259367557793254653 193689847262834172470495)
  ·
    refine ⟨290534770894251258705743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193689847262834172470495 290534770894251258705743)
    ·
      refine ⟨435802156341376888058615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290534770894251258705743 435802156341376888058615)
      ·
        refine ⟨653703234512065332087923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435802156341376888058615 653703234512065332087923)
        ·
          refine ⟨980554851768097998131885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653703234512065332087923 980554851768097998131885)
          ·
            refine ⟨367708069413036749299457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980554851768097998131885 367708069413036749299457)
            ·
              refine ⟨275781052059777561974593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367708069413036749299457 275781052059777561974593)
              ·
                refine ⟨206835789044833171480945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275781052059777561974593 206835789044833171480945)
                ·
                  refine ⟨155126841783624878610709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206835789044833171480945 155126841783624878610709)
                  ·
                    refine ⟨7271570708607416184877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 155126841783624878610709 7271570708607416184877)
                    ·
                      rfl

theorem cell22_21242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_21242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21242 prefixEnd_21242 := by exact prefixLift 21242
  have htrace : WordTrace (prefixWord ++ tailWord_21242) baseStart_21242 baseEnd_21242 := by
    simpa [prefixWord, tailWord_21242, baseEnd_21242] using wordTrace_append hprefix tailTrace_21242
  have hstable : (prefixWord ++ tailWord_21242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21242).length < 2 ^ (prefixWord ++ tailWord_21242).sum := by decide
  have hdescent : baseEnd_21242 < baseStart_21242 := by decide
  rcases family_descends (prefixWord ++ tailWord_21242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21246 : List Nat := [4, 2, 2, 1, 2, 1, 4, 6]
def baseStart_21246 : Nat := 118140960795 + 21246 * 2 ^ 59
def prefixEnd_21246 : Nat := 4983230072969 + 3 ^ 40 * 21246 * 2
def baseEnd_21246 : Nat := 808104443372526564985

theorem tailTrace_21246 : CollatzResearch.WordTrace tailWord_21246 prefixEnd_21246 808104443372526564985 := by
  unfold tailWord_21246
  simp only [CollatzResearch.WordTrace]
  refine ⟨96863160129605671628449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 516603520691230248685061 96863160129605671628449)
  ·
    refine ⟨72647370097204253721337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96863160129605671628449 72647370097204253721337)
    ·
      refine ⟨54485527572903190291003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72647370097204253721337 54485527572903190291003)
      ·
        refine ⟨81728291359354785436505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54485527572903190291003 81728291359354785436505)
        ·
          refine ⟨61296218519516089077379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81728291359354785436505 61296218519516089077379)
          ·
            refine ⟨91944327779274133616069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61296218519516089077379 91944327779274133616069)
            ·
              refine ⟨17239561458613900053013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91944327779274133616069 17239561458613900053013)
              ·
                refine ⟨808104443372526564985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17239561458613900053013 808104443372526564985)
                ·
                  rfl

theorem cell22_21246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_21246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21246 prefixEnd_21246 := by exact prefixLift 21246
  have htrace : WordTrace (prefixWord ++ tailWord_21246) baseStart_21246 baseEnd_21246 := by
    simpa [prefixWord, tailWord_21246, baseEnd_21246] using wordTrace_append hprefix tailTrace_21246
  have hstable : (prefixWord ++ tailWord_21246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21246).length < 2 ^ (prefixWord ++ tailWord_21246).sum := by decide
  have hdescent : baseEnd_21246 < baseStart_21246 := by decide
  rcases family_descends (prefixWord ++ tailWord_21246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21257 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 7]
def baseStart_21257 : Nat := 118140960795 + 21257 * 2 ^ 59
def prefixEnd_21257 : Nat := 4983230072969 + 3 ^ 40 * 21257 * 2
def baseEnd_21257 : Nat := 2425568505050792353277

theorem tailTrace_21257 : CollatzResearch.WordTrace tailWord_21257 prefixEnd_21257 2425568505050792353277 := by
  unfold tailWord_21257
  simp only [CollatzResearch.WordTrace]
  refine ⟨775306483996994251678025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 516870989331329501118683 775306483996994251678025)
  ·
    refine ⟨581479862997745688758519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 775306483996994251678025 581479862997745688758519)
    ·
      refine ⟨872219794496618533137779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581479862997745688758519 872219794496618533137779)
      ·
        refine ⟨1308329691744927799706669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872219794496618533137779 1308329691744927799706669)
        ·
          refine ⟨490623634404347924890001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1308329691744927799706669 490623634404347924890001)
          ·
            refine ⟨367967725803260943667501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490623634404347924890001 367967725803260943667501)
            ·
              refine ⟨137987897176222853875313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367967725803260943667501 137987897176222853875313)
              ·
                refine ⟨103490922882167140406485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137987897176222853875313 103490922882167140406485)
                ·
                  refine ⟨2425568505050792353277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 103490922882167140406485 2425568505050792353277)
                  ·
                    rfl

theorem cell22_21257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_21257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21257 prefixEnd_21257 := by exact prefixLift 21257
  have htrace : WordTrace (prefixWord ++ tailWord_21257) baseStart_21257 baseEnd_21257 := by
    simpa [prefixWord, tailWord_21257, baseEnd_21257] using wordTrace_append hprefix tailTrace_21257
  have hstable : (prefixWord ++ tailWord_21257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21257).length < 2 ^ (prefixWord ++ tailWord_21257).sum := by decide
  have hdescent : baseEnd_21257 < baseStart_21257 := by decide
  rcases family_descends (prefixWord ++ tailWord_21257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21274 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_21274 : Nat := 118140960795 + 21274 * 2 ^ 59
def prefixEnd_21274 : Nat := 4983230072969 + 3 ^ 40 * 21274 * 2
def baseEnd_21274 : Nat := 2427508320856666461593

theorem tailTrace_21274 : CollatzResearch.WordTrace tailWord_21274 prefixEnd_21274 2427508320856666461593 := by
  unfold tailWord_21274
  simp only [CollatzResearch.WordTrace]
  refine ⟨193981631233851538761719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 517284349956937436697917 193981631233851538761719)
  ·
    refine ⟨290972446850777308142579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193981631233851538761719 290972446850777308142579)
    ·
      refine ⟨436458670276165962213869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290972446850777308142579 436458670276165962213869)
      ·
        refine ⟨163672001353562235830201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436458670276165962213869 163672001353562235830201)
        ·
          refine ⟨122754001015171676872651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163672001353562235830201 122754001015171676872651)
          ·
            refine ⟨184131001522757515308977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122754001015171676872651 184131001522757515308977)
            ·
              refine ⟨138098251142068136481733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184131001522757515308977 138098251142068136481733)
              ·
                refine ⟨25893422089137775590325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138098251142068136481733 25893422089137775590325)
                ·
                  refine ⟨2427508320856666461593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25893422089137775590325 2427508320856666461593)
                  ·
                    rfl

theorem cell22_21274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_21274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21274 prefixEnd_21274 := by exact prefixLift 21274
  have htrace : WordTrace (prefixWord ++ tailWord_21274) baseStart_21274 baseEnd_21274 := by
    simpa [prefixWord, tailWord_21274, baseEnd_21274] using wordTrace_append hprefix tailTrace_21274
  have hstable : (prefixWord ++ tailWord_21274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21274).length < 2 ^ (prefixWord ++ tailWord_21274).sum := by decide
  have hdescent : baseEnd_21274 < baseStart_21274 := by decide
  rcases family_descends (prefixWord ++ tailWord_21274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21304 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_21304 : Nat := 118140960795 + 21304 * 2 ^ 59
def prefixEnd_21304 : Nat := 4983230072969 + 3 ^ 40 * 21304 * 2
def baseEnd_21304 : Nat := 7292794575659921134687

theorem tailTrace_21304 : CollatzResearch.WordTrace tailWord_21304 prefixEnd_21304 7292794575659921134687 := by
  unfold tailWord_21304
  simp only [CollatzResearch.WordTrace]
  refine ⟨388510357413360639319483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 518013809884480852425977 388510357413360639319483)
  ·
    refine ⟨582765536120040958979225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388510357413360639319483 582765536120040958979225)
    ·
      refine ⟨437074152090030719234419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 582765536120040958979225 437074152090030719234419)
      ·
        refine ⟨655611228135046078851629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437074152090030719234419 655611228135046078851629)
        ·
          refine ⟨245854210550642279569361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 655611228135046078851629 245854210550642279569361)
          ·
            refine ⟨184390657912981709677021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245854210550642279569361 184390657912981709677021)
            ·
              refine ⟨69146496717368141128883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184390657912981709677021 69146496717368141128883)
              ·
                refine ⟨103719745076052211693325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69146496717368141128883 103719745076052211693325)
                ·
                  refine ⟨38894904403519579384997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103719745076052211693325 38894904403519579384997)
                  ·
                    refine ⟨7292794575659921134687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38894904403519579384997 7292794575659921134687)
                    ·
                      rfl

theorem cell22_21304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_21304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21304 prefixEnd_21304 := by exact prefixLift 21304
  have htrace : WordTrace (prefixWord ++ tailWord_21304) baseStart_21304 baseEnd_21304 := by
    simpa [prefixWord, tailWord_21304, baseEnd_21304] using wordTrace_append hprefix tailTrace_21304
  have hstable : (prefixWord ++ tailWord_21304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21304).length < 2 ^ (prefixWord ++ tailWord_21304).sum := by decide
  have hdescent : baseEnd_21304 < baseStart_21304 := by decide
  rcases family_descends (prefixWord ++ tailWord_21304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21349 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_21349 : Nat := 118140960795 + 21349 * 2 ^ 59
def prefixEnd_21349 : Nat := 4983230072969 + 3 ^ 40 * 21349 * 2
def baseEnd_21349 : Nat := 7308198995294803759549

theorem tailTrace_21349 : CollatzResearch.WordTrace tailWord_21349 prefixEnd_21349 7308198995294803759549 := by
  unfold tailWord_21349
  simp only [CollatzResearch.WordTrace]
  refine ⟨778661999663693964027101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 519107999775795976018067 778661999663693964027101)
  ·
    refine ⟨291998249873885236510163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 778661999663693964027101 291998249873885236510163)
    ·
      refine ⟨437997374810827854765245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291998249873885236510163 437997374810827854765245)
      ·
        refine ⟨164249015554060445536967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 437997374810827854765245 164249015554060445536967)
        ·
          refine ⟨246373523331090668305451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164249015554060445536967 246373523331090668305451)
          ·
            refine ⟨369560284996636002458177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246373523331090668305451 369560284996636002458177)
            ·
              refine ⟨277170213747477001843633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369560284996636002458177 277170213747477001843633)
              ·
                refine ⟨207877660310607751382725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277170213747477001843633 207877660310607751382725)
                ·
                  refine ⟨38977061308238953384261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207877660310607751382725 38977061308238953384261)
                  ·
                    refine ⟨7308198995294803759549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38977061308238953384261 7308198995294803759549)
                    ·
                      rfl

theorem cell22_21349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_21349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21349 prefixEnd_21349 := by exact prefixLift 21349
  have htrace : WordTrace (prefixWord ++ tailWord_21349) baseStart_21349 baseEnd_21349 := by
    simpa [prefixWord, tailWord_21349, baseEnd_21349] using wordTrace_append hprefix tailTrace_21349
  have hstable : (prefixWord ++ tailWord_21349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21349).length < 2 ^ (prefixWord ++ tailWord_21349).sum := by decide
  have hdescent : baseEnd_21349 < baseStart_21349 := by decide
  rcases family_descends (prefixWord ++ tailWord_21349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21351 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 1, 5]
def baseStart_21351 : Nat := 118140960795 + 21351 * 2 ^ 59
def prefixEnd_21351 : Nat := 4983230072969 + 3 ^ 40 * 21351 * 2
def baseEnd_21351 : Nat := 7308883636167465209543

theorem tailTrace_21351 : CollatzResearch.WordTrace tailWord_21351 prefixEnd_21351 7308883636167465209543 := by
  unfold tailWord_21351
  simp only [CollatzResearch.WordTrace]
  refine ⟨778734945656448305599907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 519156630437632203733271 778734945656448305599907)
  ·
    refine ⟨1168102418484672458399861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 778734945656448305599907 1168102418484672458399861)
    ·
      refine ⟨109509601732938042974987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1168102418484672458399861 109509601732938042974987)
      ·
        refine ⟨164264402599407064462481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109509601732938042974987 164264402599407064462481)
        ·
          refine ⟨123198301949555298346861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164264402599407064462481 123198301949555298346861)
          ·
            refine ⟨46199363231083236880073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123198301949555298346861 46199363231083236880073)
            ·
              refine ⟨34649522423312427660055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46199363231083236880073 34649522423312427660055)
              ·
                refine ⟨51974283634968641490083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34649522423312427660055 51974283634968641490083)
                ·
                  refine ⟨77961425452452962235125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51974283634968641490083 77961425452452962235125)
                  ·
                    refine ⟨7308883636167465209543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77961425452452962235125 7308883636167465209543)
                    ·
                      rfl

theorem cell22_21351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_21351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21351 prefixEnd_21351 := by exact prefixLift 21351
  have htrace : WordTrace (prefixWord ++ tailWord_21351) baseStart_21351 baseEnd_21351 := by
    simpa [prefixWord, tailWord_21351, baseEnd_21351] using wordTrace_append hprefix tailTrace_21351
  have hstable : (prefixWord ++ tailWord_21351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21351).length < 2 ^ (prefixWord ++ tailWord_21351).sum := by decide
  have hdescent : baseEnd_21351 < baseStart_21351 := by decide
  rcases family_descends (prefixWord ++ tailWord_21351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21415 : List Nat := [1, 1, 6, 1, 4, 1, 2, 6]
def baseStart_21415 : Nat := 118140960795 + 21415 * 2 ^ 59
def prefixEnd_21415 : Nat := 4983230072969 + 3 ^ 40 * 21415 * 2
def baseEnd_21415 : Nat := 814532460454736845483

theorem tailTrace_21415 : CollatzResearch.WordTrace tailWord_21415 prefixEnd_21415 814532460454736845483 := by
  unfold tailWord_21415
  simp only [CollatzResearch.WordTrace]
  refine ⟨781069217424587235929699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 520712811616391490619799 781069217424587235929699)
  ·
    refine ⟨1171603826136880853894549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 781069217424587235929699 1171603826136880853894549)
    ·
      refine ⟨54918929350166290026307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1171603826136880853894549 54918929350166290026307)
      ·
        refine ⟨82378394025249435039461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54918929350166290026307 82378394025249435039461)
        ·
          refine ⟨15445948879734269069899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82378394025249435039461 15445948879734269069899)
          ·
            refine ⟨23168923319601403604849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15445948879734269069899 23168923319601403604849)
            ·
              refine ⟨17376692489701052703637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23168923319601403604849 17376692489701052703637)
              ·
                refine ⟨814532460454736845483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17376692489701052703637 814532460454736845483)
                ·
                  rfl

theorem cell22_21415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 6].length) (baseStart_21415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21415 prefixEnd_21415 := by exact prefixLift 21415
  have htrace : WordTrace (prefixWord ++ tailWord_21415) baseStart_21415 baseEnd_21415 := by
    simpa [prefixWord, tailWord_21415, baseEnd_21415] using wordTrace_append hprefix tailTrace_21415
  have hstable : (prefixWord ++ tailWord_21415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21415).length < 2 ^ (prefixWord ++ tailWord_21415).sum := by decide
  have hdescent : baseEnd_21415 < baseStart_21415 := by decide
  rcases family_descends (prefixWord ++ tailWord_21415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21453 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_21453 : Nat := 118140960795 + 21453 * 2 ^ 59
def prefixEnd_21453 : Nat := 4983230072969 + 3 ^ 40 * 21453 * 2
def baseEnd_21453 : Nat := 7343800320673199159231

theorem tailTrace_21453 : CollatzResearch.WordTrace tailWord_21453 prefixEnd_21453 7343800320673199159231 := by
  unfold tailWord_21453
  simp only [CollatzResearch.WordTrace]
  refine ⟨782455191286919725813013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 521636794191279817208675 782455191286919725813013)
  ·
    refine ⟨36677587091574362147485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 782455191286919725813013 36677587091574362147485)
    ·
      refine ⟨13754095159340385805307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36677587091574362147485 13754095159340385805307)
      ·
        refine ⟨20631142739010578707961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13754095159340385805307 20631142739010578707961)
        ·
          refine ⟨15473357054257934030971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20631142739010578707961 15473357054257934030971)
          ·
            refine ⟨23210035581386901046457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15473357054257934030971 23210035581386901046457)
            ·
              refine ⟨17407526686040175784843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23210035581386901046457 17407526686040175784843)
              ·
                refine ⟨26111290029060263677265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17407526686040175784843 26111290029060263677265)
                ·
                  refine ⟨19583467521795197757949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26111290029060263677265 19583467521795197757949)
                  ·
                    refine ⟨7343800320673199159231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19583467521795197757949 7343800320673199159231)
                    ·
                      rfl

theorem cell22_21453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_21453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21453 prefixEnd_21453 := by exact prefixLift 21453
  have htrace : WordTrace (prefixWord ++ tailWord_21453) baseStart_21453 baseEnd_21453 := by
    simpa [prefixWord, tailWord_21453, baseEnd_21453] using wordTrace_append hprefix tailTrace_21453
  have hstable : (prefixWord ++ tailWord_21453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21453).length < 2 ^ (prefixWord ++ tailWord_21453).sum := by decide
  have hdescent : baseEnd_21453 < baseStart_21453 := by decide
  rcases family_descends (prefixWord ++ tailWord_21453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21460 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 5]
def baseStart_21460 : Nat := 118140960795 + 21460 * 2 ^ 59
def prefixEnd_21460 : Nat := 4983230072969 + 3 ^ 40 * 21460 * 2
def baseEnd_21460 : Nat := 2448732187909171411403

theorem tailTrace_21460 : CollatzResearch.WordTrace tailWord_21460 prefixEnd_21460 2448732187909171411403 := by
  unfold tailWord_21460
  simp only [CollatzResearch.WordTrace]
  refine ⟨391355251130779960658917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 521807001507706614211889 391355251130779960658917)
  ·
    refine ⟨73379109587021242623547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 391355251130779960658917 73379109587021242623547)
    ·
      refine ⟨110068664380531863935321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73379109587021242623547 110068664380531863935321)
      ·
        refine ⟨82551498285398897951491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110068664380531863935321 82551498285398897951491)
        ·
          refine ⟨123827247428098346927237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82551498285398897951491 123827247428098346927237)
          ·
            refine ⟨23217608892768440048857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123827247428098346927237 23217608892768440048857)
            ·
              refine ⟨17413206669576330036643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23217608892768440048857 17413206669576330036643)
              ·
                refine ⟨26119810004364495054965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17413206669576330036643 26119810004364495054965)
                ·
                  refine ⟨2448732187909171411403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26119810004364495054965 2448732187909171411403)
                  ·
                    rfl

theorem cell22_21460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_21460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21460 prefixEnd_21460 := by exact prefixLift 21460
  have htrace : WordTrace (prefixWord ++ tailWord_21460) baseStart_21460 baseEnd_21460 := by
    simpa [prefixWord, tailWord_21460, baseEnd_21460] using wordTrace_append hprefix tailTrace_21460
  have hstable : (prefixWord ++ tailWord_21460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21460).length < 2 ^ (prefixWord ++ tailWord_21460).sum := by decide
  have hdescent : baseEnd_21460 < baseStart_21460 := by decide
  rcases family_descends (prefixWord ++ tailWord_21460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21505 : List Nat := [1, 2, 4, 1, 2, 2, 4, 2, 4]
def baseStart_21505 : Nat := 118140960795 + 21505 * 2 ^ 59
def prefixEnd_21505 : Nat := 4983230072969 + 3 ^ 40 * 21505 * 2
def baseEnd_21505 : Nat := 2453866994454132286357

theorem tailTrace_21505 : CollatzResearch.WordTrace tailWord_21505 prefixEnd_21505 2453866994454132286357 := by
  unfold tailWord_21505
  simp only [CollatzResearch.WordTrace]
  refine ⟨784351787098532606705969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 522901191399021737803979 784351787098532606705969)
  ·
    refine ⟨588263840323899455029477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 784351787098532606705969 588263840323899455029477)
    ·
      refine ⟨110299470060731147818027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 588263840323899455029477 110299470060731147818027)
      ·
        refine ⟨165449205091096721727041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110299470060731147818027 165449205091096721727041)
        ·
          refine ⟨124086903818322541295281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165449205091096721727041 124086903818322541295281)
          ·
            refine ⟨93065177863741905971461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124086903818322541295281 93065177863741905971461)
            ·
              refine ⟨17449720849451607369649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93065177863741905971461 17449720849451607369649)
              ·
                refine ⟨13087290637088705527237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17449720849451607369649 13087290637088705527237)
                ·
                  refine ⟨2453866994454132286357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13087290637088705527237 2453866994454132286357)
                  ·
                    rfl

theorem cell22_21505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_21505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21505 prefixEnd_21505 := by exact prefixLift 21505
  have htrace : WordTrace (prefixWord ++ tailWord_21505) baseStart_21505 baseEnd_21505 := by
    simpa [prefixWord, tailWord_21505, baseEnd_21505] using wordTrace_append hprefix tailTrace_21505
  have hstable : (prefixWord ++ tailWord_21505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21505).length < 2 ^ (prefixWord ++ tailWord_21505).sum := by decide
  have hdescent : baseEnd_21505 < baseStart_21505 := by decide
  rcases family_descends (prefixWord ++ tailWord_21505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21516 : List Nat := [2, 2, 1, 2, 3, 2, 3, 7]
def baseStart_21516 : Nat := 118140960795 + 21516 * 2 ^ 59
def prefixEnd_21516 : Nat := 4983230072969 + 3 ^ 40 * 21516 * 2
def baseEnd_21516 : Nat := 818374056462448314893

theorem tailTrace_21516 : CollatzResearch.WordTrace tailWord_21516 prefixEnd_21516 818374056462448314893 := by
  unfold tailWord_21516
  simp only [CollatzResearch.WordTrace]
  refine ⟨392376495029340742678201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 523168660039120990237601 392376495029340742678201)
  ·
    refine ⟨294282371272005557008651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 392376495029340742678201 294282371272005557008651)
    ·
      refine ⟨441423556908008335512977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294282371272005557008651 441423556908008335512977)
      ·
        refine ⟨331067667681006251634733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441423556908008335512977 331067667681006251634733)
        ·
          refine ⟨124150375380377344363025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331067667681006251634733 124150375380377344363025)
          ·
            refine ⟨93112781535283008272269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124150375380377344363025 93112781535283008272269)
            ·
              refine ⟨34917293075731128102101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93112781535283008272269 34917293075731128102101)
              ·
                refine ⟨818374056462448314893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34917293075731128102101 818374056462448314893)
                ·
                  rfl

theorem cell22_21516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 7].length) (baseStart_21516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21516 prefixEnd_21516 := by exact prefixLift 21516
  have htrace : WordTrace (prefixWord ++ tailWord_21516) baseStart_21516 baseEnd_21516 := by
    simpa [prefixWord, tailWord_21516, baseEnd_21516] using wordTrace_append hprefix tailTrace_21516
  have hstable : (prefixWord ++ tailWord_21516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21516).length < 2 ^ (prefixWord ++ tailWord_21516).sum := by decide
  have hdescent : baseEnd_21516 < baseStart_21516 := by decide
  rcases family_descends (prefixWord ++ tailWord_21516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21522 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_21522 : Nat := 118140960795 + 21522 * 2 ^ 59
def prefixEnd_21522 : Nat := 4983230072969 + 3 ^ 40 * 21522 * 2
def baseEnd_21522 : Nat := 2455806810260006394673

theorem tailTrace_21522 : CollatzResearch.WordTrace tailWord_21522 prefixEnd_21522 2455806810260006394673 := by
  unfold tailWord_21522
  simp only [CollatzResearch.WordTrace]
  refine ⟨196242957009236127518705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 523314552024629673383213 196242957009236127518705)
  ·
    refine ⟨147182217756927095639029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196242957009236127518705 147182217756927095639029)
    ·
      refine ⟨13798332914711915216159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147182217756927095639029 13798332914711915216159)
      ·
        refine ⟨20697499372067872824239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13798332914711915216159 20697499372067872824239)
        ·
          refine ⟨31046249058101809236359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20697499372067872824239 31046249058101809236359)
          ·
            refine ⟨46569373587152713854539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31046249058101809236359 46569373587152713854539)
            ·
              refine ⟨69854060380729070781809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46569373587152713854539 69854060380729070781809)
              ·
                refine ⟨52390545285546803086357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69854060380729070781809 52390545285546803086357)
                ·
                  refine ⟨2455806810260006394673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52390545285546803086357 2455806810260006394673)
                  ·
                    rfl

theorem cell22_21522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_21522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21522 prefixEnd_21522 := by exact prefixLift 21522
  have htrace : WordTrace (prefixWord ++ tailWord_21522) baseStart_21522 baseEnd_21522 := by
    simpa [prefixWord, tailWord_21522, baseEnd_21522] using wordTrace_append hprefix tailTrace_21522
  have hstable : (prefixWord ++ tailWord_21522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21522).length < 2 ^ (prefixWord ++ tailWord_21522).sum := by decide
  have hdescent : baseEnd_21522 < baseStart_21522 := by decide
  rcases family_descends (prefixWord ++ tailWord_21522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21565 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_21565 : Nat := 118140960795 + 21565 * 2 ^ 59
def prefixEnd_21565 : Nat := 4983230072969 + 3 ^ 40 * 21565 * 2
def baseEnd_21565 : Nat := 7382140209542240358887

theorem tailTrace_21565 : CollatzResearch.WordTrace tailWord_21565 prefixEnd_21565 7382140209542240358887 := by
  unfold tailWord_21565
  simp only [CollatzResearch.WordTrace]
  refine ⟨786540166881162853890149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 524360111254108569260099 786540166881162853890149)
  ·
    refine ⟨147476281290218035104403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 786540166881162853890149 147476281290218035104403)
    ·
      refine ⟨221214421935327052656605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147476281290218035104403 221214421935327052656605)
      ·
        refine ⟨82955408225747644746227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221214421935327052656605 82955408225747644746227)
        ·
          refine ⟨124433112338621467119341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82955408225747644746227 124433112338621467119341)
          ·
            refine ⟨46662417126983050169753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124433112338621467119341 46662417126983050169753)
            ·
              refine ⟨34996812845237287627315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46662417126983050169753 34996812845237287627315)
              ·
                refine ⟨52495219267855931440973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34996812845237287627315 52495219267855931440973)
                ·
                  refine ⟨19685707225445974290365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52495219267855931440973 19685707225445974290365)
                  ·
                    refine ⟨7382140209542240358887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19685707225445974290365 7382140209542240358887)
                    ·
                      rfl

theorem cell22_21565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_21565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21565 prefixEnd_21565 := by exact prefixLift 21565
  have htrace : WordTrace (prefixWord ++ tailWord_21565) baseStart_21565 baseEnd_21565 := by
    simpa [prefixWord, tailWord_21565, baseEnd_21565] using wordTrace_append hprefix tailTrace_21565
  have hstable : (prefixWord ++ tailWord_21565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21565).length < 2 ^ (prefixWord ++ tailWord_21565).sum := by decide
  have hdescent : baseEnd_21565 < baseStart_21565 := by decide
  rcases family_descends (prefixWord ++ tailWord_21565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21576 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_21576 : Nat := 118140960795 + 21576 * 2 ^ 59
def prefixEnd_21576 : Nat := 4983230072969 + 3 ^ 40 * 21576 * 2
def baseEnd_21576 : Nat := 7385905734341878333853

theorem tailTrace_21576 : CollatzResearch.WordTrace tailWord_21576 prefixEnd_21576 7385905734341878333853 := by
  unfold tailWord_21576
  simp only [CollatzResearch.WordTrace]
  refine ⟨393470684920655866270291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 524627579894207821693721 393470684920655866270291)
  ·
    refine ⟨590206027380983799405437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393470684920655866270291 590206027380983799405437)
    ·
      refine ⟨221327260267868924777039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 590206027380983799405437 221327260267868924777039)
      ·
        refine ⟨331990890401803387165559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221327260267868924777039 331990890401803387165559)
        ·
          refine ⟨497986335602705080748339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331990890401803387165559 497986335602705080748339)
          ·
            refine ⟨746979503404057621122509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497986335602705080748339 746979503404057621122509)
            ·
              refine ⟨280117313776521607920941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746979503404057621122509 280117313776521607920941)
              ·
                refine ⟨105043992666195602970353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280117313776521607920941 105043992666195602970353)
                ·
                  refine ⟨78782994499646702227765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105043992666195602970353 78782994499646702227765)
                  ·
                    refine ⟨7385905734341878333853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78782994499646702227765 7385905734341878333853)
                    ·
                      rfl

theorem cell22_21576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_21576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21576 prefixEnd_21576 := by exact prefixLift 21576
  have htrace : WordTrace (prefixWord ++ tailWord_21576) baseStart_21576 baseEnd_21576 := by
    simpa [prefixWord, tailWord_21576, baseEnd_21576] using wordTrace_append hprefix tailTrace_21576
  have hstable : (prefixWord ++ tailWord_21576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21576).length < 2 ^ (prefixWord ++ tailWord_21576).sum := by decide
  have hdescent : baseEnd_21576 < baseStart_21576 := by decide
  rcases family_descends (prefixWord ++ tailWord_21576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21651 : List Nat := [1, 1, 1, 2, 1, 2, 6, 8]
def baseStart_21651 : Nat := 118140960795 + 21651 * 2 ^ 59
def prefixEnd_21651 : Nat := 4983230072969 + 3 ^ 40 * 21651 * 2
def baseEnd_21651 : Nat := 823508863007409189847

theorem tailTrace_21651 : CollatzResearch.WordTrace tailWord_21651 prefixEnd_21651 823508863007409189847 := by
  unfold tailWord_21651
  simp only [CollatzResearch.WordTrace]
  refine ⟨789676844569599541520807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 526451229713066361013871 789676844569599541520807)
  ·
    refine ⟨1184515266854399312281211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 789676844569599541520807 1184515266854399312281211)
    ·
      refine ⟨1776772900281598968421817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1184515266854399312281211 1776772900281598968421817)
      ·
        refine ⟨1332579675211199226316363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1776772900281598968421817 1332579675211199226316363)
        ·
          refine ⟨1998869512816798839474545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332579675211199226316363 1998869512816798839474545)
          ·
            refine ⟨1499152134612599129605909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998869512816798839474545 1499152134612599129605909)
            ·
              refine ⟨70272756309965584200277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1499152134612599129605909 70272756309965584200277)
              ·
                refine ⟨823508863007409189847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 70272756309965584200277 823508863007409189847)
                ·
                  rfl

theorem cell22_21651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 8].length) (baseStart_21651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21651 prefixEnd_21651 := by exact prefixLift 21651
  have htrace : WordTrace (prefixWord ++ tailWord_21651) baseStart_21651 baseEnd_21651 := by
    simpa [prefixWord, tailWord_21651, baseEnd_21651] using wordTrace_append hprefix tailTrace_21651
  have hstable : (prefixWord ++ tailWord_21651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21651).length < 2 ^ (prefixWord ++ tailWord_21651).sum := by decide
  have hdescent : baseEnd_21651 < baseStart_21651 := by decide
  rcases family_descends (prefixWord ++ tailWord_21651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21674 : List Nat := [3, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_21674 : Nat := 118140960795 + 21674 * 2 ^ 59
def prefixEnd_21674 : Nat := 4983230072969 + 3 ^ 40 * 21674 * 2
def baseEnd_21674 : Nat := 2473151045700763127851

theorem tailTrace_21674 : CollatzResearch.WordTrace tailWord_21674 prefixEnd_21674 2473151045700763127851 := by
  unfold tailWord_21674
  simp only [CollatzResearch.WordTrace]
  refine ⟨197628930871568617402019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 527010482324182979738717 197628930871568617402019)
  ·
    refine ⟨296443396307352926103029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197628930871568617402019 296443396307352926103029)
    ·
      refine ⟨27791568403814336822159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 296443396307352926103029 27791568403814336822159)
      ·
        refine ⟨41687352605721505233239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27791568403814336822159 41687352605721505233239)
        ·
          refine ⟨62531028908582257849859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41687352605721505233239 62531028908582257849859)
          ·
            refine ⟨93796543362873386774789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62531028908582257849859 93796543362873386774789)
            ·
              refine ⟨17586851880538760020273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93796543362873386774789 17586851880538760020273)
              ·
                refine ⟨13190138910404070015205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17586851880538760020273 13190138910404070015205)
                ·
                  refine ⟨2473151045700763127851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13190138910404070015205 2473151045700763127851)
                  ·
                    rfl

theorem cell22_21674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_21674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21674 prefixEnd_21674 := by exact prefixLift 21674
  have htrace : WordTrace (prefixWord ++ tailWord_21674) baseStart_21674 baseEnd_21674 := by
    simpa [prefixWord, tailWord_21674, baseEnd_21674] using wordTrace_append hprefix tailTrace_21674
  have hstable : (prefixWord ++ tailWord_21674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21674).length < 2 ^ (prefixWord ++ tailWord_21674).sum := by decide
  have hdescent : baseEnd_21674 < baseStart_21674 := by decide
  rcases family_descends (prefixWord ++ tailWord_21674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21728 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_21728 : Nat := 118140960795 + 21728 * 2 ^ 59
def prefixEnd_21728 : Nat := 4983230072969 + 3 ^ 40 * 21728 * 2
def baseEnd_21728 : Nat := 7437938440664148533387

theorem tailTrace_21728 : CollatzResearch.WordTrace tailWord_21728 prefixEnd_21728 7437938440664148533387 := by
  unfold tailWord_21728
  simp only [CollatzResearch.WordTrace]
  refine ⟨396242632645320846036919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 528323510193761128049225 396242632645320846036919)
  ·
    refine ⟨594363948967981269055379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 396242632645320846036919 594363948967981269055379)
    ·
      refine ⟨891545923451971903583069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594363948967981269055379 891545923451971903583069)
      ·
        refine ⟨334329721294489463843651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 891545923451971903583069 334329721294489463843651)
        ·
          refine ⟨501494581941734195765477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334329721294489463843651 501494581941734195765477)
          ·
            refine ⟨94030234114075161706027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 501494581941734195765477 94030234114075161706027)
            ·
              refine ⟨141045351171112742559041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94030234114075161706027 141045351171112742559041)
              ·
                refine ⟨105784013378334556919281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141045351171112742559041 105784013378334556919281)
                ·
                  refine ⟨79338010033750917689461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105784013378334556919281 79338010033750917689461)
                  ·
                    refine ⟨7437938440664148533387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79338010033750917689461 7437938440664148533387)
                    ·
                      rfl

theorem cell22_21728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_21728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21728 prefixEnd_21728 := by exact prefixLift 21728
  have htrace : WordTrace (prefixWord ++ tailWord_21728) baseStart_21728 baseEnd_21728 := by
    simpa [prefixWord, tailWord_21728, baseEnd_21728] using wordTrace_append hprefix tailTrace_21728
  have hstable : (prefixWord ++ tailWord_21728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21728).length < 2 ^ (prefixWord ++ tailWord_21728).sum := by decide
  have hdescent : baseEnd_21728 < baseStart_21728 := by decide
  rcases family_descends (prefixWord ++ tailWord_21728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21792 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 6]
def baseStart_21792 : Nat := 118140960795 + 21792 * 2 ^ 59
def prefixEnd_21792 : Nat := 4983230072969 + 3 ^ 40 * 21792 * 2
def baseEnd_21792 : Nat := 2486615649529771644397

theorem tailTrace_21792 : CollatzResearch.WordTrace tailWord_21792 prefixEnd_21792 2486615649529771644397 := by
  unfold tailWord_21792
  simp only [CollatzResearch.WordTrace]
  refine ⟨397409768529390311201815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 529879691372520414935753 397409768529390311201815)
  ·
    refine ⟨596114652794085466802723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397409768529390311201815 596114652794085466802723)
    ·
      refine ⟨894171979191128200204085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596114652794085466802723 894171979191128200204085)
      ·
        refine ⟨83828623049168268769133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 894171979191128200204085 83828623049168268769133)
        ·
          refine ⟨31435733643438100788425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83828623049168268769133 31435733643438100788425)
          ·
            refine ⟨23576800232578575591319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31435733643438100788425 23576800232578575591319)
            ·
              refine ⟨35365200348867863386979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23576800232578575591319 35365200348867863386979)
              ·
                refine ⟨53047800523301795080469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35365200348867863386979 53047800523301795080469)
                ·
                  refine ⟨2486615649529771644397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53047800523301795080469 2486615649529771644397)
                  ·
                    rfl

theorem cell22_21792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_21792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21792 prefixEnd_21792 := by exact prefixLift 21792
  have htrace : WordTrace (prefixWord ++ tailWord_21792) baseStart_21792 baseEnd_21792 := by
    simpa [prefixWord, tailWord_21792, baseEnd_21792] using wordTrace_append hprefix tailTrace_21792
  have hstable : (prefixWord ++ tailWord_21792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21792).length < 2 ^ (prefixWord ++ tailWord_21792).sum := by decide
  have hdescent : baseEnd_21792 < baseStart_21792 := by decide
  rcases family_descends (prefixWord ++ tailWord_21792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21822 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_21822 : Nat := 118140960795 + 21822 * 2 ^ 59
def prefixEnd_21822 : Nat := 4983230072969 + 3 ^ 40 * 21822 * 2
def baseEnd_21822 : Nat := 7470116561679236683099

theorem tailTrace_21822 : CollatzResearch.WordTrace tailWord_21822 prefixEnd_21822 7470116561679236683099 := by
  unfold tailWord_21822
  simp only [CollatzResearch.WordTrace]
  refine ⟨99489215868761968249465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 530609151300063830663813 99489215868761968249465)
  ·
    refine ⟨74616911901571476187099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99489215868761968249465 74616911901571476187099)
    ·
      refine ⟨111925367852357214280649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74616911901571476187099 111925367852357214280649)
      ·
        refine ⟨83944025889267910710487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111925367852357214280649 83944025889267910710487)
        ·
          refine ⟨125916038833901866065731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83944025889267910710487 125916038833901866065731)
          ·
            refine ⟨188874058250852799098597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125916038833901866065731 188874058250852799098597)
            ·
              refine ⟨35413885922034899830987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188874058250852799098597 35413885922034899830987)
              ·
                refine ⟨53120828883052349746481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35413885922034899830987 53120828883052349746481)
                ·
                  refine ⟨39840621662289262309861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53120828883052349746481 39840621662289262309861)
                  ·
                    refine ⟨7470116561679236683099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39840621662289262309861 7470116561679236683099)
                    ·
                      rfl

theorem cell22_21822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_21822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21822 prefixEnd_21822 := by exact prefixLift 21822
  have htrace : WordTrace (prefixWord ++ tailWord_21822) baseStart_21822 baseEnd_21822 := by
    simpa [prefixWord, tailWord_21822, baseEnd_21822] using wordTrace_append hprefix tailTrace_21822
  have hstable : (prefixWord ++ tailWord_21822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21822).length < 2 ^ (prefixWord ++ tailWord_21822).sum := by decide
  have hdescent : baseEnd_21822 < baseStart_21822 := by decide
  rcases family_descends (prefixWord ++ tailWord_21822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21837 : List Nat := [1, 6, 1, 3, 1, 10]
def baseStart_21837 : Nat := 118140960795 + 21837 * 2 ^ 59
def prefixEnd_21837 : Nat := 4983230072969 + 3 ^ 40 * 21837 * 2
def baseEnd_21837 : Nat := 92287053928693797013

theorem tailTrace_21837 : CollatzResearch.WordTrace tailWord_21837 prefixEnd_21837 92287053928693797013 := by
  unfold tailWord_21837
  simp only [CollatzResearch.WordTrace]
  refine ⟨796460821895753307791765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 530973881263835538527843 796460821895753307791765)
  ·
    refine ⟨37334101026363436302739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 796460821895753307791765 37334101026363436302739)
    ·
      refine ⟨56001151539545154454109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37334101026363436302739 56001151539545154454109)
      ·
        refine ⟨21000431827329432920291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56001151539545154454109 21000431827329432920291)
        ·
          refine ⟨31500647740994149380437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21000431827329432920291 31500647740994149380437)
          ·
            refine ⟨92287053928693797013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 31500647740994149380437 92287053928693797013)
            ·
              rfl

theorem cell22_21837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 10].length) (baseStart_21837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21837 prefixEnd_21837 := by exact prefixLift 21837
  have htrace : WordTrace (prefixWord ++ tailWord_21837) baseStart_21837 baseEnd_21837 := by
    simpa [prefixWord, tailWord_21837, baseEnd_21837] using wordTrace_append hprefix tailTrace_21837
  have hstable : (prefixWord ++ tailWord_21837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21837).length < 2 ^ (prefixWord ++ tailWord_21837).sum := by decide
  have hdescent : baseEnd_21837 < baseStart_21837 := by decide
  rcases family_descends (prefixWord ++ tailWord_21837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21916 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 5]
def baseStart_21916 : Nat := 118140960795 + 21916 * 2 ^ 59
def prefixEnd_21916 : Nat := 4983230072969 + 3 ^ 40 * 21916 * 2
def baseEnd_21916 : Nat := 2500764894231441610937

theorem tailTrace_21916 : CollatzResearch.WordTrace tailWord_21916 prefixEnd_21916 2500764894231441610937 := by
  unfold tailWord_21916
  simp only [CollatzResearch.WordTrace]
  refine ⟨399671094304774899958801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 532894792406366533278401 399671094304774899958801)
  ·
    refine ⟨299753320728581174969101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 399671094304774899958801 299753320728581174969101)
    ·
      refine ⟨112407495273217940613413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299753320728581174969101 112407495273217940613413)
      ·
        refine ⟨21076405363728363865015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112407495273217940613413 21076405363728363865015)
        ·
          refine ⟨31614608045592545797523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21076405363728363865015 31614608045592545797523)
          ·
            refine ⟨47421912068388818696285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31614608045592545797523 47421912068388818696285)
            ·
              refine ⟨17783217025645807011107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47421912068388818696285 17783217025645807011107)
              ·
                refine ⟨26674825538468710516661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17783217025645807011107 26674825538468710516661)
                ·
                  refine ⟨2500764894231441610937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26674825538468710516661 2500764894231441610937)
                  ·
                    rfl

theorem cell22_21916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_21916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21916 prefixEnd_21916 := by exact prefixLift 21916
  have htrace : WordTrace (prefixWord ++ tailWord_21916) baseStart_21916 baseEnd_21916 := by
    simpa [prefixWord, tailWord_21916, baseEnd_21916] using wordTrace_append hprefix tailTrace_21916
  have hstable : (prefixWord ++ tailWord_21916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21916).length < 2 ^ (prefixWord ++ tailWord_21916).sum := by decide
  have hdescent : baseEnd_21916 < baseStart_21916 := by decide
  rcases family_descends (prefixWord ++ tailWord_21916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21925 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_21925 : Nat := 118140960795 + 21925 * 2 ^ 59
def prefixEnd_21925 : Nat := 4983230072969 + 3 ^ 40 * 21925 * 2
def baseEnd_21925 : Nat := 7505375566621301357783

theorem tailTrace_21925 : CollatzResearch.WordTrace tailWord_21925 prefixEnd_21925 7505375566621301357783 := by
  unfold tailWord_21925
  simp only [CollatzResearch.WordTrace]
  refine ⟨799670445576944336995229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 533113630384629557996819 799670445576944336995229)
  ·
    refine ⟨299876417091354126373211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 799670445576944336995229 299876417091354126373211)
    ·
      refine ⟨449814625637031189559817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299876417091354126373211 449814625637031189559817)
      ·
        refine ⟨337360969227773392169863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449814625637031189559817 337360969227773392169863)
        ·
          refine ⟨506041453841660088254795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337360969227773392169863 506041453841660088254795)
          ·
            refine ⟨759062180762490132382193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506041453841660088254795 759062180762490132382193)
            ·
              refine ⟨569296635571867599286645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759062180762490132382193 569296635571867599286645)
              ·
                refine ⟨53371559584862587433123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 569296635571867599286645 53371559584862587433123)
                ·
                  refine ⟨80057339377293881149685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53371559584862587433123 80057339377293881149685)
                  ·
                    refine ⟨7505375566621301357783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80057339377293881149685 7505375566621301357783)
                    ·
                      rfl

theorem cell22_21925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_21925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21925 prefixEnd_21925 := by exact prefixLift 21925
  have htrace : WordTrace (prefixWord ++ tailWord_21925) baseStart_21925 baseEnd_21925 := by
    simpa [prefixWord, tailWord_21925, baseEnd_21925] using wordTrace_append hprefix tailTrace_21925
  have hstable : (prefixWord ++ tailWord_21925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21925).length < 2 ^ (prefixWord ++ tailWord_21925).sum := by decide
  have hdescent : baseEnd_21925 < baseStart_21925 := by decide
  rcases family_descends (prefixWord ++ tailWord_21925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21954 : List Nat := [3, 5, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_21954 : Nat := 118140960795 + 21954 * 2 ^ 59
def prefixEnd_21954 : Nat := 4983230072969 + 3 ^ 40 * 21954 * 2
def baseEnd_21954 : Nat := 7515302859274892382695

theorem tailTrace_21954 : CollatzResearch.WordTrace tailWord_21954 prefixEnd_21954 7515302859274892382695 := by
  unfold tailWord_21954
  simp only [CollatzResearch.WordTrace]
  refine ⟨200182040617970572450229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 533818774981254859867277 200182040617970572450229)
  ·
    refine ⟨18767066307934741167209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200182040617970572450229 18767066307934741167209)
    ·
      refine ⟨14075299730951055875407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18767066307934741167209 14075299730951055875407)
      ·
        refine ⟨21112949596426583813111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14075299730951055875407 21112949596426583813111)
        ·
          refine ⟨31669424394639875719667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21112949596426583813111 31669424394639875719667)
          ·
            refine ⟨47504136591959813579501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31669424394639875719667 47504136591959813579501)
            ·
              refine ⟨17814051221984930092313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47504136591959813579501 17814051221984930092313)
              ·
                refine ⟨13360538416488697569235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17814051221984930092313 13360538416488697569235)
                ·
                  refine ⟨20040807624733046353853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13360538416488697569235 20040807624733046353853)
                  ·
                    refine ⟨7515302859274892382695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20040807624733046353853 7515302859274892382695)
                    ·
                      rfl

theorem cell22_21954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_21954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_21954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_21954 prefixEnd_21954 := by exact prefixLift 21954
  have htrace : WordTrace (prefixWord ++ tailWord_21954) baseStart_21954 baseEnd_21954 := by
    simpa [prefixWord, tailWord_21954, baseEnd_21954] using wordTrace_append hprefix tailTrace_21954
  have hstable : (prefixWord ++ tailWord_21954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21954).length < 2 ^ (prefixWord ++ tailWord_21954).sum := by decide
  have hdescent : baseEnd_21954 < baseStart_21954 := by decide
  rcases family_descends (prefixWord ++ tailWord_21954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22047 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 3, 4]
def baseStart_22047 : Nat := 118140960795 + 22047 * 2 ^ 59
def prefixEnd_22047 : Nat := 4983230072969 + 3 ^ 40 * 22047 * 2
def baseEnd_22047 : Nat := 7547138659853649807409

theorem tailTrace_22047 : CollatzResearch.WordTrace tailWord_22047 prefixEnd_22047 7547138659853649807409 := by
  unfold tailWord_22047
  simp only [CollatzResearch.WordTrace]
  refine ⟨804120151134959172936395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 536080100756639448624263 804120151134959172936395)
  ·
    refine ⟨1206180226702438759404593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 804120151134959172936395 1206180226702438759404593)
    ·
      refine ⟨904635170026829069553445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1206180226702438759404593 904635170026829069553445)
      ·
        refine ⟨169619094380030450541271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 904635170026829069553445 169619094380030450541271)
        ·
          refine ⟨254428641570045675811907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169619094380030450541271 254428641570045675811907)
          ·
            refine ⟨381642962355068513717861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254428641570045675811907 381642962355068513717861)
            ·
              refine ⟨71558055441575346322099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 381642962355068513717861 71558055441575346322099)
              ·
                refine ⟨107337083162363019483149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71558055441575346322099 107337083162363019483149)
                ·
                  refine ⟨40251406185886132306181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107337083162363019483149 40251406185886132306181)
                  ·
                    refine ⟨7547138659853649807409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40251406185886132306181 7547138659853649807409)
                    ·
                      rfl

theorem cell22_22047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_22047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22047 prefixEnd_22047 := by exact prefixLift 22047
  have htrace : WordTrace (prefixWord ++ tailWord_22047) baseStart_22047 baseEnd_22047 := by
    simpa [prefixWord, tailWord_22047, baseEnd_22047] using wordTrace_append hprefix tailTrace_22047
  have hstable : (prefixWord ++ tailWord_22047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22047).length < 2 ^ (prefixWord ++ tailWord_22047).sum := by decide
  have hdescent : baseEnd_22047 < baseStart_22047 := by decide
  rcases family_descends (prefixWord ++ tailWord_22047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22079 : List Nat := [1, 1, 2, 2, 3, 3, 2, 4, 4]
def baseStart_22079 : Nat := 118140960795 + 22079 * 2 ^ 59
def prefixEnd_22079 : Nat := 4983230072969 + 3 ^ 40 * 22079 * 2
def baseEnd_22079 : Nat := 2519364304605411002437

theorem tailTrace_22079 : CollatzResearch.WordTrace tailWord_22079 prefixEnd_22079 2519364304605411002437 := by
  unfold tailWord_22079
  simp only [CollatzResearch.WordTrace]
  refine ⟨805287287019028638101291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 536858191346019092067527 805287287019028638101291)
  ·
    refine ⟨1207930930528542957151937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 805287287019028638101291 1207930930528542957151937)
    ·
      refine ⟨905948197896407217863953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1207930930528542957151937 905948197896407217863953)
      ·
        refine ⟨679461148422305413397965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 905948197896407217863953 679461148422305413397965)
        ·
          refine ⟨254797930658364530024237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679461148422305413397965 254797930658364530024237)
          ·
            refine ⟨95549223996886698759089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254797930658364530024237 95549223996886698759089)
            ·
              refine ⟨71661917997665024069317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95549223996886698759089 71661917997665024069317)
              ·
                refine ⟨13436609624562192012997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71661917997665024069317 13436609624562192012997)
                ·
                  refine ⟨2519364304605411002437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13436609624562192012997 2519364304605411002437)
                  ·
                    rfl

theorem cell22_22079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 4].length) (baseStart_22079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22079 prefixEnd_22079 := by exact prefixLift 22079
  have htrace : WordTrace (prefixWord ++ tailWord_22079) baseStart_22079 baseEnd_22079 := by
    simpa [prefixWord, tailWord_22079, baseEnd_22079] using wordTrace_append hprefix tailTrace_22079
  have hstable : (prefixWord ++ tailWord_22079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22079).length < 2 ^ (prefixWord ++ tailWord_22079).sum := by decide
  have hdescent : baseEnd_22079 < baseStart_22079 := by decide
  rcases family_descends (prefixWord ++ tailWord_22079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22092 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_22092 : Nat := 118140960795 + 22092 * 2 ^ 59
def prefixEnd_22092 : Nat := 4983230072969 + 3 ^ 40 * 22092 * 2
def baseEnd_22092 : Nat := 7562543079488532432271

theorem tailTrace_22092 : CollatzResearch.WordTrace tailWord_22092 prefixEnd_22092 7562543079488532432271 := by
  unfold tailWord_22092
  simp only [CollatzResearch.WordTrace]
  refine ⟨402880717985965929162265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 537174290647954572216353 402880717985965929162265)
  ·
    refine ⟨302160538489474446871699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 402880717985965929162265 302160538489474446871699)
    ·
      refine ⟨453240807734211670307549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302160538489474446871699 453240807734211670307549)
      ·
        refine ⟨169965302900329376365331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453240807734211670307549 169965302900329376365331)
        ·
          refine ⟨254947954350494064547997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169965302900329376365331 254947954350494064547997)
          ·
            refine ⟨95605482881435274205499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254947954350494064547997 95605482881435274205499)
            ·
              refine ⟨143408224322152911308249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95605482881435274205499 143408224322152911308249)
              ·
                refine ⟨107556168241614683481187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143408224322152911308249 107556168241614683481187)
                ·
                  refine ⟨161334252362422025221781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107556168241614683481187 161334252362422025221781)
                  ·
                    refine ⟨7562543079488532432271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161334252362422025221781 7562543079488532432271)
                    ·
                      rfl

theorem cell22_22092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_22092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22092 prefixEnd_22092 := by exact prefixLift 22092
  have htrace : WordTrace (prefixWord ++ tailWord_22092) baseStart_22092 baseEnd_22092 := by
    simpa [prefixWord, tailWord_22092, baseEnd_22092] using wordTrace_append hprefix tailTrace_22092
  have hstable : (prefixWord ++ tailWord_22092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22092).length < 2 ^ (prefixWord ++ tailWord_22092).sum := by decide
  have hdescent : baseEnd_22092 < baseStart_22092 := by decide
  rcases family_descends (prefixWord ++ tailWord_22092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22126 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_22126 : Nat := 118140960795 + 22126 * 2 ^ 59
def prefixEnd_22126 : Nat := 4983230072969 + 3 ^ 40 * 22126 * 2
def baseEnd_22126 : Nat := 7574181974323777082167

theorem tailTrace_22126 : CollatzResearch.WordTrace tailWord_22126 prefixEnd_22126 7574181974323777082167 := by
  unfold tailWord_22126
  simp only [CollatzResearch.WordTrace]
  refine ⟨100875189731094458132779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 538001011899170443374821 100875189731094458132779)
  ·
    refine ⟨151312784596641687199169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100875189731094458132779 151312784596641687199169)
    ·
      refine ⟨113484588447481265399377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151312784596641687199169 113484588447481265399377)
      ·
        refine ⟨85113441335610949049533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113484588447481265399377 85113441335610949049533)
        ·
          refine ⟨31917540500854105893575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85113441335610949049533 31917540500854105893575)
          ·
            refine ⟨47876310751281158840363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31917540500854105893575 47876310751281158840363)
            ·
              refine ⟨71814466126921738260545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47876310751281158840363 71814466126921738260545)
              ·
                refine ⟨53860849595191303695409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71814466126921738260545 53860849595191303695409)
                ·
                  refine ⟨40395637196393477771557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53860849595191303695409 40395637196393477771557)
                  ·
                    refine ⟨7574181974323777082167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40395637196393477771557 7574181974323777082167)
                    ·
                      rfl

theorem cell22_22126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_22126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22126 prefixEnd_22126 := by exact prefixLift 22126
  have htrace : WordTrace (prefixWord ++ tailWord_22126) baseStart_22126 baseEnd_22126 := by
    simpa [prefixWord, tailWord_22126, baseEnd_22126] using wordTrace_append hprefix tailTrace_22126
  have hstable : (prefixWord ++ tailWord_22126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22126).length < 2 ^ (prefixWord ++ tailWord_22126).sum := by decide
  have hdescent : baseEnd_22126 < baseStart_22126 := by decide
  rcases family_descends (prefixWord ++ tailWord_22126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22137 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_22137 : Nat := 118140960795 + 22137 * 2 ^ 59
def prefixEnd_22137 : Nat := 4983230072969 + 3 ^ 40 * 22137 * 2
def baseEnd_22137 : Nat := 7577947499123415057133

theorem tailTrace_22137 : CollatzResearch.WordTrace tailWord_22137 prefixEnd_22137 7577947499123415057133 := by
  unfold tailWord_22137
  simp only [CollatzResearch.WordTrace]
  refine ⟨807402720808904543712665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 538268480539269695808443 807402720808904543712665)
  ·
    refine ⟨605552040606678407784499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 807402720808904543712665 605552040606678407784499)
    ·
      refine ⟨908328060910017611676749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605552040606678407784499 908328060910017611676749)
      ·
        refine ⟨340623022841256604378781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 908328060910017611676749 340623022841256604378781)
        ·
          refine ⟨127733633565471226642043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340623022841256604378781 127733633565471226642043)
          ·
            refine ⟨191600450348206839963065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127733633565471226642043 191600450348206839963065)
            ·
              refine ⟨143700337761155129972299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191600450348206839963065 143700337761155129972299)
              ·
                refine ⟨215550506641732694958449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143700337761155129972299 215550506641732694958449)
                ·
                  refine ⟨161662879981299521218837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215550506641732694958449 161662879981299521218837)
                  ·
                    refine ⟨7577947499123415057133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161662879981299521218837 7577947499123415057133)
                    ·
                      rfl

theorem cell22_22137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_22137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22137 prefixEnd_22137 := by exact prefixLift 22137
  have htrace : WordTrace (prefixWord ++ tailWord_22137) baseStart_22137 baseEnd_22137 := by
    simpa [prefixWord, tailWord_22137, baseEnd_22137] using wordTrace_append hprefix tailTrace_22137
  have hstable : (prefixWord ++ tailWord_22137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22137).length < 2 ^ (prefixWord ++ tailWord_22137).sum := by decide
  have hdescent : baseEnd_22137 < baseStart_22137 := by decide
  rcases family_descends (prefixWord ++ tailWord_22137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22199 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 3, 4]
def baseStart_22199 : Nat := 118140960795 + 22199 * 2 ^ 59
def prefixEnd_22199 : Nat := 4983230072969 + 3 ^ 40 * 22199 * 2
def baseEnd_22199 : Nat := 7599171366175920006943

theorem tailTrace_22199 : CollatzResearch.WordTrace tailWord_22199 prefixEnd_22199 7599171366175920006943 := by
  unfold tailWord_22199
  simp only [CollatzResearch.WordTrace]
  refine ⟨809664046584289132469651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 539776031056192754979767 809664046584289132469651)
  ·
    refine ⟨1214496069876433698704477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 809664046584289132469651 1214496069876433698704477)
    ·
      refine ⟨455436026203662637014179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1214496069876433698704477 455436026203662637014179)
      ·
        refine ⟨683154039305493955521269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455436026203662637014179 683154039305493955521269)
        ·
          refine ⟨64045691184890058330119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 683154039305493955521269 64045691184890058330119)
          ·
            refine ⟨96068536777335087495179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64045691184890058330119 96068536777335087495179)
            ·
              refine ⟨144102805166002631242769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96068536777335087495179 144102805166002631242769)
              ·
                refine ⟨108077103874501973432077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144102805166002631242769 108077103874501973432077)
                ·
                  refine ⟨40528913952938240037029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108077103874501973432077 40528913952938240037029)
                  ·
                    refine ⟨7599171366175920006943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40528913952938240037029 7599171366175920006943)
                    ·
                      rfl

theorem cell22_22199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_22199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22199 prefixEnd_22199 := by exact prefixLift 22199
  have htrace : WordTrace (prefixWord ++ tailWord_22199) baseStart_22199 baseEnd_22199 := by
    simpa [prefixWord, tailWord_22199, baseEnd_22199] using wordTrace_append hprefix tailTrace_22199
  have hstable : (prefixWord ++ tailWord_22199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22199).length < 2 ^ (prefixWord ++ tailWord_22199).sum := by decide
  have hdescent : baseEnd_22199 < baseStart_22199 := by decide
  rcases family_descends (prefixWord ++ tailWord_22199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22231 : List Nat := [1, 1, 3, 2, 1, 3, 4, 3, 4]
def baseStart_22231 : Nat := 118140960795 + 22231 * 2 ^ 59
def prefixEnd_22231 : Nat := 4983230072969 + 3 ^ 40 * 22231 * 2
def baseEnd_22231 : Nat := 2536708540046167735615

theorem tailTrace_22231 : CollatzResearch.WordTrace tailWord_22231 prefixEnd_22231 2536708540046167735615 := by
  unfold tailWord_22231
  simp only [CollatzResearch.WordTrace]
  refine ⟨810831182468358597634547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 540554121645572398423031 810831182468358597634547)
  ·
    refine ⟨1216246773702537896451821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810831182468358597634547 1216246773702537896451821)
    ·
      refine ⟨456092540138451711169433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1216246773702537896451821 456092540138451711169433)
      ·
        refine ⟨342069405103838783377075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456092540138451711169433 342069405103838783377075)
        ·
          refine ⟨513104107655758175065613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342069405103838783377075 513104107655758175065613)
          ·
            refine ⟨192414040370909315649605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513104107655758175065613 192414040370909315649605)
            ·
              refine ⟨36077632569545496684301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192414040370909315649605 36077632569545496684301)
              ·
                refine ⟨13529112213579561256613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36077632569545496684301 13529112213579561256613)
                ·
                  refine ⟨2536708540046167735615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13529112213579561256613 2536708540046167735615)
                  ·
                    rfl

theorem cell22_22231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 4].length) (baseStart_22231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22231 prefixEnd_22231 := by exact prefixLift 22231
  have htrace : WordTrace (prefixWord ++ tailWord_22231) baseStart_22231 baseEnd_22231 := by
    simpa [prefixWord, tailWord_22231, baseEnd_22231] using wordTrace_append hprefix tailTrace_22231
  have hstable : (prefixWord ++ tailWord_22231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22231).length < 2 ^ (prefixWord ++ tailWord_22231).sum := by decide
  have hdescent : baseEnd_22231 < baseStart_22231 := by decide
  rcases family_descends (prefixWord ++ tailWord_22231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22233 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 1, 4]
def baseStart_22233 : Nat := 118140960795 + 22233 * 2 ^ 59
def prefixEnd_22233 : Nat := 4983230072969 + 3 ^ 40 * 22233 * 2
def baseEnd_22233 : Nat := 7610810261011164656839

theorem tailTrace_22233 : CollatzResearch.WordTrace tailWord_22233 prefixEnd_22233 7610810261011164656839 := by
  unfold tailWord_22233
  simp only [CollatzResearch.WordTrace]
  refine ⟨810904128461112939207353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 540602752307408626138235 810904128461112939207353)
  ·
    refine ⟨608178096345834704405515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 810904128461112939207353 608178096345834704405515)
    ·
      refine ⟨912267144518752056608273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608178096345834704405515 912267144518752056608273)
      ·
        refine ⟨684200358389064042456205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912267144518752056608273 684200358389064042456205)
        ·
          refine ⟨256575134395899015921077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684200358389064042456205 256575134395899015921077)
          ·
            refine ⟨24053918849615532742601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256575134395899015921077 24053918849615532742601)
            ·
              refine ⟨18040439137211649556951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24053918849615532742601 18040439137211649556951)
              ·
                refine ⟨27060658705817474335427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18040439137211649556951 27060658705817474335427)
                ·
                  refine ⟨40590988058726211503141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27060658705817474335427 40590988058726211503141)
                  ·
                    refine ⟨7610810261011164656839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40590988058726211503141 7610810261011164656839)
                    ·
                      rfl

theorem cell22_22233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_22233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22233 prefixEnd_22233 := by exact prefixLift 22233
  have htrace : WordTrace (prefixWord ++ tailWord_22233) baseStart_22233 baseEnd_22233 := by
    simpa [prefixWord, tailWord_22233, baseEnd_22233] using wordTrace_append hprefix tailTrace_22233
  have hstable : (prefixWord ++ tailWord_22233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22233).length < 2 ^ (prefixWord ++ tailWord_22233).sum := by decide
  have hdescent : baseEnd_22233 < baseStart_22233 := by decide
  rcases family_descends (prefixWord ++ tailWord_22233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22244 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_22244 : Nat := 118140960795 + 22244 * 2 ^ 59
def prefixEnd_22244 : Nat := 4983230072969 + 3 ^ 40 * 22244 * 2
def baseEnd_22244 : Nat := 7614575785810802631805

theorem tailTrace_22244 : CollatzResearch.WordTrace tailWord_22244 prefixEnd_22244 7614575785810802631805 := by
  unfold tailWord_22244
  simp only [CollatzResearch.WordTrace]
  refine ⟨405652665710630908928893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 540870220947507878571857 405652665710630908928893)
  ·
    refine ⟨152119749641486590848335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 405652665710630908928893 152119749641486590848335)
    ·
      refine ⟨228179624462229886272503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152119749641486590848335 228179624462229886272503)
      ·
        refine ⟨342269436693344829408755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228179624462229886272503 342269436693344829408755)
        ·
          refine ⟨513404155040017244113133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342269436693344829408755 513404155040017244113133)
          ·
            refine ⟨192526558140006466542425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 513404155040017244113133 192526558140006466542425)
            ·
              refine ⟨144394918605004849906819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192526558140006466542425 144394918605004849906819)
              ·
                refine ⟨216592377907507274860229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144394918605004849906819 216592377907507274860229)
                ·
                  refine ⟨40611070857657614036293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216592377907507274860229 40611070857657614036293)
                  ·
                    refine ⟨7614575785810802631805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40611070857657614036293 7614575785810802631805)
                    ·
                      rfl

theorem cell22_22244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_22244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22244 prefixEnd_22244 := by exact prefixLift 22244
  have htrace : WordTrace (prefixWord ++ tailWord_22244) baseStart_22244 baseEnd_22244 := by
    simpa [prefixWord, tailWord_22244, baseEnd_22244] using wordTrace_append hprefix tailTrace_22244
  have hstable : (prefixWord ++ tailWord_22244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22244).length < 2 ^ (prefixWord ++ tailWord_22244).sum := by decide
  have hdescent : baseEnd_22244 < baseStart_22244 := by decide
  rcases family_descends (prefixWord ++ tailWord_22244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22276 : List Nat := [2, 3, 2, 2, 1, 2, 4, 6]
def baseStart_22276 : Nat := 118140960795 + 22276 * 2 ^ 59
def prefixEnd_22276 : Nat := 4983230072969 + 3 ^ 40 * 22276 * 2
def baseEnd_22276 : Nat := 847281115530376203523

theorem tailTrace_22276 : CollatzResearch.WordTrace tailWord_22276 prefixEnd_22276 847281115530376203523 := by
  unfold tailWord_22276
  simp only [CollatzResearch.WordTrace]
  refine ⟨406236233652665641511341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 541648311536887522015121 406236233652665641511341)
  ·
    refine ⟨152338587619749615566753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 406236233652665641511341 152338587619749615566753)
    ·
      refine ⟨114253940714812211675065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152338587619749615566753 114253940714812211675065)
      ·
        refine ⟨85690455536109158756299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114253940714812211675065 85690455536109158756299)
        ·
          refine ⟨128535683304163738134449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85690455536109158756299 128535683304163738134449)
          ·
            refine ⟨96401762478122803600837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128535683304163738134449 96401762478122803600837)
            ·
              refine ⟨18075330464648025675157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96401762478122803600837 18075330464648025675157)
              ·
                refine ⟨847281115530376203523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18075330464648025675157 847281115530376203523)
                ·
                  rfl

theorem cell22_22276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 6].length) (baseStart_22276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22276 prefixEnd_22276 := by exact prefixLift 22276
  have htrace : WordTrace (prefixWord ++ tailWord_22276) baseStart_22276 baseEnd_22276 := by
    simpa [prefixWord, tailWord_22276, baseEnd_22276] using wordTrace_append hprefix tailTrace_22276
  have hstable : (prefixWord ++ tailWord_22276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22276).length < 2 ^ (prefixWord ++ tailWord_22276).sum := by decide
  have hdescent : baseEnd_22276 < baseStart_22276 := by decide
  rcases family_descends (prefixWord ++ tailWord_22276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22304 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 7]
def baseStart_22304 : Nat := 118140960795 + 22304 * 2 ^ 59
def prefixEnd_22304 : Nat := 4983230072969 + 3 ^ 40 * 22304 * 2
def baseEnd_22304 : Nat := 2545038337330215377207

theorem tailTrace_22304 : CollatzResearch.WordTrace tailWord_22304 prefixEnd_22304 2545038337330215377207 := by
  unfold tailWord_22304
  simp only [CollatzResearch.WordTrace]
  refine ⟨406746855601946032520983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 542329140802594710027977 406746855601946032520983)
  ·
    refine ⟨610120283402919048781475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 406746855601946032520983 610120283402919048781475)
    ·
      refine ⟨915180425104378573172213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610120283402919048781475 915180425104378573172213)
      ·
        refine ⟨85798164853535491234895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 915180425104378573172213 85798164853535491234895)
        ·
          refine ⟨128697247280303236852343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85798164853535491234895 128697247280303236852343)
          ·
            refine ⟨193045870920454855278515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128697247280303236852343 193045870920454855278515)
            ·
              refine ⟨289568806380682282917773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193045870920454855278515 289568806380682282917773)
              ·
                refine ⟨108588302392755856094165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289568806380682282917773 108588302392755856094165)
                ·
                  refine ⟨2545038337330215377207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108588302392755856094165 2545038337330215377207)
                  ·
                    rfl

theorem cell22_22304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_22304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22304 prefixEnd_22304 := by exact prefixLift 22304
  have htrace : WordTrace (prefixWord ++ tailWord_22304) baseStart_22304 baseEnd_22304 := by
    simpa [prefixWord, tailWord_22304, baseEnd_22304] using wordTrace_append hprefix tailTrace_22304
  have hstable : (prefixWord ++ tailWord_22304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22304).length < 2 ^ (prefixWord ++ tailWord_22304).sum := by decide
  have hdescent : baseEnd_22304 < baseStart_22304 := by decide
  rcases family_descends (prefixWord ++ tailWord_22304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22308 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_22308 : Nat := 118140960795 + 22308 * 2 ^ 59
def prefixEnd_22308 : Nat := 4983230072969 + 3 ^ 40 * 22308 * 2
def baseEnd_22308 : Nat := 7636484293735969031609

theorem tailTrace_22308 : CollatzResearch.WordTrace tailWord_22308 prefixEnd_22308 7636484293735969031609 := by
  unfold tailWord_22308
  simp only [CollatzResearch.WordTrace]
  refine ⟨406819801594700374093789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 542426402126267165458385 406819801594700374093789)
  ·
    refine ⟨152557425598012640285171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 406819801594700374093789 152557425598012640285171)
    ·
      refine ⟨228836138397018960427757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152557425598012640285171 228836138397018960427757)
      ·
        refine ⟨85813551898882110160409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228836138397018960427757 85813551898882110160409)
        ·
          refine ⟨64360163924161582620307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85813551898882110160409 64360163924161582620307)
          ·
            refine ⟨96540245886242373930461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64360163924161582620307 96540245886242373930461)
            ·
              refine ⟨36202592207340890223923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96540245886242373930461 36202592207340890223923)
              ·
                refine ⟨54303888311011335335885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36202592207340890223923 54303888311011335335885)
                ·
                  refine ⟨20363958116629250750957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54303888311011335335885 20363958116629250750957)
                  ·
                    refine ⟨7636484293735969031609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20363958116629250750957 7636484293735969031609)
                    ·
                      rfl

theorem cell22_22308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_22308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22308 prefixEnd_22308 := by exact prefixLift 22308
  have htrace : WordTrace (prefixWord ++ tailWord_22308) baseStart_22308 baseEnd_22308 := by
    simpa [prefixWord, tailWord_22308, baseEnd_22308] using wordTrace_append hprefix tailTrace_22308
  have hstable : (prefixWord ++ tailWord_22308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22308).length < 2 ^ (prefixWord ++ tailWord_22308).sum := by decide
  have hdescent : baseEnd_22308 < baseStart_22308 := by decide
  rcases family_descends (prefixWord ++ tailWord_22308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22321 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 5]
def baseStart_22321 : Nat := 118140960795 + 22321 * 2 ^ 59
def prefixEnd_22321 : Nat := 4983230072969 + 3 ^ 40 * 22321 * 2
def baseEnd_22321 : Nat := 2546978153136089485523

theorem tailTrace_22321 : CollatzResearch.WordTrace tailWord_22321 prefixEnd_22321 2546978153136089485523 := by
  unfold tailWord_22321
  simp only [CollatzResearch.WordTrace]
  refine ⟨814113752142303968410817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 542742501428202645607211 814113752142303968410817)
  ·
    refine ⟨610585314106727976308113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 814113752142303968410817 610585314106727976308113)
    ·
      refine ⟨457938985580045982231085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 610585314106727976308113 457938985580045982231085)
      ·
        refine ⟨171727119592517243336657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457938985580045982231085 171727119592517243336657)
        ·
          refine ⟨128795339694387932502493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171727119592517243336657 128795339694387932502493)
          ·
            refine ⟨48298252385395474688435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128795339694387932502493 48298252385395474688435)
            ·
              refine ⟨72447378578093212032653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48298252385395474688435 72447378578093212032653)
              ·
                refine ⟨27167766966784954512245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72447378578093212032653 27167766966784954512245)
                ·
                  refine ⟨2546978153136089485523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27167766966784954512245 2546978153136089485523)
                  ·
                    rfl

theorem cell22_22321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_22321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22321 prefixEnd_22321 := by exact prefixLift 22321
  have htrace : WordTrace (prefixWord ++ tailWord_22321) baseStart_22321 baseEnd_22321 := by
    simpa [prefixWord, tailWord_22321, baseEnd_22321] using wordTrace_append hprefix tailTrace_22321
  have hstable : (prefixWord ++ tailWord_22321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22321).length < 2 ^ (prefixWord ++ tailWord_22321).sum := by decide
  have hdescent : baseEnd_22321 < baseStart_22321 := by decide
  rcases family_descends (prefixWord ++ tailWord_22321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22359 : List Nat := [1, 1, 3, 2, 6, 1, 2, 2, 1, 3]
def baseStart_22359 : Nat := 118140960795 + 22359 * 2 ^ 59
def prefixEnd_22359 : Nat := 4983230072969 + 3 ^ 40 * 22359 * 2
def baseEnd_22359 : Nat := 7653942635988836006453

theorem tailTrace_22359 : CollatzResearch.WordTrace tailWord_22359 prefixEnd_22359 7653942635988836006453 := by
  unfold tailWord_22359
  simp only [CollatzResearch.WordTrace]
  refine ⟨815499726004636458294131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 543666484003090972196087 815499726004636458294131)
  ·
    refine ⟨1223249589006954687441197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 815499726004636458294131 1223249589006954687441197)
    ·
      refine ⟨458718595877608007790449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1223249589006954687441197 458718595877608007790449)
      ·
        refine ⟨344038946908206005842837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458718595877608007790449 344038946908206005842837)
        ·
          refine ⟨16126825636322156523883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 344038946908206005842837 16126825636322156523883)
          ·
            refine ⟨24190238454483234785825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16126825636322156523883 24190238454483234785825)
            ·
              refine ⟨18142678840862426089369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24190238454483234785825 18142678840862426089369)
              ·
                refine ⟨13607009130646819567027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18142678840862426089369 13607009130646819567027)
                ·
                  refine ⟨20410513695970229350541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13607009130646819567027 20410513695970229350541)
                  ·
                    refine ⟨7653942635988836006453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20410513695970229350541 7653942635988836006453)
                    ·
                      rfl

theorem cell22_22359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_22359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22359 prefixEnd_22359 := by exact prefixLift 22359
  have htrace : WordTrace (prefixWord ++ tailWord_22359) baseStart_22359 baseEnd_22359 := by
    simpa [prefixWord, tailWord_22359, baseEnd_22359] using wordTrace_append hprefix tailTrace_22359
  have hstable : (prefixWord ++ tailWord_22359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22359).length < 2 ^ (prefixWord ++ tailWord_22359).sum := by decide
  have hdescent : baseEnd_22359 < baseStart_22359 := by decide
  rcases family_descends (prefixWord ++ tailWord_22359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22379 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 1, 6]
def baseStart_22379 : Nat := 118140960795 + 22379 * 2 ^ 59
def prefixEnd_22379 : Nat := 4983230072969 + 3 ^ 40 * 22379 * 2
def baseEnd_22379 : Nat := 7660789044715450506391

theorem tailTrace_22379 : CollatzResearch.WordTrace tailWord_22379 prefixEnd_22379 7660789044715450506391 := by
  unfold tailWord_22379
  simp only [CollatzResearch.WordTrace]
  refine ⟨816229185932179874022191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 544152790621453249348127 816229185932179874022191)
  ·
    refine ⟨1224343778898269811033287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816229185932179874022191 1224343778898269811033287)
    ·
      refine ⟨1836515668347404716549931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1224343778898269811033287 1836515668347404716549931)
      ·
        refine ⟨2754773502521107074824897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836515668347404716549931 2754773502521107074824897)
        ·
          refine ⟨2066080126890830306118673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2754773502521107074824897 2066080126890830306118673)
          ·
            refine ⟨1549560095168122729589005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2066080126890830306118673 1549560095168122729589005)
            ·
              refine ⟨581085035688046023595877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1549560095168122729589005 581085035688046023595877)
              ·
                refine ⟨108953444191508629424227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 581085035688046023595877 108953444191508629424227)
                ·
                  refine ⟨163430166287262944136341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108953444191508629424227 163430166287262944136341)
                  ·
                    refine ⟨7660789044715450506391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 163430166287262944136341 7660789044715450506391)
                    ·
                      rfl

theorem cell22_22379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_22379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22379 prefixEnd_22379 := by exact prefixLift 22379
  have htrace : WordTrace (prefixWord ++ tailWord_22379) baseStart_22379 baseEnd_22379 := by
    simpa [prefixWord, tailWord_22379, baseEnd_22379] using wordTrace_append hprefix tailTrace_22379
  have hstable : (prefixWord ++ tailWord_22379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22379).length < 2 ^ (prefixWord ++ tailWord_22379).sum := by decide
  have hdescent : baseEnd_22379 < baseStart_22379 := by decide
  rcases family_descends (prefixWord ++ tailWord_22379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22381 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_22381 : Nat := 118140960795 + 22381 * 2 ^ 59
def prefixEnd_22381 : Nat := 4983230072969 + 3 ^ 40 * 22381 * 2
def baseEnd_22381 : Nat := 7661473685588111956385

theorem tailTrace_22381 : CollatzResearch.WordTrace tailWord_22381 prefixEnd_22381 7661473685588111956385 := by
  unfold tailWord_22381
  simp only [CollatzResearch.WordTrace]
  refine ⟨816302131924934215594997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 544201421283289477063331 816302131924934215594997)
  ·
    refine ⟨76528324867962582712031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 816302131924934215594997 76528324867962582712031)
    ·
      refine ⟨114792487301943874068047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76528324867962582712031 114792487301943874068047)
      ·
        refine ⟨172188730952915811102071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114792487301943874068047 172188730952915811102071)
        ·
          refine ⟨258283096429373716653107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172188730952915811102071 258283096429373716653107)
          ·
            refine ⟨387424644644060574979661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258283096429373716653107 387424644644060574979661)
            ·
              refine ⟨145284241741522715617373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387424644644060574979661 145284241741522715617373)
              ·
                refine ⟨54481590653071018356515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145284241741522715617373 54481590653071018356515)
                ·
                  refine ⟨81722385979606527534773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54481590653071018356515 81722385979606527534773)
                  ·
                    refine ⟨7661473685588111956385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81722385979606527534773 7661473685588111956385)
                    ·
                      rfl

theorem cell22_22381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_22381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22381 prefixEnd_22381 := by exact prefixLift 22381
  have htrace : WordTrace (prefixWord ++ tailWord_22381) baseStart_22381 baseEnd_22381 := by
    simpa [prefixWord, tailWord_22381, baseEnd_22381] using wordTrace_append hprefix tailTrace_22381
  have hstable : (prefixWord ++ tailWord_22381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22381).length < 2 ^ (prefixWord ++ tailWord_22381).sum := by decide
  have hdescent : baseEnd_22381 < baseStart_22381 := by decide
  rcases family_descends (prefixWord ++ tailWord_22381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22394 : List Nat := [3, 1, 1, 1, 1, 1, 4, 10]
def baseStart_22394 : Nat := 118140960795 + 22394 * 2 ^ 59
def prefixEnd_22394 : Nat := 4983230072969 + 3 ^ 40 * 22394 * 2
def baseEnd_22394 : Nat := 851769316806712375705

theorem tailTrace_22394 : CollatzResearch.WordTrace tailWord_22394 prefixEnd_22394 851769316806712375705 := by
  unfold tailWord_22394
  simp only [CollatzResearch.WordTrace]
  refine ⟨204194070219459358954559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 544517520585224957212157 204194070219459358954559)
  ·
    refine ⟨306291105329189038431839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204194070219459358954559 306291105329189038431839)
    ·
      refine ⟨459436657993783557647759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306291105329189038431839 459436657993783557647759)
      ·
        refine ⟨689154986990675336471639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459436657993783557647759 689154986990675336471639)
        ·
          refine ⟨1033732480486013004707459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689154986990675336471639 1033732480486013004707459)
          ·
            refine ⟨1550598720729019507061189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033732480486013004707459 1550598720729019507061189)
            ·
              refine ⟨290737260136691157573973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1550598720729019507061189 290737260136691157573973)
              ·
                refine ⟨851769316806712375705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 290737260136691157573973 851769316806712375705)
                ·
                  rfl

theorem cell22_22394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_22394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22394 prefixEnd_22394 := by exact prefixLift 22394
  have htrace : WordTrace (prefixWord ++ tailWord_22394) baseStart_22394 baseEnd_22394 := by
    simpa [prefixWord, tailWord_22394, baseEnd_22394] using wordTrace_append hprefix tailTrace_22394
  have hstable : (prefixWord ++ tailWord_22394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22394).length < 2 ^ (prefixWord ++ tailWord_22394).sum := by decide
  have hdescent : baseEnd_22394 < baseStart_22394 := by decide
  rcases family_descends (prefixWord ++ tailWord_22394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22535 : List Nat := [1, 1, 4, 3, 1, 3, 1, 4, 4]
def baseStart_22535 : Nat := 118140960795 + 22535 * 2 ^ 59
def prefixEnd_22535 : Nat := 4983230072969 + 3 ^ 40 * 22535 * 2
def baseEnd_22535 : Nat := 2571397010927681201971

theorem tailTrace_22535 : CollatzResearch.WordTrace tailWord_22535 prefixEnd_22535 2571397010927681201971 := by
  unfold tailWord_22535
  simp only [CollatzResearch.WordTrace]
  refine ⟨821918973367018516701059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 547945982244679011134039 821918973367018516701059)
  ·
    refine ⟨1232878460050527775051589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 821918973367018516701059 1232878460050527775051589)
    ·
      refine ⟨231164711259473957822173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1232878460050527775051589 231164711259473957822173)
      ·
        refine ⟨86686766722302734183315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231164711259473957822173 86686766722302734183315)
        ·
          refine ⟨130030150083454101274973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86686766722302734183315 130030150083454101274973)
          ·
            refine ⟨48761306281295287978115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130030150083454101274973 48761306281295287978115)
            ·
              refine ⟨73141959421942931967173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48761306281295287978115 73141959421942931967173)
              ·
                refine ⟨13714117391614299743845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73141959421942931967173 13714117391614299743845)
                ·
                  refine ⟨2571397010927681201971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13714117391614299743845 2571397010927681201971)
                  ·
                    rfl

theorem cell22_22535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 4].length) (baseStart_22535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22535 prefixEnd_22535 := by exact prefixLift 22535
  have htrace : WordTrace (prefixWord ++ tailWord_22535) baseStart_22535 baseEnd_22535 := by
    simpa [prefixWord, tailWord_22535, baseEnd_22535] using wordTrace_append hprefix tailTrace_22535
  have hstable : (prefixWord ++ tailWord_22535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22535).length < 2 ^ (prefixWord ++ tailWord_22535).sum := by decide
  have hdescent : baseEnd_22535 < baseStart_22535 := by decide
  rcases family_descends (prefixWord ++ tailWord_22535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22563 : List Nat := [1, 1, 1, 4, 3, 1, 5, 6]
def baseStart_22563 : Nat := 118140960795 + 22563 * 2 ^ 59
def prefixEnd_22563 : Nat := 4983230072969 + 3 ^ 40 * 22563 * 2
def baseEnd_22563 : Nat := 858197333888922656203

theorem tailTrace_22563 : CollatzResearch.WordTrace tailWord_22563 prefixEnd_22563 858197333888922656203 := by
  unfold tailWord_22563
  simp only [CollatzResearch.WordTrace]
  refine ⟨822940217265579298720343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 548626811510386199146895 822940217265579298720343)
  ·
    refine ⟨1234410325898368948080515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 822940217265579298720343 1234410325898368948080515)
    ·
      refine ⟨1851615488847553422120773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234410325898368948080515 1851615488847553422120773)
      ·
        refine ⟨347177904158916266647645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1851615488847553422120773 347177904158916266647645)
        ·
          refine ⟨130191714059593599992867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347177904158916266647645 130191714059593599992867)
          ·
            refine ⟨195287571089390399989301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130191714059593599992867 195287571089390399989301)
            ·
              refine ⟨18308209789630349998997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195287571089390399989301 18308209789630349998997)
              ·
                refine ⟨858197333888922656203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18308209789630349998997 858197333888922656203)
                ·
                  rfl

theorem cell22_22563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 6].length) (baseStart_22563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22563 prefixEnd_22563 := by exact prefixLift 22563
  have htrace : WordTrace (prefixWord ++ tailWord_22563) baseStart_22563 baseEnd_22563 := by
    simpa [prefixWord, tailWord_22563, baseEnd_22563] using wordTrace_append hprefix tailTrace_22563
  have hstable : (prefixWord ++ tailWord_22563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22563).length < 2 ^ (prefixWord ++ tailWord_22563).sum := by decide
  have hdescent : baseEnd_22563 < baseStart_22563 := by decide
  rcases family_descends (prefixWord ++ tailWord_22563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22565 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_22565 : Nat := 118140960795 + 22565 * 2 ^ 59
def prefixEnd_22565 : Nat := 4983230072969 + 3 ^ 40 * 22565 * 2
def baseEnd_22565 : Nat := 7724460645872965355821

theorem tailTrace_22565 : CollatzResearch.WordTrace tailWord_22565 prefixEnd_22565 7724460645872965355821 := by
  unfold tailWord_22565
  simp only [CollatzResearch.WordTrace]
  refine ⟨823013163258333640293149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 548675442172222426862099 823013163258333640293149)
  ·
    refine ⟨308629936221875115109931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 823013163258333640293149 308629936221875115109931)
    ·
      refine ⟨462944904332812672664897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308629936221875115109931 462944904332812672664897)
      ·
        refine ⟨347208678249609504498673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462944904332812672664897 347208678249609504498673)
        ·
          refine ⟨260406508687207128374005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347208678249609504498673 260406508687207128374005)
          ·
            refine ⟨24413110189425668285063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260406508687207128374005 24413110189425668285063)
            ·
              refine ⟨36619665284138502427595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24413110189425668285063 36619665284138502427595)
              ·
                refine ⟨54929497926207753641393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36619665284138502427595 54929497926207753641393)
                ·
                  refine ⟨41197123444655815231045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54929497926207753641393 41197123444655815231045)
                  ·
                    refine ⟨7724460645872965355821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41197123444655815231045 7724460645872965355821)
                    ·
                      rfl

theorem cell22_22565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_22565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22565 prefixEnd_22565 := by exact prefixLift 22565
  have htrace : WordTrace (prefixWord ++ tailWord_22565) baseStart_22565 baseEnd_22565 := by
    simpa [prefixWord, tailWord_22565, baseEnd_22565] using wordTrace_append hprefix tailTrace_22565
  have hstable : (prefixWord ++ tailWord_22565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22565).length < 2 ^ (prefixWord ++ tailWord_22565).sum := by decide
  have hdescent : baseEnd_22565 < baseStart_22565 := by decide
  rcases family_descends (prefixWord ++ tailWord_22565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22580 : List Nat := [2, 5, 1, 2, 2, 1, 9]
def baseStart_22580 : Nat := 118140960795 + 22580 * 2 ^ 59
def prefixEnd_22580 : Nat := 4983230072969 + 3 ^ 40 * 22580 * 2
def baseEnd_22580 : Nat := 286281313052515786325

theorem tailTrace_22580 : CollatzResearch.WordTrace tailWord_22580 prefixEnd_22580 286281313052515786325 := by
  unfold tailWord_22580
  simp only [CollatzResearch.WordTrace]
  refine ⟨411780129101995601044597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 549040172135994134726129 411780129101995601044597)
  ·
    refine ⟨38604387103312087597931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 411780129101995601044597 38604387103312087597931)
    ·
      refine ⟨57906580654968131396897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38604387103312087597931 57906580654968131396897)
      ·
        refine ⟨43429935491226098547673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57906580654968131396897 43429935491226098547673)
        ·
          refine ⟨32572451618419573910755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43429935491226098547673 32572451618419573910755)
          ·
            refine ⟨48858677427629360866133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32572451618419573910755 48858677427629360866133)
            ·
              refine ⟨286281313052515786325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 48858677427629360866133 286281313052515786325)
              ·
                rfl

theorem cell22_22580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 9].length) (baseStart_22580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22580 prefixEnd_22580 := by exact prefixLift 22580
  have htrace : WordTrace (prefixWord ++ tailWord_22580) baseStart_22580 baseEnd_22580 := by
    simpa [prefixWord, tailWord_22580, baseEnd_22580] using wordTrace_append hprefix tailTrace_22580
  have hstable : (prefixWord ++ tailWord_22580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22580).length < 2 ^ (prefixWord ++ tailWord_22580).sum := by decide
  have hdescent : baseEnd_22580 < baseStart_22580 := by decide
  rcases family_descends (prefixWord ++ tailWord_22580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22584 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 2, 3]
def baseStart_22584 : Nat := 118140960795 + 22584 * 2 ^ 59
def prefixEnd_22584 : Nat := 4983230072969 + 3 ^ 40 * 22584 * 2
def baseEnd_22584 : Nat := 7730964734163249130763

theorem tailTrace_22584 : CollatzResearch.WordTrace tailWord_22584 prefixEnd_22584 7730964734163249130763 := by
  unfold tailWord_22584
  simp only [CollatzResearch.WordTrace]
  refine ⟨411853075094749942617403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 549137433459666590156537 411853075094749942617403)
  ·
    refine ⟨617779612642124913926105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 411853075094749942617403 617779612642124913926105)
    ·
      refine ⟨463334709481593685444579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 617779612642124913926105 463334709481593685444579)
      ·
        refine ⟨695002064222390528166869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463334709481593685444579 695002064222390528166869)
        ·
          refine ⟨16289110880212278003911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 695002064222390528166869 16289110880212278003911)
          ·
            refine ⟨24433666320318417005867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16289110880212278003911 24433666320318417005867)
            ·
              refine ⟨36650499480477625508801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24433666320318417005867 36650499480477625508801)
              ·
                refine ⟨27487874610358219131601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36650499480477625508801 27487874610358219131601)
                ·
                  refine ⟨20615905957768664348701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27487874610358219131601 20615905957768664348701)
                  ·
                    refine ⟨7730964734163249130763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20615905957768664348701 7730964734163249130763)
                    ·
                      rfl

theorem cell22_22584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_22584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22584 prefixEnd_22584 := by exact prefixLift 22584
  have htrace : WordTrace (prefixWord ++ tailWord_22584) baseStart_22584 baseEnd_22584 := by
    simpa [prefixWord, tailWord_22584, baseEnd_22584] using wordTrace_append hprefix tailTrace_22584
  have hstable : (prefixWord ++ tailWord_22584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22584).length < 2 ^ (prefixWord ++ tailWord_22584).sum := by decide
  have hdescent : baseEnd_22584 < baseStart_22584 := by decide
  rcases family_descends (prefixWord ++ tailWord_22584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22614 : List Nat := [5, 2, 2, 1, 1, 3, 2, 6]
def baseStart_22614 : Nat := 118140960795 + 22614 * 2 ^ 59
def prefixEnd_22614 : Nat := 4983230072969 + 3 ^ 40 * 22614 * 2
def baseEnd_22614 : Nat := 860137149694796764519

theorem tailTrace_22614 : CollatzResearch.WordTrace tailWord_22614 prefixEnd_22614 860137149694796764519 := by
  unfold tailWord_22614
  simp only [CollatzResearch.WordTrace]
  refine ⟨51550021255050938051681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 549866893387210005884597 51550021255050938051681)
  ·
    refine ⟨38662515941288203538761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51550021255050938051681 38662515941288203538761)
    ·
      refine ⟨28996886955966152654071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38662515941288203538761 28996886955966152654071)
      ·
        refine ⟨43495330433949228981107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28996886955966152654071 43495330433949228981107)
        ·
          refine ⟨65242995650923843471661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43495330433949228981107 65242995650923843471661)
          ·
            refine ⟨24466123369096441301873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65242995650923843471661 24466123369096441301873)
            ·
              refine ⟨18349592526822330976405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24466123369096441301873 18349592526822330976405)
              ·
                refine ⟨860137149694796764519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18349592526822330976405 860137149694796764519)
                ·
                  rfl

theorem cell22_22614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_22614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22614 prefixEnd_22614 := by exact prefixLift 22614
  have htrace : WordTrace (prefixWord ++ tailWord_22614) baseStart_22614 baseEnd_22614 := by
    simpa [prefixWord, tailWord_22614, baseEnd_22614] using wordTrace_append hprefix tailTrace_22614
  have hstable : (prefixWord ++ tailWord_22614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22614).length < 2 ^ (prefixWord ++ tailWord_22614).sum := by decide
  have hdescent : baseEnd_22614 < baseStart_22614 := by decide
  rcases family_descends (prefixWord ++ tailWord_22614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22629 : List Nat := [1, 3, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_22629 : Nat := 118140960795 + 22629 * 2 ^ 59
def prefixEnd_22629 : Nat := 4983230072969 + 3 ^ 40 * 22629 * 2
def baseEnd_22629 : Nat := 7746369153798131755625

theorem tailTrace_22629 : CollatzResearch.WordTrace tailWord_22629 prefixEnd_22629 7746369153798131755625 := by
  unfold tailWord_22629
  simp only [CollatzResearch.WordTrace]
  refine ⟨825347435026472570622941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 550231623350981713748627 825347435026472570622941)
  ·
    refine ⟨309505288134927213983603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 825347435026472570622941 309505288134927213983603)
    ·
      refine ⟨464257932202390820975405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309505288134927213983603 464257932202390820975405)
      ·
        refine ⟨174096724575896557865777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 464257932202390820975405 174096724575896557865777)
        ·
          refine ⟨130572543431922418399333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174096724575896557865777 130572543431922418399333)
          ·
            refine ⟨24482351893485453449875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130572543431922418399333 24482351893485453449875)
            ·
              refine ⟨36723527840228180174813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24482351893485453449875 36723527840228180174813)
              ·
                refine ⟨13771322940085567565555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36723527840228180174813 13771322940085567565555)
                ·
                  refine ⟨20656984410128351348333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13771322940085567565555 20656984410128351348333)
                  ·
                    refine ⟨7746369153798131755625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20656984410128351348333 7746369153798131755625)
                    ·
                      rfl

theorem cell22_22629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_22629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22629 prefixEnd_22629 := by exact prefixLift 22629
  have htrace : WordTrace (prefixWord ++ tailWord_22629) baseStart_22629 baseEnd_22629 := by
    simpa [prefixWord, tailWord_22629, baseEnd_22629] using wordTrace_append hprefix tailTrace_22629
  have hstable : (prefixWord ++ tailWord_22629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22629).length < 2 ^ (prefixWord ++ tailWord_22629).sum := by decide
  have hdescent : baseEnd_22629 < baseStart_22629 := by decide
  rcases family_descends (prefixWord ++ tailWord_22629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22646 : List Nat := [5, 1, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_22646 : Nat := 118140960795 + 22646 * 2 ^ 59
def prefixEnd_22646 : Nat := 4983230072969 + 3 ^ 40 * 22646 * 2
def baseEnd_22646 : Nat := 7752188601215754080573

theorem tailTrace_22646 : CollatzResearch.WordTrace tailWord_22646 prefixEnd_22646 7752188601215754080573 := by
  unfold tailWord_22646
  simp only [CollatzResearch.WordTrace]
  refine ⟨51622967247805279624487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 550644983976589649327861 51622967247805279624487)
  ·
    refine ⟨77434450871707919436731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51622967247805279624487 77434450871707919436731)
    ·
      refine ⟨116151676307561879155097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77434450871707919436731 116151676307561879155097)
      ·
        refine ⟨87113757230671409366323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116151676307561879155097 87113757230671409366323)
        ·
          refine ⟨130670635846007114049485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87113757230671409366323 130670635846007114049485)
          ·
            refine ⟨49001488442252667768557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130670635846007114049485 49001488442252667768557)
            ·
              refine ⟨18375558165844750413209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49001488442252667768557 18375558165844750413209)
              ·
                refine ⟨13781668624383562809907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18375558165844750413209 13781668624383562809907)
                ·
                  refine ⟨20672502936575344214861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13781668624383562809907 20672502936575344214861)
                  ·
                    refine ⟨7752188601215754080573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20672502936575344214861 7752188601215754080573)
                    ·
                      rfl

theorem cell22_22646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_22646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22646 prefixEnd_22646 := by exact prefixLift 22646
  have htrace : WordTrace (prefixWord ++ tailWord_22646) baseStart_22646 baseEnd_22646 := by
    simpa [prefixWord, tailWord_22646, baseEnd_22646] using wordTrace_append hprefix tailTrace_22646
  have hstable : (prefixWord ++ tailWord_22646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22646).length < 2 ^ (prefixWord ++ tailWord_22646).sum := by decide
  have hdescent : baseEnd_22646 < baseStart_22646 := by decide
  rcases family_descends (prefixWord ++ tailWord_22646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22685 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_22685 : Nat := 118140960795 + 22685 * 2 ^ 59
def prefixEnd_22685 : Nat := 4983230072969 + 3 ^ 40 * 22685 * 2
def baseEnd_22685 : Nat := 7765539098232652355453

theorem tailTrace_22685 : CollatzResearch.WordTrace tailWord_22685 prefixEnd_22685 7765539098232652355453 := by
  unfold tailWord_22685
  simp only [CollatzResearch.WordTrace]
  refine ⟨827389922823594134661509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 551593281882396089774339 827389922823594134661509)
  ·
    refine ⟨155135610529423900249033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 827389922823594134661509 155135610529423900249033)
    ·
      refine ⟨116351707897067925186775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155135610529423900249033 116351707897067925186775)
      ·
        refine ⟨174527561845601887780163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116351707897067925186775 174527561845601887780163)
        ·
          refine ⟨261791342768402831670245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174527561845601887780163 261791342768402831670245)
          ·
            refine ⟨49085876769075530938171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261791342768402831670245 49085876769075530938171)
            ·
              refine ⟨73628815153613296407257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49085876769075530938171 73628815153613296407257)
              ·
                refine ⟨55221611365209972305443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73628815153613296407257 55221611365209972305443)
                ·
                  refine ⟨82832417047814958458165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55221611365209972305443 82832417047814958458165)
                  ·
                    refine ⟨7765539098232652355453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82832417047814958458165 7765539098232652355453)
                    ·
                      rfl

theorem cell22_22685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_22685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22685 prefixEnd_22685 := by exact prefixLift 22685
  have htrace : WordTrace (prefixWord ++ tailWord_22685) baseStart_22685 baseEnd_22685 := by
    simpa [prefixWord, tailWord_22685, baseEnd_22685] using wordTrace_append hprefix tailTrace_22685
  have hstable : (prefixWord ++ tailWord_22685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22685).length < 2 ^ (prefixWord ++ tailWord_22685).sum := by decide
  have hdescent : baseEnd_22685 < baseStart_22685 := by decide
  rcases family_descends (prefixWord ++ tailWord_22685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22728 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_22728 : Nat := 118140960795 + 22728 * 2 ^ 59
def prefixEnd_22728 : Nat := 4983230072969 + 3 ^ 40 * 22728 * 2
def baseEnd_22728 : Nat := 7780258876994873530321

theorem tailTrace_22728 : CollatzResearch.WordTrace tailWord_22728 prefixEnd_22728 7780258876994873530321 := by
  unfold tailWord_22728
  simp only [CollatzResearch.WordTrace]
  refine ⟨414479130833906239238419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 552638841111874985651225 414479130833906239238419)
  ·
    refine ⟨621718696250859358857629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414479130833906239238419 621718696250859358857629)
    ·
      refine ⟨233144511094072259571611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 621718696250859358857629 233144511094072259571611)
      ·
        refine ⟨349716766641108389357417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233144511094072259571611 349716766641108389357417)
        ·
          refine ⟨262287574980831292018063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349716766641108389357417 262287574980831292018063)
          ·
            refine ⟨393431362471246938027095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262287574980831292018063 393431362471246938027095)
            ·
              refine ⟨590147043706870407040643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393431362471246938027095 590147043706870407040643)
              ·
                refine ⟨885220565560305610560965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590147043706870407040643 885220565560305610560965)
                ·
                  refine ⟨165978856042557301980181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885220565560305610560965 165978856042557301980181)
                  ·
                    refine ⟨7780258876994873530321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 165978856042557301980181 7780258876994873530321)
                    ·
                      rfl

theorem cell22_22728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_22728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22728 prefixEnd_22728 := by exact prefixLift 22728
  have htrace : WordTrace (prefixWord ++ tailWord_22728) baseStart_22728 baseEnd_22728 := by
    simpa [prefixWord, tailWord_22728, baseEnd_22728] using wordTrace_append hprefix tailTrace_22728
  have hstable : (prefixWord ++ tailWord_22728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22728).length < 2 ^ (prefixWord ++ tailWord_22728).sum := by decide
  have hdescent : baseEnd_22728 < baseStart_22728 := by decide
  rcases family_descends (prefixWord ++ tailWord_22728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22743 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 7]
def baseStart_22743 : Nat := 118140960795 + 22743 * 2 ^ 59
def prefixEnd_22743 : Nat := 4983230072969 + 3 ^ 40 * 22743 * 2
def baseEnd_22743 : Nat := 2595131227846611468425

theorem tailTrace_22743 : CollatzResearch.WordTrace tailWord_22743 prefixEnd_22743 2595131227846611468425 := by
  unfold tailWord_22743
  simp only [CollatzResearch.WordTrace]
  refine ⟨829505356613470040272883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 553003571075646693515255 829505356613470040272883)
  ·
    refine ⟨1244258034920205060409325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829505356613470040272883 1244258034920205060409325)
    ·
      refine ⟨466596763095076897653497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1244258034920205060409325 466596763095076897653497)
      ·
        refine ⟨349947572321307673240123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466596763095076897653497 349947572321307673240123)
        ·
          refine ⟨524921358481961509860185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349947572321307673240123 524921358481961509860185)
          ·
            refine ⟨393691018861471132395139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524921358481961509860185 393691018861471132395139)
            ·
              refine ⟨590536528292206698592709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393691018861471132395139 590536528292206698592709)
              ·
                refine ⟨110725599054788755986133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590536528292206698592709 110725599054788755986133)
                ·
                  refine ⟨2595131227846611468425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110725599054788755986133 2595131227846611468425)
                  ·
                    rfl

theorem cell22_22743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 7].length) (baseStart_22743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22743 prefixEnd_22743 := by exact prefixLift 22743
  have htrace : WordTrace (prefixWord ++ tailWord_22743) baseStart_22743 baseEnd_22743 := by
    simpa [prefixWord, tailWord_22743, baseEnd_22743] using wordTrace_append hprefix tailTrace_22743
  have hstable : (prefixWord ++ tailWord_22743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22743).length < 2 ^ (prefixWord ++ tailWord_22743).sum := by decide
  have hdescent : baseEnd_22743 < baseStart_22743 := by decide
  rcases family_descends (prefixWord ++ tailWord_22743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22747 : List Nat := [1, 1, 1, 1, 1, 1, 1, 11, 1, 3]
def baseStart_22747 : Nat := 118140960795 + 22747 * 2 ^ 59
def prefixEnd_22747 : Nat := 4983230072969 + 3 ^ 40 * 22747 * 2
def baseEnd_22747 : Nat := 7786762965285157305263

theorem tailTrace_22747 : CollatzResearch.WordTrace tailWord_22747 prefixEnd_22747 7786762965285157305263 := by
  unfold tailWord_22747
  simp only [CollatzResearch.WordTrace]
  refine ⟨829651248598978723418495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 553100832399319148945663 829651248598978723418495)
  ·
    refine ⟨1244476872898468085127743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829651248598978723418495 1244476872898468085127743)
    ·
      refine ⟨1866715309347702127691615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244476872898468085127743 1866715309347702127691615)
      ·
        refine ⟨2800072964021553191537423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866715309347702127691615 2800072964021553191537423)
        ·
          refine ⟨4200109446032329787306135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800072964021553191537423 4200109446032329787306135)
          ·
            refine ⟨6300164169048494680959203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200109446032329787306135 6300164169048494680959203)
            ·
              refine ⟨9450246253572742021438805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6300164169048494680959203 9450246253572742021438805)
              ·
                refine ⟨13843134160506946320467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 9450246253572742021438805 13843134160506946320467)
                ·
                  refine ⟨20764701240760419480701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13843134160506946320467 20764701240760419480701)
                  ·
                    refine ⟨7786762965285157305263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20764701240760419480701 7786762965285157305263)
                    ·
                      rfl

theorem cell22_22747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 1, 3].length) (baseStart_22747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22747 prefixEnd_22747 := by exact prefixLift 22747
  have htrace : WordTrace (prefixWord ++ tailWord_22747) baseStart_22747 baseEnd_22747 := by
    simpa [prefixWord, tailWord_22747, baseEnd_22747] using wordTrace_append hprefix tailTrace_22747
  have hstable : (prefixWord ++ tailWord_22747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22747).length < 2 ^ (prefixWord ++ tailWord_22747).sum := by decide
  have hdescent : baseEnd_22747 < baseStart_22747 := by decide
  rcases family_descends (prefixWord ++ tailWord_22747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22760 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 7]
def baseStart_22760 : Nat := 118140960795 + 22760 * 2 ^ 59
def prefixEnd_22760 : Nat := 4983230072969 + 3 ^ 40 * 22760 * 2
def baseEnd_22760 : Nat := 2597071043652485576741

theorem tailTrace_22760 : CollatzResearch.WordTrace tailWord_22760 prefixEnd_22760 2597071043652485576741 := by
  unfold tailWord_22760
  simp only [CollatzResearch.WordTrace]
  refine ⟨415062698775940971820867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 553416931701254629094489 415062698775940971820867)
  ·
    refine ⟨622594048163911457731301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 415062698775940971820867 622594048163911457731301)
    ·
      refine ⟨116736384030733398324619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 622594048163911457731301 116736384030733398324619)
      ·
        refine ⟨175104576046100097486929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116736384030733398324619 175104576046100097486929)
        ·
          refine ⟨131328432034575073115197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175104576046100097486929 131328432034575073115197)
          ·
            refine ⟨49248162012965652418199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131328432034575073115197 49248162012965652418199)
            ·
              refine ⟨73872243019448478627299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49248162012965652418199 73872243019448478627299)
              ·
                refine ⟨110808364529172717940949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73872243019448478627299 110808364529172717940949)
                ·
                  refine ⟨2597071043652485576741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110808364529172717940949 2597071043652485576741)
                  ·
                    rfl

theorem cell22_22760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_22760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22760 prefixEnd_22760 := by exact prefixLift 22760
  have htrace : WordTrace (prefixWord ++ tailWord_22760) baseStart_22760 baseEnd_22760 := by
    simpa [prefixWord, tailWord_22760, baseEnd_22760] using wordTrace_append hprefix tailTrace_22760
  have hstable : (prefixWord ++ tailWord_22760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22760).length < 2 ^ (prefixWord ++ tailWord_22760).sum := by decide
  have hdescent : baseEnd_22760 < baseStart_22760 := by decide
  rcases family_descends (prefixWord ++ tailWord_22760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22807 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 1, 4]
def baseStart_22807 : Nat := 118140960795 + 22807 * 2 ^ 59
def prefixEnd_22807 : Nat := 4983230072969 + 3 ^ 40 * 22807 * 2
def baseEnd_22807 : Nat := 7807302191465000805079

theorem tailTrace_22807 : CollatzResearch.WordTrace tailWord_22807 prefixEnd_22807 7807302191465000805079 := by
  unfold tailWord_22807
  simp only [CollatzResearch.WordTrace]
  refine ⟨831839628381608970602675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 554559752254405980401783 831839628381608970602675)
  ·
    refine ⟨1247759442572413455904013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831839628381608970602675 1247759442572413455904013)
    ·
      refine ⟨467909790964655045964005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1247759442572413455904013 467909790964655045964005)
      ·
        refine ⟨87733085805872821118251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 467909790964655045964005 87733085805872821118251)
        ·
          refine ⟨131599628708809231677377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87733085805872821118251 131599628708809231677377)
          ·
            refine ⟨98699721531606923758033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131599628708809231677377 98699721531606923758033)
            ·
              refine ⟨74024791148705192818525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98699721531606923758033 74024791148705192818525)
              ·
                refine ⟨27759296680764447306947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74024791148705192818525 27759296680764447306947)
                ·
                  refine ⟨41638945021146670960421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27759296680764447306947 41638945021146670960421)
                  ·
                    refine ⟨7807302191465000805079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41638945021146670960421 7807302191465000805079)
                    ·
                      rfl

theorem cell22_22807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_22807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22807 prefixEnd_22807 := by exact prefixLift 22807
  have htrace : WordTrace (prefixWord ++ tailWord_22807) baseStart_22807 baseEnd_22807 := by
    simpa [prefixWord, tailWord_22807, baseEnd_22807] using wordTrace_append hprefix tailTrace_22807
  have hstable : (prefixWord ++ tailWord_22807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22807).length < 2 ^ (prefixWord ++ tailWord_22807).sum := by decide
  have hdescent : baseEnd_22807 < baseStart_22807 := by decide
  rcases family_descends (prefixWord ++ tailWord_22807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22835 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 4, 4]
def baseStart_22835 : Nat := 118140960795 + 22835 * 2 ^ 59
def prefixEnd_22835 : Nat := 4983230072969 + 3 ^ 40 * 22835 * 2
def baseEnd_22835 : Nat := 7816887163682261104993

theorem tailTrace_22835 : CollatzResearch.WordTrace tailWord_22835 prefixEnd_22835 7816887163682261104993 := by
  unfold tailWord_22835
  simp only [CollatzResearch.WordTrace]
  refine ⟨832860872280169752621959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 555240581520113168414639 832860872280169752621959)
  ·
    refine ⟨1249291308420254628932939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832860872280169752621959 1249291308420254628932939)
    ·
      refine ⟨1873936962630381943399409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249291308420254628932939 1873936962630381943399409)
      ·
        refine ⟨1405452721972786457549557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1873936962630381943399409 1405452721972786457549557)
        ·
          refine ⟨131761192684948730395271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1405452721972786457549557 131761192684948730395271)
          ·
            refine ⟨197641789027423095592907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131761192684948730395271 197641789027423095592907)
            ·
              refine ⟨296462683541134643389361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197641789027423095592907 296462683541134643389361)
              ·
                refine ⟨222347012655850982542021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296462683541134643389361 222347012655850982542021)
                ·
                  refine ⟨41690064872972059226629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222347012655850982542021 41690064872972059226629)
                  ·
                    refine ⟨7816887163682261104993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41690064872972059226629 7816887163682261104993)
                    ·
                      rfl

theorem cell22_22835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_22835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22835 prefixEnd_22835 := by exact prefixLift 22835
  have htrace : WordTrace (prefixWord ++ tailWord_22835) baseStart_22835 baseEnd_22835 := by
    simpa [prefixWord, tailWord_22835, baseEnd_22835] using wordTrace_append hprefix tailTrace_22835
  have hstable : (prefixWord ++ tailWord_22835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22835).length < 2 ^ (prefixWord ++ tailWord_22835).sum := by decide
  have hdescent : baseEnd_22835 < baseStart_22835 := by decide
  rcases family_descends (prefixWord ++ tailWord_22835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22916 : List Nat := [2, 3, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_22916 : Nat := 118140960795 + 22916 * 2 ^ 59
def prefixEnd_22916 : Nat := 4983230072969 + 3 ^ 40 * 22916 * 2
def baseEnd_22916 : Nat := 7844615119025049829745

theorem tailTrace_22916 : CollatzResearch.WordTrace tailWord_22916 prefixEnd_22916 7844615119025049829745 := by
  unfold tailWord_22916
  simp only [CollatzResearch.WordTrace]
  refine ⟨417907592493360293160301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 557210123324480390880401 417907592493360293160301)
  ·
    refine ⟨156715347185010109935113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 417907592493360293160301 156715347185010109935113)
    ·
      refine ⟨117536510388757582451335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156715347185010109935113 117536510388757582451335)
      ·
        refine ⟨176304765583136373677003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117536510388757582451335 176304765583136373677003)
        ·
          refine ⟨264457148374704560515505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176304765583136373677003 264457148374704560515505)
          ·
            refine ⟨198342861281028420386629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264457148374704560515505 198342861281028420386629)
            ·
              refine ⟨37189286490192828822493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198342861281028420386629 37189286490192828822493)
              ·
                refine ⟨13945982433822310808435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37189286490192828822493 13945982433822310808435)
                ·
                  refine ⟨20918973650733466212653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13945982433822310808435 20918973650733466212653)
                  ·
                    refine ⟨7844615119025049829745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20918973650733466212653 7844615119025049829745)
                    ·
                      rfl

theorem cell22_22916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_22916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22916 prefixEnd_22916 := by exact prefixLift 22916
  have htrace : WordTrace (prefixWord ++ tailWord_22916) baseStart_22916 baseEnd_22916 := by
    simpa [prefixWord, tailWord_22916, baseEnd_22916] using wordTrace_append hprefix tailTrace_22916
  have hstable : (prefixWord ++ tailWord_22916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22916).length < 2 ^ (prefixWord ++ tailWord_22916).sum := by decide
  have hdescent : baseEnd_22916 < baseStart_22916 := by decide
  rcases family_descends (prefixWord ++ tailWord_22916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22985 : List Nat := [1, 2, 1, 1, 2, 1, 14]
def baseStart_22985 : Nat := 118140960795 + 22985 * 2 ^ 59
def prefixEnd_22985 : Nat := 4983230072969 + 3 ^ 40 * 22985 * 2
def baseEnd_22985 : Nat := 291416119597476661279

theorem tailTrace_22985 : CollatzResearch.WordTrace tailWord_22985 prefixEnd_22985 291416119597476661279 := by
  unfold tailWord_22985
  simp only [CollatzResearch.WordTrace]
  refine ⟨838331821736745370582409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 558887881157830247054939 838331821736745370582409)
  ·
    refine ⟨628748866302559027936807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 838331821736745370582409 628748866302559027936807)
    ·
      refine ⟨943123299453838541905211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628748866302559027936807 943123299453838541905211)
      ·
        refine ⟨1414684949180757812857817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943123299453838541905211 1414684949180757812857817)
        ·
          refine ⟨1061013711885568359643363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414684949180757812857817 1061013711885568359643363)
          ·
            refine ⟨1591520567828352539465045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061013711885568359643363 1591520567828352539465045)
            ·
              refine ⟨291416119597476661279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 1591520567828352539465045 291416119597476661279)
              ·
                rfl

theorem cell22_22985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 14].length) (baseStart_22985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_22985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_22985 prefixEnd_22985 := by exact prefixLift 22985
  have htrace : WordTrace (prefixWord ++ tailWord_22985) baseStart_22985 baseEnd_22985 := by
    simpa [prefixWord, tailWord_22985, baseEnd_22985] using wordTrace_append hprefix tailTrace_22985
  have hstable : (prefixWord ++ tailWord_22985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22985).length < 2 ^ (prefixWord ++ tailWord_22985).sum := by decide
  have hdescent : baseEnd_22985 < baseStart_22985 := by decide
  rcases family_descends (prefixWord ++ tailWord_22985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23002 : List Nat := [3, 1, 1, 2, 3, 1, 4, 7]
def baseStart_23002 : Nat := 118140960795 + 23002 * 2 ^ 59
def prefixEnd_23002 : Nat := 4983230072969 + 3 ^ 40 * 23002 * 2
def baseEnd_23002 : Nat := 874894964061054686609

theorem tailTrace_23002 : CollatzResearch.WordTrace tailWord_23002 prefixEnd_23002 874894964061054686609 := by
  unfold tailWord_23002
  simp only [CollatzResearch.WordTrace]
  refine ⟨209737965668789318487815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 559301241783438182634173 209737965668789318487815)
  ·
    refine ⟨314606948503183977731723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209737965668789318487815 314606948503183977731723)
    ·
      refine ⟨471910422754775966597585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314606948503183977731723 471910422754775966597585)
      ·
        refine ⟨353932817066081974948189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471910422754775966597585 353932817066081974948189)
        ·
          refine ⟨132724806399780740605571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353932817066081974948189 132724806399780740605571)
          ·
            refine ⟨199087209599671110908357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132724806399780740605571 199087209599671110908357)
            ·
              refine ⟨37328851799938333295317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199087209599671110908357 37328851799938333295317)
              ·
                refine ⟨874894964061054686609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37328851799938333295317 874894964061054686609)
                ·
                  rfl

theorem cell22_23002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_23002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23002 prefixEnd_23002 := by exact prefixLift 23002
  have htrace : WordTrace (prefixWord ++ tailWord_23002) baseStart_23002 baseEnd_23002 := by
    simpa [prefixWord, tailWord_23002, baseEnd_23002] using wordTrace_append hprefix tailTrace_23002
  have hstable : (prefixWord ++ tailWord_23002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23002).length < 2 ^ (prefixWord ++ tailWord_23002).sum := by decide
  have hdescent : baseEnd_23002 < baseStart_23002 := by decide
  rcases family_descends (prefixWord ++ tailWord_23002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23010 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_23010 : Nat := 118140960795 + 23010 * 2 ^ 59
def prefixEnd_23010 : Nat := 4983230072969 + 3 ^ 40 * 23010 * 2
def baseEnd_23010 : Nat := 7876793240040137979457

theorem tailTrace_23010 : CollatzResearch.WordTrace tailWord_23010 prefixEnd_23010 7876793240040137979457 := by
  unfold tailWord_23010
  simp only [CollatzResearch.WordTrace]
  refine ⟨209810911661543660060621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 559495764430783093494989 209810911661543660060621)
  ·
    refine ⟨78679091873078872522733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209810911661543660060621 78679091873078872522733)
    ·
      refine ⟨29504659452404577196025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78679091873078872522733 29504659452404577196025)
      ·
        refine ⟨22128494589303432897019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29504659452404577196025 22128494589303432897019)
        ·
          refine ⟨33192741883955149345529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22128494589303432897019 33192741883955149345529)
          ·
            refine ⟨24894556412966362009147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33192741883955149345529 24894556412966362009147)
            ·
              refine ⟨37341834619449543013721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24894556412966362009147 37341834619449543013721)
              ·
                refine ⟨28006375964587157260291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37341834619449543013721 28006375964587157260291)
                ·
                  refine ⟨42009563946880735890437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28006375964587157260291 42009563946880735890437)
                  ·
                    refine ⟨7876793240040137979457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42009563946880735890437 7876793240040137979457)
                    ·
                      rfl

theorem cell22_23010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_23010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23010 prefixEnd_23010 := by exact prefixLift 23010
  have htrace : WordTrace (prefixWord ++ tailWord_23010) baseStart_23010 baseEnd_23010 := by
    simpa [prefixWord, tailWord_23010, baseEnd_23010] using wordTrace_append hprefix tailTrace_23010
  have hstable : (prefixWord ++ tailWord_23010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23010).length < 2 ^ (prefixWord ++ tailWord_23010).sum := by decide
  have hdescent : baseEnd_23010 < baseStart_23010 := by decide
  rcases family_descends (prefixWord ++ tailWord_23010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23021 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_23021 : Nat := 118140960795 + 23021 * 2 ^ 59
def prefixEnd_23021 : Nat := 4983230072969 + 3 ^ 40 * 23021 * 2
def baseEnd_23021 : Nat := 7880558764839775954423

theorem tailTrace_23021 : CollatzResearch.WordTrace tailWord_23021 prefixEnd_23021 7880558764839775954423 := by
  unfold tailWord_23021
  simp only [CollatzResearch.WordTrace]
  refine ⟨839644849606323518892917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 559763233070882345928611 839644849606323518892917)
  ·
    refine ⟨78716704650592829896211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 839644849606323518892917 78716704650592829896211)
    ·
      refine ⟨118075056975889244844317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78716704650592829896211 118075056975889244844317)
      ·
        refine ⟨44278146365958466816619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118075056975889244844317 44278146365958466816619)
        ·
          refine ⟨66417219548937700224929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44278146365958466816619 66417219548937700224929)
          ·
            refine ⟨49812914661703275168697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66417219548937700224929 49812914661703275168697)
            ·
              refine ⟨37359685996277456376523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49812914661703275168697 37359685996277456376523)
              ·
                refine ⟨56039528994416184564785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37359685996277456376523 56039528994416184564785)
                ·
                  refine ⟨42029646745812138423589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56039528994416184564785 42029646745812138423589)
                  ·
                    refine ⟨7880558764839775954423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42029646745812138423589 7880558764839775954423)
                    ·
                      rfl

theorem cell22_23021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_23021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23021 prefixEnd_23021 := by exact prefixLift 23021
  have htrace : WordTrace (prefixWord ++ tailWord_23021) baseStart_23021 baseEnd_23021 := by
    simpa [prefixWord, tailWord_23021, baseEnd_23021] using wordTrace_append hprefix tailTrace_23021
  have hstable : (prefixWord ++ tailWord_23021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23021).length < 2 ^ (prefixWord ++ tailWord_23021).sum := by decide
  have hdescent : baseEnd_23021 < baseStart_23021 := by decide
  rcases family_descends (prefixWord ++ tailWord_23021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23042 : List Nat := [3, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_23042 : Nat := 118140960795 + 23042 * 2 ^ 59
def prefixEnd_23042 : Nat := 4983230072969 + 3 ^ 40 * 23042 * 2
def baseEnd_23042 : Nat := 2629249164667573726453

theorem tailTrace_23042 : CollatzResearch.WordTrace tailWord_23042 prefixEnd_23042 2629249164667573726453 := by
  unfold tailWord_23042
  simp only [CollatzResearch.WordTrace]
  refine ⟨210102695632561026351845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 560273855020162736938253 210102695632561026351845)
  ·
    refine ⟨39394255431105192440971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210102695632561026351845 39394255431105192440971)
    ·
      refine ⟨59091383146657788661457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39394255431105192440971 59091383146657788661457)
      ·
        refine ⟨44318537359993341496093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59091383146657788661457 44318537359993341496093)
        ·
          refine ⟨16619451509997503061035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44318537359993341496093 16619451509997503061035)
          ·
            refine ⟨24929177264996254591553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16619451509997503061035 24929177264996254591553)
            ·
              refine ⟨18696882948747190943665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24929177264996254591553 18696882948747190943665)
              ·
                refine ⟨14022662211560393207749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18696882948747190943665 14022662211560393207749)
                ·
                  refine ⟨2629249164667573726453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14022662211560393207749 2629249164667573726453)
                  ·
                    rfl

theorem cell22_23042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_23042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23042 prefixEnd_23042 := by exact prefixLift 23042
  have htrace : WordTrace (prefixWord ++ tailWord_23042) baseStart_23042 baseEnd_23042 := by
    simpa [prefixWord, tailWord_23042, baseEnd_23042] using wordTrace_append hprefix tailTrace_23042
  have hstable : (prefixWord ++ tailWord_23042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23042).length < 2 ^ (prefixWord ++ tailWord_23042).sum := by decide
  have hdescent : baseEnd_23042 < baseStart_23042 := by decide
  rcases family_descends (prefixWord ++ tailWord_23042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23053 : List Nat := [1, 7, 1, 1, 1, 3, 1, 7]
def baseStart_23053 : Nat := 118140960795 + 23053 * 2 ^ 59
def prefixEnd_23053 : Nat := 4983230072969 + 3 ^ 40 * 23053 * 2
def baseEnd_23053 : Nat := 876834779866928794925

theorem tailTrace_23053 : CollatzResearch.WordTrace tailWord_23053 prefixEnd_23053 876834779866928794925 := by
  unfold tailWord_23053
  simp only [CollatzResearch.WordTrace]
  refine ⟨840811985490392984057813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 560541323660261989371875 840811985490392984057813)
  ·
    refine ⟨19706530909931085563855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 840811985490392984057813 19706530909931085563855)
    ·
      refine ⟨29559796364896628345783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19706530909931085563855 29559796364896628345783)
      ·
        refine ⟨44339694547344942518675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29559796364896628345783 44339694547344942518675)
        ·
          refine ⟨66509541821017413778013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44339694547344942518675 66509541821017413778013)
          ·
            refine ⟨24941078182881530166755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66509541821017413778013 24941078182881530166755)
            ·
              refine ⟨37411617274322295250133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24941078182881530166755 37411617274322295250133)
              ·
                refine ⟨876834779866928794925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37411617274322295250133 876834779866928794925)
                ·
                  rfl

theorem cell22_23053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 7].length) (baseStart_23053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23053 prefixEnd_23053 := by exact prefixLift 23053
  have htrace : WordTrace (prefixWord ++ tailWord_23053) baseStart_23053 baseEnd_23053 := by
    simpa [prefixWord, tailWord_23053, baseEnd_23053] using wordTrace_append hprefix tailTrace_23053
  have hstable : (prefixWord ++ tailWord_23053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23053).length < 2 ^ (prefixWord ++ tailWord_23053).sum := by decide
  have hdescent : baseEnd_23053 < baseStart_23053 := by decide
  rcases family_descends (prefixWord ++ tailWord_23053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23064 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 5]
def baseStart_23064 : Nat := 118140960795 + 23064 * 2 ^ 59
def prefixEnd_23064 : Nat := 4983230072969 + 3 ^ 40 * 23064 * 2
def baseEnd_23064 : Nat := 2631759514533999043097

theorem tailTrace_23064 : CollatzResearch.WordTrace tailWord_23064 prefixEnd_23064 2631759514533999043097 := by
  unfold tailWord_23064
  simp only [CollatzResearch.WordTrace]
  refine ⟨420606594225270931354123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 560808792300361241805497 420606594225270931354123)
  ·
    refine ⟨630909891337906397031185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 420606594225270931354123 630909891337906397031185)
    ·
      refine ⟨473182418503429797773389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630909891337906397031185 473182418503429797773389)
      ·
        refine ⟨177443406938786174165021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473182418503429797773389 177443406938786174165021)
        ·
          refine ⟨66541277602044815311883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177443406938786174165021 66541277602044815311883)
          ·
            refine ⟨99811916403067222967825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66541277602044815311883 99811916403067222967825)
            ·
              refine ⟨74858937302300417225869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99811916403067222967825 74858937302300417225869)
              ·
                refine ⟨28072101488362656459701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74858937302300417225869 28072101488362656459701)
                ·
                  refine ⟨2631759514533999043097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28072101488362656459701 2631759514533999043097)
                  ·
                    rfl

theorem cell22_23064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_23064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23064 prefixEnd_23064 := by exact prefixLift 23064
  have htrace : WordTrace (prefixWord ++ tailWord_23064) baseStart_23064 baseEnd_23064 := by
    simpa [prefixWord, tailWord_23064, baseEnd_23064] using wordTrace_append hprefix tailTrace_23064
  have hstable : (prefixWord ++ tailWord_23064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23064).length < 2 ^ (prefixWord ++ tailWord_23064).sum := by decide
  have hdescent : baseEnd_23064 < baseStart_23064 := by decide
  rcases family_descends (prefixWord ++ tailWord_23064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23107 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 3, 5]
def baseStart_23107 : Nat := 118140960795 + 23107 * 2 ^ 59
def prefixEnd_23107 : Nat := 4983230072969 + 3 ^ 40 * 23107 * 2
def baseEnd_23107 : Nat := 7909998322364218304159

theorem tailTrace_23107 : CollatzResearch.WordTrace tailWord_23107 prefixEnd_23107 7909998322364218304159 := by
  unfold tailWord_23107
  simp only [CollatzResearch.WordTrace]
  refine ⟨842781527294760206523575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 561854351529840137682383 842781527294760206523575)
  ·
    refine ⟨1264172290942140309785363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 842781527294760206523575 1264172290942140309785363)
    ·
      refine ⟨1896258436413210464678045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264172290942140309785363 1896258436413210464678045)
      ·
        refine ⟨711096913654953924254267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1896258436413210464678045 711096913654953924254267)
        ·
          refine ⟨1066645370482430886381401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711096913654953924254267 1066645370482430886381401)
          ·
            refine ⟨799984027861823164786051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066645370482430886381401 799984027861823164786051)
            ·
              refine ⟨1199976041792734747179077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799984027861823164786051 1199976041792734747179077)
              ·
                refine ⟨224995507836137765096077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1199976041792734747179077 224995507836137765096077)
                ·
                  refine ⟨84373315438551661911029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224995507836137765096077 84373315438551661911029)
                  ·
                    refine ⟨7909998322364218304159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84373315438551661911029 7909998322364218304159)
                    ·
                      rfl

theorem cell22_23107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_23107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23107 prefixEnd_23107 := by exact prefixLift 23107
  have htrace : WordTrace (prefixWord ++ tailWord_23107) baseStart_23107 baseEnd_23107 := by
    simpa [prefixWord, tailWord_23107, baseEnd_23107] using wordTrace_append hprefix tailTrace_23107
  have hstable : (prefixWord ++ tailWord_23107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23107).length < 2 ^ (prefixWord ++ tailWord_23107).sum := by decide
  have hdescent : baseEnd_23107 < baseStart_23107 := by decide
  rcases family_descends (prefixWord ++ tailWord_23107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23109 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 6]
def baseStart_23109 : Nat := 118140960795 + 23109 * 2 ^ 59
def prefixEnd_23109 : Nat := 4983230072969 + 3 ^ 40 * 23109 * 2
def baseEnd_23109 : Nat := 2636894321078959918051

theorem tailTrace_23109 : CollatzResearch.WordTrace tailWord_23109 prefixEnd_23109 2636894321078959918051 := by
  unfold tailWord_23109
  simp only [CollatzResearch.WordTrace]
  refine ⟨842854473287514548096381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 561902982191676365397587 842854473287514548096381)
  ·
    refine ⟨316070427482817955536143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 842854473287514548096381 316070427482817955536143)
    ·
      refine ⟨474105641224226933304215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316070427482817955536143 474105641224226933304215)
      ·
        refine ⟨711158461836340399956323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474105641224226933304215 711158461836340399956323)
        ·
          refine ⟨1066737692754510599934485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711158461836340399956323 1066737692754510599934485)
          ·
            refine ⟨50003329347867684371929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1066737692754510599934485 50003329347867684371929)
            ·
              refine ⟨37502497010900763278947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50003329347867684371929 37502497010900763278947)
              ·
                refine ⟨56253745516351144918421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37502497010900763278947 56253745516351144918421)
                ·
                  refine ⟨2636894321078959918051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56253745516351144918421 2636894321078959918051)
                  ·
                    rfl

theorem cell22_23109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_23109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23109 prefixEnd_23109 := by exact prefixLift 23109
  have htrace : WordTrace (prefixWord ++ tailWord_23109) baseStart_23109 baseEnd_23109 := by
    simpa [prefixWord, tailWord_23109, baseEnd_23109] using wordTrace_append hprefix tailTrace_23109
  have hstable : (prefixWord ++ tailWord_23109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23109).length < 2 ^ (prefixWord ++ tailWord_23109).sum := by decide
  have hdescent : baseEnd_23109 < baseStart_23109 := by decide
  rcases family_descends (prefixWord ++ tailWord_23109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23139 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 2, 4]
def baseStart_23139 : Nat := 118140960795 + 23139 * 2 ^ 59
def prefixEnd_23139 : Nat := 4983230072969 + 3 ^ 40 * 23139 * 2
def baseEnd_23139 : Nat := 7920952576326801504061

theorem tailTrace_23139 : CollatzResearch.WordTrace tailWord_23139 prefixEnd_23139 7920952576326801504061 := by
  unfold tailWord_23139
  simp only [CollatzResearch.WordTrace]
  refine ⟨843948663178829671688471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 562632442119219781125647 843948663178829671688471)
  ·
    refine ⟨1265922994768244507532707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 843948663178829671688471 1265922994768244507532707)
    ·
      refine ⟨1898884492152366761299061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1265922994768244507532707 1898884492152366761299061)
      ·
        refine ⟨178020421139284383871787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1898884492152366761299061 178020421139284383871787)
        ·
          refine ⟨267030631708926575807681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178020421139284383871787 267030631708926575807681)
          ·
            refine ⟨200272973781694931855761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267030631708926575807681 200272973781694931855761)
            ·
              refine ⟨150204730336271198891821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200272973781694931855761 150204730336271198891821)
              ·
                refine ⟨56326773876101699584433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150204730336271198891821 56326773876101699584433)
                ·
                  refine ⟨42245080407076274688325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56326773876101699584433 42245080407076274688325)
                  ·
                    refine ⟨7920952576326801504061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42245080407076274688325 7920952576326801504061)
                    ·
                      rfl

theorem cell22_23139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_23139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23139 prefixEnd_23139 := by exact prefixLift 23139
  have htrace : WordTrace (prefixWord ++ tailWord_23139) baseStart_23139 baseEnd_23139 := by
    simpa [prefixWord, tailWord_23139, baseEnd_23139] using wordTrace_append hprefix tailTrace_23139
  have hstable : (prefixWord ++ tailWord_23139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23139).length < 2 ^ (prefixWord ++ tailWord_23139).sum := by decide
  have hdescent : baseEnd_23139 < baseStart_23139 := by decide
  rcases family_descends (prefixWord ++ tailWord_23139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23246 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_23246 : Nat := 118140960795 + 23246 * 2 ^ 59
def prefixEnd_23246 : Nat := 4983230072969 + 3 ^ 40 * 23246 * 2
def baseEnd_23246 : Nat := 7957580863014189078733

theorem tailTrace_23246 : CollatzResearch.WordTrace tailWord_23246 prefixEnd_23246 7957580863014189078733 := by
  unfold tailWord_23246
  simp only [CollatzResearch.WordTrace]
  refine ⟨105981409223898368229199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 565234182527457963889061 105981409223898368229199)
  ·
    refine ⟨158972113835847552343799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105981409223898368229199 158972113835847552343799)
    ·
      refine ⟨238458170753771328515699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158972113835847552343799 238458170753771328515699)
      ·
        refine ⟨357687256130656992773549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238458170753771328515699 357687256130656992773549)
        ·
          refine ⟨134132721048996372290081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357687256130656992773549 134132721048996372290081)
          ·
            refine ⟨100599540786747279217561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134132721048996372290081 100599540786747279217561)
            ·
              refine ⟨75449655590060459413171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100599540786747279217561 75449655590060459413171)
              ·
                refine ⟨113174483385090689119757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75449655590060459413171 113174483385090689119757)
                ·
                  refine ⟨42440431269409008419909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113174483385090689119757 42440431269409008419909)
                  ·
                    refine ⟨7957580863014189078733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42440431269409008419909 7957580863014189078733)
                    ·
                      rfl

theorem cell22_23246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_23246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23246 prefixEnd_23246 := by exact prefixLift 23246
  have htrace : WordTrace (prefixWord ++ tailWord_23246) baseStart_23246 baseEnd_23246 := by
    simpa [prefixWord, tailWord_23246, baseEnd_23246] using wordTrace_append hprefix tailTrace_23246
  have hstable : (prefixWord ++ tailWord_23246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23246).length < 2 ^ (prefixWord ++ tailWord_23246).sum := by decide
  have hdescent : baseEnd_23246 < baseStart_23246 := by decide
  rcases family_descends (prefixWord ++ tailWord_23246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23263 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 1, 4]
def baseStart_23263 : Nat := 118140960795 + 23263 * 2 ^ 59
def prefixEnd_23263 : Nat := 4983230072969 + 3 ^ 40 * 23263 * 2
def baseEnd_23263 : Nat := 7963400310431811403681

theorem tailTrace_23263 : CollatzResearch.WordTrace tailWord_23263 prefixEnd_23263 7963400310431811403681 := by
  unfold tailWord_23263
  simp only [CollatzResearch.WordTrace]
  refine ⟨848471314729598849202443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 565647543153065899468295 848471314729598849202443)
  ·
    refine ⟨1272706972094398273803665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 848471314729598849202443 1272706972094398273803665)
    ·
      refine ⟨954530229070798705352749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1272706972094398273803665 954530229070798705352749)
      ·
        refine ⟨357948835901549514507281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 954530229070798705352749 357948835901549514507281)
        ·
          refine ⟨268461626926162135880461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357948835901549514507281 268461626926162135880461)
          ·
            refine ⟨100673110097310800955173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268461626926162135880461 100673110097310800955173)
            ·
              refine ⟨18876208143245775179095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100673110097310800955173 18876208143245775179095)
              ·
                refine ⟨28314312214868662768643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18876208143245775179095 28314312214868662768643)
                ·
                  refine ⟨42471468322302994152965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28314312214868662768643 42471468322302994152965)
                  ·
                    refine ⟨7963400310431811403681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42471468322302994152965 7963400310431811403681)
                    ·
                      rfl

theorem cell22_23263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_23263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23263 prefixEnd_23263 := by exact prefixLift 23263
  have htrace : WordTrace (prefixWord ++ tailWord_23263) baseStart_23263 baseEnd_23263 := by
    simpa [prefixWord, tailWord_23263, baseEnd_23263] using wordTrace_append hprefix tailTrace_23263
  have hstable : (prefixWord ++ tailWord_23263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23263).length < 2 ^ (prefixWord ++ tailWord_23263).sum := by decide
  have hdescent : baseEnd_23263 < baseStart_23263 := by decide
  rcases family_descends (prefixWord ++ tailWord_23263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23278 : List Nat := [4, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_23278 : Nat := 118140960795 + 23278 * 2 ^ 59
def prefixEnd_23278 : Nat := 4983230072969 + 3 ^ 40 * 23278 * 2
def baseEnd_23278 : Nat := 2656178372325590759545

theorem tailTrace_23278 : CollatzResearch.WordTrace tailWord_23278 prefixEnd_23278 2656178372325590759545 := by
  unfold tailWord_23278
  simp only [CollatzResearch.WordTrace]
  refine ⟨106127301209407051374811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 566012273116837607332325 106127301209407051374811)
  ·
    refine ⟨159190951814110577062217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106127301209407051374811 159190951814110577062217)
    ·
      refine ⟨119393213860582932796663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159190951814110577062217 119393213860582932796663)
      ·
        refine ⟨179089820790874399194995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119393213860582932796663 179089820790874399194995)
        ·
          refine ⟨268634731186311598792493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179089820790874399194995 268634731186311598792493)
          ·
            refine ⟨100738024194866849547185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268634731186311598792493 100738024194866849547185)
            ·
              refine ⟨75553518146150137160389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100738024194866849547185 75553518146150137160389)
              ·
                refine ⟨14166284652403150717573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75553518146150137160389 14166284652403150717573)
                ·
                  refine ⟨2656178372325590759545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14166284652403150717573 2656178372325590759545)
                  ·
                    rfl

theorem cell22_23278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_23278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23278 prefixEnd_23278 := by exact prefixLift 23278
  have htrace : WordTrace (prefixWord ++ tailWord_23278) baseStart_23278 baseEnd_23278 := by
    simpa [prefixWord, tailWord_23278, baseEnd_23278] using wordTrace_append hprefix tailTrace_23278
  have hstable : (prefixWord ++ tailWord_23278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23278).length < 2 ^ (prefixWord ++ tailWord_23278).sum := by decide
  have hdescent : baseEnd_23278 < baseStart_23278 := by decide
  rcases family_descends (prefixWord ++ tailWord_23278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23325 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_23325 : Nat := 118140960795 + 23325 * 2 ^ 59
def prefixEnd_23325 : Nat := 4983230072969 + 3 ^ 40 * 23325 * 2
def baseEnd_23325 : Nat := 7984624177484316353491

theorem tailTrace_23325 : CollatzResearch.WordTrace tailWord_23325 prefixEnd_23325 7984624177484316353491 := by
  unfold tailWord_23325
  simp only [CollatzResearch.WordTrace]
  refine ⟨850732640504983437959429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 567155093669988958639619 850732640504983437959429)
  ·
    refine ⟨159512370094684394617393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 850732640504983437959429 159512370094684394617393)
    ·
      refine ⟨119634277571013295963045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159512370094684394617393 119634277571013295963045)
      ·
        refine ⟨22431427044564992993071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119634277571013295963045 22431427044564992993071)
        ·
          refine ⟨33647140566847489489607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22431427044564992993071 33647140566847489489607)
          ·
            refine ⟨50470710850271234234411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33647140566847489489607 50470710850271234234411)
            ·
              refine ⟨75706066275406851351617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50470710850271234234411 75706066275406851351617)
              ·
                refine ⟨56779549706555138513713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75706066275406851351617 56779549706555138513713)
                ·
                  refine ⟨42584662279916353885285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56779549706555138513713 42584662279916353885285)
                  ·
                    refine ⟨7984624177484316353491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42584662279916353885285 7984624177484316353491)
                    ·
                      rfl

theorem cell22_23325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_23325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23325 prefixEnd_23325 := by exact prefixLift 23325
  have htrace : WordTrace (prefixWord ++ tailWord_23325) baseStart_23325 baseEnd_23325 := by
    simpa [prefixWord, tailWord_23325, baseEnd_23325] using wordTrace_append hprefix tailTrace_23325
  have hstable : (prefixWord ++ tailWord_23325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23325).length < 2 ^ (prefixWord ++ tailWord_23325).sum := by decide
  have hdescent : baseEnd_23325 < baseStart_23325 := by decide
  rcases family_descends (prefixWord ++ tailWord_23325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23336 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_23336 : Nat := 118140960795 + 23336 * 2 ^ 59
def prefixEnd_23336 : Nat := 4983230072969 + 3 ^ 40 * 23336 * 2
def baseEnd_23336 : Nat := 7988389702283954328457

theorem tailTrace_23336 : CollatzResearch.WordTrace tailWord_23336 prefixEnd_23336 7988389702283954328457 := by
  unfold tailWord_23336
  simp only [CollatzResearch.WordTrace]
  refine ⟨425566921732566158304931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 567422562310088211073241 425566921732566158304931)
  ·
    refine ⟨638350382598849237457397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425566921732566158304931 638350382598849237457397)
    ·
      refine ⟨59845348368642116011631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 638350382598849237457397 59845348368642116011631)
      ·
        refine ⟨89768022552963174017447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59845348368642116011631 89768022552963174017447)
        ·
          refine ⟨134652033829444761026171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89768022552963174017447 134652033829444761026171)
          ·
            refine ⟨201978050744167141539257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134652033829444761026171 201978050744167141539257)
            ·
              refine ⟨151483538058125356154443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201978050744167141539257 151483538058125356154443)
              ·
                refine ⟨227225307087188034231665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151483538058125356154443 227225307087188034231665)
                ·
                  refine ⟨170418980315391025673749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227225307087188034231665 170418980315391025673749)
                  ·
                    refine ⟨7988389702283954328457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 170418980315391025673749 7988389702283954328457)
                    ·
                      rfl

theorem cell22_23336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_23336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23336 prefixEnd_23336 := by exact prefixLift 23336
  have htrace : WordTrace (prefixWord ++ tailWord_23336) baseStart_23336 baseEnd_23336 := by
    simpa [prefixWord, tailWord_23336, baseEnd_23336] using wordTrace_append hprefix tailTrace_23336
  have hstable : (prefixWord ++ tailWord_23336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23336).length < 2 ^ (prefixWord ++ tailWord_23336).sum := by decide
  have hdescent : baseEnd_23336 < baseStart_23336 := by decide
  rcases family_descends (prefixWord ++ tailWord_23336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23351 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 5]
def baseStart_23351 : Nat := 118140960795 + 23351 * 2 ^ 59
def prefixEnd_23351 : Nat := 4983230072969 + 3 ^ 40 * 23351 * 2
def baseEnd_23351 : Nat := 2664508169609638401137

theorem tailTrace_23351 : CollatzResearch.WordTrace tailWord_23351 prefixEnd_23351 2664508169609638401137 := by
  unfold tailWord_23351
  simp only [CollatzResearch.WordTrace]
  refine ⟨851680938410789878405907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 567787292273859918937271 851680938410789878405907)
  ·
    refine ⟨1277521407616184817608861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 851680938410789878405907 1277521407616184817608861)
    ·
      refine ⟨479070527856069306603323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1277521407616184817608861 479070527856069306603323)
      ·
        refine ⟨718605791784103959904985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479070527856069306603323 718605791784103959904985)
        ·
          refine ⟨538954343838077969928739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718605791784103959904985 538954343838077969928739)
          ·
            refine ⟨808431515757116954893109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538954343838077969928739 808431515757116954893109)
            ·
              refine ⟨75790454602229714521229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 808431515757116954893109 75790454602229714521229)
              ·
                refine ⟨28421420475836142945461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75790454602229714521229 28421420475836142945461)
                ·
                  refine ⟨2664508169609638401137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28421420475836142945461 2664508169609638401137)
                  ·
                    rfl

theorem cell22_23351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 5].length) (baseStart_23351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23351 prefixEnd_23351 := by exact prefixLift 23351
  have htrace : WordTrace (prefixWord ++ tailWord_23351) baseStart_23351 baseEnd_23351 := by
    simpa [prefixWord, tailWord_23351, baseEnd_23351] using wordTrace_append hprefix tailTrace_23351
  have hstable : (prefixWord ++ tailWord_23351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23351).length < 2 ^ (prefixWord ++ tailWord_23351).sum := by decide
  have hdescent : baseEnd_23351 < baseStart_23351 := by decide
  rcases family_descends (prefixWord ++ tailWord_23351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23411 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 1, 5]
def baseStart_23411 : Nat := 118140960795 + 23411 * 2 ^ 59
def prefixEnd_23411 : Nat := 4983230072969 + 3 ^ 40 * 23411 * 2
def baseEnd_23411 : Nat := 8014063735008758703227

theorem tailTrace_23411 : CollatzResearch.WordTrace tailWord_23411 prefixEnd_23411 8014063735008758703227 := by
  unfold tailWord_23411
  simp only [CollatzResearch.WordTrace]
  refine ⟨853869318193420125590087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 569246212128946750393391 853869318193420125590087)
  ·
    refine ⟨1280803977290130188385131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853869318193420125590087 1280803977290130188385131)
    ·
      refine ⟨1921205965935195282577697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280803977290130188385131 1921205965935195282577697)
      ·
        refine ⟨1440904474451396461933273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1921205965935195282577697 1440904474451396461933273)
        ·
          refine ⟨1080678355838547346449955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1440904474451396461933273 1080678355838547346449955)
          ·
            refine ⟨1621017533757821019674933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080678355838547346449955 1621017533757821019674933)
            ·
              refine ⟨151970393789795720594525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1621017533757821019674933 151970393789795720594525)
              ·
                refine ⟨56988897671173395222947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151970393789795720594525 56988897671173395222947)
                ·
                  refine ⟨85483346506760092834421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56988897671173395222947 85483346506760092834421)
                  ·
                    refine ⟨8014063735008758703227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85483346506760092834421 8014063735008758703227)
                    ·
                      rfl

theorem cell22_23411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_23411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23411 prefixEnd_23411 := by exact prefixLift 23411
  have htrace : WordTrace (prefixWord ++ tailWord_23411) baseStart_23411 baseEnd_23411 := by
    simpa [prefixWord, tailWord_23411, baseEnd_23411] using wordTrace_append hprefix tailTrace_23411
  have hstable : (prefixWord ++ tailWord_23411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23411).length < 2 ^ (prefixWord ++ tailWord_23411).sum := by decide
  have hdescent : baseEnd_23411 < baseStart_23411 := by decide
  rcases family_descends (prefixWord ++ tailWord_23411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23413 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 6]
def baseStart_23413 : Nat := 118140960795 + 23413 * 2 ^ 59
def prefixEnd_23413 : Nat := 4983230072969 + 3 ^ 40 * 23413 * 2
def baseEnd_23413 : Nat := 2671582791960473384407

theorem tailTrace_23413 : CollatzResearch.WordTrace tailWord_23413 prefixEnd_23413 2671582791960473384407 := by
  unfold tailWord_23413
  simp only [CollatzResearch.WordTrace]
  refine ⟨853942264186174467162893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 569294842790782978108595 853942264186174467162893)
  ·
    refine ⟨320228349069815425186085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 853942264186174467162893 320228349069815425186085)
    ·
      refine ⟨60042815450590392222391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320228349069815425186085 60042815450590392222391)
      ·
        refine ⟨90064223175885588333587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60042815450590392222391 90064223175885588333587)
        ·
          refine ⟨135096334763828382500381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90064223175885588333587 135096334763828382500381)
          ·
            refine ⟨50661125536435643437643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135096334763828382500381 50661125536435643437643)
            ·
              refine ⟨75991688304653465156465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50661125536435643437643 75991688304653465156465)
              ·
                refine ⟨56993766228490098867349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75991688304653465156465 56993766228490098867349)
                ·
                  refine ⟨2671582791960473384407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56993766228490098867349 2671582791960473384407)
                  ·
                    rfl

theorem cell22_23413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_23413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23413 prefixEnd_23413 := by exact prefixLift 23413
  have htrace : WordTrace (prefixWord ++ tailWord_23413) baseStart_23413 baseEnd_23413 := by
    simpa [prefixWord, tailWord_23413, baseEnd_23413] using wordTrace_append hprefix tailTrace_23413
  have hstable : (prefixWord ++ tailWord_23413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23413).length < 2 ^ (prefixWord ++ tailWord_23413).sum := by decide
  have hdescent : baseEnd_23413 < baseStart_23413 := by decide
  rcases family_descends (prefixWord ++ tailWord_23413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23428 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_23428 : Nat := 118140960795 + 23428 * 2 ^ 59
def prefixEnd_23428 : Nat := 4983230072969 + 3 ^ 40 * 23428 * 2
def baseEnd_23428 : Nat := 8019883182426381028175

theorem tailTrace_23428 : CollatzResearch.WordTrace tailWord_23428 prefixEnd_23428 8019883182426381028175 := by
  unfold tailWord_23428
  simp only [CollatzResearch.WordTrace]
  refine ⟨427244679565916014479469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 569659572754554685972625 427244679565916014479469)
  ·
    refine ⟨160216754837218505429801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 427244679565916014479469 160216754837218505429801)
    ·
      refine ⟨120162566127913879072351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160216754837218505429801 120162566127913879072351)
      ·
        refine ⟨180243849191870818608527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120162566127913879072351 180243849191870818608527)
        ·
          refine ⟨270365773787806227912791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180243849191870818608527 270365773787806227912791)
          ·
            refine ⟨405548660681709341869187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270365773787806227912791 405548660681709341869187)
            ·
              refine ⟨608322991022564012803781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405548660681709341869187 608322991022564012803781)
              ·
                refine ⟨114060560816730752400709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 608322991022564012803781 114060560816730752400709)
                ·
                  refine ⟨21386355153137016075133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114060560816730752400709 21386355153137016075133)
                  ·
                    refine ⟨8019883182426381028175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21386355153137016075133 8019883182426381028175)
                    ·
                      rfl

theorem cell22_23428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_23428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23428 prefixEnd_23428 := by exact prefixLift 23428
  have htrace : WordTrace (prefixWord ++ tailWord_23428) baseStart_23428 baseEnd_23428 := by
    simpa [prefixWord, tailWord_23428, baseEnd_23428] using wordTrace_append hprefix tailTrace_23428
  have hstable : (prefixWord ++ tailWord_23428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23428).length < 2 ^ (prefixWord ++ tailWord_23428).sum := by decide
  have hdescent : baseEnd_23428 < baseStart_23428 := by decide
  rcases family_descends (prefixWord ++ tailWord_23428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23432 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 1, 4]
def baseStart_23432 : Nat := 118140960795 + 23432 * 2 ^ 59
def prefixEnd_23432 : Nat := 4983230072969 + 3 ^ 40 * 23432 * 2
def baseEnd_23432 : Nat := 8021252464171703928163

theorem tailTrace_23432 : CollatzResearch.WordTrace tailWord_23432 prefixEnd_23432 8021252464171703928163 := by
  unfold tailWord_23432
  simp only [CollatzResearch.WordTrace]
  refine ⟨427317625558670356052275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 569756834078227141403033 427317625558670356052275)
  ·
    refine ⟨640976438338005534078413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 427317625558670356052275 640976438338005534078413)
    ·
      refine ⟨240366164376752075279405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 640976438338005534078413 240366164376752075279405)
      ·
        refine ⟨90137311641282028229777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240366164376752075279405 90137311641282028229777)
        ·
          refine ⟨67602983730961521172333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90137311641282028229777 67602983730961521172333)
          ·
            refine ⟨25351118899110570439625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67602983730961521172333 25351118899110570439625)
            ·
              refine ⟨19013339174332927829719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25351118899110570439625 19013339174332927829719)
              ·
                refine ⟨28520008761499391744579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19013339174332927829719 28520008761499391744579)
                ·
                  refine ⟨42780013142249087616869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28520008761499391744579 42780013142249087616869)
                  ·
                    refine ⟨8021252464171703928163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42780013142249087616869 8021252464171703928163)
                    ·
                      rfl

theorem cell22_23432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_23432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23432 prefixEnd_23432 := by exact prefixLift 23432
  have htrace : WordTrace (prefixWord ++ tailWord_23432) baseStart_23432 baseEnd_23432 := by
    simpa [prefixWord, tailWord_23432, baseEnd_23432] using wordTrace_append hprefix tailTrace_23432
  have hstable : (prefixWord ++ tailWord_23432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23432).length < 2 ^ (prefixWord ++ tailWord_23432).sum := by decide
  have hdescent : baseEnd_23432 < baseStart_23432 := by decide
  rcases family_descends (prefixWord ++ tailWord_23432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23445 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_23445 : Nat := 118140960795 + 23445 * 2 ^ 59
def prefixEnd_23445 : Nat := 4983230072969 + 3 ^ 40 * 23445 * 2
def baseEnd_23445 : Nat := 8025702629844003353123

theorem tailTrace_23445 : CollatzResearch.WordTrace tailWord_23445 prefixEnd_23445 8025702629844003353123 := by
  unfold tailWord_23445
  simp only [CollatzResearch.WordTrace]
  refine ⟨855109400070243932327789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 570072933380162621551859 855109400070243932327789)
  ·
    refine ⟨320666025026341474622921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 855109400070243932327789 320666025026341474622921)
    ·
      refine ⟨240499518769756105967191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320666025026341474622921 240499518769756105967191)
      ·
        refine ⟨360749278154634158950787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240499518769756105967191 360749278154634158950787)
        ·
          refine ⟨541123917231951238426181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360749278154634158950787 541123917231951238426181)
          ·
            refine ⟨101460734480990857204909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 541123917231951238426181 101460734480990857204909)
            ·
              refine ⟨38047775430371571451841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101460734480990857204909 38047775430371571451841)
              ·
                refine ⟨28535831572778678588881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38047775430371571451841 28535831572778678588881)
                ·
                  refine ⟨21401873679584008941661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28535831572778678588881 21401873679584008941661)
                  ·
                    refine ⟨8025702629844003353123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21401873679584008941661 8025702629844003353123)
                    ·
                      rfl

theorem cell22_23445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_23445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23445 prefixEnd_23445 := by exact prefixLift 23445
  have htrace : WordTrace (prefixWord ++ tailWord_23445) baseStart_23445 baseEnd_23445 := by
    simpa [prefixWord, tailWord_23445, baseEnd_23445] using wordTrace_append hprefix tailTrace_23445
  have hstable : (prefixWord ++ tailWord_23445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23445).length < 2 ^ (prefixWord ++ tailWord_23445).sum := by decide
  have hdescent : baseEnd_23445 < baseStart_23445 := by decide
  rcases family_descends (prefixWord ++ tailWord_23445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23492 : List Nat := [2, 3, 3, 3, 2, 1, 8]
def baseStart_23492 : Nat := 118140960795 + 23492 * 2 ^ 59
def prefixEnd_23492 : Nat := 4983230072969 + 3 ^ 40 * 23492 * 2
def baseEnd_23492 : Nat := 297844136679686941777

theorem tailTrace_23492 : CollatzResearch.WordTrace tailWord_23492 prefixEnd_23492 297844136679686941777 := by
  unfold tailWord_23492
  simp only [CollatzResearch.WordTrace]
  refine ⟨428411815449985479644365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 571215753933313972859153 428411815449985479644365)
  ·
    refine ⟨160654430793744554866637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 428411815449985479644365 160654430793744554866637)
    ·
      refine ⟨60245411547654208074989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160654430793744554866637 60245411547654208074989)
      ·
        refine ⟨22592029330370328028121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60245411547654208074989 22592029330370328028121)
        ·
          refine ⟨16944021997777746021091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22592029330370328028121 16944021997777746021091)
          ·
            refine ⟨25416032996666619031637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16944021997777746021091 25416032996666619031637)
            ·
              refine ⟨297844136679686941777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 25416032996666619031637 297844136679686941777)
              ·
                rfl

theorem cell22_23492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 8].length) (baseStart_23492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23492 prefixEnd_23492 := by exact prefixLift 23492
  have htrace : WordTrace (prefixWord ++ tailWord_23492) baseStart_23492 baseEnd_23492 := by
    simpa [prefixWord, tailWord_23492, baseEnd_23492] using wordTrace_append hprefix tailTrace_23492
  have hstable : (prefixWord ++ tailWord_23492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23492).length < 2 ^ (prefixWord ++ tailWord_23492).sum := by decide
  have hdescent : baseEnd_23492 < baseStart_23492 := by decide
  rcases family_descends (prefixWord ++ tailWord_23492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23554 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_23554 : Nat := 118140960795 + 23554 * 2 ^ 59
def prefixEnd_23554 : Nat := 4983230072969 + 3 ^ 40 * 23554 * 2
def baseEnd_23554 : Nat := 2687671852468017459263

theorem tailTrace_23554 : CollatzResearch.WordTrace tailWord_23554 prefixEnd_23554 2687671852468017459263 := by
  unfold tailWord_23554
  simp only [CollatzResearch.WordTrace]
  refine ⟨214771239168838887011429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 572723304450237032030477 214771239168838887011429)
  ·
    refine ⟨40269607344157291314643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 214771239168838887011429 40269607344157291314643)
    ·
      refine ⟨60404411016235936971965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40269607344157291314643 60404411016235936971965)
      ·
        refine ⟨22651654131088476364487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60404411016235936971965 22651654131088476364487)
        ·
          refine ⟨33977481196632714546731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22651654131088476364487 33977481196632714546731)
          ·
            refine ⟨50966221794949071820097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33977481196632714546731 50966221794949071820097)
            ·
              refine ⟨38224666346211803865073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50966221794949071820097 38224666346211803865073)
              ·
                refine ⟨28668499759658852898805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38224666346211803865073 28668499759658852898805)
                ·
                  refine ⟨2687671852468017459263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28668499759658852898805 2687671852468017459263)
                  ·
                    rfl

theorem cell22_23554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_23554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23554 prefixEnd_23554 := by exact prefixLift 23554
  have htrace : WordTrace (prefixWord ++ tailWord_23554) baseStart_23554 baseEnd_23554 := by
    simpa [prefixWord, tailWord_23554, baseEnd_23554] using wordTrace_append hprefix tailTrace_23554
  have hstable : (prefixWord ++ tailWord_23554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23554).length < 2 ^ (prefixWord ++ tailWord_23554).sum := by decide
  have hdescent : baseEnd_23554 < baseStart_23554 := by decide
  rcases family_descends (prefixWord ++ tailWord_23554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23578 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_23578 : Nat := 118140960795 + 23578 * 2 ^ 59
def prefixEnd_23578 : Nat := 4983230072969 + 3 ^ 40 * 23578 * 2
def baseEnd_23578 : Nat := 8071231247875989777715

theorem tailTrace_23578 : CollatzResearch.WordTrace tailWord_23578 prefixEnd_23578 8071231247875989777715 := by
  unfold tailWord_23578
  simp only [CollatzResearch.WordTrace]
  refine ⟨214990077147101911729847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 573306872392271764612925 214990077147101911729847)
  ·
    refine ⟨322485115720652867594771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214990077147101911729847 322485115720652867594771)
    ·
      refine ⟨483727673580979301392157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322485115720652867594771 483727673580979301392157)
      ·
        refine ⟨181397877592867238022059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483727673580979301392157 181397877592867238022059)
        ·
          refine ⟨272096816389300857033089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181397877592867238022059 272096816389300857033089)
          ·
            refine ⟨204072612291975642774817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272096816389300857033089 204072612291975642774817)
            ·
              refine ⟨153054459218981732081113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204072612291975642774817 153054459218981732081113)
              ·
                refine ⟨114790844414236299060835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153054459218981732081113 114790844414236299060835)
                ·
                  refine ⟨172186266621354448591253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114790844414236299060835 172186266621354448591253)
                  ·
                    refine ⟨8071231247875989777715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172186266621354448591253 8071231247875989777715)
                    ·
                      rfl

theorem cell22_23578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_23578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23578 prefixEnd_23578 := by exact prefixLift 23578
  have htrace : WordTrace (prefixWord ++ tailWord_23578) baseStart_23578 baseEnd_23578 := by
    simpa [prefixWord, tailWord_23578, baseEnd_23578] using wordTrace_append hprefix tailTrace_23578
  have hstable : (prefixWord ++ tailWord_23578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23578).length < 2 ^ (prefixWord ++ tailWord_23578).sum := by decide
  have hdescent : baseEnd_23578 < baseStart_23578 := by decide
  rcases family_descends (prefixWord ++ tailWord_23578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23614 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_23614 : Nat := 118140960795 + 23614 * 2 ^ 59
def prefixEnd_23614 : Nat := 4983230072969 + 3 ^ 40 * 23614 * 2
def baseEnd_23614 : Nat := 8083554783583895877605

theorem tailTrace_23614 : CollatzResearch.WordTrace tailWord_23614 prefixEnd_23614 8083554783583895877605 := by
  unfold tailWord_23614
  simp only [CollatzResearch.WordTrace]
  refine ⟨107659167057248224403737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 574182224305323863486597 107659167057248224403737)
  ·
    refine ⟨80744375292936168302803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107659167057248224403737 80744375292936168302803)
    ·
      refine ⟨121116562939404252454205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80744375292936168302803 121116562939404252454205)
      ·
        refine ⟨45418711102276594670327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121116562939404252454205 45418711102276594670327)
        ·
          refine ⟨68128066653414892005491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45418711102276594670327 68128066653414892005491)
          ·
            refine ⟨102192099980122338008237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68128066653414892005491 102192099980122338008237)
            ·
              refine ⟨38322037492545876753089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102192099980122338008237 38322037492545876753089)
              ·
                refine ⟨28741528119409407564817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38322037492545876753089 28741528119409407564817)
                ·
                  refine ⟨21556146089557055673613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28741528119409407564817 21556146089557055673613)
                  ·
                    refine ⟨8083554783583895877605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21556146089557055673613 8083554783583895877605)
                    ·
                      rfl

theorem cell22_23614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_23614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23614 prefixEnd_23614 := by exact prefixLift 23614
  have htrace : WordTrace (prefixWord ++ tailWord_23614) baseStart_23614 baseEnd_23614 := by
    simpa [prefixWord, tailWord_23614, baseEnd_23614] using wordTrace_append hprefix tailTrace_23614
  have hstable : (prefixWord ++ tailWord_23614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23614).length < 2 ^ (prefixWord ++ tailWord_23614).sum := by decide
  have hdescent : baseEnd_23614 < baseStart_23614 := by decide
  rcases family_descends (prefixWord ++ tailWord_23614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23715 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 6, 3]
def baseStart_23715 : Nat := 118140960795 + 23715 * 2 ^ 59
def prefixEnd_23715 : Nat := 4983230072969 + 3 ^ 40 * 23715 * 2
def baseEnd_23715 : Nat := 8118129147653299102295

theorem tailTrace_23715 : CollatzResearch.WordTrace tailWord_23715 prefixEnd_23715 8118129147653299102295 := by
  unfold tailWord_23715
  simp only [CollatzResearch.WordTrace]
  refine ⟨864957109092080044656599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 576638072728053363104399 864957109092080044656599)
  ·
    refine ⟨1297435663638120066984899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864957109092080044656599 1297435663638120066984899)
    ·
      refine ⟨1946153495457180100477349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1297435663638120066984899 1946153495457180100477349)
      ·
        refine ⟨364903780398221268839503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1946153495457180100477349 364903780398221268839503)
        ·
          refine ⟨547355670597331903259255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364903780398221268839503 547355670597331903259255)
          ·
            refine ⟨821033505895997854888883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547355670597331903259255 821033505895997854888883)
            ·
              refine ⟨1231550258843996782333325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821033505895997854888883 1231550258843996782333325)
              ·
                refine ⟨461831347066498793374997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1231550258843996782333325 461831347066498793374997)
                ·
                  refine ⟨21648344393742130939453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 461831347066498793374997 21648344393742130939453)
                  ·
                    refine ⟨8118129147653299102295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21648344393742130939453 8118129147653299102295)
                    ·
                      rfl

theorem cell22_23715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 3].length) (baseStart_23715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23715 prefixEnd_23715 := by exact prefixLift 23715
  have htrace : WordTrace (prefixWord ++ tailWord_23715) baseStart_23715 baseEnd_23715 := by
    simpa [prefixWord, tailWord_23715, baseEnd_23715] using wordTrace_append hprefix tailTrace_23715
  have hstable : (prefixWord ++ tailWord_23715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23715).length < 2 ^ (prefixWord ++ tailWord_23715).sum := by decide
  have hdescent : baseEnd_23715 < baseStart_23715 := by decide
  rcases family_descends (prefixWord ++ tailWord_23715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23762 : List Nat := [3, 2, 2, 2, 1, 1, 5, 6]
def baseStart_23762 : Nat := 118140960795 + 23762 * 2 ^ 59
def prefixEnd_23762 : Nat := 4983230072969 + 3 ^ 40 * 23762 * 2
def baseEnd_23762 : Nat := 903802023128982575239

theorem tailTrace_23762 : CollatzResearch.WordTrace tailWord_23762 prefixEnd_23762 903802023128982575239 := by
  unfold tailWord_23762
  simp only [CollatzResearch.WordTrace]
  refine ⟨216667834980451767904385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 577780893281204714411693 216667834980451767904385)
  ·
    refine ⟨162500876235338825928289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216667834980451767904385 162500876235338825928289)
    ·
      refine ⟨121875657176504119446217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162500876235338825928289 121875657176504119446217)
      ·
        refine ⟨91406742882378089584663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121875657176504119446217 91406742882378089584663)
        ·
          refine ⟨137110114323567134376995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91406742882378089584663 137110114323567134376995)
          ·
            refine ⟨205665171485350701565493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137110114323567134376995 205665171485350701565493)
            ·
              refine ⟨19281109826751628271765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205665171485350701565493 19281109826751628271765)
              ·
                refine ⟨903802023128982575239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19281109826751628271765 903802023128982575239)
                ·
                  rfl

theorem cell22_23762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_23762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23762 prefixEnd_23762 := by exact prefixLift 23762
  have htrace : WordTrace (prefixWord ++ tailWord_23762) baseStart_23762 baseEnd_23762 := by
    simpa [prefixWord, tailWord_23762, baseEnd_23762] using wordTrace_append hprefix tailTrace_23762
  have hstable : (prefixWord ++ tailWord_23762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23762).length < 2 ^ (prefixWord ++ tailWord_23762).sum := by decide
  have hdescent : baseEnd_23762 < baseStart_23762 := by decide
  rcases family_descends (prefixWord ++ tailWord_23762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23764 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_23764 : Nat := 118140960795 + 23764 * 2 ^ 59
def prefixEnd_23764 : Nat := 4983230072969 + 3 ^ 40 * 23764 * 2
def baseEnd_23764 : Nat := 8134902849033504627145

theorem tailTrace_23764 : CollatzResearch.WordTrace tailWord_23764 prefixEnd_23764 8134902849033504627145 := by
  unfold tailWord_23764
  simp only [CollatzResearch.WordTrace]
  refine ⟨433372142957280706595173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 577829523943040942126897 433372142957280706595173)
  ·
    refine ⟨81257276804490132486595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 433372142957280706595173 81257276804490132486595)
    ·
      refine ⟨121885915206735198729893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81257276804490132486595 121885915206735198729893)
      ·
        refine ⟨22853609101262849761855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121885915206735198729893 22853609101262849761855)
        ·
          refine ⟨34280413651894274642783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22853609101262849761855 34280413651894274642783)
          ·
            refine ⟨51420620477841411964175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34280413651894274642783 51420620477841411964175)
            ·
              refine ⟨77130930716762117946263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51420620477841411964175 77130930716762117946263)
              ·
                refine ⟨115696396075143176919395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77130930716762117946263 115696396075143176919395)
                ·
                  refine ⟨173544594112714765379093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115696396075143176919395 173544594112714765379093)
                  ·
                    refine ⟨8134902849033504627145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173544594112714765379093 8134902849033504627145)
                    ·
                      rfl

theorem cell22_23764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_23764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23764 prefixEnd_23764 := by exact prefixLift 23764
  have htrace : WordTrace (prefixWord ++ tailWord_23764) baseStart_23764 baseEnd_23764 := by
    simpa [prefixWord, tailWord_23764, baseEnd_23764] using wordTrace_append hprefix tailTrace_23764
  have hstable : (prefixWord ++ tailWord_23764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23764).length < 2 ^ (prefixWord ++ tailWord_23764).sum := by decide
  have hdescent : baseEnd_23764 < baseStart_23764 := by decide
  rcases family_descends (prefixWord ++ tailWord_23764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23783 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 2, 3]
def baseStart_23783 : Nat := 118140960795 + 23783 * 2 ^ 59
def prefixEnd_23783 : Nat := 4983230072969 + 3 ^ 40 * 23783 * 2
def baseEnd_23783 : Nat := 8141406937323788402087

theorem tailTrace_23783 : CollatzResearch.WordTrace tailWord_23783 prefixEnd_23783 8141406937323788402087 := by
  unfold tailWord_23783
  simp only [CollatzResearch.WordTrace]
  refine ⟨867437272845727658132003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 578291515230485105421335 867437272845727658132003)
  ·
    refine ⟨1301155909268591487198005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867437272845727658132003 1301155909268591487198005)
    ·
      refine ⟨121983366493930451924813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1301155909268591487198005 121983366493930451924813)
      ·
        refine ⟨45743762435223919471805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121983366493930451924813 45743762435223919471805)
        ·
          refine ⟨17153910913208969801927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45743762435223919471805 17153910913208969801927)
          ·
            refine ⟨25730866369813454702891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17153910913208969801927 25730866369813454702891)
            ·
              refine ⟨38596299554720182054337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25730866369813454702891 38596299554720182054337)
              ·
                refine ⟨28947224666040136540753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38596299554720182054337 28947224666040136540753)
                ·
                  refine ⟨21710418499530102405565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28947224666040136540753 21710418499530102405565)
                  ·
                    refine ⟨8141406937323788402087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21710418499530102405565 8141406937323788402087)
                    ·
                      rfl

theorem cell22_23783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_23783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23783 prefixEnd_23783 := by exact prefixLift 23783
  have htrace : WordTrace (prefixWord ++ tailWord_23783) baseStart_23783 baseEnd_23783 := by
    simpa [prefixWord, tailWord_23783, baseEnd_23783] using wordTrace_append hprefix tailTrace_23783
  have hstable : (prefixWord ++ tailWord_23783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23783).length < 2 ^ (prefixWord ++ tailWord_23783).sum := by decide
  have hdescent : baseEnd_23783 < baseStart_23783 := by decide
  rcases family_descends (prefixWord ++ tailWord_23783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23957 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_23957 : Nat := 118140960795 + 23957 * 2 ^ 59
def prefixEnd_23957 : Nat := 4983230072969 + 3 ^ 40 * 23957 * 2
def baseEnd_23957 : Nat := 8200970693245334551553

theorem tailTrace_23957 : CollatzResearch.WordTrace tailWord_23957 prefixEnd_23957 8200970693245334551553 := by
  unfold tailWord_23957
  simp only [CollatzResearch.WordTrace]
  refine ⟨873783574215355374966125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 582522382810236916644083 873783574215355374966125)
  ·
    refine ⟨327668840330758265612297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 873783574215355374966125 327668840330758265612297)
    ·
      refine ⟨245751630248068699209223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327668840330758265612297 245751630248068699209223)
      ·
        refine ⟨368627445372103048813835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245751630248068699209223 368627445372103048813835)
        ·
          refine ⟨552941168058154573220753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368627445372103048813835 552941168058154573220753)
          ·
            refine ⟨414705876043615929915565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552941168058154573220753 414705876043615929915565)
            ·
              refine ⟨155514703516355973718337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414705876043615929915565 155514703516355973718337)
              ·
                refine ⟨116636027637266980288753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155514703516355973718337 116636027637266980288753)
                ·
                  refine ⟨87477020727950235216565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116636027637266980288753 87477020727950235216565)
                  ·
                    refine ⟨8200970693245334551553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87477020727950235216565 8200970693245334551553)
                    ·
                      rfl

theorem cell22_23957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_23957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_23957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_23957 prefixEnd_23957 := by exact prefixLift 23957
  have htrace : WordTrace (prefixWord ++ tailWord_23957) baseStart_23957 baseEnd_23957 := by
    simpa [prefixWord, tailWord_23957, baseEnd_23957] using wordTrace_append hprefix tailTrace_23957
  have hstable : (prefixWord ++ tailWord_23957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23957).length < 2 ^ (prefixWord ++ tailWord_23957).sum := by decide
  have hdescent : baseEnd_23957 < baseStart_23957 := by decide
  rcases family_descends (prefixWord ++ tailWord_23957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24047 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 2, 7]
def baseStart_24047 : Nat := 118140960795 + 24047 * 2 ^ 59
def prefixEnd_24047 : Nat := 4983230072969 + 3 ^ 40 * 24047 * 2
def baseEnd_24047 : Nat := 8231779532515099801277

theorem tailTrace_24047 : CollatzResearch.WordTrace tailWord_24047 prefixEnd_24047 8231779532515099801277 := by
  unfold tailWord_24047
  simp only [CollatzResearch.WordTrace]
  refine ⟨877066143889300745742395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 584710762592867163828263 877066143889300745742395)
  ·
    refine ⟨1315599215833951118613593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 877066143889300745742395 1315599215833951118613593)
    ·
      refine ⟨986699411875463338960195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1315599215833951118613593 986699411875463338960195)
      ·
        refine ⟨1480049117813195008440293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986699411875463338960195 1480049117813195008440293)
        ·
          refine ⟨277509209589974064082555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1480049117813195008440293 277509209589974064082555)
          ·
            refine ⟨416263814384961096123833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277509209589974064082555 416263814384961096123833)
            ·
              refine ⟨312197860788720822092875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416263814384961096123833 312197860788720822092875)
              ·
                refine ⟨468296791183081233139313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312197860788720822092875 468296791183081233139313)
                ·
                  refine ⟨351222593387310924854485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468296791183081233139313 351222593387310924854485)
                  ·
                    refine ⟨8231779532515099801277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 351222593387310924854485 8231779532515099801277)
                    ·
                      rfl

theorem cell22_24047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_24047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24047 prefixEnd_24047 := by exact prefixLift 24047
  have htrace : WordTrace (prefixWord ++ tailWord_24047) baseStart_24047 baseEnd_24047 := by
    simpa [prefixWord, tailWord_24047, baseEnd_24047] using wordTrace_append hprefix tailTrace_24047
  have hstable : (prefixWord ++ tailWord_24047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24047).length < 2 ^ (prefixWord ++ tailWord_24047).sum := by decide
  have hdescent : baseEnd_24047 < baseStart_24047 := by decide
  rcases family_descends (prefixWord ++ tailWord_24047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24156 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 6]
def baseStart_24156 : Nat := 118140960795 + 24156 * 2 ^ 59
def prefixEnd_24156 : Nat := 4983230072969 + 3 ^ 40 * 24156 * 2
def baseEnd_24156 : Nat := 2756364153358382941981

theorem tailTrace_24156 : CollatzResearch.WordTrace tailWord_24156 prefixEnd_24156 2756364153358382941981 := by
  unfold tailWord_24156
  simp only [CollatzResearch.WordTrace]
  refine ⟨440520850247206180730161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 587361133662941574306881 440520850247206180730161)
  ·
    refine ⟨330390637685404635547621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 440520850247206180730161 330390637685404635547621)
    ·
      refine ⟨61948244566013369165179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330390637685404635547621 61948244566013369165179)
      ·
        refine ⟨92922366849020053747769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61948244566013369165179 92922366849020053747769)
        ·
          refine ⟨69691775136765040310827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92922366849020053747769 69691775136765040310827)
          ·
            refine ⟨104537662705147560466241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69691775136765040310827 104537662705147560466241)
            ·
              refine ⟨78403247028860670349681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104537662705147560466241 78403247028860670349681)
              ·
                refine ⟨58802435271645502762261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78403247028860670349681 58802435271645502762261)
                ·
                  refine ⟨2756364153358382941981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58802435271645502762261 2756364153358382941981)
                  ·
                    rfl

theorem cell22_24156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_24156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24156 prefixEnd_24156 := by exact prefixLift 24156
  have htrace : WordTrace (prefixWord ++ tailWord_24156) baseStart_24156 baseEnd_24156 := by
    simpa [prefixWord, tailWord_24156, baseEnd_24156] using wordTrace_append hprefix tailTrace_24156
  have hstable : (prefixWord ++ tailWord_24156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24156).length < 2 ^ (prefixWord ++ tailWord_24156).sum := by decide
  have hdescent : baseEnd_24156 < baseStart_24156 := by decide
  rcases family_descends (prefixWord ++ tailWord_24156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24169 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_24169 : Nat := 118140960795 + 24169 * 2 ^ 59
def prefixEnd_24169 : Nat := 4983230072969 + 3 ^ 40 * 24169 * 2
def baseEnd_24169 : Nat := 8273542625747448250903

theorem tailTrace_24169 : CollatzResearch.WordTrace tailWord_24169 prefixEnd_24169 8273542625747448250903 := by
  unfold tailWord_24169
  simp only [CollatzResearch.WordTrace]
  refine ⟨881515849447315581683561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 587677232964877054455707 881515849447315581683561)
  ·
    refine ⟨661136887085486686262671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 881515849447315581683561 661136887085486686262671)
    ·
      refine ⟨991705330628230029394007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661136887085486686262671 991705330628230029394007)
      ·
        refine ⟨1487557995942345044091011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991705330628230029394007 1487557995942345044091011)
        ·
          refine ⟨2231336993913517566136517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487557995942345044091011 2231336993913517566136517)
          ·
            refine ⟨418375686358784543650597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2231336993913517566136517 418375686358784543650597)
            ·
              refine ⟨78445441192272101934487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 418375686358784543650597 78445441192272101934487)
              ·
                refine ⟨117668161788408152901731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78445441192272101934487 117668161788408152901731)
                ·
                  refine ⟨176502242682612229352597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117668161788408152901731 176502242682612229352597)
                  ·
                    refine ⟨8273542625747448250903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 176502242682612229352597 8273542625747448250903)
                    ·
                      rfl

theorem cell22_24169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_24169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24169 prefixEnd_24169 := by exact prefixLift 24169
  have htrace : WordTrace (prefixWord ++ tailWord_24169) baseStart_24169 baseEnd_24169 := by
    simpa [prefixWord, tailWord_24169, baseEnd_24169] using wordTrace_append hprefix tailTrace_24169
  have hstable : (prefixWord ++ tailWord_24169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24169).length < 2 ^ (prefixWord ++ tailWord_24169).sum := by decide
  have hdescent : baseEnd_24169 < baseStart_24169 := by decide
  rcases family_descends (prefixWord ++ tailWord_24169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24229 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 9]
def baseStart_24229 : Nat := 118140960795 + 24229 * 2 ^ 59
def prefixEnd_24229 : Nat := 4983230072969 + 3 ^ 40 * 24229 * 2
def baseEnd_24229 : Nat := 2764693950642430583573

theorem tailTrace_24229 : CollatzResearch.WordTrace tailWord_24229 prefixEnd_24229 2764693950642430583573 := by
  unfold tailWord_24229
  simp only [CollatzResearch.WordTrace]
  refine ⟨883704229229945828867741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 589136152819963885911827 883704229229945828867741)
  ·
    refine ⟨331389085961229685825403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 883704229229945828867741 331389085961229685825403)
    ·
      refine ⟨497083628941844528738105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331389085961229685825403 497083628941844528738105)
      ·
        refine ⟨372812721706383396553579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497083628941844528738105 372812721706383396553579)
        ·
          refine ⟨559219082559575094830369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372812721706383396553579 559219082559575094830369)
          ·
            refine ⟨419414311919681321122777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559219082559575094830369 419414311919681321122777)
            ·
              refine ⟨314560733939760990842083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419414311919681321122777 314560733939760990842083)
              ·
                refine ⟨471841100909641486263125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314560733939760990842083 471841100909641486263125)
                ·
                  refine ⟨2764693950642430583573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 471841100909641486263125 2764693950642430583573)
                  ·
                    rfl

theorem cell22_24229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_24229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24229 prefixEnd_24229 := by exact prefixLift 24229
  have htrace : WordTrace (prefixWord ++ tailWord_24229) baseStart_24229 baseEnd_24229 := by
    simpa [prefixWord, tailWord_24229, baseEnd_24229] using wordTrace_append hprefix tailTrace_24229
  have hstable : (prefixWord ++ tailWord_24229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24229).length < 2 ^ (prefixWord ++ tailWord_24229).sum := by decide
  have hdescent : baseEnd_24229 < baseStart_24229 := by decide
  rcases family_descends (prefixWord ++ tailWord_24229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24250 : List Nat := [3, 1, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_24250 : Nat := 118140960795 + 24250 * 2 ^ 59
def prefixEnd_24250 : Nat := 4983230072969 + 3 ^ 40 * 24250 * 2
def baseEnd_24250 : Nat := 8301270581090236975655

theorem tailTrace_24250 : CollatzResearch.WordTrace tailWord_24250 prefixEnd_24250 8301270581090236975655 := by
  unfold tailWord_24250
  simp only [CollatzResearch.WordTrace]
  refine ⟨221117540538466603845551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 589646774769244276921469 221117540538466603845551)
  ·
    refine ⟨331676310807699905768327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221117540538466603845551 331676310807699905768327)
    ·
      refine ⟨497514466211549858652491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331676310807699905768327 497514466211549858652491)
      ·
        refine ⟨746271699317324787978737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497514466211549858652491 746271699317324787978737)
        ·
          refine ⟨559703774487993590984053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746271699317324787978737 559703774487993590984053)
          ·
            refine ⟨52472228858249399154755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 559703774487993590984053 52472228858249399154755)
            ·
              refine ⟨78708343287374098732133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52472228858249399154755 78708343287374098732133)
              ·
                refine ⟨14757814366382643512275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78708343287374098732133 14757814366382643512275)
                ·
                  refine ⟨22136721549573965268413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14757814366382643512275 22136721549573965268413)
                  ·
                    refine ⟨8301270581090236975655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22136721549573965268413 8301270581090236975655)
                    ·
                      rfl

theorem cell22_24250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_24250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24250 prefixEnd_24250 := by exact prefixLift 24250
  have htrace : WordTrace (prefixWord ++ tailWord_24250) baseStart_24250 baseEnd_24250 := by
    simpa [prefixWord, tailWord_24250, baseEnd_24250] using wordTrace_append hprefix tailTrace_24250
  have hstable : (prefixWord ++ tailWord_24250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24250).length < 2 ^ (prefixWord ++ tailWord_24250).sum := by decide
  have hdescent : baseEnd_24250 < baseStart_24250 := by decide
  rcases family_descends (prefixWord ++ tailWord_24250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24284 : List Nat := [2, 2, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_24284 : Nat := 118140960795 + 24284 * 2 ^ 59
def prefixEnd_24284 : Nat := 4983230072969 + 3 ^ 40 * 24284 * 2
def baseEnd_24284 : Nat := 8312909475925481625551

theorem tailTrace_24284 : CollatzResearch.WordTrace tailWord_24284 prefixEnd_24284 8312909475925481625551 := by
  unfold tailWord_24284
  simp only [CollatzResearch.WordTrace]
  refine ⟨442855122015345111059953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 590473496020460148079937 442855122015345111059953)
  ·
    refine ⟨332141341511508833294965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 442855122015345111059953 332141341511508833294965)
    ·
      refine ⟨31138250766703953121403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 332141341511508833294965 31138250766703953121403)
      ·
        refine ⟨46707376150055929682105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31138250766703953121403 46707376150055929682105)
        ·
          refine ⟨35030532112541947261579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46707376150055929682105 35030532112541947261579)
          ·
            refine ⟨52545798168812920892369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35030532112541947261579 52545798168812920892369)
            ·
              refine ⟨39409348626609690669277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52545798168812920892369 39409348626609690669277)
              ·
                refine ⟨14778505734978634000979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39409348626609690669277 14778505734978634000979)
                ·
                  refine ⟨22167758602467951001469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14778505734978634000979 22167758602467951001469)
                  ·
                    refine ⟨8312909475925481625551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22167758602467951001469 8312909475925481625551)
                    ·
                      rfl

theorem cell22_24284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_24284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24284 prefixEnd_24284 := by exact prefixLift 24284
  have htrace : WordTrace (prefixWord ++ tailWord_24284) baseStart_24284 baseEnd_24284 := by
    simpa [prefixWord, tailWord_24284, baseEnd_24284] using wordTrace_append hprefix tailTrace_24284
  have hstable : (prefixWord ++ tailWord_24284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24284).length < 2 ^ (prefixWord ++ tailWord_24284).sum := by decide
  have hdescent : baseEnd_24284 < baseStart_24284 := by decide
  rcases family_descends (prefixWord ++ tailWord_24284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24293 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_24293 : Nat := 118140960795 + 24293 * 2 ^ 59
def prefixEnd_24293 : Nat := 4983230072969 + 3 ^ 40 * 24293 * 2
def baseEnd_24293 : Nat := 8315990359852458150523

theorem tailTrace_24293 : CollatzResearch.WordTrace tailWord_24293 prefixEnd_24293 8315990359852458150523 := by
  unfold tailWord_24293
  simp only [CollatzResearch.WordTrace]
  refine ⟨886038500998084759197533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 590692333998723172798355 886038500998084759197533)
  ·
    refine ⟨332264437874281784699075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 886038500998084759197533 332264437874281784699075)
    ·
      refine ⟨498396656811422677048613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332264437874281784699075 498396656811422677048613)
      ·
        refine ⟨93449373152141751946615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 498396656811422677048613 93449373152141751946615)
        ·
          refine ⟨140174059728212627919923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93449373152141751946615 140174059728212627919923)
          ·
            refine ⟨210261089592318941879885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140174059728212627919923 210261089592318941879885)
            ·
              refine ⟨78847908597119603204957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210261089592318941879885 78847908597119603204957)
              ·
                refine ⟨29567965723919851201859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78847908597119603204957 29567965723919851201859)
                ·
                  refine ⟨44351948585879776802789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29567965723919851201859 44351948585879776802789)
                  ·
                    refine ⟨8315990359852458150523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44351948585879776802789 8315990359852458150523)
                    ·
                      rfl

theorem cell22_24293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_24293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24293 prefixEnd_24293 := by exact prefixLift 24293
  have htrace : WordTrace (prefixWord ++ tailWord_24293) baseStart_24293 baseEnd_24293 := by
    simpa [prefixWord, tailWord_24293, baseEnd_24293] using wordTrace_append hprefix tailTrace_24293
  have hstable : (prefixWord ++ tailWord_24293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24293).length < 2 ^ (prefixWord ++ tailWord_24293).sum := by decide
  have hdescent : baseEnd_24293 < baseStart_24293 := by decide
  rcases family_descends (prefixWord ++ tailWord_24293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24321 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_24321 : Nat := 118140960795 + 24321 * 2 ^ 59
def prefixEnd_24321 : Nat := 4983230072969 + 3 ^ 40 * 24321 * 2
def baseEnd_24321 : Nat := 8325575332069718450437

theorem tailTrace_24321 : CollatzResearch.WordTrace tailWord_24321 prefixEnd_24321 8325575332069718450437 := by
  unfold tailWord_24321
  simp only [CollatzResearch.WordTrace]
  refine ⟨887059744896645541216817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 591373163264430360811211 887059744896645541216817)
  ·
    refine ⟨665294808672484155912613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 887059744896645541216817 665294808672484155912613)
    ·
      refine ⟨124742776626090779233615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 665294808672484155912613 124742776626090779233615)
      ·
        refine ⟨187114164939136168850423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124742776626090779233615 187114164939136168850423)
        ·
          refine ⟨280671247408704253275635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187114164939136168850423 280671247408704253275635)
          ·
            refine ⟨421006871113056379913453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280671247408704253275635 421006871113056379913453)
            ·
              refine ⟨157877576667396142467545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421006871113056379913453 157877576667396142467545)
              ·
                refine ⟨118408182500547106850659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157877576667396142467545 118408182500547106850659)
                ·
                  refine ⟨177612273750820660275989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118408182500547106850659 177612273750820660275989)
                  ·
                    refine ⟨8325575332069718450437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 177612273750820660275989 8325575332069718450437)
                    ·
                      rfl

theorem cell22_24321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_24321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24321 prefixEnd_24321 := by exact prefixLift 24321
  have htrace : WordTrace (prefixWord ++ tailWord_24321) baseStart_24321 baseEnd_24321 := by
    simpa [prefixWord, tailWord_24321, baseEnd_24321] using wordTrace_append hprefix tailTrace_24321
  have hstable : (prefixWord ++ tailWord_24321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24321).length < 2 ^ (prefixWord ++ tailWord_24321).sum := by decide
  have hdescent : baseEnd_24321 < baseStart_24321 := by decide
  rcases family_descends (prefixWord ++ tailWord_24321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24323 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 2, 3]
def baseStart_24323 : Nat := 118140960795 + 24323 * 2 ^ 59
def prefixEnd_24323 : Nat := 4983230072969 + 3 ^ 40 * 24323 * 2
def baseEnd_24323 : Nat := 8326259972942379900431

theorem tailTrace_24323 : CollatzResearch.WordTrace tailWord_24323 prefixEnd_24323 8326259972942379900431 := by
  unfold tailWord_24323
  simp only [CollatzResearch.WordTrace]
  refine ⟨887132690889399882789623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 591421793926266588526415 887132690889399882789623)
  ·
    refine ⟨1330699036334099824184435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887132690889399882789623 1330699036334099824184435)
    ·
      refine ⟨1996048554501149736276653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330699036334099824184435 1996048554501149736276653)
      ·
        refine ⟨748518207937931151103745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1996048554501149736276653 748518207937931151103745)
        ·
          refine ⟨561388655953448363327809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748518207937931151103745 561388655953448363327809)
          ·
            refine ⟨421041491965086272495857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561388655953448363327809 421041491965086272495857)
            ·
              refine ⟨315781118973814704371893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421041491965086272495857 315781118973814704371893)
              ·
                refine ⟨29604479903795128534865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315781118973814704371893 29604479903795128534865)
                ·
                  refine ⟨22203359927846346401149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29604479903795128534865 22203359927846346401149)
                  ·
                    refine ⟨8326259972942379900431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22203359927846346401149 8326259972942379900431)
                    ·
                      rfl

theorem cell22_24323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 3].length) (baseStart_24323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24323 prefixEnd_24323 := by exact prefixLift 24323
  have htrace : WordTrace (prefixWord ++ tailWord_24323) baseStart_24323 baseEnd_24323 := by
    simpa [prefixWord, tailWord_24323, baseEnd_24323] using wordTrace_append hprefix tailTrace_24323
  have hstable : (prefixWord ++ tailWord_24323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24323).length < 2 ^ (prefixWord ++ tailWord_24323).sum := by decide
  have hdescent : baseEnd_24323 < baseStart_24323 := by decide
  rcases family_descends (prefixWord ++ tailWord_24323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24374 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_24374 : Nat := 118140960795 + 24374 * 2 ^ 59
def prefixEnd_24374 : Nat := 4983230072969 + 3 ^ 40 * 24374 * 2
def baseEnd_24374 : Nat := 8343718315195246875275

theorem tailTrace_24374 : CollatzResearch.WordTrace tailWord_24374 prefixEnd_24374 8343718315195246875275 := by
  unfold tailWord_24374
  simp only [CollatzResearch.WordTrace]
  refine ⟨55562050856539724556011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 592661875803090395264117 55562050856539724556011)
  ·
    refine ⟨83343076284809586834017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55562050856539724556011 83343076284809586834017)
    ·
      refine ⟨62507307213607190125513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83343076284809586834017 62507307213607190125513)
      ·
        refine ⟨46880480410205392594135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62507307213607190125513 46880480410205392594135)
        ·
          refine ⟨70320720615308088891203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46880480410205392594135 70320720615308088891203)
          ·
            refine ⟨105481080922962133336805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70320720615308088891203 105481080922962133336805)
            ·
              refine ⟨19777702673055400000651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105481080922962133336805 19777702673055400000651)
              ·
                refine ⟨29666554009583100000977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19777702673055400000651 29666554009583100000977)
                ·
                  refine ⟨22249915507187325000733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29666554009583100000977 22249915507187325000733)
                  ·
                    refine ⟨8343718315195246875275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22249915507187325000733 8343718315195246875275)
                    ·
                      rfl

theorem cell22_24374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_24374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24374 prefixEnd_24374 := by exact prefixLift 24374
  have htrace : WordTrace (prefixWord ++ tailWord_24374) baseStart_24374 baseEnd_24374 := by
    simpa [prefixWord, tailWord_24374, baseEnd_24374] using wordTrace_append hprefix tailTrace_24374
  have hstable : (prefixWord ++ tailWord_24374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24374).length < 2 ^ (prefixWord ++ tailWord_24374).sum := by decide
  have hdescent : baseEnd_24374 < baseStart_24374 := by decide
  rcases family_descends (prefixWord ++ tailWord_24374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24428 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_24428 : Nat := 118140960795 + 24428 * 2 ^ 59
def prefixEnd_24428 : Nat := 4983230072969 + 3 ^ 40 * 24428 * 2
def baseEnd_24428 : Nat := 8362203618757106025109

theorem tailTrace_24428 : CollatzResearch.WordTrace tailWord_24428 prefixEnd_24428 8362203618757106025109 := by
  unfold tailWord_24428
  simp only [CollatzResearch.WordTrace]
  refine ⟨445481177754501407680969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 593974903672668543574625 445481177754501407680969)
  ·
    refine ⟨334110883315876055760727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 445481177754501407680969 334110883315876055760727)
    ·
      refine ⟨501166324973814083641091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334110883315876055760727 501166324973814083641091)
      ·
        refine ⟨751749487460721125461637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501166324973814083641091 751749487460721125461637)
        ·
          refine ⟨140953028898885211024057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 751749487460721125461637 140953028898885211024057)
          ·
            refine ⟨105714771674163908268043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140953028898885211024057 105714771674163908268043)
            ·
              refine ⟨158572157511245862402065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105714771674163908268043 158572157511245862402065)
              ·
                refine ⟨118929118133434396801549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158572157511245862402065 118929118133434396801549)
                ·
                  refine ⟨44598419300037898800581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118929118133434396801549 44598419300037898800581)
                  ·
                    refine ⟨8362203618757106025109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44598419300037898800581 8362203618757106025109)
                    ·
                      rfl

theorem cell22_24428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_24428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24428 prefixEnd_24428 := by exact prefixLift 24428
  have htrace : WordTrace (prefixWord ++ tailWord_24428) baseStart_24428 baseEnd_24428 := by
    simpa [prefixWord, tailWord_24428, baseEnd_24428] using wordTrace_append hprefix tailTrace_24428
  have hstable : (prefixWord ++ tailWord_24428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24428).length < 2 ^ (prefixWord ++ tailWord_24428).sum := by decide
  have hdescent : baseEnd_24428 < baseStart_24428 := by decide
  rcases family_descends (prefixWord ++ tailWord_24428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24430 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_24430 : Nat := 118140960795 + 24430 * 2 ^ 59
def prefixEnd_24430 : Nat := 4983230072969 + 3 ^ 40 * 24430 * 2
def baseEnd_24430 : Nat := 8362888259629767475103

theorem tailTrace_24430 : CollatzResearch.WordTrace tailWord_24430 prefixEnd_24430 8362888259629767475103 := by
  unfold tailWord_24430
  simp only [CollatzResearch.WordTrace]
  refine ⟨111379412687719644616843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 594023534334504771289829 111379412687719644616843)
  ·
    refine ⟨167069119031579466925265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111379412687719644616843 167069119031579466925265)
    ·
      refine ⟨125301839273684600193949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167069119031579466925265 125301839273684600193949)
      ·
        refine ⟨46988189727631725072731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125301839273684600193949 46988189727631725072731)
        ·
          refine ⟨70482284591447587609097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46988189727631725072731 70482284591447587609097)
          ·
            refine ⟨52861713443585690706823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70482284591447587609097 52861713443585690706823)
            ·
              refine ⟨79292570165378536060235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52861713443585690706823 79292570165378536060235)
              ·
                refine ⟨118938855248067804090353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79292570165378536060235 118938855248067804090353)
                ·
                  refine ⟨89204141436050853067765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118938855248067804090353 89204141436050853067765)
                  ·
                    refine ⟨8362888259629767475103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89204141436050853067765 8362888259629767475103)
                    ·
                      rfl

theorem cell22_24430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_24430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24430 prefixEnd_24430 := by exact prefixLift 24430
  have htrace : WordTrace (prefixWord ++ tailWord_24430) baseStart_24430 baseEnd_24430 := by
    simpa [prefixWord, tailWord_24430, baseEnd_24430] using wordTrace_append hprefix tailTrace_24430
  have hstable : (prefixWord ++ tailWord_24430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24430).length < 2 ^ (prefixWord ++ tailWord_24430).sum := by decide
  have hdescent : baseEnd_24430 < baseStart_24430 := by decide
  rcases family_descends (prefixWord ++ tailWord_24430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24473 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_24473 : Nat := 118140960795 + 24473 * 2 ^ 59
def prefixEnd_24473 : Nat := 4983230072969 + 3 ^ 40 * 24473 * 2
def baseEnd_24473 : Nat := 8377608038391988649971

theorem tailTrace_24473 : CollatzResearch.WordTrace tailWord_24473 prefixEnd_24473 8377608038391988649971 := by
  unfold tailWord_24473
  simp only [CollatzResearch.WordTrace]
  refine ⟨892603640345975500750073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 595069093563983667166715 892603640345975500750073)
  ·
    refine ⟨669452730259481625562555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 892603640345975500750073 669452730259481625562555)
    ·
      refine ⟨1004179095389222438343833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669452730259481625562555 1004179095389222438343833)
      ·
        refine ⟨753134321541916828757875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004179095389222438343833 753134321541916828757875)
        ·
          refine ⟨1129701482312875243136813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753134321541916828757875 1129701482312875243136813)
          ·
            refine ⟨423638055867328216176305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1129701482312875243136813 423638055867328216176305)
            ·
              refine ⟨317728541900496162132229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423638055867328216176305 317728541900496162132229)
              ·
                refine ⟨59574101606343030399793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317728541900496162132229 59574101606343030399793)
                ·
                  refine ⟨44680576204757272799845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59574101606343030399793 44680576204757272799845)
                  ·
                    refine ⟨8377608038391988649971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44680576204757272799845 8377608038391988649971)
                    ·
                      rfl

theorem cell22_24473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_24473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24473 prefixEnd_24473 := by exact prefixLift 24473
  have htrace : WordTrace (prefixWord ++ tailWord_24473) baseStart_24473 baseEnd_24473 := by
    simpa [prefixWord, tailWord_24473, baseEnd_24473] using wordTrace_append hprefix tailTrace_24473
  have hstable : (prefixWord ++ tailWord_24473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24473).length < 2 ^ (prefixWord ++ tailWord_24473).sum := by decide
  have hdescent : baseEnd_24473 < baseStart_24473 := by decide
  rcases family_descends (prefixWord ++ tailWord_24473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24548 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_24548 : Nat := 118140960795 + 24548 * 2 ^ 59
def prefixEnd_24548 : Nat := 4983230072969 + 3 ^ 40 * 24548 * 2
def baseEnd_24548 : Nat := 8403282071116793024741

theorem tailTrace_24548 : CollatzResearch.WordTrace tailWord_24548 prefixEnd_24548 8403282071116793024741 := by
  unfold tailWord_24548
  simp only [CollatzResearch.WordTrace]
  refine ⟨447669557537131654865149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 596892743382842206486865 447669557537131654865149)
  ·
    refine ⟨167876084076424370574431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 447669557537131654865149 167876084076424370574431)
    ·
      refine ⟨251814126114636555861647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167876084076424370574431 251814126114636555861647)
      ·
        refine ⟨377721189171954833792471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251814126114636555861647 377721189171954833792471)
        ·
          refine ⟨566581783757932250688707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377721189171954833792471 566581783757932250688707)
          ·
            refine ⟨849872675636898376033061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566581783757932250688707 849872675636898376033061)
            ·
              refine ⟨159351126681918445506199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 849872675636898376033061 159351126681918445506199)
              ·
                refine ⟨239026690022877668259299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159351126681918445506199 239026690022877668259299)
                ·
                  refine ⟨358540035034316502388949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239026690022877668259299 358540035034316502388949)
                  ·
                    refine ⟨8403282071116793024741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 358540035034316502388949 8403282071116793024741)
                    ·
                      rfl

theorem cell22_24548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_24548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24548 prefixEnd_24548 := by exact prefixLift 24548
  have htrace : WordTrace (prefixWord ++ tailWord_24548) baseStart_24548 baseEnd_24548 := by
    simpa [prefixWord, tailWord_24548, baseEnd_24548] using wordTrace_append hprefix tailTrace_24548
  have hstable : (prefixWord ++ tailWord_24548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24548).length < 2 ^ (prefixWord ++ tailWord_24548).sum := by decide
  have hdescent : baseEnd_24548 < baseStart_24548 := by decide
  rcases family_descends (prefixWord ++ tailWord_24548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24612 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 6]
def baseStart_24612 : Nat := 118140960795 + 24612 * 2 ^ 59
def prefixEnd_24612 : Nat := 4983230072969 + 3 ^ 40 * 24612 * 2
def baseEnd_24612 : Nat := 2808396859680653141515

theorem tailTrace_24612 : CollatzResearch.WordTrace tailWord_24612 prefixEnd_24612 2808396859680653141515 := by
  unfold tailWord_24612
  simp only [CollatzResearch.WordTrace]
  refine ⟨448836693421201120030045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 598448924561601493373393 448836693421201120030045)
  ·
    refine ⟨168313760032950420011267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 448836693421201120030045 168313760032950420011267)
    ·
      refine ⟨252470640049425630016901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168313760032950420011267 252470640049425630016901)
      ·
        refine ⟨47338245009267305628169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252470640049425630016901 47338245009267305628169)
        ·
          refine ⟨35503683756950479221127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47338245009267305628169 35503683756950479221127)
          ·
            refine ⟨53255525635425718831691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35503683756950479221127 53255525635425718831691)
            ·
              refine ⟨79883288453138578247537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53255525635425718831691 79883288453138578247537)
              ·
                refine ⟨59912466339853933685653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79883288453138578247537 59912466339853933685653)
                ·
                  refine ⟨2808396859680653141515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59912466339853933685653 2808396859680653141515)
                  ·
                    rfl

theorem cell22_24612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_24612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24612 prefixEnd_24612 := by exact prefixLift 24612
  have htrace : WordTrace (prefixWord ++ tailWord_24612) baseStart_24612 baseEnd_24612 := by
    simpa [prefixWord, tailWord_24612, baseEnd_24612] using wordTrace_append hprefix tailTrace_24612
  have hstable : (prefixWord ++ tailWord_24612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24612).length < 2 ^ (prefixWord ++ tailWord_24612).sum := by decide
  have hdescent : baseEnd_24612 < baseStart_24612 := by decide
  rcases family_descends (prefixWord ++ tailWord_24612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24625 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_24625 : Nat := 118140960795 + 24625 * 2 ^ 59
def prefixEnd_24625 : Nat := 4983230072969 + 3 ^ 40 * 24625 * 2
def baseEnd_24625 : Nat := 8429640744714258849505

theorem tailTrace_24625 : CollatzResearch.WordTrace tailWord_24625 prefixEnd_24625 8429640744714258849505 := by
  unfold tailWord_24625
  simp only [CollatzResearch.WordTrace]
  refine ⟨898147535795305460283329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 598765023863536973522219 898147535795305460283329)
  ·
    refine ⟨673610651846479095212497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 898147535795305460283329 673610651846479095212497)
    ·
      refine ⟨505207988884859321409373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 673610651846479095212497 505207988884859321409373)
      ·
        refine ⟨189452995831822245528515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505207988884859321409373 189452995831822245528515)
        ·
          refine ⟨284179493747733368292773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189452995831822245528515 284179493747733368292773)
          ·
            refine ⟨53283655077700006554895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284179493747733368292773 53283655077700006554895)
            ·
              refine ⟨79925482616550009832343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53283655077700006554895 79925482616550009832343)
              ·
                refine ⟨119888223924825014748515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79925482616550009832343 119888223924825014748515)
                ·
                  refine ⟨179832335887237522122773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119888223924825014748515 179832335887237522122773)
                  ·
                    refine ⟨8429640744714258849505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 179832335887237522122773 8429640744714258849505)
                    ·
                      rfl

theorem cell22_24625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_24625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24625 prefixEnd_24625 := by exact prefixLift 24625
  have htrace : WordTrace (prefixWord ++ tailWord_24625) baseStart_24625 baseEnd_24625 := by
    simpa [prefixWord, tailWord_24625, baseEnd_24625] using wordTrace_append hprefix tailTrace_24625
  have hstable : (prefixWord ++ tailWord_24625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24625).length < 2 ^ (prefixWord ++ tailWord_24625).sum := by decide
  have hdescent : baseEnd_24625 < baseStart_24625 := by decide
  rcases family_descends (prefixWord ++ tailWord_24625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24655 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 7, 3]
def baseStart_24655 : Nat := 118140960795 + 24655 * 2 ^ 59
def prefixEnd_24655 : Nat := 4983230072969 + 3 ^ 40 * 24655 * 2
def baseEnd_24655 : Nat := 8439910357804180599413

theorem tailTrace_24655 : CollatzResearch.WordTrace tailWord_24655 prefixEnd_24655 8439910357804180599413 := by
  unfold tailWord_24655
  simp only [CollatzResearch.WordTrace]
  refine ⟨899241725686620583875419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 599494483791080389250279 899241725686620583875419)
  ·
    refine ⟨1348862588529930875813129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 899241725686620583875419 1348862588529930875813129)
    ·
      refine ⟨1011646941397448156859847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1348862588529930875813129 1011646941397448156859847)
      ·
        refine ⟨1517470412096172235289771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011646941397448156859847 1517470412096172235289771)
        ·
          refine ⟨2276205618144258352934657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517470412096172235289771 2276205618144258352934657)
          ·
            refine ⟨1707154213608193764700993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276205618144258352934657 1707154213608193764700993)
            ·
              refine ⟨1280365660206145323525745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707154213608193764700993 1280365660206145323525745)
              ·
                refine ⟨960274245154608992644309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280365660206145323525745 960274245154608992644309)
                ·
                  refine ⟨22506427620811148265101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 960274245154608992644309 22506427620811148265101)
                  ·
                    refine ⟨8439910357804180599413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22506427620811148265101 8439910357804180599413)
                    ·
                      rfl

theorem cell22_24655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_24655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24655 prefixEnd_24655 := by exact prefixLift 24655
  have htrace : WordTrace (prefixWord ++ tailWord_24655) baseStart_24655 baseEnd_24655 := by
    simpa [prefixWord, tailWord_24655, baseEnd_24655] using wordTrace_append hprefix tailTrace_24655
  have hstable : (prefixWord ++ tailWord_24655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24655).length < 2 ^ (prefixWord ++ tailWord_24655).sum := by decide
  have hdescent : baseEnd_24655 < baseStart_24655 := by decide
  rcases family_descends (prefixWord ++ tailWord_24655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24672 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 3, 3]
def baseStart_24672 : Nat := 118140960795 + 24672 * 2 ^ 59
def prefixEnd_24672 : Nat := 4983230072969 + 3 ^ 40 * 24672 * 2
def baseEnd_24672 : Nat := 8445729805221802924361

theorem tailTrace_24672 : CollatzResearch.WordTrace tailWord_24672 prefixEnd_24672 8445729805221802924361 := by
  unfold tailWord_24672
  simp only [CollatzResearch.WordTrace]
  refine ⟨449930883312516243622135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 599907844416688324829513 449930883312516243622135)
  ·
    refine ⟨674896324968774365433203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 449930883312516243622135 674896324968774365433203)
    ·
      refine ⟨1012344487453161548149805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674896324968774365433203 1012344487453161548149805)
      ·
        refine ⟨379629182794935580556177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1012344487453161548149805 379629182794935580556177)
        ·
          refine ⟨284721887096201685417133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379629182794935580556177 284721887096201685417133)
          ·
            refine ⟨106770707661075632031425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284721887096201685417133 106770707661075632031425)
            ·
              refine ⟨80078030745806724023569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106770707661075632031425 80078030745806724023569)
              ·
                refine ⟨60058523059355043017677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80078030745806724023569 60058523059355043017677)
                ·
                  refine ⟨22521946147258141131629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60058523059355043017677 22521946147258141131629)
                  ·
                    refine ⟨8445729805221802924361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22521946147258141131629 8445729805221802924361)
                    ·
                      rfl

theorem cell22_24672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_24672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24672 prefixEnd_24672 := by exact prefixLift 24672
  have htrace : WordTrace (prefixWord ++ tailWord_24672) baseStart_24672 baseEnd_24672 := by
    simpa [prefixWord, tailWord_24672, baseEnd_24672] using wordTrace_append hprefix tailTrace_24672
  have hstable : (prefixWord ++ tailWord_24672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24672).length < 2 ^ (prefixWord ++ tailWord_24672).sum := by decide
  have hdescent : baseEnd_24672 < baseStart_24672 := by decide
  rcases family_descends (prefixWord ++ tailWord_24672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24685 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 9]
def baseStart_24685 : Nat := 118140960795 + 24685 * 2 ^ 59
def prefixEnd_24685 : Nat := 4983230072969 + 3 ^ 40 * 24685 * 2
def baseEnd_24685 : Nat := 2816726656964700783107

theorem tailTrace_24685 : CollatzResearch.WordTrace tailWord_24685 prefixEnd_24685 2816726656964700783107 := by
  unfold tailWord_24685
  simp only [CollatzResearch.WordTrace]
  refine ⟨900335915577935707467509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 600223943718623804978339 900335915577935707467509)
  ·
    refine ⟨84406492085431472575079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 900335915577935707467509 84406492085431472575079)
    ·
      refine ⟨126609738128147208862619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84406492085431472575079 126609738128147208862619)
      ·
        refine ⟨189914607192220813293929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126609738128147208862619 189914607192220813293929)
        ·
          refine ⟨142435955394165609970447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189914607192220813293929 142435955394165609970447)
          ·
            refine ⟨213653933091248414955671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142435955394165609970447 213653933091248414955671)
            ·
              refine ⟨320480899636872622433507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213653933091248414955671 320480899636872622433507)
              ·
                refine ⟨480721349455308933650261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320480899636872622433507 480721349455308933650261)
                ·
                  refine ⟨2816726656964700783107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 480721349455308933650261 2816726656964700783107)
                  ·
                    rfl

theorem cell22_24685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_24685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24685 prefixEnd_24685 := by exact prefixLift 24685
  have htrace : WordTrace (prefixWord ++ tailWord_24685) baseStart_24685 baseEnd_24685 := by
    simpa [prefixWord, tailWord_24685, baseEnd_24685] using wordTrace_append hprefix tailTrace_24685
  have hstable : (prefixWord ++ tailWord_24685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24685).length < 2 ^ (prefixWord ++ tailWord_24685).sum := by decide
  have hdescent : baseEnd_24685 < baseStart_24685 := by decide
  rcases family_descends (prefixWord ++ tailWord_24685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24732 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_24732 : Nat := 118140960795 + 24732 * 2 ^ 59
def prefixEnd_24732 : Nat := 4983230072969 + 3 ^ 40 * 24732 * 2
def baseEnd_24732 : Nat := 8466269031401646424177

theorem tailTrace_24732 : CollatzResearch.WordTrace tailWord_24732 prefixEnd_24732 8466269031401646424177 := by
  unfold tailWord_24732
  simp only [CollatzResearch.WordTrace]
  refine ⟨451025073203831367214225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 601366764271775156285633 451025073203831367214225)
  ·
    refine ⟨338268804902873525410669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 451025073203831367214225 338268804902873525410669)
    ·
      refine ⟨126850801838577572029001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338268804902873525410669 126850801838577572029001)
      ·
        refine ⟨95138101378933179021751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126850801838577572029001 95138101378933179021751)
        ·
          refine ⟨142707152068399768532627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95138101378933179021751 142707152068399768532627)
          ·
            refine ⟨214060728102599652798941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142707152068399768532627 214060728102599652798941)
            ·
              refine ⟨80272773038474869799603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214060728102599652798941 80272773038474869799603)
              ·
                refine ⟨120409159557712304699405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80272773038474869799603 120409159557712304699405)
                ·
                  refine ⟨45153434834142114262277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120409159557712304699405 45153434834142114262277)
                  ·
                    refine ⟨8466269031401646424177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45153434834142114262277 8466269031401646424177)
                    ·
                      rfl

theorem cell22_24732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_24732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24732 prefixEnd_24732 := by exact prefixLift 24732
  have htrace : WordTrace (prefixWord ++ tailWord_24732) baseStart_24732 baseEnd_24732 := by
    simpa [prefixWord, tailWord_24732, baseEnd_24732] using wordTrace_append hprefix tailTrace_24732
  have hstable : (prefixWord ++ tailWord_24732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24732).length < 2 ^ (prefixWord ++ tailWord_24732).sum := by decide
  have hdescent : baseEnd_24732 < baseStart_24732 := by decide
  rcases family_descends (prefixWord ++ tailWord_24732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24757 : List Nat := [1, 3, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_24757 : Nat := 118140960795 + 24757 * 2 ^ 59
def prefixEnd_24757 : Nat := 4983230072969 + 3 ^ 40 * 24757 * 2
def baseEnd_24757 : Nat := 8474827042309914549101

theorem tailTrace_24757 : CollatzResearch.WordTrace tailWord_24757 prefixEnd_24757 8474827042309914549101 := by
  unfold tailWord_24757
  simp only [CollatzResearch.WordTrace]
  refine ⟨902961971317092004088525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 601974647544728002725683 902961971317092004088525)
  ·
    refine ⟨338610739243909501533197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 902961971317092004088525 338610739243909501533197)
    ·
      refine ⟨126979027216466063074949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338610739243909501533197 126979027216466063074949)
      ·
        refine ⟨23808567603087386826553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126979027216466063074949 23808567603087386826553)
        ·
          refine ⟨17856425702315540119915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23808567603087386826553 17856425702315540119915)
          ·
            refine ⟨26784638553473310179873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17856425702315540119915 26784638553473310179873)
            ·
              refine ⟨20088478915104982634905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26784638553473310179873 20088478915104982634905)
              ·
                refine ⟨15066359186328736976179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20088478915104982634905 15066359186328736976179)
                ·
                  refine ⟨22599538779493105464269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15066359186328736976179 22599538779493105464269)
                  ·
                    refine ⟨8474827042309914549101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22599538779493105464269 8474827042309914549101)
                    ·
                      rfl

theorem cell22_24757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_24757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24757 prefixEnd_24757 := by exact prefixLift 24757
  have htrace : WordTrace (prefixWord ++ tailWord_24757) baseStart_24757 baseEnd_24757 := by
    simpa [prefixWord, tailWord_24757, baseEnd_24757] using wordTrace_append hprefix tailTrace_24757
  have hstable : (prefixWord ++ tailWord_24757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24757).length < 2 ^ (prefixWord ++ tailWord_24757).sum := by decide
  have hdescent : baseEnd_24757 < baseStart_24757 := by decide
  rcases family_descends (prefixWord ++ tailWord_24757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24762 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_24762 : Nat := 118140960795 + 24762 * 2 ^ 59
def prefixEnd_24762 : Nat := 4983230072969 + 3 ^ 40 * 24762 * 2
def baseEnd_24762 : Nat := 8476538644491568174085

theorem tailTrace_24762 : CollatzResearch.WordTrace tailWord_24762 prefixEnd_24762 8476538644491568174085 := by
  unfold tailWord_24762
  simp only [CollatzResearch.WordTrace]
  refine ⟨225786084074744464505135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 602096224199318572013693 225786084074744464505135)
  ·
    refine ⟨338679126112116696757703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225786084074744464505135 338679126112116696757703)
    ·
      refine ⟨508018689168175045136555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338679126112116696757703 508018689168175045136555)
      ·
        refine ⟨762028033752262567704833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508018689168175045136555 762028033752262567704833)
        ·
          refine ⟨571521025314196925778625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762028033752262567704833 571521025314196925778625)
          ·
            refine ⟨428640768985647694333969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571521025314196925778625 428640768985647694333969)
            ·
              refine ⟨321480576739235770750477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428640768985647694333969 321480576739235770750477)
              ·
                refine ⟨120555216277213414031429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321480576739235770750477 120555216277213414031429)
                ·
                  refine ⟨22604103051977515130893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120555216277213414031429 22604103051977515130893)
                  ·
                    refine ⟨8476538644491568174085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22604103051977515130893 8476538644491568174085)
                    ·
                      rfl

theorem cell22_24762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_24762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24762 prefixEnd_24762 := by exact prefixLift 24762
  have htrace : WordTrace (prefixWord ++ tailWord_24762) baseStart_24762 baseEnd_24762 := by
    simpa [prefixWord, tailWord_24762, baseEnd_24762] using wordTrace_append hprefix tailTrace_24762
  have hstable : (prefixWord ++ tailWord_24762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24762).length < 2 ^ (prefixWord ++ tailWord_24762).sum := by decide
  have hdescent : baseEnd_24762 < baseStart_24762 := by decide
  rcases family_descends (prefixWord ++ tailWord_24762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24813 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_24813 : Nat := 118140960795 + 24813 * 2 ^ 59
def prefixEnd_24813 : Nat := 4983230072969 + 3 ^ 40 * 24813 * 2
def baseEnd_24813 : Nat := 8493996986744435148929

theorem tailTrace_24813 : CollatzResearch.WordTrace tailWord_24813 prefixEnd_24813 8493996986744435148929 := by
  unfold tailWord_24813
  simp only [CollatzResearch.WordTrace]
  refine ⟨905004459114213568127093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 603336306076142378751395 905004459114213568127093)
  ·
    refine ⟨84844168041957522011915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 905004459114213568127093 84844168041957522011915)
    ·
      refine ⟨127266252062936283017873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84844168041957522011915 127266252062936283017873)
      ·
        refine ⟨95449689047202212263405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127266252062936283017873 95449689047202212263405)
        ·
          refine ⟨35793633392700829598777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95449689047202212263405 35793633392700829598777)
          ·
            refine ⟨26845225044525622199083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35793633392700829598777 26845225044525622199083)
            ·
              refine ⟨40267837566788433298625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26845225044525622199083 40267837566788433298625)
              ·
                refine ⟨30200878175091324973969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40267837566788433298625 30200878175091324973969)
                ·
                  refine ⟨22650658631318493730477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30200878175091324973969 22650658631318493730477)
                  ·
                    refine ⟨8493996986744435148929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22650658631318493730477 8493996986744435148929)
                    ·
                      rfl

theorem cell22_24813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_24813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24813 prefixEnd_24813 := by exact prefixLift 24813
  have htrace : WordTrace (prefixWord ++ tailWord_24813) baseStart_24813 baseEnd_24813 := by
    simpa [prefixWord, tailWord_24813, baseEnd_24813] using wordTrace_append hprefix tailTrace_24813
  have hstable : (prefixWord ++ tailWord_24813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24813).length < 2 ^ (prefixWord ++ tailWord_24813).sum := by decide
  have hdescent : baseEnd_24813 < baseStart_24813 := by decide
  rcases family_descends (prefixWord ++ tailWord_24813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24822 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_24822 : Nat := 118140960795 + 24822 * 2 ^ 59
def prefixEnd_24822 : Nat := 4983230072969 + 3 ^ 40 * 24822 * 2
def baseEnd_24822 : Nat := 8497077870671411673901

theorem tailTrace_24822 : CollatzResearch.WordTrace tailWord_24822 prefixEnd_24822 8497077870671411673901 := by
  unfold tailWord_24822
  simp only [CollatzResearch.WordTrace]
  refine ⟨56583294755100506575295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 603555144054405403469813 56583294755100506575295)
  ·
    refine ⟨84874942132650759862943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56583294755100506575295 84874942132650759862943)
    ·
      refine ⟨127312413198976139794415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84874942132650759862943 127312413198976139794415)
      ·
        refine ⟨190968619798464209691623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127312413198976139794415 190968619798464209691623)
        ·
          refine ⟨286452929697696314537435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190968619798464209691623 286452929697696314537435)
          ·
            refine ⟨429679394546544471806153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286452929697696314537435 429679394546544471806153)
            ·
              refine ⟨322259545909908353854615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429679394546544471806153 322259545909908353854615)
              ·
                refine ⟨483389318864862530781923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322259545909908353854615 483389318864862530781923)
                ·
                  refine ⟨725083978297293796172885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483389318864862530781923 725083978297293796172885)
                  ·
                    refine ⟨8497077870671411673901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 725083978297293796172885 8497077870671411673901)
                    ·
                      rfl

theorem cell22_24822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_24822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24822 prefixEnd_24822 := by exact prefixLift 24822
  have htrace : WordTrace (prefixWord ++ tailWord_24822) baseStart_24822 baseEnd_24822 := by
    simpa [prefixWord, tailWord_24822, baseEnd_24822] using wordTrace_append hprefix tailTrace_24822
  have hstable : (prefixWord ++ tailWord_24822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24822).length < 2 ^ (prefixWord ++ tailWord_24822).sum := by decide
  have hdescent : baseEnd_24822 < baseStart_24822 := by decide
  rcases family_descends (prefixWord ++ tailWord_24822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24914 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_24914 : Nat := 118140960795 + 24914 * 2 ^ 59
def prefixEnd_24914 : Nat := 4983230072969 + 3 ^ 40 * 24914 * 2
def baseEnd_24914 : Nat := 8528571350813838373619

theorem tailTrace_24914 : CollatzResearch.WordTrace tailWord_24914 prefixEnd_24914 8528571350813838373619 := by
  unfold tailWord_24914
  simp only [CollatzResearch.WordTrace]
  refine ⟨227172057937076954388449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 605792154498871878369197 227172057937076954388449)
  ·
    refine ⟨170379043452807715791337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227172057937076954388449 170379043452807715791337)
    ·
      refine ⟨127784282589605786843503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170379043452807715791337 127784282589605786843503)
      ·
        refine ⟨191676423884408680265255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127784282589605786843503 191676423884408680265255)
        ·
          refine ⟨287514635826613020397883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191676423884408680265255 287514635826613020397883)
          ·
            refine ⟨431271953739919530596825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287514635826613020397883 431271953739919530596825)
            ·
              refine ⟨323453965304939647947619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431271953739919530596825 323453965304939647947619)
              ·
                refine ⟨485180947957409471921429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323453965304939647947619 485180947957409471921429)
                ·
                  refine ⟨22742856935503568996317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 485180947957409471921429 22742856935503568996317)
                  ·
                    refine ⟨8528571350813838373619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22742856935503568996317 8528571350813838373619)
                    ·
                      rfl

theorem cell22_24914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_24914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24914 prefixEnd_24914 := by exact prefixLift 24914
  have htrace : WordTrace (prefixWord ++ tailWord_24914) baseStart_24914 baseEnd_24914 := by
    simpa [prefixWord, tailWord_24914, baseEnd_24914] using wordTrace_append hprefix tailTrace_24914
  have hstable : (prefixWord ++ tailWord_24914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24914).length < 2 ^ (prefixWord ++ tailWord_24914).sum := by decide
  have hdescent : baseEnd_24914 < baseStart_24914 := by decide
  rcases family_descends (prefixWord ++ tailWord_24914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24931 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 2, 3]
def baseStart_24931 : Nat := 118140960795 + 24931 * 2 ^ 59
def prefixEnd_24931 : Nat := 4983230072969 + 3 ^ 40 * 24931 * 2
def baseEnd_24931 : Nat := 8534390798231460698567

theorem tailTrace_24931 : CollatzResearch.WordTrace tailWord_24931 prefixEnd_24931 8534390798231460698567 := by
  unfold tailWord_24931
  simp only [CollatzResearch.WordTrace]
  refine ⟨909308272686719720922647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606205515124479813948431 909308272686719720922647)
  ·
    refine ⟨1363962409030079581383971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 909308272686719720922647 1363962409030079581383971)
    ·
      refine ⟨2045943613545119372075957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363962409030079581383971 2045943613545119372075957)
      ·
        refine ⟨191807213769854941132121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2045943613545119372075957 191807213769854941132121)
        ·
          refine ⟨143855410327391205849091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191807213769854941132121 143855410327391205849091)
          ·
            refine ⟨215783115491086808773637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143855410327391205849091 215783115491086808773637)
            ·
              refine ⟨40459334154578776645057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215783115491086808773637 40459334154578776645057)
              ·
                refine ⟨30344500615934082483793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40459334154578776645057 30344500615934082483793)
                ·
                  refine ⟨22758375461950561862845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30344500615934082483793 22758375461950561862845)
                  ·
                    refine ⟨8534390798231460698567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22758375461950561862845 8534390798231460698567)
                    ·
                      rfl

theorem cell22_24931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 3].length) (baseStart_24931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24931 prefixEnd_24931 := by exact prefixLift 24931
  have htrace : WordTrace (prefixWord ++ tailWord_24931) baseStart_24931 baseEnd_24931 := by
    simpa [prefixWord, tailWord_24931, baseEnd_24931] using wordTrace_append hprefix tailTrace_24931
  have hstable : (prefixWord ++ tailWord_24931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24931).length < 2 ^ (prefixWord ++ tailWord_24931).sum := by decide
  have hdescent : baseEnd_24931 < baseStart_24931 := by decide
  rcases family_descends (prefixWord ++ tailWord_24931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24933 : List Nat := [1, 3, 1, 3, 1, 5, 2, 2, 4]
def baseStart_24933 : Nat := 118140960795 + 24933 * 2 ^ 59
def prefixEnd_24933 : Nat := 4983230072969 + 3 ^ 40 * 24933 * 2
def baseEnd_24933 : Nat := 2845025146368040716187

theorem tailTrace_24933 : CollatzResearch.WordTrace tailWord_24933 prefixEnd_24933 2845025146368040716187 := by
  unfold tailWord_24933
  simp only [CollatzResearch.WordTrace]
  refine ⟨909381218679474062495453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606254145786316041663635 909381218679474062495453)
  ·
    refine ⟨341017957004802773435795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 909381218679474062495453 341017957004802773435795)
    ·
      refine ⟨511526935507204160153693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341017957004802773435795 511526935507204160153693)
      ·
        refine ⟨191822600815201560057635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511526935507204160153693 191822600815201560057635)
        ·
          refine ⟨287733901222802340086453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191822600815201560057635 287733901222802340086453)
          ·
            refine ⟨26975053239637719383105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287733901222802340086453 26975053239637719383105)
            ·
              refine ⟨20231289929728289537329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26975053239637719383105 20231289929728289537329)
              ·
                refine ⟨15173467447296217152997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20231289929728289537329 15173467447296217152997)
                ·
                  refine ⟨2845025146368040716187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15173467447296217152997 2845025146368040716187)
                  ·
                    rfl

theorem cell22_24933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_24933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24933 prefixEnd_24933 := by exact prefixLift 24933
  have htrace : WordTrace (prefixWord ++ tailWord_24933) baseStart_24933 baseEnd_24933 := by
    simpa [prefixWord, tailWord_24933, baseEnd_24933] using wordTrace_append hprefix tailTrace_24933
  have hstable : (prefixWord ++ tailWord_24933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24933).length < 2 ^ (prefixWord ++ tailWord_24933).sum := by decide
  have hdescent : baseEnd_24933 < baseStart_24933 := by decide
  rcases family_descends (prefixWord ++ tailWord_24933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24944 : List Nat := [2, 1, 1, 1, 4, 5, 1, 7]
def baseStart_24944 : Nat := 118140960795 + 24944 * 2 ^ 59
def prefixEnd_24944 : Nat := 4983230072969 + 3 ^ 40 * 24944 * 2
def baseEnd_24944 : Nat := 948760107100417791503

theorem tailTrace_24944 : CollatzResearch.WordTrace tailWord_24944 prefixEnd_24944 948760107100417791503 := by
  unfold tailWord_24944
  simp only [CollatzResearch.WordTrace]
  refine ⟨454891210819811470572943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 606521614426415294097257 454891210819811470572943)
  ·
    refine ⟨682336816229717205859415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454891210819811470572943 682336816229717205859415)
    ·
      refine ⟨1023505224344575808789123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682336816229717205859415 1023505224344575808789123)
      ·
        refine ⟨1535257836516863713183685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023505224344575808789123 1535257836516863713183685)
        ·
          refine ⟨287860844346911946221941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1535257836516863713183685 287860844346911946221941)
          ·
            refine ⟨26986954157522994958307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287860844346911946221941 26986954157522994958307)
            ·
              refine ⟨40480431236284492437461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26986954157522994958307 40480431236284492437461)
              ·
                refine ⟨948760107100417791503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40480431236284492437461 948760107100417791503)
                ·
                  rfl

theorem cell22_24944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 7].length) (baseStart_24944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24944 prefixEnd_24944 := by exact prefixLift 24944
  have htrace : WordTrace (prefixWord ++ tailWord_24944) baseStart_24944 baseEnd_24944 := by
    simpa [prefixWord, tailWord_24944, baseEnd_24944] using wordTrace_append hprefix tailTrace_24944
  have hstable : (prefixWord ++ tailWord_24944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24944).length < 2 ^ (prefixWord ++ tailWord_24944).sum := by decide
  have hdescent : baseEnd_24944 < baseStart_24944 := by decide
  rcases family_descends (prefixWord ++ tailWord_24944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24959 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 3, 3]
def baseStart_24959 : Nat := 118140960795 + 24959 * 2 ^ 59
def prefixEnd_24959 : Nat := 4983230072969 + 3 ^ 40 * 24959 * 2
def baseEnd_24959 : Nat := 8543975770448720998481

theorem tailTrace_24959 : CollatzResearch.WordTrace tailWord_24959 prefixEnd_24959 8543975770448720998481 := by
  unfold tailWord_24959
  simp only [CollatzResearch.WordTrace]
  refine ⟨910329516585280502941931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606886344390187001961287 910329516585280502941931)
  ·
    refine ⟨1365494274877920754412897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910329516585280502941931 1365494274877920754412897)
    ·
      refine ⟨1024120706158440565809673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1365494274877920754412897 1024120706158440565809673)
      ·
        refine ⟨768090529618830424357255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024120706158440565809673 768090529618830424357255)
        ·
          refine ⟨1152135794428245636535883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768090529618830424357255 1152135794428245636535883)
          ·
            refine ⟨1728203691642368454803825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152135794428245636535883 1728203691642368454803825)
            ·
              refine ⟨1296152768731776341102869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728203691642368454803825 1296152768731776341102869)
              ·
                refine ⟨60757161034302015989197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1296152768731776341102869 60757161034302015989197)
                ·
                  refine ⟨22783935387863255995949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60757161034302015989197 22783935387863255995949)
                  ·
                    refine ⟨8543975770448720998481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22783935387863255995949 8543975770448720998481)
                    ·
                      rfl

theorem cell22_24959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_24959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24959 prefixEnd_24959 := by exact prefixLift 24959
  have htrace : WordTrace (prefixWord ++ tailWord_24959) baseStart_24959 baseEnd_24959 := by
    simpa [prefixWord, tailWord_24959, baseEnd_24959] using wordTrace_append hprefix tailTrace_24959
  have hstable : (prefixWord ++ tailWord_24959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24959).length < 2 ^ (prefixWord ++ tailWord_24959).sum := by decide
  have hdescent : baseEnd_24959 < baseStart_24959 := by decide
  rcases family_descends (prefixWord ++ tailWord_24959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24961 : List Nat := [1, 2, 4, 3, 1, 2, 3, 6]
def baseStart_24961 : Nat := 118140960795 + 24961 * 2 ^ 59
def prefixEnd_24961 : Nat := 4983230072969 + 3 ^ 40 * 24961 * 2
def baseEnd_24961 : Nat := 949406712369042494275

theorem tailTrace_24961 : CollatzResearch.WordTrace tailWord_24961 prefixEnd_24961 949406712369042494275 := by
  unfold tailWord_24961
  simp only [CollatzResearch.WordTrace]
  refine ⟨910402462578034844514737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606934975052023229676491 910402462578034844514737)
  ·
    refine ⟨682801846933526133386053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 910402462578034844514737 682801846933526133386053)
    ·
      refine ⟨128025346300036150009885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 682801846933526133386053 128025346300036150009885)
      ·
        refine ⟨48009504862513556253707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128025346300036150009885 48009504862513556253707)
        ·
          refine ⟨72014257293770334380561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48009504862513556253707 72014257293770334380561)
          ·
            refine ⟨54010692970327750785421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72014257293770334380561 54010692970327750785421)
            ·
              refine ⟨20254009863872906544533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54010692970327750785421 20254009863872906544533)
              ·
                refine ⟨949406712369042494275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20254009863872906544533 949406712369042494275)
                ·
                  rfl

theorem cell22_24961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 6].length) (baseStart_24961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24961 prefixEnd_24961 := by exact prefixLift 24961
  have htrace : WordTrace (prefixWord ++ tailWord_24961) baseStart_24961 baseEnd_24961 := by
    simpa [prefixWord, tailWord_24961, baseEnd_24961] using wordTrace_append hprefix tailTrace_24961
  have hstable : (prefixWord ++ tailWord_24961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24961).length < 2 ^ (prefixWord ++ tailWord_24961).sum := by decide
  have hdescent : baseEnd_24961 < baseStart_24961 := by decide
  rcases family_descends (prefixWord ++ tailWord_24961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24963 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 2, 4]
def baseStart_24963 : Nat := 118140960795 + 24963 * 2 ^ 59
def prefixEnd_24963 : Nat := 4983230072969 + 3 ^ 40 * 24963 * 2
def baseEnd_24963 : Nat := 8545345052194043898469

theorem tailTrace_24963 : CollatzResearch.WordTrace tailWord_24963 prefixEnd_24963 8545345052194043898469 := by
  unfold tailWord_24963
  simp only [CollatzResearch.WordTrace]
  refine ⟨910475408570789186087543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 606983605713859457391695 910475408570789186087543)
  ·
    refine ⟨1365713112856183779131315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910475408570789186087543 1365713112856183779131315)
    ·
      refine ⟨2048569669284275668696973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365713112856183779131315 2048569669284275668696973)
      ·
        refine ⟨768213625981603375761365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2048569669284275668696973 768213625981603375761365)
        ·
          refine ⟨18005006858943829119407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 768213625981603375761365 18005006858943829119407)
          ·
            refine ⟨27007510288415743679111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18005006858943829119407 27007510288415743679111)
            ·
              refine ⟨40511265432623615518667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27007510288415743679111 40511265432623615518667)
              ·
                refine ⟨60766898148935423278001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40511265432623615518667 60766898148935423278001)
                ·
                  refine ⟨45575173611701567458501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60766898148935423278001 45575173611701567458501)
                  ·
                    refine ⟨8545345052194043898469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45575173611701567458501 8545345052194043898469)
                    ·
                      rfl

theorem cell22_24963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 4].length) (baseStart_24963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24963 prefixEnd_24963 := by exact prefixLift 24963
  have htrace : WordTrace (prefixWord ++ tailWord_24963) baseStart_24963 baseEnd_24963 := by
    simpa [prefixWord, tailWord_24963, baseEnd_24963] using wordTrace_append hprefix tailTrace_24963
  have hstable : (prefixWord ++ tailWord_24963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24963).length < 2 ^ (prefixWord ++ tailWord_24963).sum := by decide
  have hdescent : baseEnd_24963 < baseStart_24963 := by decide
  rcases family_descends (prefixWord ++ tailWord_24963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24982 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_24982 : Nat := 118140960795 + 24982 * 2 ^ 59
def prefixEnd_24982 : Nat := 4983230072969 + 3 ^ 40 * 24982 * 2
def baseEnd_24982 : Nat := 8551849140484327673411

theorem tailTrace_24982 : CollatzResearch.WordTrace tailWord_24982 prefixEnd_24982 8551849140484327673411 := by
  unfold tailWord_24982
  simp only [CollatzResearch.WordTrace]
  refine ⟨56948024718872214439325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 607445597001303620686133 56948024718872214439325)
  ·
    refine ⟨21355509269577080414747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56948024718872214439325 21355509269577080414747)
    ·
      refine ⟨32033263904365620622121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21355509269577080414747 32033263904365620622121)
      ·
        refine ⟨24024947928274215466591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32033263904365620622121 24024947928274215466591)
        ·
          refine ⟨36037421892411323199887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24024947928274215466591 36037421892411323199887)
          ·
            refine ⟨54056132838616984799831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36037421892411323199887 54056132838616984799831)
            ·
              refine ⟨81084199257925477199747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54056132838616984799831 81084199257925477199747)
              ·
                refine ⟨121626298886888215799621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81084199257925477199747 121626298886888215799621)
                ·
                  refine ⟨22804931041291540462429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121626298886888215799621 22804931041291540462429)
                  ·
                    refine ⟨8551849140484327673411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22804931041291540462429 8551849140484327673411)
                    ·
                      rfl

theorem cell22_24982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_24982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_24982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_24982 prefixEnd_24982 := by exact prefixLift 24982
  have htrace : WordTrace (prefixWord ++ tailWord_24982) baseStart_24982 baseEnd_24982 := by
    simpa [prefixWord, tailWord_24982, baseEnd_24982] using wordTrace_append hprefix tailTrace_24982
  have hstable : (prefixWord ++ tailWord_24982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24982).length < 2 ^ (prefixWord ++ tailWord_24982).sum := by decide
  have hdescent : baseEnd_24982 < baseStart_24982 := by decide
  rcases family_descends (prefixWord ++ tailWord_24982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25012 : List Nat := [2, 5, 2, 2, 2, 1, 2, 6]
def baseStart_25012 : Nat := 118140960795 + 25012 * 2 ^ 59
def prefixEnd_25012 : Nat := 4983230072969 + 3 ^ 40 * 25012 * 2
def baseEnd_25012 : Nat := 951346528174916602591

theorem tailTrace_25012 : CollatzResearch.WordTrace tailWord_25012 prefixEnd_25012 951346528174916602591 := by
  unfold tailWord_25012
  simp only [CollatzResearch.WordTrace]
  refine ⟨456131292696635277310645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 608175056928847036414193 456131292696635277310645)
  ·
    refine ⟨42762308690309557247873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 456131292696635277310645 42762308690309557247873)
    ·
      refine ⟨32071731517732167935905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42762308690309557247873 32071731517732167935905)
      ·
        refine ⟨24053798638299125951929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32071731517732167935905 24053798638299125951929)
        ·
          refine ⟨18040348978724344463947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24053798638299125951929 18040348978724344463947)
          ·
            refine ⟨27060523468086516695921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18040348978724344463947 27060523468086516695921)
            ·
              refine ⟨20295392601064887521941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27060523468086516695921 20295392601064887521941)
              ·
                refine ⟨951346528174916602591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20295392601064887521941 951346528174916602591)
                ·
                  rfl

theorem cell22_25012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 6].length) (baseStart_25012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25012 prefixEnd_25012 := by exact prefixLift 25012
  have htrace : WordTrace (prefixWord ++ tailWord_25012) baseStart_25012 baseEnd_25012 := by
    simpa [prefixWord, tailWord_25012, baseEnd_25012] using wordTrace_append hprefix tailTrace_25012
  have hstable : (prefixWord ++ tailWord_25012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25012).length < 2 ^ (prefixWord ++ tailWord_25012).sum := by decide
  have hdescent : baseEnd_25012 < baseStart_25012 := by decide
  rcases family_descends (prefixWord ++ tailWord_25012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25109 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_25109 : Nat := 118140960795 + 25109 * 2 ^ 59
def prefixEnd_25109 : Nat := 4983230072969 + 3 ^ 40 * 25109 * 2
def baseEnd_25109 : Nat := 8595323835898329748021

theorem tailTrace_25109 : CollatzResearch.WordTrace tailWord_25109 prefixEnd_25109 8595323835898329748021 := by
  unfold tailWord_25109
  simp only [CollatzResearch.WordTrace]
  refine ⟨915800466041856120902381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 610533644027904080601587 915800466041856120902381)
  ·
    refine ⟨343425174765696045338393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 915800466041856120902381 343425174765696045338393)
    ·
      refine ⟨257568881074272034003795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343425174765696045338393 257568881074272034003795)
      ·
        refine ⟨386353321611408051005693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257568881074272034003795 386353321611408051005693)
        ·
          refine ⟨144882495604278019127135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386353321611408051005693 144882495604278019127135)
          ·
            refine ⟨217323743406417028690703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144882495604278019127135 217323743406417028690703)
            ·
              refine ⟨325985615109625543036055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217323743406417028690703 325985615109625543036055)
              ·
                refine ⟨488978422664438314554083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325985615109625543036055 488978422664438314554083)
                ·
                  refine ⟨733467633996657471831125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488978422664438314554083 733467633996657471831125)
                  ·
                    refine ⟨8595323835898329748021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 733467633996657471831125 8595323835898329748021)
                    ·
                      rfl

theorem cell22_25109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_25109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25109 prefixEnd_25109 := by exact prefixLift 25109
  have htrace : WordTrace (prefixWord ++ tailWord_25109) baseStart_25109 baseEnd_25109 := by
    simpa [prefixWord, tailWord_25109, baseEnd_25109] using wordTrace_append hprefix tailTrace_25109
  have hstable : (prefixWord ++ tailWord_25109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25109).length < 2 ^ (prefixWord ++ tailWord_25109).sum := by decide
  have hdescent : baseEnd_25109 < baseStart_25109 := by decide
  rcases family_descends (prefixWord ++ tailWord_25109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25128 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 5, 3]
def baseStart_25128 : Nat := 118140960795 + 25128 * 2 ^ 59
def prefixEnd_25128 : Nat := 4983230072969 + 3 ^ 40 * 25128 * 2
def baseEnd_25128 : Nat := 8601827924188613522963

theorem tailTrace_25128 : CollatzResearch.WordTrace tailWord_25128 prefixEnd_25128 8601827924188613522963 := by
  unfold tailWord_25128
  simp only [CollatzResearch.WordTrace]
  refine ⟨458246726486511182922019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 610995635315348243896025 458246726486511182922019)
  ·
    refine ⟨687370089729766774383029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 458246726486511182922019 687370089729766774383029)
    ·
      refine ⟨64440945912165635098409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 687370089729766774383029 64440945912165635098409)
      ·
        refine ⟨48330709434124226323807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64440945912165635098409 48330709434124226323807)
        ·
          refine ⟨72496064151186339485711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48330709434124226323807 72496064151186339485711)
          ·
            refine ⟨108744096226779509228567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72496064151186339485711 108744096226779509228567)
            ·
              refine ⟨163116144340169263842851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108744096226779509228567 163116144340169263842851)
              ·
                refine ⟨244674216510253895764277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163116144340169263842851 244674216510253895764277)
                ·
                  refine ⟨22938207797836302727901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244674216510253895764277 22938207797836302727901)
                  ·
                    refine ⟨8601827924188613522963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22938207797836302727901 8601827924188613522963)
                    ·
                      rfl

theorem cell22_25128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_25128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25128 prefixEnd_25128 := by exact prefixLift 25128
  have htrace : WordTrace (prefixWord ++ tailWord_25128) baseStart_25128 baseEnd_25128 := by
    simpa [prefixWord, tailWord_25128, baseEnd_25128] using wordTrace_append hprefix tailTrace_25128
  have hstable : (prefixWord ++ tailWord_25128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25128).length < 2 ^ (prefixWord ++ tailWord_25128).sum := by decide
  have hdescent : baseEnd_25128 < baseStart_25128 := by decide
  rcases family_descends (prefixWord ++ tailWord_25128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25139 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 1, 7]
def baseStart_25139 : Nat := 118140960795 + 25139 * 2 ^ 59
def prefixEnd_25139 : Nat := 4983230072969 + 3 ^ 40 * 25139 * 2
def baseEnd_25139 : Nat := 8605593448988251497929

theorem tailTrace_25139 : CollatzResearch.WordTrace tailWord_25139 prefixEnd_25139 8605593448988251497929 := by
  unfold tailWord_25139
  simp only [CollatzResearch.WordTrace]
  refine ⟨916894655933171244494471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 611263103955447496329647 916894655933171244494471)
  ·
    refine ⟨1375341983899756866741707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 916894655933171244494471 1375341983899756866741707)
    ·
      refine ⟨2063012975849635300112561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375341983899756866741707 2063012975849635300112561)
      ·
        refine ⟨1547259731887226475084421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2063012975849635300112561 1547259731887226475084421)
        ·
          refine ⟨290111199728854964078329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1547259731887226475084421 290111199728854964078329)
          ·
            refine ⟨217583399796641223058747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290111199728854964078329 217583399796641223058747)
            ·
              refine ⟨326375099694961834588121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217583399796641223058747 326375099694961834588121)
              ·
                refine ⟨244781324771221375941091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326375099694961834588121 244781324771221375941091)
                ·
                  refine ⟨367171987156832063911637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244781324771221375941091 367171987156832063911637)
                  ·
                    refine ⟨8605593448988251497929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 367171987156832063911637 8605593448988251497929)
                    ·
                      rfl

theorem cell22_25139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_25139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25139 prefixEnd_25139 := by exact prefixLift 25139
  have htrace : WordTrace (prefixWord ++ tailWord_25139) baseStart_25139 baseEnd_25139 := by
    simpa [prefixWord, tailWord_25139, baseEnd_25139] using wordTrace_append hprefix tailTrace_25139
  have hstable : (prefixWord ++ tailWord_25139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25139).length < 2 ^ (prefixWord ++ tailWord_25139).sum := by decide
  have hdescent : baseEnd_25139 < baseStart_25139 := by decide
  rcases family_descends (prefixWord ++ tailWord_25139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25145 : List Nat := [1, 2, 1, 5, 1, 1, 4, 3, 1, 3]
def baseStart_25145 : Nat := 118140960795 + 25145 * 2 ^ 59
def prefixEnd_25145 : Nat := 4983230072969 + 3 ^ 40 * 25145 * 2
def baseEnd_25145 : Nat := 8607647371606235847911

theorem tailTrace_25145 : CollatzResearch.WordTrace tailWord_25145 prefixEnd_25145 8607647371606235847911 := by
  unfold tailWord_25145
  simp only [CollatzResearch.WordTrace]
  refine ⟨917113493911434269212889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 611408995940956179475259 917113493911434269212889)
  ·
    refine ⟨687835120433575701909667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 917113493911434269212889 687835120433575701909667)
    ·
      refine ⟨1031752680650363552864501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687835120433575701909667 1031752680650363552864501)
      ·
        refine ⟨96726813810971583081047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1031752680650363552864501 96726813810971583081047)
        ·
          refine ⟨145090220716457374621571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96726813810971583081047 145090220716457374621571)
          ·
            refine ⟨217635331074686061932357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145090220716457374621571 217635331074686061932357)
            ·
              refine ⟨40806624576503636612317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217635331074686061932357 40806624576503636612317)
              ·
                refine ⟨15302484216188863729619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40806624576503636612317 15302484216188863729619)
                ·
                  refine ⟨22953726324283295594429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15302484216188863729619 22953726324283295594429)
                  ·
                    refine ⟨8607647371606235847911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22953726324283295594429 8607647371606235847911)
                    ·
                      rfl

theorem cell22_25145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 3].length) (baseStart_25145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25145 prefixEnd_25145 := by exact prefixLift 25145
  have htrace : WordTrace (prefixWord ++ tailWord_25145) baseStart_25145 baseEnd_25145 := by
    simpa [prefixWord, tailWord_25145, baseEnd_25145] using wordTrace_append hprefix tailTrace_25145
  have hstable : (prefixWord ++ tailWord_25145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25145).length < 2 ^ (prefixWord ++ tailWord_25145).sum := by decide
  have hdescent : baseEnd_25145 < baseStart_25145 := by decide
  rcases family_descends (prefixWord ++ tailWord_25145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25188 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_25188 : Nat := 118140960795 + 25188 * 2 ^ 59
def prefixEnd_25188 : Nat := 4983230072969 + 3 ^ 40 * 25188 * 2
def baseEnd_25188 : Nat := 8622367150368457022779

theorem tailTrace_25188 : CollatzResearch.WordTrace tailWord_25188 prefixEnd_25188 8622367150368457022779 := by
  unfold tailWord_25188
  simp only [CollatzResearch.WordTrace]
  refine ⟨459340916377826306514109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 612454555170435075352145 459340916377826306514109)
  ·
    refine ⟨172252843641684864942791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 459340916377826306514109 172252843641684864942791)
    ·
      refine ⟨258379265462527297414187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172252843641684864942791 258379265462527297414187)
      ·
        refine ⟨387568898193790946121281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258379265462527297414187 387568898193790946121281)
        ·
          refine ⟨290676673645343209590961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387568898193790946121281 290676673645343209590961)
          ·
            refine ⟨218007505234007407193221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290676673645343209590961 218007505234007407193221)
            ·
              refine ⟨40876407231376388848729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218007505234007407193221 40876407231376388848729)
              ·
                refine ⟨30657305423532291636547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40876407231376388848729 30657305423532291636547)
                ·
                  refine ⟨45985958135298437454821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30657305423532291636547 45985958135298437454821)
                  ·
                    refine ⟨8622367150368457022779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45985958135298437454821 8622367150368457022779)
                    ·
                      rfl

theorem cell22_25188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_25188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25188 prefixEnd_25188 := by exact prefixLift 25188
  have htrace : WordTrace (prefixWord ++ tailWord_25188) baseStart_25188 baseEnd_25188 := by
    simpa [prefixWord, tailWord_25188, baseEnd_25188] using wordTrace_append hprefix tailTrace_25188
  have hstable : (prefixWord ++ tailWord_25188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25188).length < 2 ^ (prefixWord ++ tailWord_25188).sum := by decide
  have hdescent : baseEnd_25188 < baseStart_25188 := by decide
  rcases family_descends (prefixWord ++ tailWord_25188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25216 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_25216 : Nat := 118140960795 + 25216 * 2 ^ 59
def prefixEnd_25216 : Nat := 4983230072969 + 3 ^ 40 * 25216 * 2
def baseEnd_25216 : Nat := 8631952122585717322693

theorem tailTrace_25216 : CollatzResearch.WordTrace tailWord_25216 prefixEnd_25216 8631952122585717322693 := by
  unfold tailWord_25216
  simp only [CollatzResearch.WordTrace]
  refine ⟨459851538327106697523751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 613135384436142263365001 459851538327106697523751)
  ·
    refine ⟨689777307490660046285627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459851538327106697523751 689777307490660046285627)
    ·
      refine ⟨1034665961235990069428441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689777307490660046285627 1034665961235990069428441)
      ·
        refine ⟨775999470926992552071331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1034665961235990069428441 775999470926992552071331)
        ·
          refine ⟨1163999206390488828106997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775999470926992552071331 1163999206390488828106997)
          ·
            refine ⟨109124925599108327635031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1163999206390488828106997 109124925599108327635031)
            ·
              refine ⟨163687388398662491452547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109124925599108327635031 163687388398662491452547)
              ·
                refine ⟨245531082597993737178821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163687388398662491452547 245531082597993737178821)
                ·
                  refine ⟨46037077987123825721029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245531082597993737178821 46037077987123825721029)
                  ·
                    refine ⟨8631952122585717322693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46037077987123825721029 8631952122585717322693)
                    ·
                      rfl

theorem cell22_25216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_25216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25216 prefixEnd_25216 := by exact prefixLift 25216
  have htrace : WordTrace (prefixWord ++ tailWord_25216) baseStart_25216 baseEnd_25216 := by
    simpa [prefixWord, tailWord_25216, baseEnd_25216] using wordTrace_append hprefix tailTrace_25216
  have hstable : (prefixWord ++ tailWord_25216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25216).length < 2 ^ (prefixWord ++ tailWord_25216).sum := by decide
  have hdescent : baseEnd_25216 < baseStart_25216 := by decide
  rcases family_descends (prefixWord ++ tailWord_25216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25353 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_25353 : Nat := 118140960795 + 25353 * 2 ^ 59
def prefixEnd_25353 : Nat := 4983230072969 + 3 ^ 40 * 25353 * 2
def baseEnd_25353 : Nat := 8678850022363026647273

theorem tailTrace_25353 : CollatzResearch.WordTrace tailWord_25353 prefixEnd_25353 8678850022363026647273 := by
  unfold tailWord_25353
  simp only [CollatzResearch.WordTrace]
  refine ⟨924699877157885792784713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 616466584771923861856475 924699877157885792784713)
  ·
    refine ⟨693524907868414344588535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 924699877157885792784713 693524907868414344588535)
    ·
      refine ⟨1040287361802621516882803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693524907868414344588535 1040287361802621516882803)
      ·
        refine ⟨1560431042703932275324205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040287361802621516882803 1560431042703932275324205)
        ·
          refine ⟨585161641013974603246577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1560431042703932275324205 585161641013974603246577)
          ·
            refine ⟨438871230760480952434933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585161641013974603246577 438871230760480952434933)
            ·
              refine ⟨41144177883795089290775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 438871230760480952434933 41144177883795089290775)
              ·
                refine ⟨61716266825692633936163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41144177883795089290775 61716266825692633936163)
                ·
                  refine ⟨92574400238538950904245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61716266825692633936163 92574400238538950904245)
                  ·
                    refine ⟨8678850022363026647273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92574400238538950904245 8678850022363026647273)
                    ·
                      rfl

theorem cell22_25353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_25353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25353 prefixEnd_25353 := by exact prefixLift 25353
  have htrace : WordTrace (prefixWord ++ tailWord_25353) baseStart_25353 baseEnd_25353 := by
    simpa [prefixWord, tailWord_25353, baseEnd_25353] using wordTrace_append hprefix tailTrace_25353
  have hstable : (prefixWord ++ tailWord_25353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25353).length < 2 ^ (prefixWord ++ tailWord_25353).sum := by decide
  have hdescent : baseEnd_25353 < baseStart_25353 := by decide
  rcases family_descends (prefixWord ++ tailWord_25353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25368 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_25368 : Nat := 118140960795 + 25368 * 2 ^ 59
def prefixEnd_25368 : Nat := 4983230072969 + 3 ^ 40 * 25368 * 2
def baseEnd_25368 : Nat := 8683984828907987522227

theorem tailTrace_25368 : CollatzResearch.WordTrace tailWord_25368 prefixEnd_25368 8683984828907987522227 := by
  unfold tailWord_25368
  simp only [CollatzResearch.WordTrace]
  refine ⟨462623486051771677290379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 616831314735695569720505 462623486051771677290379)
  ·
    refine ⟨693935229077657515935569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 462623486051771677290379 693935229077657515935569)
    ·
      refine ⟨520451421808243136951677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 693935229077657515935569 520451421808243136951677)
      ·
        refine ⟨195169283178091176356879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520451421808243136951677 195169283178091176356879)
        ·
          refine ⟨292753924767136764535319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195169283178091176356879 292753924767136764535319)
          ·
            refine ⟨439130887150705146802979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292753924767136764535319 439130887150705146802979)
            ·
              refine ⟨658696330726057720204469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439130887150705146802979 658696330726057720204469)
              ·
                refine ⟨61752781005567911269169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 658696330726057720204469 61752781005567911269169)
                ·
                  refine ⟨46314585754175933451877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61752781005567911269169 46314585754175933451877)
                  ·
                    refine ⟨8683984828907987522227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46314585754175933451877 8683984828907987522227)
                    ·
                      rfl

theorem cell22_25368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_25368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25368 prefixEnd_25368 := by exact prefixLift 25368
  have htrace : WordTrace (prefixWord ++ tailWord_25368) baseStart_25368 baseEnd_25368 := by
    simpa [prefixWord, tailWord_25368, baseEnd_25368] using wordTrace_append hprefix tailTrace_25368
  have hstable : (prefixWord ++ tailWord_25368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25368).length < 2 ^ (prefixWord ++ tailWord_25368).sum := by decide
  have hdescent : baseEnd_25368 < baseStart_25368 := by decide
  rcases family_descends (prefixWord ++ tailWord_25368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25372 : List Nat := [2, 2, 3, 1, 1, 5, 1, 3, 4]
def baseStart_25372 : Nat := 118140960795 + 25372 * 2 ^ 59
def prefixEnd_25372 : Nat := 4983230072969 + 3 ^ 40 * 25372 * 2
def baseEnd_25372 : Nat := 2895118036884436807405

theorem tailTrace_25372 : CollatzResearch.WordTrace tailWord_25372 prefixEnd_25372 2895118036884436807405 := by
  unfold tailWord_25372
  simp only [CollatzResearch.WordTrace]
  refine ⟨462696432044526018863185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 616928576059368025150913 462696432044526018863185)
  ·
    refine ⟨347022324033394514147389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 462696432044526018863185 347022324033394514147389)
    ·
      refine ⟨130133371512522942805271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347022324033394514147389 130133371512522942805271)
      ·
        refine ⟨195200057268784414207907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130133371512522942805271 195200057268784414207907)
        ·
          refine ⟨292800085903176621311861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195200057268784414207907 292800085903176621311861)
          ·
            refine ⟨27450008053422808247987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292800085903176621311861 27450008053422808247987)
            ·
              refine ⟨41175012080134212371981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27450008053422808247987 41175012080134212371981)
              ·
                refine ⟨15440629530050329639493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41175012080134212371981 15440629530050329639493)
                ·
                  refine ⟨2895118036884436807405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15440629530050329639493 2895118036884436807405)
                  ·
                    rfl

theorem cell22_25372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_25372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25372 prefixEnd_25372 := by exact prefixLift 25372
  have htrace : WordTrace (prefixWord ++ tailWord_25372) baseStart_25372 baseEnd_25372 := by
    simpa [prefixWord, tailWord_25372, baseEnd_25372] using wordTrace_append hprefix tailTrace_25372
  have hstable : (prefixWord ++ tailWord_25372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25372).length < 2 ^ (prefixWord ++ tailWord_25372).sum := by decide
  have hdescent : baseEnd_25372 < baseStart_25372 := by decide
  rcases family_descends (prefixWord ++ tailWord_25372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25389 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 6]
def baseStart_25389 : Nat := 118140960795 + 25389 * 2 ^ 59
def prefixEnd_25389 : Nat := 4983230072969 + 3 ^ 40 * 25389 * 2
def baseEnd_25389 : Nat := 2897057852690310915721

theorem tailTrace_25389 : CollatzResearch.WordTrace tailWord_25389 prefixEnd_25389 2897057852690310915721 := by
  unfold tailWord_25389
  simp only [CollatzResearch.WordTrace]
  refine ⟨926012905027463941095221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 617341936684975960730147 926012905027463941095221)
  ·
    refine ⟨86813709846324744477677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 926012905027463941095221 86813709846324744477677)
    ·
      refine ⟨32555141192371779179129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86813709846324744477677 32555141192371779179129)
      ·
        refine ⟨24416355894278834384347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32555141192371779179129 24416355894278834384347)
        ·
          refine ⟨36624533841418251576521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24416355894278834384347 36624533841418251576521)
          ·
            refine ⟨27468400381063688682391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36624533841418251576521 27468400381063688682391)
            ·
              refine ⟨41202600571595533023587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27468400381063688682391 41202600571595533023587)
              ·
                refine ⟨61803900857393299535381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41202600571595533023587 61803900857393299535381)
                ·
                  refine ⟨2897057852690310915721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61803900857393299535381 2897057852690310915721)
                  ·
                    rfl

theorem cell22_25389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_25389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25389 prefixEnd_25389 := by exact prefixLift 25389
  have htrace : WordTrace (prefixWord ++ tailWord_25389) baseStart_25389 baseEnd_25389 := by
    simpa [prefixWord, tailWord_25389, baseEnd_25389] using wordTrace_append hprefix tailTrace_25389
  have hstable : (prefixWord ++ tailWord_25389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25389).length < 2 ^ (prefixWord ++ tailWord_25389).sum := by decide
  have hdescent : baseEnd_25389 < baseStart_25389 := by decide
  rcases family_descends (prefixWord ++ tailWord_25389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25462 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_25462 : Nat := 118140960795 + 25462 * 2 ^ 59
def prefixEnd_25462 : Nat := 4983230072969 + 3 ^ 40 * 25462 * 2
def baseEnd_25462 : Nat := 2905387649974358557313

theorem tailTrace_25462 : CollatzResearch.WordTrace tailWord_25462 prefixEnd_25462 2905387649974358557313 := by
  unfold tailWord_25462
  simp only [CollatzResearch.WordTrace]
  refine ⟨58042214610187338031415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 619116955841998272335093 58042214610187338031415)
  ·
    refine ⟨87063321915281007047123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58042214610187338031415 87063321915281007047123)
    ·
      refine ⟨130594982872921510570685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87063321915281007047123 130594982872921510570685)
      ·
        refine ⟨48973118577345566464007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130594982872921510570685 48973118577345566464007)
        ·
          refine ⟨73459677866018349696011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48973118577345566464007 73459677866018349696011)
          ·
            refine ⟨110189516799027524544017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73459677866018349696011 110189516799027524544017)
            ·
              refine ⟨82642137599270643408013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110189516799027524544017 82642137599270643408013)
              ·
                refine ⟨30990801599726491278005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82642137599270643408013 30990801599726491278005)
                ·
                  refine ⟨2905387649974358557313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30990801599726491278005 2905387649974358557313)
                  ·
                    rfl

theorem cell22_25462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_25462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25462 prefixEnd_25462 := by exact prefixLift 25462
  have htrace : WordTrace (prefixWord ++ tailWord_25462) baseStart_25462 baseEnd_25462 := by
    simpa [prefixWord, tailWord_25462, baseEnd_25462] using wordTrace_append hprefix tailTrace_25462
  have hstable : (prefixWord ++ tailWord_25462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25462).length < 2 ^ (prefixWord ++ tailWord_25462).sum := by decide
  have hdescent : baseEnd_25462 < baseStart_25462 := by decide
  rcases family_descends (prefixWord ++ tailWord_25462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25475 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 1, 4]
def baseStart_25475 : Nat := 118140960795 + 25475 * 2 ^ 59
def prefixEnd_25475 : Nat := 4983230072969 + 3 ^ 40 * 25475 * 2
def baseEnd_25475 : Nat := 8720613115595375096899

theorem tailTrace_25475 : CollatzResearch.WordTrace tailWord_25475 prefixEnd_25475 8720613115595375096899 := by
  unfold tailWord_25475
  simp only [CollatzResearch.WordTrace]
  refine ⟨929149582715900628725879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 619433055143933752483919 929149582715900628725879)
  ·
    refine ⟨1393724374073850943088819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 929149582715900628725879 1393724374073850943088819)
    ·
      refine ⟨2090586561110776414633229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393724374073850943088819 2090586561110776414633229)
      ·
        refine ⟨783969960416541155487461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2090586561110776414633229 783969960416541155487461)
        ·
          refine ⟨146994367578101466653899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 783969960416541155487461 146994367578101466653899)
          ·
            refine ⟨220491551367152199980849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146994367578101466653899 220491551367152199980849)
            ·
              refine ⟨165368663525364149985637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220491551367152199980849 165368663525364149985637)
              ·
                refine ⟨31006624411005778122307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165368663525364149985637 31006624411005778122307)
                ·
                  refine ⟨46509936616508667183461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31006624411005778122307 46509936616508667183461)
                  ·
                    refine ⟨8720613115595375096899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46509936616508667183461 8720613115595375096899)
                    ·
                      rfl

theorem cell22_25475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 4].length) (baseStart_25475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25475 prefixEnd_25475 := by exact prefixLift 25475
  have htrace : WordTrace (prefixWord ++ tailWord_25475) baseStart_25475 baseEnd_25475 := by
    simpa [prefixWord, tailWord_25475, baseEnd_25475] using wordTrace_append hprefix tailTrace_25475
  have hstable : (prefixWord ++ tailWord_25475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25475).length < 2 ^ (prefixWord ++ tailWord_25475).sum := by decide
  have hdescent : baseEnd_25475 < baseStart_25475 := by decide
  rcases family_descends (prefixWord ++ tailWord_25475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25492 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_25492 : Nat := 118140960795 + 25492 * 2 ^ 59
def prefixEnd_25492 : Nat := 4983230072969 + 3 ^ 40 * 25492 * 2
def baseEnd_25492 : Nat := 8726432563012997421847

theorem tailTrace_25492 : CollatzResearch.WordTrace tailWord_25492 prefixEnd_25492 8726432563012997421847 := by
  unfold tailWord_25492
  simp only [CollatzResearch.WordTrace]
  refine ⟨464884811827156266047365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 619846415769541688063153 464884811827156266047365)
  ·
    refine ⟨87165902217591799883881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 464884811827156266047365 87165902217591799883881)
    ·
      refine ⟨65374426663193849912911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87165902217591799883881 65374426663193849912911)
      ·
        refine ⟨98061639994790774869367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65374426663193849912911 98061639994790774869367)
        ·
          refine ⟨147092459992186162304051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98061639994790774869367 147092459992186162304051)
          ·
            refine ⟨220638689988279243456077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147092459992186162304051 220638689988279243456077)
            ·
              refine ⟨82739508745604716296029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220638689988279243456077 82739508745604716296029)
              ·
                refine ⟨31027315779601768611011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82739508745604716296029 31027315779601768611011)
                ·
                  refine ⟨46540973669402652916517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31027315779601768611011 46540973669402652916517)
                  ·
                    refine ⟨8726432563012997421847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46540973669402652916517 8726432563012997421847)
                    ·
                      rfl

theorem cell22_25492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_25492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25492 prefixEnd_25492 := by exact prefixLift 25492
  have htrace : WordTrace (prefixWord ++ tailWord_25492) baseStart_25492 baseEnd_25492 := by
    simpa [prefixWord, tailWord_25492, baseEnd_25492] using wordTrace_append hprefix tailTrace_25492
  have hstable : (prefixWord ++ tailWord_25492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25492).length < 2 ^ (prefixWord ++ tailWord_25492).sum := by decide
  have hdescent : baseEnd_25492 < baseStart_25492 := by decide
  rcases family_descends (prefixWord ++ tailWord_25492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25494 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_25494 : Nat := 118140960795 + 25494 * 2 ^ 59
def prefixEnd_25494 : Nat := 4983230072969 + 3 ^ 40 * 25494 * 2
def baseEnd_25494 : Nat := 8727117203885658871841

theorem tailTrace_25494 : CollatzResearch.WordTrace tailWord_25494 prefixEnd_25494 8727117203885658871841 := by
  unfold tailWord_25494
  simp only [CollatzResearch.WordTrace]
  refine ⟨58115160602941679604221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 619895046431377915778357 58115160602941679604221)
  ·
    refine ⟨21793185226103129851583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58115160602941679604221 21793185226103129851583)
    ·
      refine ⟨32689777839154694777375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21793185226103129851583 32689777839154694777375)
      ·
        refine ⟨49034666758732042166063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32689777839154694777375 49034666758732042166063)
        ·
          refine ⟨73552000138098063249095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49034666758732042166063 73552000138098063249095)
          ·
            refine ⟨110328000207147094873643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73552000138098063249095 110328000207147094873643)
            ·
              refine ⟨165492000310720642310465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110328000207147094873643 165492000310720642310465)
              ·
                refine ⟨124119000233040481732849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165492000310720642310465 124119000233040481732849)
                ·
                  refine ⟨93089250174780361299637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124119000233040481732849 93089250174780361299637)
                  ·
                    refine ⟨8727117203885658871841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93089250174780361299637 8727117203885658871841)
                    ·
                      rfl

theorem cell22_25494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_25494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25494 prefixEnd_25494 := by exact prefixLift 25494
  have htrace : WordTrace (prefixWord ++ tailWord_25494) baseStart_25494 baseEnd_25494 := by
    simpa [prefixWord, tailWord_25494, baseEnd_25494] using wordTrace_append hprefix tailTrace_25494
  have hstable : (prefixWord ++ tailWord_25494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25494).length < 2 ^ (prefixWord ++ tailWord_25494).sum := by decide
  have hdescent : baseEnd_25494 < baseStart_25494 := by decide
  rcases family_descends (prefixWord ++ tailWord_25494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25573 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_25573 : Nat := 118140960795 + 25573 * 2 ^ 59
def prefixEnd_25573 : Nat := 4983230072969 + 3 ^ 40 * 25573 * 2
def baseEnd_25573 : Nat := 8754160518355786146599

theorem tailTrace_25573 : CollatzResearch.WordTrace tailWord_25573 prefixEnd_25573 8754160518355786146599 := by
  unfold tailWord_25573
  simp only [CollatzResearch.WordTrace]
  refine ⟨932723936360863365793373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 621815957573908910528915 932723936360863365793373)
  ·
    refine ⟨349771476135323762172515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 932723936360863365793373 349771476135323762172515)
    ·
      refine ⟨524657214202985643258773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349771476135323762172515 524657214202985643258773)
      ·
        refine ⟨24593306915764952027755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 524657214202985643258773 24593306915764952027755)
        ·
          refine ⟨36889960373647428041633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24593306915764952027755 36889960373647428041633)
          ·
            refine ⟨27667470280235571031225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36889960373647428041633 27667470280235571031225)
            ·
              refine ⟨20750602710176678273419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27667470280235571031225 20750602710176678273419)
              ·
                refine ⟨31125904065265017410129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20750602710176678273419 31125904065265017410129)
                ·
                  refine ⟨23344428048948763057597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31125904065265017410129 23344428048948763057597)
                  ·
                    refine ⟨8754160518355786146599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23344428048948763057597 8754160518355786146599)
                    ·
                      rfl

theorem cell22_25573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_25573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25573 prefixEnd_25573 := by exact prefixLift 25573
  have htrace : WordTrace (prefixWord ++ tailWord_25573) baseStart_25573 baseEnd_25573 := by
    simpa [prefixWord, tailWord_25573, baseEnd_25573] using wordTrace_append hprefix tailTrace_25573
  have hstable : (prefixWord ++ tailWord_25573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25573).length < 2 ^ (prefixWord ++ tailWord_25573).sum := by decide
  have hdescent : baseEnd_25573 < baseStart_25573 := by decide
  rcases family_descends (prefixWord ++ tailWord_25573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25657 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_25657 : Nat := 118140960795 + 25657 * 2 ^ 59
def prefixEnd_25657 : Nat := 4983230072969 + 3 ^ 40 * 25657 * 2
def baseEnd_25657 : Nat := 8782915435007567046341

theorem tailTrace_25657 : CollatzResearch.WordTrace tailWord_25657 prefixEnd_25657 8782915435007567046341 := by
  unfold tailWord_25657
  simp only [CollatzResearch.WordTrace]
  refine ⟨935787668056545711851225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 623858445371030474567483 935787668056545711851225)
  ·
    refine ⟨701840751042409283888419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 935787668056545711851225 701840751042409283888419)
    ·
      refine ⟨1052761126563613925832629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701840751042409283888419 1052761126563613925832629)
      ·
        refine ⟨98696355615338805546809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1052761126563613925832629 98696355615338805546809)
        ·
          refine ⟨74022266711504104160107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98696355615338805546809 74022266711504104160107)
          ·
            refine ⟨111033400067256156240161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74022266711504104160107 111033400067256156240161)
            ·
              refine ⟨83275050050442117180121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111033400067256156240161 83275050050442117180121)
              ·
                refine ⟨62456287537831587885091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83275050050442117180121 62456287537831587885091)
                ·
                  refine ⟨93684431306747381827637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62456287537831587885091 93684431306747381827637)
                  ·
                    refine ⟨8782915435007567046341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93684431306747381827637 8782915435007567046341)
                    ·
                      rfl

theorem cell22_25657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_25657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25657 prefixEnd_25657 := by exact prefixLift 25657
  have htrace : WordTrace (prefixWord ++ tailWord_25657) baseStart_25657 baseEnd_25657 := by
    simpa [prefixWord, tailWord_25657, baseEnd_25657] using wordTrace_append hprefix tailTrace_25657
  have hstable : (prefixWord ++ tailWord_25657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25657).length < 2 ^ (prefixWord ++ tailWord_25657).sum := by decide
  have hdescent : baseEnd_25657 < baseStart_25657 := by decide
  rcases family_descends (prefixWord ++ tailWord_25657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25661 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_25661 : Nat := 118140960795 + 25661 * 2 ^ 59
def prefixEnd_25661 : Nat := 4983230072969 + 3 ^ 40 * 25661 * 2
def baseEnd_25661 : Nat := 8784284716752889946329

theorem tailTrace_25661 : CollatzResearch.WordTrace tailWord_25661 prefixEnd_25661 8784284716752889946329 := by
  unfold tailWord_25661
  simp only [CollatzResearch.WordTrace]
  refine ⟨935933560042054394996837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 623955706694702929997891 935933560042054394996837)
  ·
    refine ⟨175487542507885199061907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 935933560042054394996837 175487542507885199061907)
    ·
      refine ⟨263231313761827798592861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175487542507885199061907 263231313761827798592861)
      ·
        refine ⟨98711742660685424472323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263231313761827798592861 98711742660685424472323)
        ·
          refine ⟨148067613991028136708485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98711742660685424472323 148067613991028136708485)
          ·
            refine ⟨27762677623317775632841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148067613991028136708485 27762677623317775632841)
            ·
              refine ⟨20822008217488331724631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27762677623317775632841 20822008217488331724631)
              ·
                refine ⟨31233012326232497586947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20822008217488331724631 31233012326232497586947)
                ·
                  refine ⟨46849518489348746380421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31233012326232497586947 46849518489348746380421)
                  ·
                    refine ⟨8784284716752889946329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46849518489348746380421 8784284716752889946329)
                    ·
                      rfl

theorem cell22_25661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_25661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25661 prefixEnd_25661 := by exact prefixLift 25661
  have htrace : WordTrace (prefixWord ++ tailWord_25661) baseStart_25661 baseEnd_25661 := by
    simpa [prefixWord, tailWord_25661, baseEnd_25661] using wordTrace_append hprefix tailTrace_25661
  have hstable : (prefixWord ++ tailWord_25661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25661).length < 2 ^ (prefixWord ++ tailWord_25661).sum := by decide
  have hdescent : baseEnd_25661 < baseStart_25661 := by decide
  rcases family_descends (prefixWord ++ tailWord_25661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25674 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_25674 : Nat := 118140960795 + 25674 * 2 ^ 59
def prefixEnd_25674 : Nat := 4983230072969 + 3 ^ 40 * 25674 * 2
def baseEnd_25674 : Nat := 8788734882425189371289

theorem tailTrace_25674 : CollatzResearch.WordTrace tailWord_25674 prefixEnd_25674 8788734882425189371289 := by
  unfold tailWord_25674
  simp only [CollatzResearch.WordTrace]
  refine ⟨234101927248739403805019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 624271805996638410146717 234101927248739403805019)
  ·
    refine ⟨351152890873109105707529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234101927248739403805019 351152890873109105707529)
    ·
      refine ⟨263364668154831829280647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351152890873109105707529 263364668154831829280647)
      ·
        refine ⟨395047002232247743920971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263364668154831829280647 395047002232247743920971)
        ·
          refine ⟨592570503348371615881457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395047002232247743920971 592570503348371615881457)
          ·
            refine ⟨444427877511278711911093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592570503348371615881457 444427877511278711911093)
            ·
              refine ⟨41665113516682379241665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 444427877511278711911093 41665113516682379241665)
              ·
                refine ⟨31248835137511784431249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41665113516682379241665 31248835137511784431249)
                ·
                  refine ⟨23436626353133838323437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31248835137511784431249 23436626353133838323437)
                  ·
                    refine ⟨8788734882425189371289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23436626353133838323437 8788734882425189371289)
                    ·
                      rfl

theorem cell22_25674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_25674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25674 prefixEnd_25674 := by exact prefixLift 25674
  have htrace : WordTrace (prefixWord ++ tailWord_25674) baseStart_25674 baseEnd_25674 := by
    simpa [prefixWord, tailWord_25674, baseEnd_25674] using wordTrace_append hprefix tailTrace_25674
  have hstable : (prefixWord ++ tailWord_25674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25674).length < 2 ^ (prefixWord ++ tailWord_25674).sum := by decide
  have hdescent : baseEnd_25674 < baseStart_25674 := by decide
  rcases family_descends (prefixWord ++ tailWord_25674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25704 : List Nat := [2, 1, 4, 4, 1, 1, 1, 8]
def baseStart_25704 : Nat := 118140960795 + 25704 * 2 ^ 59
def prefixEnd_25704 : Nat := 4983230072969 + 3 ^ 40 * 25704 * 2
def baseEnd_25704 : Nat := 977667166168345680133

theorem tailTrace_25704 : CollatzResearch.WordTrace tailWord_25704 prefixEnd_25704 977667166168345680133 := by
  unfold tailWord_25704
  simp only [CollatzResearch.WordTrace]
  refine ⟨468750949443136369406083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 625001265924181825874777 468750949443136369406083)
  ·
    refine ⟨703126424164704554109125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468750949443136369406083 703126424164704554109125)
    ·
      refine ⟨131836204530882103895461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 703126424164704554109125 131836204530882103895461)
      ·
        refine ⟨24719288349540394480399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131836204530882103895461 24719288349540394480399)
        ·
          refine ⟨37078932524310591720599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24719288349540394480399 37078932524310591720599)
          ·
            refine ⟨55618398786465887580899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37078932524310591720599 55618398786465887580899)
            ·
              refine ⟨83427598179698831371349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55618398786465887580899 83427598179698831371349)
              ·
                refine ⟨977667166168345680133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 83427598179698831371349 977667166168345680133)
                ·
                  rfl

theorem cell22_25704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 8].length) (baseStart_25704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25704 prefixEnd_25704 := by exact prefixLift 25704
  have htrace : WordTrace (prefixWord ++ tailWord_25704) baseStart_25704 baseEnd_25704 := by
    simpa [prefixWord, tailWord_25704, baseEnd_25704] using wordTrace_append hprefix tailTrace_25704
  have hstable : (prefixWord ++ tailWord_25704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25704).length < 2 ^ (prefixWord ++ tailWord_25704).sum := by decide
  have hdescent : baseEnd_25704 < baseStart_25704 := by decide
  rcases family_descends (prefixWord ++ tailWord_25704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25732 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 7]
def baseStart_25732 : Nat := 118140960795 + 25732 * 2 ^ 59
def prefixEnd_25732 : Nat := 4983230072969 + 3 ^ 40 * 25732 * 2
def baseEnd_25732 : Nat := 2936196489244123807037

theorem tailTrace_25732 : CollatzResearch.WordTrace tailWord_25732 prefixEnd_25732 2936196489244123807037 := by
  unfold tailWord_25732
  simp only [CollatzResearch.WordTrace]
  refine ⟨469261571392416760415725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 625682095189889013887633 469261571392416760415725)
  ·
    refine ⟨175973089272156285155897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 469261571392416760415725 175973089272156285155897)
    ·
      refine ⟨131979816954117213866923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175973089272156285155897 131979816954117213866923)
      ·
        refine ⟨197969725431175820800385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131979816954117213866923 197969725431175820800385)
        ·
          refine ⟨148477294073381865600289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197969725431175820800385 148477294073381865600289)
          ·
            refine ⟨111357970555036399200217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148477294073381865600289 111357970555036399200217)
            ·
              refine ⟨83518477916277299400163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111357970555036399200217 83518477916277299400163)
              ·
                refine ⟨125277716874415949100245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83518477916277299400163 125277716874415949100245)
                ·
                  refine ⟨2936196489244123807037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125277716874415949100245 2936196489244123807037)
                  ·
                    rfl

theorem cell22_25732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_25732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25732 prefixEnd_25732 := by exact prefixLift 25732
  have htrace : WordTrace (prefixWord ++ tailWord_25732) baseStart_25732 baseEnd_25732 := by
    simpa [prefixWord, tailWord_25732, baseEnd_25732] using wordTrace_append hprefix tailTrace_25732
  have hstable : (prefixWord ++ tailWord_25732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25732).length < 2 ^ (prefixWord ++ tailWord_25732).sum := by decide
  have hdescent : baseEnd_25732 < baseStart_25732 := by decide
  rcases family_descends (prefixWord ++ tailWord_25732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25824 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_25824 : Nat := 118140960795 + 25824 * 2 ^ 59
def prefixEnd_25824 : Nat := 4983230072969 + 3 ^ 40 * 25824 * 2
def baseEnd_25824 : Nat := 8840082947874798120829

theorem tailTrace_25824 : CollatzResearch.WordTrace tailWord_25824 prefixEnd_25824 8840082947874798120829 := by
  unfold tailWord_25824
  simp only [CollatzResearch.WordTrace]
  refine ⟨470939329225766616590263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 627919105634355488787017 470939329225766616590263)
  ·
    refine ⟨706408993838649924885395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470939329225766616590263 706408993838649924885395)
    ·
      refine ⟨1059613490757974887328093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706408993838649924885395 1059613490757974887328093)
      ·
        refine ⟨397355059034240582748035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1059613490757974887328093 397355059034240582748035)
        ·
          refine ⟨596032588551360874122053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397355059034240582748035 596032588551360874122053)
          ·
            refine ⟨111756110353380163897885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 596032588551360874122053 111756110353380163897885)
            ·
              refine ⟨41908541382517561461707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111756110353380163897885 41908541382517561461707)
              ·
                refine ⟨62862812073776342192561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41908541382517561461707 62862812073776342192561)
                ·
                  refine ⟨47147109055332256644421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62862812073776342192561 47147109055332256644421)
                  ·
                    refine ⟨8840082947874798120829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47147109055332256644421 8840082947874798120829)
                    ·
                      rfl

theorem cell22_25824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_25824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25824 prefixEnd_25824 := by exact prefixLift 25824
  have htrace : WordTrace (prefixWord ++ tailWord_25824) baseStart_25824 baseEnd_25824 := by
    simpa [prefixWord, tailWord_25824, baseEnd_25824] using wordTrace_append hprefix tailTrace_25824
  have hstable : (prefixWord ++ tailWord_25824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25824).length < 2 ^ (prefixWord ++ tailWord_25824).sum := by decide
  have hdescent : baseEnd_25824 < baseStart_25824 := by decide
  rcases family_descends (prefixWord ++ tailWord_25824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25901 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 7]
def baseStart_25901 : Nat := 118140960795 + 25901 * 2 ^ 59
def prefixEnd_25901 : Nat := 4983230072969 + 3 ^ 40 * 25901 * 2
def baseEnd_25901 : Nat := 2955480540490754648531

theorem tailTrace_25901 : CollatzResearch.WordTrace tailWord_25901 prefixEnd_25901 2955480540490754648531 := by
  unfold tailWord_25901
  simp only [CollatzResearch.WordTrace]
  refine ⟨944687079172575383733557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 629791386115050255822371 944687079172575383733557)
  ·
    refine ⟨88564413672428942225021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 944687079172575383733557 88564413672428942225021)
    ·
      refine ⟨33211655127160853334383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88564413672428942225021 33211655127160853334383)
      ·
        refine ⟨49817482690741280001575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33211655127160853334383 49817482690741280001575)
        ·
          refine ⟨74726224036111920002363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49817482690741280001575 74726224036111920002363)
          ·
            refine ⟨112089336054167880003545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74726224036111920002363 112089336054167880003545)
            ·
              refine ⟨84067002040625910002659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112089336054167880003545 84067002040625910002659)
              ·
                refine ⟨126100503060938865003989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84067002040625910002659 126100503060938865003989)
                ·
                  refine ⟨2955480540490754648531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 126100503060938865003989 2955480540490754648531)
                  ·
                    rfl

theorem cell22_25901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_25901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25901 prefixEnd_25901 := by exact prefixLift 25901
  have htrace : WordTrace (prefixWord ++ tailWord_25901) baseStart_25901 baseEnd_25901 := by
    simpa [prefixWord, tailWord_25901, baseEnd_25901] using wordTrace_append hprefix tailTrace_25901
  have hstable : (prefixWord ++ tailWord_25901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25901).length < 2 ^ (prefixWord ++ tailWord_25901).sum := by decide
  have hdescent : baseEnd_25901 < baseStart_25901 := by decide
  rcases family_descends (prefixWord ++ tailWord_25901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25905 : List Nat := [1, 2, 2, 3, 3, 2, 3, 2, 1, 3]
def baseStart_25905 : Nat := 118140960795 + 25905 * 2 ^ 59
def prefixEnd_25905 : Nat := 4983230072969 + 3 ^ 40 * 25905 * 2
def baseEnd_25905 : Nat := 8867810903217586845581

theorem tailTrace_25905 : CollatzResearch.WordTrace tailWord_25905 prefixEnd_25905 8867810903217586845581 := by
  unfold tailWord_25905
  simp only [CollatzResearch.WordTrace]
  refine ⟨944832971158084066879169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 629888647438722711252779 944832971158084066879169)
  ·
    refine ⟨708624728368563050159377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 944832971158084066879169 708624728368563050159377)
    ·
      refine ⟨531468546276422287619533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 708624728368563050159377 531468546276422287619533)
      ·
        refine ⟨199300704853658357857325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531468546276422287619533 199300704853658357857325)
        ·
          refine ⟨74737764320121884196497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199300704853658357857325 74737764320121884196497)
          ·
            refine ⟨56053323240091413147373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74737764320121884196497 56053323240091413147373)
            ·
              refine ⟨21019996215034279930265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56053323240091413147373 21019996215034279930265)
              ·
                refine ⟨15764997161275709947699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21019996215034279930265 15764997161275709947699)
                ·
                  refine ⟨23647495741913564921549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15764997161275709947699 23647495741913564921549)
                  ·
                    refine ⟨8867810903217586845581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23647495741913564921549 8867810903217586845581)
                    ·
                      rfl

theorem cell22_25905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_25905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25905 prefixEnd_25905 := by exact prefixLift 25905
  have htrace : WordTrace (prefixWord ++ tailWord_25905) baseStart_25905 baseEnd_25905 := by
    simpa [prefixWord, tailWord_25905, baseEnd_25905] using wordTrace_append hprefix tailTrace_25905
  have hstable : (prefixWord ++ tailWord_25905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25905).length < 2 ^ (prefixWord ++ tailWord_25905).sum := by decide
  have hdescent : baseEnd_25905 < baseStart_25905 := by decide
  rcases family_descends (prefixWord ++ tailWord_25905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25914 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_25914 : Nat := 118140960795 + 25914 * 2 ^ 59
def prefixEnd_25914 : Nat := 4983230072969 + 3 ^ 40 * 25914 * 2
def baseEnd_25914 : Nat := 8870891787144563370553

theorem tailTrace_25914 : CollatzResearch.WordTrace tailWord_25914 prefixEnd_25914 8870891787144563370553 := by
  unfold tailWord_25914
  simp only [CollatzResearch.WordTrace]
  refine ⟨236290307031369650989199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 630107485416985735971197 236290307031369650989199)
  ·
    refine ⟨354435460547054476483799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236290307031369650989199 354435460547054476483799)
    ·
      refine ⟨531653190820581714725699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354435460547054476483799 531653190820581714725699)
      ·
        refine ⟨797479786230872572088549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531653190820581714725699 797479786230872572088549)
        ·
          refine ⟨149527459918288607266603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 797479786230872572088549 149527459918288607266603)
          ·
            refine ⟨224291189877432910899905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149527459918288607266603 224291189877432910899905)
            ·
              refine ⟨168218392408074683174929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224291189877432910899905 168218392408074683174929)
              ·
                refine ⟨126163794306056012381197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168218392408074683174929 126163794306056012381197)
                ·
                  refine ⟨47311422864771004642949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126163794306056012381197 47311422864771004642949)
                  ·
                    refine ⟨8870891787144563370553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47311422864771004642949 8870891787144563370553)
                    ·
                      rfl

theorem cell22_25914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_25914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25914 prefixEnd_25914 := by exact prefixLift 25914
  have htrace : WordTrace (prefixWord ++ tailWord_25914) baseStart_25914 baseEnd_25914 := by
    simpa [prefixWord, tailWord_25914, baseEnd_25914] using wordTrace_append hprefix tailTrace_25914
  have hstable : (prefixWord ++ tailWord_25914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25914).length < 2 ^ (prefixWord ++ tailWord_25914).sum := by decide
  have hdescent : baseEnd_25914 < baseStart_25914 := by decide
  rcases family_descends (prefixWord ++ tailWord_25914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25944 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_25944 : Nat := 118140960795 + 25944 * 2 ^ 59
def prefixEnd_25944 : Nat := 4983230072969 + 3 ^ 40 * 25944 * 2
def baseEnd_25944 : Nat := 8881161400234485120461

theorem tailTrace_25944 : CollatzResearch.WordTrace tailWord_25944 prefixEnd_25944 8881161400234485120461 := by
  unfold tailWord_25944
  simp only [CollatzResearch.WordTrace]
  refine ⟨473127709008396863774443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 630836945344529151699257 473127709008396863774443)
  ·
    refine ⟨709691563512595295661665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473127709008396863774443 709691563512595295661665)
    ·
      refine ⟨532268672634446471746249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 709691563512595295661665 532268672634446471746249)
      ·
        refine ⟨399201504475834853809687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532268672634446471746249 399201504475834853809687)
        ·
          refine ⟨598802256713752280714531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399201504475834853809687 598802256713752280714531)
          ·
            refine ⟨898203385070628421071797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598802256713752280714531 898203385070628421071797)
            ·
              refine ⟨84206567350371414475481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 898203385070628421071797 84206567350371414475481)
              ·
                refine ⟨63154925512778560856611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84206567350371414475481 63154925512778560856611)
                ·
                  refine ⟨94732388269167841284917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63154925512778560856611 94732388269167841284917)
                  ·
                    refine ⟨8881161400234485120461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94732388269167841284917 8881161400234485120461)
                    ·
                      rfl

theorem cell22_25944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_25944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25944 prefixEnd_25944 := by exact prefixLift 25944
  have htrace : WordTrace (prefixWord ++ tailWord_25944) baseStart_25944 baseEnd_25944 := by
    simpa [prefixWord, tailWord_25944, baseEnd_25944] using wordTrace_append hprefix tailTrace_25944
  have hstable : (prefixWord ++ tailWord_25944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25944).length < 2 ^ (prefixWord ++ tailWord_25944).sum := by decide
  have hdescent : baseEnd_25944 < baseStart_25944 := by decide
  rcases family_descends (prefixWord ++ tailWord_25944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25991 : List Nat := [1, 1, 4, 2, 2, 3, 3, 6]
def baseStart_25991 : Nat := 118140960795 + 25991 * 2 ^ 59
def prefixEnd_25991 : Nat := 4983230072969 + 3 ^ 40 * 25991 * 2
def baseEnd_25991 : Nat := 988583384526892132813

theorem tailTrace_25991 : CollatzResearch.WordTrace tailWord_25991 prefixEnd_25991 988583384526892132813 := by
  unfold tailWord_25991
  simp only [CollatzResearch.WordTrace]
  refine ⟨947969648846520754509827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 631979765897680503006551 947969648846520754509827)
  ·
    refine ⟨1421954473269781131764741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947969648846520754509827 1421954473269781131764741)
    ·
      refine ⟨266616463738083962205889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1421954473269781131764741 266616463738083962205889)
      ·
        refine ⟨199962347803562971654417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266616463738083962205889 199962347803562971654417)
        ·
          refine ⟨149971760852672228740813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199962347803562971654417 149971760852672228740813)
          ·
            refine ⟨56239410319752085777805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149971760852672228740813 56239410319752085777805)
            ·
              refine ⟨21089778869907032166677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56239410319752085777805 21089778869907032166677)
              ·
                refine ⟨988583384526892132813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21089778869907032166677 988583384526892132813)
                ·
                  rfl

theorem cell22_25991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 6].length) (baseStart_25991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25991 prefixEnd_25991 := by exact prefixLift 25991
  have htrace : WordTrace (prefixWord ++ tailWord_25991) baseStart_25991 baseEnd_25991 := by
    simpa [prefixWord, tailWord_25991, baseEnd_25991] using wordTrace_append hprefix tailTrace_25991
  have hstable : (prefixWord ++ tailWord_25991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25991).length < 2 ^ (prefixWord ++ tailWord_25991).sum := by decide
  have hdescent : baseEnd_25991 < baseStart_25991 := by decide
  rcases family_descends (prefixWord ++ tailWord_25991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25993 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 2, 4]
def baseStart_25993 : Nat := 118140960795 + 25993 * 2 ^ 59
def prefixEnd_25993 : Nat := 4983230072969 + 3 ^ 40 * 25993 * 2
def baseEnd_25993 : Nat := 8897935101614690645311

theorem tailTrace_25993 : CollatzResearch.WordTrace tailWord_25993 prefixEnd_25993 8897935101614690645311 := by
  unfold tailWord_25993
  simp only [CollatzResearch.WordTrace]
  refine ⟨948042594839275096082633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 632028396559516730721755 948042594839275096082633)
  ·
    refine ⟨711031946129456322061975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 948042594839275096082633 711031946129456322061975)
    ·
      refine ⟨1066547919194184483092963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 711031946129456322061975 1066547919194184483092963)
      ·
        refine ⟨1599821878791276724639445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066547919194184483092963 1599821878791276724639445)
        ·
          refine ⟨37495825284170548233737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1599821878791276724639445 37495825284170548233737)
          ·
            refine ⟨28121868963127911175303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37495825284170548233737 28121868963127911175303)
            ·
              refine ⟨42182803444691866762955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28121868963127911175303 42182803444691866762955)
              ·
                refine ⟨63274205167037800144433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42182803444691866762955 63274205167037800144433)
                ·
                  refine ⟨47455653875278350108325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63274205167037800144433 47455653875278350108325)
                  ·
                    refine ⟨8897935101614690645311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47455653875278350108325 8897935101614690645311)
                    ·
                      rfl

theorem cell22_25993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_25993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_25993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_25993 prefixEnd_25993 := by exact prefixLift 25993
  have htrace : WordTrace (prefixWord ++ tailWord_25993) baseStart_25993 baseEnd_25993 := by
    simpa [prefixWord, tailWord_25993, baseEnd_25993] using wordTrace_append hprefix tailTrace_25993
  have hstable : (prefixWord ++ tailWord_25993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25993).length < 2 ^ (prefixWord ++ tailWord_25993).sum := by decide
  have hdescent : baseEnd_25993 < baseStart_25993 := by decide
  rcases family_descends (prefixWord ++ tailWord_25993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26012 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_26012 : Nat := 118140960795 + 26012 * 2 ^ 59
def prefixEnd_26012 : Nat := 4983230072969 + 3 ^ 40 * 26012 * 2
def baseEnd_26012 : Nat := 8904439189904974420253

theorem tailTrace_26012 : CollatzResearch.WordTrace tailWord_26012 prefixEnd_26012 8904439189904974420253 := by
  unfold tailWord_26012
  simp only [CollatzResearch.WordTrace]
  refine ⟨474367790885220670512145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 632490387846960894016193 474367790885220670512145)
  ·
    refine ⟨355775843163915502884109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 474367790885220670512145 355775843163915502884109)
    ·
      refine ⟨133415941186468313581541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355775843163915502884109 133415941186468313581541)
      ·
        refine ⟨25015488972462808796539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133415941186468313581541 25015488972462808796539)
        ·
          refine ⟨37523233458694213194809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25015488972462808796539 37523233458694213194809)
          ·
            refine ⟨28142425094020659896107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37523233458694213194809 28142425094020659896107)
            ·
              refine ⟨42213637641030989844161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28142425094020659896107 42213637641030989844161)
              ·
                refine ⟨31660228230773242383121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42213637641030989844161 31660228230773242383121)
                ·
                  refine ⟨23745171173079931787341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31660228230773242383121 23745171173079931787341)
                  ·
                    refine ⟨8904439189904974420253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23745171173079931787341 8904439189904974420253)
                    ·
                      rfl

theorem cell22_26012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_26012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26012 prefixEnd_26012 := by exact prefixLift 26012
  have htrace : WordTrace (prefixWord ++ tailWord_26012) baseStart_26012 baseEnd_26012 := by
    simpa [prefixWord, tailWord_26012, baseEnd_26012] using wordTrace_append hprefix tailTrace_26012
  have hstable : (prefixWord ++ tailWord_26012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26012).length < 2 ^ (prefixWord ++ tailWord_26012).sum := by decide
  have hdescent : baseEnd_26012 < baseStart_26012 := by decide
  rcases family_descends (prefixWord ++ tailWord_26012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26019 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 7]
def baseStart_26019 : Nat := 118140960795 + 26019 * 2 ^ 59
def prefixEnd_26019 : Nat := 4983230072969 + 3 ^ 40 * 26019 * 2
def baseEnd_26019 : Nat := 2968945144319763165077

theorem tailTrace_26019 : CollatzResearch.WordTrace tailWord_26019 prefixEnd_26019 2968945144319763165077 := by
  unfold tailWord_26019
  simp only [CollatzResearch.WordTrace]
  refine ⟨948990892745081536529111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 632660595163387691019407 948990892745081536529111)
  ·
    refine ⟨1423486339117622304793667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948990892745081536529111 1423486339117622304793667)
    ·
      refine ⟨2135229508676433457190501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423486339117622304793667 2135229508676433457190501)
      ·
        refine ⟨400355532876831273223219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2135229508676433457190501 400355532876831273223219)
        ·
          refine ⟨600533299315246909834829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400355532876831273223219 600533299315246909834829)
          ·
            refine ⟨225199987243217591188061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600533299315246909834829 225199987243217591188061)
            ·
              refine ⟨84449995216206596695523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225199987243217591188061 84449995216206596695523)
              ·
                refine ⟨126674992824309895043285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84449995216206596695523 126674992824309895043285)
                ·
                  refine ⟨2968945144319763165077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 126674992824309895043285 2968945144319763165077)
                  ·
                    rfl

theorem cell22_26019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 7].length) (baseStart_26019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26019 prefixEnd_26019 := by exact prefixLift 26019
  have htrace : WordTrace (prefixWord ++ tailWord_26019) baseStart_26019 baseEnd_26019 := by
    simpa [prefixWord, tailWord_26019, baseEnd_26019] using wordTrace_append hprefix tailTrace_26019
  have hstable : (prefixWord ++ tailWord_26019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26019).length < 2 ^ (prefixWord ++ tailWord_26019).sum := by decide
  have hdescent : baseEnd_26019 < baseStart_26019 := by decide
  rcases family_descends (prefixWord ++ tailWord_26019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26023 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 3, 3]
def baseStart_26023 : Nat := 118140960795 + 26023 * 2 ^ 59
def prefixEnd_26023 : Nat := 4983230072969 + 3 ^ 40 * 26023 * 2
def baseEnd_26023 : Nat := 8908204714704612395219

theorem tailTrace_26023 : CollatzResearch.WordTrace tailWord_26023 prefixEnd_26023 8908204714704612395219 := by
  unfold tailWord_26023
  simp only [CollatzResearch.WordTrace]
  refine ⟨949136784730590219674723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 632757856487060146449815 949136784730590219674723)
  ·
    refine ⟨1423705177095885329512085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949136784730590219674723 1423705177095885329512085)
    ·
      refine ⟨66736180176369624820879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1423705177095885329512085 66736180176369624820879)
      ·
        refine ⟨100104270264554437231319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66736180176369624820879 100104270264554437231319)
        ·
          refine ⟨150156405396831655846979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100104270264554437231319 150156405396831655846979)
          ·
            refine ⟨225234608095247483770469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150156405396831655846979 225234608095247483770469)
            ·
              refine ⟨42231489017858903206963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225234608095247483770469 42231489017858903206963)
              ·
                refine ⟨63347233526788354810445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42231489017858903206963 63347233526788354810445)
                ·
                  refine ⟨23755212572545633053917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63347233526788354810445 23755212572545633053917)
                  ·
                    refine ⟨8908204714704612395219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23755212572545633053917 8908204714704612395219)
                    ·
                      rfl

theorem cell22_26023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_26023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26023 prefixEnd_26023 := by exact prefixLift 26023
  have htrace : WordTrace (prefixWord ++ tailWord_26023) baseStart_26023 baseEnd_26023 := by
    simpa [prefixWord, tailWord_26023, baseEnd_26023] using wordTrace_append hprefix tailTrace_26023
  have hstable : (prefixWord ++ tailWord_26023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26023).length < 2 ^ (prefixWord ++ tailWord_26023).sum := by decide
  have hdescent : baseEnd_26023 < baseStart_26023 := by decide
  rcases family_descends (prefixWord ++ tailWord_26023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26034 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_26034 : Nat := 118140960795 + 26034 * 2 ^ 59
def prefixEnd_26034 : Nat := 4983230072969 + 3 ^ 40 * 26034 * 2
def baseEnd_26034 : Nat := 8911970239504250370185

theorem tailTrace_26034 : CollatzResearch.WordTrace tailWord_26034 prefixEnd_26034 8911970239504250370185 := by
  unfold tailWord_26034
  simp only [CollatzResearch.WordTrace]
  refine ⟨237384496922684774581289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 633025325127159398883437 237384496922684774581289)
  ·
    refine ⟨178038372692013580935967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237384496922684774581289 178038372692013580935967)
    ·
      refine ⟨267057559038020371403951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178038372692013580935967 267057559038020371403951)
      ·
        refine ⟨400586338557030557105927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267057559038020371403951 400586338557030557105927)
        ·
          refine ⟨600879507835545835658891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400586338557030557105927 600879507835545835658891)
          ·
            refine ⟨901319261753318753488337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600879507835545835658891 901319261753318753488337)
            ·
              refine ⟨675989446314989065116253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901319261753318753488337 675989446314989065116253)
              ·
                refine ⟨253496042368120899418595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675989446314989065116253 253496042368120899418595)
                ·
                  refine ⟨380244063552181349127893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253496042368120899418595 380244063552181349127893)
                  ·
                    refine ⟨8911970239504250370185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 380244063552181349127893 8911970239504250370185)
                    ·
                      rfl

theorem cell22_26034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_26034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26034 prefixEnd_26034 := by exact prefixLift 26034
  have htrace : WordTrace (prefixWord ++ tailWord_26034) baseStart_26034 baseEnd_26034 := by
    simpa [prefixWord, tailWord_26034, baseEnd_26034] using wordTrace_append hprefix tailTrace_26034
  have hstable : (prefixWord ++ tailWord_26034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26034).length < 2 ^ (prefixWord ++ tailWord_26034).sum := by decide
  have hdescent : baseEnd_26034 < baseStart_26034 := by decide
  rcases family_descends (prefixWord ++ tailWord_26034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26081 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 6]
def baseStart_26081 : Nat := 118140960795 + 26081 * 2 ^ 59
def prefixEnd_26081 : Nat := 4983230072969 + 3 ^ 40 * 26081 * 2
def baseEnd_26081 : Nat := 2976019766670598148347

theorem tailTrace_26081 : CollatzResearch.WordTrace tailWord_26081 prefixEnd_26081 2976019766670598148347 := by
  unfold tailWord_26081
  simp only [CollatzResearch.WordTrace]
  refine ⟨951252218520466125286097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 634168145680310750190731 951252218520466125286097)
  ·
    refine ⟨713439163890349593964573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 951252218520466125286097 713439163890349593964573)
    ·
      refine ⟨267539686458881097736715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 713439163890349593964573 267539686458881097736715)
      ·
        refine ⟨401309529688321646605073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267539686458881097736715 401309529688321646605073)
        ·
          refine ⟨300982147266241234953805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401309529688321646605073 300982147266241234953805)
          ·
            refine ⟨112868305224840463107677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300982147266241234953805 112868305224840463107677)
            ·
              refine ⟨42325614459315173665379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112868305224840463107677 42325614459315173665379)
              ·
                refine ⟨63488421688972760498069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42325614459315173665379 63488421688972760498069)
                ·
                  refine ⟨2976019766670598148347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63488421688972760498069 2976019766670598148347)
                  ·
                    rfl

theorem cell22_26081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_26081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26081 prefixEnd_26081 := by exact prefixLift 26081
  have htrace : WordTrace (prefixWord ++ tailWord_26081) baseStart_26081 baseEnd_26081 := by
    simpa [prefixWord, tailWord_26081, baseEnd_26081] using wordTrace_append hprefix tailTrace_26081
  have hstable : (prefixWord ++ tailWord_26081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26081).length < 2 ^ (prefixWord ++ tailWord_26081).sum := by decide
  have hdescent : baseEnd_26081 < baseStart_26081 := by decide
  rcases family_descends (prefixWord ++ tailWord_26081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26113 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_26113 : Nat := 118140960795 + 26113 * 2 ^ 59
def prefixEnd_26113 : Nat := 4983230072969 + 3 ^ 40 * 26113 * 2
def baseEnd_26113 : Nat := 8939013553974377644943

theorem tailTrace_26113 : CollatzResearch.WordTrace tailWord_26113 prefixEnd_26113 8939013553974377644943 := by
  unfold tailWord_26113
  simp only [CollatzResearch.WordTrace]
  refine ⟨952419354404535590450993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 634946236269690393633995 952419354404535590450993)
  ·
    refine ⟨714314515803401692838245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 952419354404535590450993 714314515803401692838245)
    ·
      refine ⟨133933971713137817407171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 714314515803401692838245 133933971713137817407171)
      ·
        refine ⟨200900957569706726110757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133933971713137817407171 200900957569706726110757)
        ·
          refine ⟨37668929544320011145767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200900957569706726110757 37668929544320011145767)
          ·
            refine ⟨56503394316480016718651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37668929544320011145767 56503394316480016718651)
            ·
              refine ⟨84755091474720025077977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56503394316480016718651 84755091474720025077977)
              ·
                refine ⟨63566318606040018808483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84755091474720025077977 63566318606040018808483)
                ·
                  refine ⟨95349477909060028212725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63566318606040018808483 95349477909060028212725)
                  ·
                    refine ⟨8939013553974377644943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95349477909060028212725 8939013553974377644943)
                    ·
                      rfl

theorem cell22_26113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_26113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26113 prefixEnd_26113 := by exact prefixLift 26113
  have htrace : WordTrace (prefixWord ++ tailWord_26113) baseStart_26113 baseEnd_26113 := by
    simpa [prefixWord, tailWord_26113, baseEnd_26113] using wordTrace_append hprefix tailTrace_26113
  have hstable : (prefixWord ++ tailWord_26113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26113).length < 2 ^ (prefixWord ++ tailWord_26113).sum := by decide
  have hdescent : baseEnd_26113 < baseStart_26113 := by decide
  rcases family_descends (prefixWord ++ tailWord_26113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26126 : List Nat := [4, 1, 1, 2, 4, 10]
def baseStart_26126 : Nat := 118140960795 + 26126 * 2 ^ 59
def prefixEnd_26126 : Nat := 4983230072969 + 3 ^ 40 * 26126 * 2
def baseEnd_26126 : Nat := 110413132341317000863

theorem tailTrace_26126 : CollatzResearch.WordTrace tailWord_26126 prefixEnd_26126 110413132341317000863 := by
  unfold tailWord_26126
  simp only [CollatzResearch.WordTrace]
  refine ⟨119111687919679851334279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 635262335571625873782821 119111687919679851334279)
  ·
    refine ⟨178667531879519777001419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119111687919679851334279 178667531879519777001419)
    ·
      refine ⟨268001297819279665502129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178667531879519777001419 268001297819279665502129)
      ·
        refine ⟨201000973364459749126597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268001297819279665502129 201000973364459749126597)
        ·
          refine ⟨37687682505836202961237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201000973364459749126597 37687682505836202961237)
          ·
            refine ⟨110413132341317000863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 37687682505836202961237 110413132341317000863)
            ·
              rfl

theorem cell22_26126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 10].length) (baseStart_26126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26126 prefixEnd_26126 := by exact prefixLift 26126
  have htrace : WordTrace (prefixWord ++ tailWord_26126) baseStart_26126 baseEnd_26126 := by
    simpa [prefixWord, tailWord_26126, baseEnd_26126] using wordTrace_append hprefix tailTrace_26126
  have hstable : (prefixWord ++ tailWord_26126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26126).length < 2 ^ (prefixWord ++ tailWord_26126).sum := by decide
  have hdescent : baseEnd_26126 < baseStart_26126 := by decide
  rcases family_descends (prefixWord ++ tailWord_26126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26132 : List Nat := [2, 4, 3, 1, 2, 1, 1, 4, 4]
def baseStart_26132 : Nat := 118140960795 + 26132 * 2 ^ 59
def prefixEnd_26132 : Nat := 4983230072969 + 3 ^ 40 * 26132 * 2
def baseEnd_26132 : Nat := 2981839214088220473295

theorem tailTrace_26132 : CollatzResearch.WordTrace tailWord_26132 prefixEnd_26132 2981839214088220473295 := by
  unfold tailWord_26132
  simp only [CollatzResearch.WordTrace]
  refine ⟨476556170667850917696325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 635408227557134556928433 476556170667850917696325)
  ·
    refine ⟨89354282000222047068061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 476556170667850917696325 89354282000222047068061)
    ·
      refine ⟨33507855750083267650523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89354282000222047068061 33507855750083267650523)
      ·
        refine ⟨50261783625124901475785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33507855750083267650523 50261783625124901475785)
        ·
          refine ⟨37696337718843676106839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50261783625124901475785 37696337718843676106839)
          ·
            refine ⟨56544506578265514160259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37696337718843676106839 56544506578265514160259)
            ·
              refine ⟨84816759867398271240389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56544506578265514160259 84816759867398271240389)
              ·
                refine ⟨15903142475137175857573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84816759867398271240389 15903142475137175857573)
                ·
                  refine ⟨2981839214088220473295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15903142475137175857573 2981839214088220473295)
                  ·
                    rfl

theorem cell22_26132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_26132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26132 prefixEnd_26132 := by exact prefixLift 26132
  have htrace : WordTrace (prefixWord ++ tailWord_26132) baseStart_26132 baseEnd_26132 := by
    simpa [prefixWord, tailWord_26132, baseEnd_26132] using wordTrace_append hprefix tailTrace_26132
  have hstable : (prefixWord ++ tailWord_26132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26132).length < 2 ^ (prefixWord ++ tailWord_26132).sum := by decide
  have hdescent : baseEnd_26132 < baseStart_26132 := by decide
  rcases family_descends (prefixWord ++ tailWord_26132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26175 : List Nat := [1, 1, 2, 2, 3, 3, 1, 5, 1, 3]
def baseStart_26175 : Nat := 118140960795 + 26175 * 2 ^ 59
def prefixEnd_26175 : Nat := 4983230072969 + 3 ^ 40 * 26175 * 2
def baseEnd_26175 : Nat := 8960237421026882594753

theorem tailTrace_26175 : CollatzResearch.WordTrace tailWord_26175 prefixEnd_26175 8960237421026882594753 := by
  unfold tailWord_26175
  simp only [CollatzResearch.WordTrace]
  refine ⟨954680680179920179207979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 636453786786613452805319 954680680179920179207979)
  ·
    refine ⟨1432021020269880268811969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954680680179920179207979 1432021020269880268811969)
    ·
      refine ⟨1074015765202410201608977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1432021020269880268811969 1074015765202410201608977)
      ·
        refine ⟨805511823901807651206733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1074015765202410201608977 805511823901807651206733)
        ·
          refine ⟨302066933963177869202525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 805511823901807651206733 302066933963177869202525)
          ·
            refine ⟨113275100236191700950947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302066933963177869202525 113275100236191700950947)
            ·
              refine ⟨169912650354287551426421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113275100236191700950947 169912650354287551426421)
              ·
                refine ⟨15929310970714457946227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169912650354287551426421 15929310970714457946227)
                ·
                  refine ⟨23893966456071686919341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15929310970714457946227 23893966456071686919341)
                  ·
                    refine ⟨8960237421026882594753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23893966456071686919341 8960237421026882594753)
                    ·
                      rfl

theorem cell22_26175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 3].length) (baseStart_26175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26175 prefixEnd_26175 := by exact prefixLift 26175
  have htrace : WordTrace (prefixWord ++ tailWord_26175) baseStart_26175 baseEnd_26175 := by
    simpa [prefixWord, tailWord_26175, baseEnd_26175] using wordTrace_append hprefix tailTrace_26175
  have hstable : (prefixWord ++ tailWord_26175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26175).length < 2 ^ (prefixWord ++ tailWord_26175).sum := by decide
  have hdescent : baseEnd_26175 < baseStart_26175 := by decide
  rcases family_descends (prefixWord ++ tailWord_26175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26186 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_26186 : Nat := 118140960795 + 26186 * 2 ^ 59
def prefixEnd_26186 : Nat := 4983230072969 + 3 ^ 40 * 26186 * 2
def baseEnd_26186 : Nat := 8964002945826520569719

theorem tailTrace_26186 : CollatzResearch.WordTrace tailWord_26186 prefixEnd_26186 8964002945826520569719 := by
  unfold tailWord_26186
  simp only [CollatzResearch.WordTrace]
  refine ⟨238770470785017264464603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 636721255426712705238941 238770470785017264464603)
  ·
    refine ⟨358155706177525896696905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238770470785017264464603 358155706177525896696905)
    ·
      refine ⟨268616779633144422522679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358155706177525896696905 268616779633144422522679)
      ·
        refine ⟨402925169449716633784019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268616779633144422522679 402925169449716633784019)
        ·
          refine ⟨604387754174574950676029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402925169449716633784019 604387754174574950676029)
          ·
            refine ⟨226645407815465606503511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604387754174574950676029 226645407815465606503511)
            ·
              refine ⟨339968111723198409755267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226645407815465606503511 339968111723198409755267)
              ·
                refine ⟨509952167584797614632901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339968111723198409755267 509952167584797614632901)
                ·
                  refine ⟨95616031422149552743669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509952167584797614632901 95616031422149552743669)
                  ·
                    refine ⟨8964002945826520569719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95616031422149552743669 8964002945826520569719)
                    ·
                      rfl

theorem cell22_26186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_26186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26186 prefixEnd_26186 := by exact prefixLift 26186
  have htrace : WordTrace (prefixWord ++ tailWord_26186) baseStart_26186 baseEnd_26186 := by
    simpa [prefixWord, tailWord_26186, baseEnd_26186] using wordTrace_append hprefix tailTrace_26186
  have hstable : (prefixWord ++ tailWord_26186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26186).length < 2 ^ (prefixWord ++ tailWord_26186).sum := by decide
  have hdescent : baseEnd_26186 < baseStart_26186 := by decide
  rcases family_descends (prefixWord ++ tailWord_26186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26188 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 5]
def baseStart_26188 : Nat := 118140960795 + 26188 * 2 ^ 59
def prefixEnd_26188 : Nat := 4983230072969 + 3 ^ 40 * 26188 * 2
def baseEnd_26188 : Nat := 2988229195566394006571

theorem tailTrace_26188 : CollatzResearch.WordTrace tailWord_26188 prefixEnd_26188 2988229195566394006571 := by
  unfold tailWord_26188
  simp only [CollatzResearch.WordTrace]
  refine ⟨477577414566411699715609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 636769886088548932954145 477577414566411699715609)
  ·
    refine ⟨358183060924808774786707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 477577414566411699715609 358183060924808774786707)
    ·
      refine ⟨537274591387213162180061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358183060924808774786707 537274591387213162180061)
      ·
        refine ⟨201477971770204935817523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537274591387213162180061 201477971770204935817523)
        ·
          refine ⟨302216957655307403726285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201477971770204935817523 302216957655307403726285)
          ·
            refine ⟨113331359120740276397357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302216957655307403726285 113331359120740276397357)
            ·
              refine ⟨42499259670277603649009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113331359120740276397357 42499259670277603649009)
              ·
                refine ⟨31874444752708202736757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42499259670277603649009 31874444752708202736757)
                ·
                  refine ⟨2988229195566394006571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31874444752708202736757 2988229195566394006571)
                  ·
                    rfl

theorem cell22_26188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_26188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26188 prefixEnd_26188 := by exact prefixLift 26188
  have htrace : WordTrace (prefixWord ++ tailWord_26188) baseStart_26188 baseEnd_26188 := by
    simpa [prefixWord, tailWord_26188, baseEnd_26188] using wordTrace_append hprefix tailTrace_26188
  have hstable : (prefixWord ++ tailWord_26188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26188).length < 2 ^ (prefixWord ++ tailWord_26188).sum := by decide
  have hdescent : baseEnd_26188 < baseStart_26188 := by decide
  rcases family_descends (prefixWord ++ tailWord_26188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26201 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_26201 : Nat := 118140960795 + 26201 * 2 ^ 59
def prefixEnd_26201 : Nat := 4983230072969 + 3 ^ 40 * 26201 * 2
def baseEnd_26201 : Nat := 8969137752371481444673

theorem tailTrace_26201 : CollatzResearch.WordTrace tailWord_26201 prefixEnd_26201 8969137752371481444673 := by
  unfold tailWord_26201
  simp only [CollatzResearch.WordTrace]
  refine ⟨955628978085726619654457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 637085985390484413102971 955628978085726619654457)
  ·
    refine ⟨716721733564294964740843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 955628978085726619654457 716721733564294964740843)
    ·
      refine ⟨1075082600346442447111265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716721733564294964740843 1075082600346442447111265)
      ·
        refine ⟨806311950259831835333449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1075082600346442447111265 806311950259831835333449)
        ·
          refine ⟨604733962694873876500087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806311950259831835333449 604733962694873876500087)
          ·
            refine ⟨907100944042310814750131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604733962694873876500087 907100944042310814750131)
            ·
              refine ⟨1360651416063466222125197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907100944042310814750131 1360651416063466222125197)
              ·
                refine ⟨510244281023799833296949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1360651416063466222125197 510244281023799833296949)
                ·
                  refine ⟨47835401345981234371589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510244281023799833296949 47835401345981234371589)
                  ·
                    refine ⟨8969137752371481444673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47835401345981234371589 8969137752371481444673)
                    ·
                      rfl

theorem cell22_26201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_26201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26201 prefixEnd_26201 := by exact prefixLift 26201
  have htrace : WordTrace (prefixWord ++ tailWord_26201) baseStart_26201 baseEnd_26201 := by
    simpa [prefixWord, tailWord_26201, baseEnd_26201] using wordTrace_append hprefix tailTrace_26201
  have hstable : (prefixWord ++ tailWord_26201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26201).length < 2 ^ (prefixWord ++ tailWord_26201).sum := by decide
  have hdescent : baseEnd_26201 < baseStart_26201 := by decide
  rcases family_descends (prefixWord ++ tailWord_26201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26231 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 3, 5]
def baseStart_26231 : Nat := 118140960795 + 26231 * 2 ^ 59
def prefixEnd_26231 : Nat := 4983230072969 + 3 ^ 40 * 26231 * 2
def baseEnd_26231 : Nat := 8979407365461403194581

theorem tailTrace_26231 : CollatzResearch.WordTrace tailWord_26231 prefixEnd_26231 8979407365461403194581 := by
  unfold tailWord_26231
  simp only [CollatzResearch.WordTrace]
  refine ⟨956723167977041743246547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 637815445318027828831031 956723167977041743246547)
  ·
    refine ⟨1435084751965562614869821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 956723167977041743246547 1435084751965562614869821)
    ·
      refine ⟨538156781987085980576183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1435084751965562614869821 538156781987085980576183)
      ·
        refine ⟨807235172980628970864275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538156781987085980576183 807235172980628970864275)
        ·
          refine ⟨1210852759470943456296413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807235172980628970864275 1210852759470943456296413)
          ·
            refine ⟨454069784801603796111155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210852759470943456296413 454069784801603796111155)
            ·
              refine ⟨681104677202405694166733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454069784801603796111155 681104677202405694166733)
              ·
                refine ⟨255414253950902135312525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 681104677202405694166733 255414253950902135312525)
                ·
                  refine ⟨95780345231588300742197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255414253950902135312525 95780345231588300742197)
                  ·
                    refine ⟨8979407365461403194581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95780345231588300742197 8979407365461403194581)
                    ·
                      rfl

theorem cell22_26231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_26231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26231 prefixEnd_26231 := by exact prefixLift 26231
  have htrace : WordTrace (prefixWord ++ tailWord_26231) baseStart_26231 baseEnd_26231 := by
    simpa [prefixWord, tailWord_26231, baseEnd_26231] using wordTrace_append hprefix tailTrace_26231
  have hstable : (prefixWord ++ tailWord_26231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26231).length < 2 ^ (prefixWord ++ tailWord_26231).sum := by decide
  have hdescent : baseEnd_26231 < baseStart_26231 := by decide
  rcases family_descends (prefixWord ++ tailWord_26231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26250 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_26250 : Nat := 118140960795 + 26250 * 2 ^ 59
def prefixEnd_26250 : Nat := 4983230072969 + 3 ^ 40 * 26250 * 2
def baseEnd_26250 : Nat := 2995303817917228989841

theorem tailTrace_26250 : CollatzResearch.WordTrace tailWord_26250 prefixEnd_26250 2995303817917228989841 := by
  unfold tailWord_26250
  simp only [CollatzResearch.WordTrace]
  refine ⟨239354038727051997047051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 638277436605471992125469 239354038727051997047051)
  ·
    refine ⟨359031058090577995570577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239354038727051997047051 359031058090577995570577)
    ·
      refine ⟨269273293567933496677933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359031058090577995570577 269273293567933496677933)
      ·
        refine ⟨100977485087975061254225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269273293567933496677933 100977485087975061254225)
        ·
          refine ⟨75733113815981295940669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100977485087975061254225 75733113815981295940669)
          ·
            refine ⟨28399917680992985977751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75733113815981295940669 28399917680992985977751)
            ·
              refine ⟨42599876521489478966627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28399917680992985977751 42599876521489478966627)
              ·
                refine ⟨63899814782234218449941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42599876521489478966627 63899814782234218449941)
                ·
                  refine ⟨2995303817917228989841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63899814782234218449941 2995303817917228989841)
                  ·
                    rfl

theorem cell22_26250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_26250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26250 prefixEnd_26250 := by exact prefixLift 26250
  have htrace : WordTrace (prefixWord ++ tailWord_26250) baseStart_26250 baseEnd_26250 := by
    simpa [prefixWord, tailWord_26250, baseEnd_26250] using wordTrace_append hprefix tailTrace_26250
  have hstable : (prefixWord ++ tailWord_26250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26250).length < 2 ^ (prefixWord ++ tailWord_26250).sum := by decide
  have hdescent : baseEnd_26250 < baseStart_26250 := by decide
  rcases family_descends (prefixWord ++ tailWord_26250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26308 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_26308 : Nat := 118140960795 + 26308 * 2 ^ 59
def prefixEnd_26308 : Nat := 4983230072969 + 3 ^ 40 * 26308 * 2
def baseEnd_26308 : Nat := 9005766039058869019345

theorem tailTrace_26308 : CollatzResearch.WordTrace tailWord_26308 prefixEnd_26308 9005766039058869019345 := by
  unfold tailWord_26308
  simp only [CollatzResearch.WordTrace]
  refine ⟨479765794349041946899789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 639687725798722595866385 479765794349041946899789)
  ·
    refine ⟨179912172880890730087421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 479765794349041946899789 179912172880890730087421)
    ·
      refine ⟨67467064830334023782783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179912172880890730087421 67467064830334023782783)
      ·
        refine ⟨101200597245501035674175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67467064830334023782783 101200597245501035674175)
        ·
          refine ⟨151800895868251553511263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101200597245501035674175 151800895868251553511263)
          ·
            refine ⟨227701343802377330266895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151800895868251553511263 227701343802377330266895)
            ·
              refine ⟨341552015703565995400343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227701343802377330266895 341552015703565995400343)
              ·
                refine ⟨512328023555348993100515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341552015703565995400343 512328023555348993100515)
                ·
                  refine ⟨768492035333023489650773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512328023555348993100515 768492035333023489650773)
                  ·
                    refine ⟨9005766039058869019345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 768492035333023489650773 9005766039058869019345)
                    ·
                      rfl

theorem cell22_26308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_26308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26308 prefixEnd_26308 := by exact prefixLift 26308
  have htrace : WordTrace (prefixWord ++ tailWord_26308) baseStart_26308 baseEnd_26308 := by
    simpa [prefixWord, tailWord_26308, baseEnd_26308] using wordTrace_append hprefix tailTrace_26308
  have hstable : (prefixWord ++ tailWord_26308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26308).length < 2 ^ (prefixWord ++ tailWord_26308).sum := by decide
  have hdescent : baseEnd_26308 < baseStart_26308 := by decide
  rcases family_descends (prefixWord ++ tailWord_26308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26344 : List Nat := [2, 1, 4, 1, 3, 2, 2, 3, 1, 3]
def baseStart_26344 : Nat := 118140960795 + 26344 * 2 ^ 59
def prefixEnd_26344 : Nat := 4983230072969 + 3 ^ 40 * 26344 * 2
def baseEnd_26344 : Nat := 9018089574766775119235

theorem tailTrace_26344 : CollatzResearch.WordTrace tailWord_26344 prefixEnd_26344 9018089574766775119235 := by
  unfold tailWord_26344
  simp only [CollatzResearch.WordTrace]
  refine ⟨480422308283831021055043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 640563077711774694740057 480422308283831021055043)
  ·
    refine ⟨720633462425746531582565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 480422308283831021055043 720633462425746531582565)
    ·
      refine ⟨135118774204827474671731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 720633462425746531582565 135118774204827474671731)
      ·
        refine ⟨202678161307241212007597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135118774204827474671731 202678161307241212007597)
        ·
          refine ⟨76004310490215454502849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202678161307241212007597 76004310490215454502849)
          ·
            refine ⟨57003232867661590877137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76004310490215454502849 57003232867661590877137)
            ·
              refine ⟨42752424650746193157853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57003232867661590877137 42752424650746193157853)
              ·
                refine ⟨16032159244029822434195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42752424650746193157853 16032159244029822434195)
                ·
                  refine ⟨24048238866044733651293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16032159244029822434195 24048238866044733651293)
                  ·
                    refine ⟨9018089574766775119235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24048238866044733651293 9018089574766775119235)
                    ·
                      rfl

theorem cell22_26344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_26344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26344 prefixEnd_26344 := by exact prefixLift 26344
  have htrace : WordTrace (prefixWord ++ tailWord_26344) baseStart_26344 baseEnd_26344 := by
    simpa [prefixWord, tailWord_26344, baseEnd_26344] using wordTrace_append hprefix tailTrace_26344
  have hstable : (prefixWord ++ tailWord_26344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26344).length < 2 ^ (prefixWord ++ tailWord_26344).sum := by decide
  have hdescent : baseEnd_26344 < baseStart_26344 := by decide
  rcases family_descends (prefixWord ++ tailWord_26344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26383 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 1, 5]
def baseStart_26383 : Nat := 118140960795 + 26383 * 2 ^ 59
def prefixEnd_26383 : Nat := 4983230072969 + 3 ^ 40 * 26383 * 2
def baseEnd_26383 : Nat := 9031440071783673394115

theorem tailTrace_26383 : CollatzResearch.WordTrace tailWord_26383 prefixEnd_26383 9031440071783673394115 := by
  unfold tailWord_26383
  simp only [CollatzResearch.WordTrace]
  refine ⟨962267063426371702779803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 641511375617581135186535 962267063426371702779803)
  ·
    refine ⟨1443400595139557554169705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962267063426371702779803 1443400595139557554169705)
    ·
      refine ⟨1082550446354668165627279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1443400595139557554169705 1082550446354668165627279)
      ·
        refine ⟨1623825669532002248440919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082550446354668165627279 1623825669532002248440919)
        ·
          refine ⟨2435738504298003372661379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623825669532002248440919 2435738504298003372661379)
          ·
            refine ⟨3653607756447005058992069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435738504298003372661379 3653607756447005058992069)
            ·
              refine ⟨685051454333813448561013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3653607756447005058992069 685051454333813448561013)
              ·
                refine ⟨64223573843795010802595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685051454333813448561013 64223573843795010802595)
                ·
                  refine ⟨96335360765692516203893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64223573843795010802595 96335360765692516203893)
                  ·
                    refine ⟨9031440071783673394115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96335360765692516203893 9031440071783673394115)
                    ·
                      rfl

theorem cell22_26383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_26383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26383 prefixEnd_26383 := by exact prefixLift 26383
  have htrace : WordTrace (prefixWord ++ tailWord_26383) baseStart_26383 baseEnd_26383 := by
    simpa [prefixWord, tailWord_26383, baseEnd_26383] using wordTrace_append hprefix tailTrace_26383
  have hstable : (prefixWord ++ tailWord_26383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26383).length < 2 ^ (prefixWord ++ tailWord_26383).sum := by decide
  have hdescent : baseEnd_26383 < baseStart_26383 := by decide
  rcases family_descends (prefixWord ++ tailWord_26383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26400 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 6, 3]
def baseStart_26400 : Nat := 118140960795 + 26400 * 2 ^ 59
def prefixEnd_26400 : Nat := 4983230072969 + 3 ^ 40 * 26400 * 2
def baseEnd_26400 : Nat := 9037259519201295719063

theorem tailTrace_26400 : CollatzResearch.WordTrace tailWord_26400 prefixEnd_26400 9037259519201295719063 := by
  unfold tailWord_26400
  simp only [CollatzResearch.WordTrace]
  refine ⟨481443552182391803074327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 641924736243189070765769 481443552182391803074327)
  ·
    refine ⟨722165328273587704611491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481443552182391803074327 722165328273587704611491)
    ·
      refine ⟨1083247992410381556917237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722165328273587704611491 1083247992410381556917237)
      ·
        refine ⟨101554499288473270960991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1083247992410381556917237 101554499288473270960991)
        ·
          refine ⟨152331748932709906441487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101554499288473270960991 152331748932709906441487)
          ·
            refine ⟨228497623399064859662231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152331748932709906441487 228497623399064859662231)
            ·
              refine ⟨342746435098597289493347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228497623399064859662231 342746435098597289493347)
              ·
                refine ⟨514119652647895934240021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342746435098597289493347 514119652647895934240021)
                ·
                  refine ⟨24099358717870121917501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 514119652647895934240021 24099358717870121917501)
                  ·
                    refine ⟨9037259519201295719063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24099358717870121917501 9037259519201295719063)
                    ·
                      rfl

theorem cell22_26400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_26400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26400 prefixEnd_26400 := by exact prefixLift 26400
  have htrace : WordTrace (prefixWord ++ tailWord_26400) baseStart_26400 baseEnd_26400 := by
    simpa [prefixWord, tailWord_26400, baseEnd_26400] using wordTrace_append hprefix tailTrace_26400
  have hstable : (prefixWord ++ tailWord_26400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26400).length < 2 ^ (prefixWord ++ tailWord_26400).sum := by decide
  have hdescent : baseEnd_26400 < baseStart_26400 := by decide
  rcases family_descends (prefixWord ++ tailWord_26400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26419 : List Nat := [1, 1, 1, 2, 7, 1, 3, 2, 4]
def baseStart_26419 : Nat := 118140960795 + 26419 * 2 ^ 59
def prefixEnd_26419 : Nat := 4983230072969 + 3 ^ 40 * 26419 * 2
def baseEnd_26419 : Nat := 3014587869163859831335

theorem tailTrace_26419 : CollatzResearch.WordTrace tailWord_26419 prefixEnd_26419 3014587869163859831335 := by
  unfold tailWord_26419
  simp only [CollatzResearch.WordTrace]
  refine ⟨963580091295949851090311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 642386727530633234060207 963580091295949851090311)
  ·
    refine ⟨1445370136943924776635467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 963580091295949851090311 1445370136943924776635467)
    ·
      refine ⟨2168055205415887164953201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445370136943924776635467 2168055205415887164953201)
      ·
        refine ⟨1626041404061915373714901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2168055205415887164953201 1626041404061915373714901)
        ·
          refine ⟨38110345407701141571443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1626041404061915373714901 38110345407701141571443)
          ·
            refine ⟨57165518111551712357165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38110345407701141571443 57165518111551712357165)
            ·
              refine ⟨21437069291831892133937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57165518111551712357165 21437069291831892133937)
              ·
                refine ⟨16077801968873919100453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21437069291831892133937 16077801968873919100453)
                ·
                  refine ⟨3014587869163859831335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16077801968873919100453 3014587869163859831335)
                  ·
                    rfl

theorem cell22_26419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 4].length) (baseStart_26419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26419 prefixEnd_26419 := by exact prefixLift 26419
  have htrace : WordTrace (prefixWord ++ tailWord_26419) baseStart_26419 baseEnd_26419 := by
    simpa [prefixWord, tailWord_26419, baseEnd_26419] using wordTrace_append hprefix tailTrace_26419
  have hstable : (prefixWord ++ tailWord_26419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26419).length < 2 ^ (prefixWord ++ tailWord_26419).sum := by decide
  have hdescent : baseEnd_26419 < baseStart_26419 := by decide
  rcases family_descends (prefixWord ++ tailWord_26419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26430 : List Nat := [4, 2, 1, 2, 2, 1, 1, 9]
def baseStart_26430 : Nat := 118140960795 + 26430 * 2 ^ 59
def prefixEnd_26430 : Nat := 4983230072969 + 3 ^ 40 * 26430 * 2
def baseEnd_26430 : Nat := 1005281014699024163219

theorem tailTrace_26430 : CollatzResearch.WordTrace tailWord_26430 prefixEnd_26430 1005281014699024163219 := by
  unfold tailWord_26430
  simp only [CollatzResearch.WordTrace]
  refine ⟨120497661782012341217593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 642654196170732486493829 120497661782012341217593)
  ·
    refine ⟨90373246336509255913195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120497661782012341217593 90373246336509255913195)
    ·
      refine ⟨135559869504763883869793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90373246336509255913195 135559869504763883869793)
      ·
        refine ⟨101669902128572912902345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135559869504763883869793 101669902128572912902345)
        ·
          refine ⟨76252426596429684676759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101669902128572912902345 76252426596429684676759)
          ·
            refine ⟨114378639894644527015139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76252426596429684676759 114378639894644527015139)
            ·
              refine ⟨171567959841966790522709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114378639894644527015139 171567959841966790522709)
              ·
                refine ⟨1005281014699024163219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 171567959841966790522709 1005281014699024163219)
                ·
                  rfl

theorem cell22_26430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_26430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_26430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_26430 prefixEnd_26430 := by exact prefixLift 26430
  have htrace : WordTrace (prefixWord ++ tailWord_26430) baseStart_26430 baseEnd_26430 := by
    simpa [prefixWord, tailWord_26430, baseEnd_26430] using wordTrace_append hprefix tailTrace_26430
  have hstable : (prefixWord ++ tailWord_26430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26430).length < 2 ^ (prefixWord ++ tailWord_26430).sum := by decide
  have hdescent : baseEnd_26430 < baseStart_26430 := by decide
  rcases family_descends (prefixWord ++ tailWord_26430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
