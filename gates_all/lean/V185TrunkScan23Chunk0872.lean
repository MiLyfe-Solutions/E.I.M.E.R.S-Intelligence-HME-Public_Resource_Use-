import V185TrunkScan23Chunk0871

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5160534 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5160534 : Nat := 118140960795 + 5160534 * 2 ^ 59
def prefixEnd_5160534 : Nat := 4983230072969 + 3 ^ 40 * 5160534 * 2
def baseEnd_5160534 : Nat := 2649834375869417620692143

theorem tailTrace_5160534 : CollatzResearch.WordTrace tailWord_5160534 prefixEnd_5160534 2649834375869417620692143 := by
  unfold tailWord_5160534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11763758617892133867783041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125480091924182761256352437 11763758617892133867783041)
  ·
    refine ⟨8822818963419100400837281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11763758617892133867783041 8822818963419100400837281)
    ·
      refine ⟨6617114222564325300627961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8822818963419100400837281 6617114222564325300627961)
      ·
        refine ⟨4962835666923243975470971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6617114222564325300627961 4962835666923243975470971)
        ·
          refine ⟨7444253500384865963206457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4962835666923243975470971 7444253500384865963206457)
          ·
            refine ⟨5583190125288649472404843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7444253500384865963206457 5583190125288649472404843)
            ·
              refine ⟨8374785187932974208607265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583190125288649472404843 8374785187932974208607265)
              ·
                refine ⟨6281088890949730656455449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8374785187932974208607265 6281088890949730656455449)
                ·
                  refine ⟨4710816668212297992341587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6281088890949730656455449 4710816668212297992341587)
                  ·
                    refine ⟨7066225002318446988512381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4710816668212297992341587 7066225002318446988512381)
                    ·
                      refine ⟨2649834375869417620692143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7066225002318446988512381 2649834375869417620692143)
                      ·
                        rfl

theorem cell23_5160534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5160534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160534 prefixEnd_5160534 := by exact prefixLift 5160534
  have htrace : WordTrace (prefixWord ++ tailWord_5160534) baseStart_5160534 baseEnd_5160534 := by
    simpa [prefixWord, tailWord_5160534, baseEnd_5160534] using wordTrace_append hprefix tailTrace_5160534
  have hstable : (prefixWord ++ tailWord_5160534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160534).length < 2 ^ (prefixWord ++ tailWord_5160534).sum := by decide
  have hdescent : baseEnd_5160534 < baseStart_5160534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160540 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_5160540 : Nat := 118140960795 + 5160540 * 2 ^ 59
def prefixEnd_5160540 : Nat := 4983230072969 + 3 ^ 40 * 5160540 * 2
def baseEnd_5160540 : Nat := 2649837456753344597217115

theorem tailTrace_5160540 : CollatzResearch.WordTrace tailWord_5160540 prefixEnd_5160540 2649837456753344597217115 := by
  unfold tailWord_5160540
  simp only [CollatzResearch.WordTrace]
  refine ⟨94110178362126202454623537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125480237816168269939498049 94110178362126202454623537)
  ·
    refine ⟨70582633771594651840967653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94110178362126202454623537 70582633771594651840967653)
    ·
      refine ⟨13234243832173997220181435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70582633771594651840967653 13234243832173997220181435)
      ·
        refine ⟨19851365748260995830272153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13234243832173997220181435 19851365748260995830272153)
        ·
          refine ⟨14888524311195746872704115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19851365748260995830272153 14888524311195746872704115)
          ·
            refine ⟨22332786466793620309056173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14888524311195746872704115 22332786466793620309056173)
            ·
              refine ⟨8374794925047607615896065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22332786466793620309056173 8374794925047607615896065)
              ·
                refine ⟨6281096193785705711922049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8374794925047607615896065 6281096193785705711922049)
                ·
                  refine ⟨4710822145339279283941537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6281096193785705711922049 4710822145339279283941537)
                  ·
                    refine ⟨3533116609004459462956153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710822145339279283941537 3533116609004459462956153)
                    ·
                      refine ⟨2649837456753344597217115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533116609004459462956153 2649837456753344597217115)
                      ·
                        rfl

theorem cell23_5160540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_5160540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160540 prefixEnd_5160540 := by exact prefixLift 5160540
  have htrace : WordTrace (prefixWord ++ tailWord_5160540) baseStart_5160540 baseEnd_5160540 := by
    simpa [prefixWord, tailWord_5160540, baseEnd_5160540] using wordTrace_append hprefix tailTrace_5160540
  have hstable : (prefixWord ++ tailWord_5160540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160540).length < 2 ^ (prefixWord ++ tailWord_5160540).sum := by decide
  have hdescent : baseEnd_5160540 < baseStart_5160540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160557 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_5160557 : Nat := 118140960795 + 5160557 * 2 ^ 59
def prefixEnd_5160557 : Nat := 4983230072969 + 3 ^ 40 * 5160557 * 2
def baseEnd_5160557 : Nat := 2649846185924471030704537

theorem tailTrace_5160557 : CollatzResearch.WordTrace tailWord_5160557 prefixEnd_5160557 2649846185924471030704537 := by
  unfold tailWord_5160557
  simp only [CollatzResearch.WordTrace]
  refine ⟨188220976765190816812615925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125480651176793877875077283 188220976765190816812615925)
  ·
    refine ⟨17645716571736639076182743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188220976765190816812615925 17645716571736639076182743)
    ·
      refine ⟨26468574857604958614274115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17645716571736639076182743 26468574857604958614274115)
      ·
        refine ⟨39702862286407437921411173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26468574857604958614274115 39702862286407437921411173)
        ·
          refine ⟨7444286678701394610264595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39702862286407437921411173 7444286678701394610264595)
          ·
            refine ⟨11166430018052091915396893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7444286678701394610264595 11166430018052091915396893)
            ·
              refine ⟨4187411256769534468273835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11166430018052091915396893 4187411256769534468273835)
              ·
                refine ⟨6281116885154301702410753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187411256769534468273835 6281116885154301702410753)
                ·
                  refine ⟨4710837663865726276808065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6281116885154301702410753 4710837663865726276808065)
                  ·
                    refine ⟨3533128247899294707606049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4710837663865726276808065 3533128247899294707606049)
                    ·
                      refine ⟨2649846185924471030704537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533128247899294707606049 2649846185924471030704537)
                      ·
                        rfl

theorem cell23_5160557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_5160557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160557 prefixEnd_5160557 := by exact prefixLift 5160557
  have htrace : WordTrace (prefixWord ++ tailWord_5160557) baseStart_5160557 baseEnd_5160557 := by
    simpa [prefixWord, tailWord_5160557, baseEnd_5160557] using wordTrace_append hprefix tailTrace_5160557
  have hstable : (prefixWord ++ tailWord_5160557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160557).length < 2 ^ (prefixWord ++ tailWord_5160557).sum := by decide
  have hdescent : baseEnd_5160557 < baseStart_5160557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160572 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_5160572 : Nat := 118140960795 + 5160572 * 2 ^ 59
def prefixEnd_5160572 : Nat := 4983230072969 + 3 ^ 40 * 5160572 * 2
def baseEnd_5160572 : Nat := 883284629378096157338989

theorem tailTrace_5160572 : CollatzResearch.WordTrace tailWord_5160572 prefixEnd_5160572 883284629378096157338989 := by
  unfold tailWord_5160572
  simp only [CollatzResearch.WordTrace]
  refine ⟨94110761930068237187205985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125481015906757649582941313 94110761930068237187205985)
  ·
    refine ⟨70583071447551177890404489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94110761930068237187205985 70583071447551177890404489)
    ·
      refine ⟨52937303585663383417803367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70583071447551177890404489 52937303585663383417803367)
      ·
        refine ⟨79405955378495075126705051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52937303585663383417803367 79405955378495075126705051)
        ·
          refine ⟨119108933067742612690057577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79405955378495075126705051 119108933067742612690057577)
          ·
            refine ⟨89331699800806959517543183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119108933067742612690057577 89331699800806959517543183)
            ·
              refine ⟨133997549701210439276314775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89331699800806959517543183 133997549701210439276314775)
              ·
                refine ⟨200996324551815658914472163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133997549701210439276314775 200996324551815658914472163)
                ·
                  refine ⟨301494486827723488371708245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200996324551815658914472163 301494486827723488371708245)
                  ·
                    refine ⟨883284629378096157338989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 301494486827723488371708245 883284629378096157338989)
                    ·
                      rfl

theorem cell23_5160572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_5160572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160572 prefixEnd_5160572 := by exact prefixLift 5160572
  have htrace : WordTrace (prefixWord ++ tailWord_5160572) baseStart_5160572 baseEnd_5160572 := by
    simpa [prefixWord, tailWord_5160572, baseEnd_5160572] using wordTrace_append hprefix tailTrace_5160572
  have hstable : (prefixWord ++ tailWord_5160572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160572).length < 2 ^ (prefixWord ++ tailWord_5160572).sum := by decide
  have hdescent : baseEnd_5160572 < baseStart_5160572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160579 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 4]
def baseStart_5160579 : Nat := 118140960795 + 5160579 * 2 ^ 59
def prefixEnd_5160579 : Nat := 4983230072969 + 3 ^ 40 * 5160579 * 2
def baseEnd_5160579 : Nat := 2649857482498869944629435

theorem tailTrace_5160579 : CollatzResearch.WordTrace tailWord_5160579 prefixEnd_5160579 2649857482498869944629435 := by
  unfold tailWord_5160579
  simp only [CollatzResearch.WordTrace]
  refine ⟨188221779171111114569916791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125481186114074076379944527 188221779171111114569916791)
  ·
    refine ⟨282332668756666671854875187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188221779171111114569916791 282332668756666671854875187)
    ·
      refine ⟨423499003135000007782312781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282332668756666671854875187 423499003135000007782312781)
      ·
        refine ⟨158812126175625002918367293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423499003135000007782312781 158812126175625002918367293)
        ·
          refine ⟨59554547315859376094387735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158812126175625002918367293 59554547315859376094387735)
          ·
            refine ⟨89331820973789064141581603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59554547315859376094387735 89331820973789064141581603)
            ·
              refine ⟨133997731460683596212372405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89331820973789064141581603 133997731460683596212372405)
              ·
                refine ⟨12562287324439087144909913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133997731460683596212372405 12562287324439087144909913)
                ·
                  refine ⟨9421715493329315358682435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12562287324439087144909913 9421715493329315358682435)
                  ·
                    refine ⟨14132573239993973038023653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9421715493329315358682435 14132573239993973038023653)
                    ·
                      refine ⟨2649857482498869944629435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14132573239993973038023653 2649857482498869944629435)
                      ·
                        rfl

theorem cell23_5160579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_5160579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160579 prefixEnd_5160579 := by exact prefixLift 5160579
  have htrace : WordTrace (prefixWord ++ tailWord_5160579) baseStart_5160579 baseEnd_5160579 := by
    simpa [prefixWord, tailWord_5160579, baseEnd_5160579] using wordTrace_append hprefix tailTrace_5160579
  have hstable : (prefixWord ++ tailWord_5160579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160579).length < 2 ^ (prefixWord ++ tailWord_5160579).sum := by decide
  have hdescent : baseEnd_5160579 < baseStart_5160579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160580 : List Nat := [2, 3, 2, 1, 5, 1, 1, 3, 5]
def baseStart_5160580 : Nat := 118140960795 + 5160580 * 2 ^ 59
def prefixEnd_5160580 : Nat := 4983230072969 + 3 ^ 40 * 5160580 * 2
def baseEnd_5160580 : Nat := 294428666219947160079659

theorem tailTrace_5160580 : CollatzResearch.WordTrace tailWord_5160580 prefixEnd_5160580 294428666219947160079659 := by
  unfold tailWord_5160580
  simp only [CollatzResearch.WordTrace]
  refine ⟨94110907822053745870351597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125481210429404994493802129 94110907822053745870351597)
  ·
    refine ⟨35291590433270154701381849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94110907822053745870351597 35291590433270154701381849)
    ·
      refine ⟨26468692824952616026036387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35291590433270154701381849 26468692824952616026036387)
      ·
        refine ⟨39703039237428924039054581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26468692824952616026036387 39703039237428924039054581)
        ·
          refine ⟨3722159928508961628661367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39703039237428924039054581 3722159928508961628661367)
          ·
            refine ⟨5583239892763442442992051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722159928508961628661367 5583239892763442442992051)
            ·
              refine ⟨8374859839145163664488077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583239892763442442992051 8374859839145163664488077)
              ·
                refine ⟨3140572439679436374183029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8374859839145163664488077 3140572439679436374183029)
                ·
                  refine ⟨294428666219947160079659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3140572439679436374183029 294428666219947160079659)
                  ·
                    rfl

theorem cell23_5160580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_5160580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160580 prefixEnd_5160580 := by exact prefixLift 5160580
  have htrace : WordTrace (prefixWord ++ tailWord_5160580) baseStart_5160580 baseEnd_5160580 := by
    simpa [prefixWord, tailWord_5160580, baseEnd_5160580] using wordTrace_append hprefix tailTrace_5160580
  have hstable : (prefixWord ++ tailWord_5160580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160580).length < 2 ^ (prefixWord ++ tailWord_5160580).sum := by decide
  have hdescent : baseEnd_5160580 < baseStart_5160580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160592 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_5160592 : Nat := 118140960795 + 5160592 * 2 ^ 59
def prefixEnd_5160592 : Nat := 4983230072969 + 3 ^ 40 * 5160592 * 2
def baseEnd_5160592 : Nat := 2649864157747378393766875

theorem tailTrace_5160592 : CollatzResearch.WordTrace tailWord_5160592 prefixEnd_5160592 2649864157747378393766875 := by
  unfold tailWord_5160592
  simp only [CollatzResearch.WordTrace]
  refine ⟨94111126660032008895070015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125481502213376011860093353 94111126660032008895070015)
  ·
    refine ⟨141166689990048013342605023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94111126660032008895070015 141166689990048013342605023)
    ·
      refine ⟨211750034985072020013907535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141166689990048013342605023 211750034985072020013907535)
      ·
        refine ⟨317625052477608030020861303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211750034985072020013907535 317625052477608030020861303)
        ·
          refine ⟨476437578716412045031291955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317625052477608030020861303 476437578716412045031291955)
          ·
            refine ⟨714656368074618067546937933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476437578716412045031291955 714656368074618067546937933)
            ·
              refine ⟨267996138027981775330101725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 714656368074618067546937933 267996138027981775330101725)
              ·
                refine ⟨100498551760493165748788147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267996138027981775330101725 100498551760493165748788147)
                ·
                  refine ⟨150747827640739748623182221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100498551760493165748788147 150747827640739748623182221)
                  ·
                    refine ⟨56530435365277405733693333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150747827640739748623182221 56530435365277405733693333)
                    ·
                      refine ⟨2649864157747378393766875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56530435365277405733693333 2649864157747378393766875)
                      ·
                        rfl

theorem cell23_5160592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_5160592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160592 prefixEnd_5160592 := by exact prefixLift 5160592
  have htrace : WordTrace (prefixWord ++ tailWord_5160592) baseStart_5160592 baseEnd_5160592 := by
    simpa [prefixWord, tailWord_5160592, baseEnd_5160592] using wordTrace_append hprefix tailTrace_5160592
  have hstable : (prefixWord ++ tailWord_5160592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160592).length < 2 ^ (prefixWord ++ tailWord_5160592).sum := by decide
  have hdescent : baseEnd_5160592 < baseStart_5160592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160630 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5160630 : Nat := 118140960795 + 5160630 * 2 ^ 59
def prefixEnd_5160630 : Nat := 4983230072969 + 3 ^ 40 * 5160630 * 2
def baseEnd_5160630 : Nat := 2649883670012249245091701

theorem tailTrace_5160630 : CollatzResearch.WordTrace tailWord_5160630 prefixEnd_5160630 2649883670012249245091701 := by
  unfold tailWord_5160630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11763977455870396892501459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125482426195950900186682229 11763977455870396892501459)
  ·
    refine ⟨17645966183805595338752189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11763977455870396892501459 17645966183805595338752189)
    ·
      refine ⟨6617237318927098252032071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17645966183805595338752189 6617237318927098252032071)
      ·
        refine ⟨9925855978390647378048107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617237318927098252032071 9925855978390647378048107)
        ·
          refine ⟨14888783967585971067072161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9925855978390647378048107 14888783967585971067072161)
          ·
            refine ⟨11166587975689478300304121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14888783967585971067072161 11166587975689478300304121)
            ·
              refine ⟨8374940981767108725228091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11166587975689478300304121 8374940981767108725228091)
              ·
                refine ⟨12562411472650663087842137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8374940981767108725228091 12562411472650663087842137)
                ·
                  refine ⟨9421808604487997315881603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12562411472650663087842137 9421808604487997315881603)
                  ·
                    refine ⟨14132712906731995973822405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9421808604487997315881603 14132712906731995973822405)
                    ·
                      refine ⟨2649883670012249245091701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14132712906731995973822405 2649883670012249245091701)
                      ·
                        rfl

theorem cell23_5160630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5160630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160630 prefixEnd_5160630 := by exact prefixLift 5160630
  have htrace : WordTrace (prefixWord ++ tailWord_5160630) baseStart_5160630 baseEnd_5160630 := by
    simpa [prefixWord, tailWord_5160630, baseEnd_5160630] using wordTrace_append hprefix tailTrace_5160630
  have hstable : (prefixWord ++ tailWord_5160630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160630).length < 2 ^ (prefixWord ++ tailWord_5160630).sum := by decide
  have hdescent : baseEnd_5160630 < baseStart_5160630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160653 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 6]
def baseStart_5160653 : Nat := 118140960795 + 5160653 * 2 ^ 59
def prefixEnd_5160653 : Nat := 4983230072969 + 3 ^ 40 * 5160653 * 2
def baseEnd_5160653 : Nat := 294432831118589183900455

theorem tailTrace_5160653 : CollatzResearch.WordTrace tailWord_5160653 prefixEnd_5160653 294432831118589183900455 := by
  unfold tailWord_5160653
  simp only [CollatzResearch.WordTrace]
  refine ⟨188224478172843025208110613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125482985448562016805407075 188224478172843025208110613)
  ·
    refine ⟨8823022414352016806630185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 188224478172843025208110613 8823022414352016806630185)
    ·
      refine ⟨6617266810764012604972639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8823022414352016806630185 6617266810764012604972639)
      ·
        refine ⟨9925900216146018907458959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617266810764012604972639 9925900216146018907458959)
        ·
          refine ⟨14888850324219028361188439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9925900216146018907458959 14888850324219028361188439)
          ·
            refine ⟨22333275486328542541782659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14888850324219028361188439 22333275486328542541782659)
            ·
              refine ⟨33499913229492813812673989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22333275486328542541782659 33499913229492813812673989)
              ·
                refine ⟨6281233730529902589876373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33499913229492813812673989 6281233730529902589876373)
                ·
                  refine ⟨294432831118589183900455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6281233730529902589876373 294432831118589183900455)
                  ·
                    rfl

theorem cell23_5160653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_5160653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160653 prefixEnd_5160653 := by exact prefixLift 5160653
  have htrace : WordTrace (prefixWord ++ tailWord_5160653) baseStart_5160653 baseEnd_5160653 := by
    simpa [prefixWord, tailWord_5160653, baseEnd_5160653] using wordTrace_append hprefix tailTrace_5160653
  have hstable : (prefixWord ++ tailWord_5160653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160653).length < 2 ^ (prefixWord ++ tailWord_5160653).sum := by decide
  have hdescent : baseEnd_5160653 < baseStart_5160653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160656 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 4, 3, 2]
def baseStart_5160656 : Nat := 118140960795 + 5160656 * 2 ^ 59
def prefixEnd_5160656 : Nat := 4983230072969 + 3 ^ 40 * 5160656 * 2
def baseEnd_5160656 : Nat := 2649897020509266143366581

theorem tailTrace_5160656 : CollatzResearch.WordTrace tailWord_5160656 prefixEnd_5160656 2649897020509266143366581 := by
  unfold tailWord_5160656
  simp only [CollatzResearch.WordTrace]
  refine ⟨94112293795916078360234911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125483058394554771146979881 94112293795916078360234911)
  ·
    refine ⟨141168440693874117540352367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94112293795916078360234911 141168440693874117540352367)
    ·
      refine ⟨211752661040811176310528551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141168440693874117540352367 211752661040811176310528551)
      ·
        refine ⟨317628991561216764465792827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211752661040811176310528551 317628991561216764465792827)
        ·
          refine ⟨476443487341825146698689241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317628991561216764465792827 476443487341825146698689241)
          ·
            refine ⟨357332615506368860024016931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476443487341825146698689241 357332615506368860024016931)
            ·
              refine ⟨535998923259553290036025397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357332615506368860024016931 535998923259553290036025397)
              ·
                refine ⟨50249899055583120940877381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 535998923259553290036025397 50249899055583120940877381)
                ·
                  refine ⟨9421856072921835176414509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50249899055583120940877381 9421856072921835176414509)
                  ·
                    refine ⟨3533196027345688191155441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9421856072921835176414509 3533196027345688191155441)
                    ·
                      refine ⟨2649897020509266143366581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533196027345688191155441 2649897020509266143366581)
                      ·
                        rfl

theorem cell23_5160656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 3, 2].length) (baseStart_5160656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160656 prefixEnd_5160656 := by exact prefixLift 5160656
  have htrace : WordTrace (prefixWord ++ tailWord_5160656) baseStart_5160656 baseEnd_5160656 := by
    simpa [prefixWord, tailWord_5160656, baseEnd_5160656] using wordTrace_append hprefix tailTrace_5160656
  have hstable : (prefixWord ++ tailWord_5160656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160656).length < 2 ^ (prefixWord ++ tailWord_5160656).sum := by decide
  have hdescent : baseEnd_5160656 < baseStart_5160656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160686 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_5160686 : Nat := 118140960795 + 5160686 * 2 ^ 59
def prefixEnd_5160686 : Nat := 4983230072969 + 3 ^ 40 * 5160686 * 2
def baseEnd_5160686 : Nat := 2649912424928901025991443

theorem tailTrace_5160686 : CollatzResearch.WordTrace tailWord_5160686 prefixEnd_5160686 2649912424928901025991443 := by
  unfold tailWord_5160686
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528210222715433980507739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125483787854482314562707941 23528210222715433980507739)
  ·
    refine ⟨35292315334073150970761609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23528210222715433980507739 35292315334073150970761609)
    ·
      refine ⟨26469236500554863228071207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35292315334073150970761609 26469236500554863228071207)
      ·
        refine ⟨39703854750832294842106811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26469236500554863228071207 39703854750832294842106811)
        ·
          refine ⟨59555782126248442263160217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39703854750832294842106811 59555782126248442263160217)
          ·
            refine ⟨44666836594686331697370163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59555782126248442263160217 44666836594686331697370163)
            ·
              refine ⟨67000254892029497546055245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44666836594686331697370163 67000254892029497546055245)
              ·
                refine ⟨25125095584511061579770717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67000254892029497546055245 25125095584511061579770717)
                ·
                  refine ⟨9421910844191648092414019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25125095584511061579770717 9421910844191648092414019)
                  ·
                    refine ⟨14132866266287472138621029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9421910844191648092414019 14132866266287472138621029)
                    ·
                      refine ⟨2649912424928901025991443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14132866266287472138621029 2649912424928901025991443)
                      ·
                        rfl

theorem cell23_5160686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_5160686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160686 prefixEnd_5160686 := by exact prefixLift 5160686
  have htrace : WordTrace (prefixWord ++ tailWord_5160686) baseStart_5160686 baseEnd_5160686 := by
    simpa [prefixWord, tailWord_5160686, baseEnd_5160686] using wordTrace_append hprefix tailTrace_5160686
  have hstable : (prefixWord ++ tailWord_5160686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160686).length < 2 ^ (prefixWord ++ tailWord_5160686).sum := by decide
  have hdescent : baseEnd_5160686 < baseStart_5160686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160699 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4]
def baseStart_5160699 : Nat := 118140960795 + 5160699 * 2 ^ 59
def prefixEnd_5160699 : Nat := 4983230072969 + 3 ^ 40 * 5160699 * 2
def baseEnd_5160699 : Nat := 2649919100177409475128883

theorem tailTrace_5160699 : CollatzResearch.WordTrace tailWord_5160699 prefixEnd_5160699 2649919100177409475128883 := by
  unfold tailWord_5160699
  simp only [CollatzResearch.WordTrace]
  refine ⟨188226155930676375064285151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125484103953784250042856767 188226155930676375064285151)
  ·
    refine ⟨282339233896014562596427727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188226155930676375064285151 282339233896014562596427727)
    ·
      refine ⟨423508850844021843894641591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282339233896014562596427727 423508850844021843894641591)
      ·
        refine ⟨635263276266032765841962387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423508850844021843894641591 635263276266032765841962387)
        ·
          refine ⟨952894914399049148762943581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635263276266032765841962387 952894914399049148762943581)
          ·
            refine ⟨357335592899643430786103843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 952894914399049148762943581 357335592899643430786103843)
            ·
              refine ⟨536003389349465146179155765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357335592899643430786103843 536003389349465146179155765)
              ·
                refine ⟨50250317751512357454295853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 536003389349465146179155765 50250317751512357454295853)
                ·
                  refine ⟨18843869156817134045360945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50250317751512357454295853 18843869156817134045360945)
                  ·
                    refine ⟨14132901867612850534020709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18843869156817134045360945 14132901867612850534020709)
                    ·
                      refine ⟨2649919100177409475128883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14132901867612850534020709 2649919100177409475128883)
                      ·
                        rfl

theorem cell23_5160699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_5160699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160699 prefixEnd_5160699 := by exact prefixLift 5160699
  have htrace : WordTrace (prefixWord ++ tailWord_5160699) baseStart_5160699 baseEnd_5160699 := by
    simpa [prefixWord, tailWord_5160699, baseEnd_5160699] using wordTrace_append hprefix tailTrace_5160699
  have hstable : (prefixWord ++ tailWord_5160699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160699).length < 2 ^ (prefixWord ++ tailWord_5160699).sum := by decide
  have hdescent : baseEnd_5160699 < baseStart_5160699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160703 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 1, 1, 4]
def baseStart_5160703 : Nat := 118140960795 + 5160703 * 2 ^ 59
def prefixEnd_5160703 : Nat := 4983230072969 + 3 ^ 40 * 5160703 * 2
def baseEnd_5160703 : Nat := 2649921154100027459478865

theorem tailTrace_5160703 : CollatzResearch.WordTrace tailWord_5160703 prefixEnd_5160703 2649921154100027459478865 := by
  unfold tailWord_5160703
  simp only [CollatzResearch.WordTrace]
  refine ⟨188226301822661883747430763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125484201215107922498287175 188226301822661883747430763)
  ·
    refine ⟨282339452733992825621146145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188226301822661883747430763 282339452733992825621146145)
    ·
      refine ⟨211754589550494619215859609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282339452733992825621146145 211754589550494619215859609)
      ·
        refine ⟨158815942162870964411894707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211754589550494619215859609 158815942162870964411894707)
        ·
          refine ⟨238223913244306446617842061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158815942162870964411894707 238223913244306446617842061)
          ·
            refine ⟨89333967466614917481690773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238223913244306446617842061 89333967466614917481690773)
            ·
              refine ⟨4187529724997574256954255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89333967466614917481690773 4187529724997574256954255)
              ·
                refine ⟨6281294587496361385431383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187529724997574256954255 6281294587496361385431383)
                ·
                  refine ⟨9421941881244542078147075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281294587496361385431383 9421941881244542078147075)
                  ·
                    refine ⟨14132912821866813117220613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9421941881244542078147075 14132912821866813117220613)
                    ·
                      refine ⟨2649921154100027459478865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14132912821866813117220613 2649921154100027459478865)
                      ·
                        rfl

theorem cell23_5160703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_5160703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160703 prefixEnd_5160703 := by exact prefixLift 5160703
  have htrace : WordTrace (prefixWord ++ tailWord_5160703) baseStart_5160703 baseEnd_5160703 := by
    simpa [prefixWord, tailWord_5160703, baseEnd_5160703] using wordTrace_append hprefix tailTrace_5160703
  have hstable : (prefixWord ++ tailWord_5160703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160703).length < 2 ^ (prefixWord ++ tailWord_5160703).sum := by decide
  have hdescent : baseEnd_5160703 < baseStart_5160703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160730 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_5160730 : Nat := 118140960795 + 5160730 * 2 ^ 59
def prefixEnd_5160730 : Nat := 4983230072969 + 3 ^ 40 * 5160730 * 2
def baseEnd_5160730 : Nat := 883311672692566284613747

theorem tailTrace_5160730 : CollatzResearch.WordTrace tailWord_5160730 prefixEnd_5160730 883311672692566284613747 := by
  unfold tailWord_5160730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47056821648391016839665911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125484857729042711572442429 47056821648391016839665911)
  ·
    refine ⟨70585232472586525259498867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47056821648391016839665911 70585232472586525259498867)
    ·
      refine ⟨105877848708879787889248301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70585232472586525259498867 105877848708879787889248301)
      ·
        refine ⟨39704193265829920458468113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105877848708879787889248301 39704193265829920458468113)
        ·
          refine ⟨29778144949372440343851085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39704193265829920458468113 29778144949372440343851085)
          ·
            refine ⟨11166804356014665128944157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29778144949372440343851085 11166804356014665128944157)
            ·
              refine ⟨4187551633505499423354059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11166804356014665128944157 4187551633505499423354059)
              ·
                refine ⟨6281327450258249135031089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187551633505499423354059 6281327450258249135031089)
                ·
                  refine ⟨4710995587693686851273317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6281327450258249135031089 4710995587693686851273317)
                  ·
                    refine ⟨883311672692566284613747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4710995587693686851273317 883311672692566284613747)
                    ·
                      rfl

theorem cell23_5160730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_5160730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160730 prefixEnd_5160730 := by exact prefixLift 5160730
  have htrace : WordTrace (prefixWord ++ tailWord_5160730) baseStart_5160730 baseEnd_5160730 := by
    simpa [prefixWord, tailWord_5160730, baseEnd_5160730] using wordTrace_append hprefix tailTrace_5160730
  have hstable : (prefixWord ++ tailWord_5160730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160730).length < 2 ^ (prefixWord ++ tailWord_5160730).sum := by decide
  have hdescent : baseEnd_5160730 < baseStart_5160730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160739 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 2, 7]
def baseStart_5160739 : Nat := 118140960795 + 5160739 * 2 ^ 59
def prefixEnd_5160739 : Nat := 4983230072969 + 3 ^ 40 * 5160739 * 2
def baseEnd_5160739 : Nat := 883313213134529772876233

theorem tailTrace_5160739 : CollatzResearch.WordTrace tailWord_5160739 prefixEnd_5160739 883313213134529772876233 := by
  unfold tailWord_5160739
  simp only [CollatzResearch.WordTrace]
  refine ⟨188227614850531461895741271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125485076567020974597160847 188227614850531461895741271)
  ·
    refine ⟨282341422275797192843611907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188227614850531461895741271 282341422275797192843611907)
    ·
      refine ⟨423512133413695789265417861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282341422275797192843611907 423512133413695789265417861)
      ·
        refine ⟨79408525015067960487265849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423512133413695789265417861 79408525015067960487265849)
        ·
          refine ⟨59556393761300970365449387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79408525015067960487265849 59556393761300970365449387)
          ·
            refine ⟨89334590641951455548174081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59556393761300970365449387 89334590641951455548174081)
            ·
              refine ⟨67000942981463591661130561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89334590641951455548174081 67000942981463591661130561)
              ·
                refine ⟨50250707236097693745847921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67000942981463591661130561 50250707236097693745847921)
                ·
                  refine ⟨37688030427073270309385941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50250707236097693745847921 37688030427073270309385941)
                  ·
                    refine ⟨883313213134529772876233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37688030427073270309385941 883313213134529772876233)
                    ·
                      rfl

theorem cell23_5160739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 7].length) (baseStart_5160739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160739 prefixEnd_5160739 := by exact prefixLift 5160739
  have htrace : WordTrace (prefixWord ++ tailWord_5160739) baseStart_5160739 baseEnd_5160739 := by
    simpa [prefixWord, tailWord_5160739, baseEnd_5160739] using wordTrace_append hprefix tailTrace_5160739
  have hstable : (prefixWord ++ tailWord_5160739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160739).length < 2 ^ (prefixWord ++ tailWord_5160739).sum := by decide
  have hdescent : baseEnd_5160739 < baseStart_5160739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160740 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_5160740 : Nat := 118140960795 + 5160740 * 2 ^ 59
def prefixEnd_5160740 : Nat := 4983230072969 + 3 ^ 40 * 5160740 * 2
def baseEnd_5160740 : Nat := 2649940152884243814716195

theorem tailTrace_5160740 : CollatzResearch.WordTrace tailWord_5160740 prefixEnd_5160740 2649940152884243814716195 := by
  unfold tailWord_5160740
  simp only [CollatzResearch.WordTrace]
  refine ⟨94113825661763919533263837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125485100882351892711018449 94113825661763919533263837)
  ·
    refine ⟨35292684623161469824973939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94113825661763919533263837 35292684623161469824973939)
    ·
      refine ⟨52939026934742204737460909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35292684623161469824973939 52939026934742204737460909)
      ·
        refine ⟨19852135100528326776547841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52939026934742204737460909 19852135100528326776547841)
        ·
          refine ⟨14889101325396245082410881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19852135100528326776547841 14889101325396245082410881)
          ·
            refine ⟨11166825994047183811808161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14889101325396245082410881 11166825994047183811808161)
            ·
              refine ⟨8375119495535387858856121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11166825994047183811808161 8375119495535387858856121)
              ·
                refine ⟨6281339621651540894142091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8375119495535387858856121 6281339621651540894142091)
                ·
                  refine ⟨9422009432477311341213137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281339621651540894142091 9422009432477311341213137)
                  ·
                    refine ⟨7066507074357983505909853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9422009432477311341213137 7066507074357983505909853)
                    ·
                      refine ⟨2649940152884243814716195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7066507074357983505909853 2649940152884243814716195)
                      ·
                        rfl

theorem cell23_5160740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_5160740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160740 prefixEnd_5160740 := by exact prefixLift 5160740
  have htrace : WordTrace (prefixWord ++ tailWord_5160740) baseStart_5160740 baseEnd_5160740 := by
    simpa [prefixWord, tailWord_5160740, baseEnd_5160740] using wordTrace_append hprefix tailTrace_5160740
  have hstable : (prefixWord ++ tailWord_5160740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160740).length < 2 ^ (prefixWord ++ tailWord_5160740).sum := by decide
  have hdescent : baseEnd_5160740 < baseStart_5160740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160753 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_5160753 : Nat := 118140960795 + 5160753 * 2 ^ 59
def prefixEnd_5160753 : Nat := 4983230072969 + 3 ^ 40 * 5160753 * 2
def baseEnd_5160753 : Nat := 2649946828132752263853635

theorem tailTrace_5160753 : CollatzResearch.WordTrace tailWord_5160753 prefixEnd_5160753 2649946828132752263853635 := by
  unfold tailWord_5160753
  simp only [CollatzResearch.WordTrace]
  refine ⟨188228125472480742286750913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125485416981653828191167275 188228125472480742286750913)
  ·
    refine ⟨141171094104360556715063185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188228125472480742286750913 141171094104360556715063185)
    ·
      refine ⟨105878320578270417536297389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141171094104360556715063185 105878320578270417536297389)
      ·
        refine ⟨39704370216851406576111521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105878320578270417536297389 39704370216851406576111521)
        ·
          refine ⟨29778277662638554932083641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39704370216851406576111521 29778277662638554932083641)
          ·
            refine ⟨22333708246978916199062731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29778277662638554932083641 22333708246978916199062731)
            ·
              refine ⟨33500562370468374298594097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22333708246978916199062731 33500562370468374298594097)
              ·
                refine ⟨25125421777851280723945573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33500562370468374298594097 25125421777851280723945573)
                ·
                  refine ⟨4711016583347115135739795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25125421777851280723945573 4711016583347115135739795)
                  ·
                    refine ⟨7066524875020672703609693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4711016583347115135739795 7066524875020672703609693)
                    ·
                      refine ⟨2649946828132752263853635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7066524875020672703609693 2649946828132752263853635)
                      ·
                        rfl

theorem cell23_5160753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_5160753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160753 prefixEnd_5160753 := by exact prefixLift 5160753
  have htrace : WordTrace (prefixWord ++ tailWord_5160753) baseStart_5160753 baseEnd_5160753 := by
    simpa [prefixWord, tailWord_5160753, baseEnd_5160753] using wordTrace_append hprefix tailTrace_5160753
  have hstable : (prefixWord ++ tailWord_5160753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160753).length < 2 ^ (prefixWord ++ tailWord_5160753).sum := by decide
  have hdescent : baseEnd_5160753 < baseStart_5160753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160754 : List Nat := [3, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_5160754 : Nat := 118140960795 + 5160754 * 2 ^ 59
def prefixEnd_5160754 : Nat := 4983230072969 + 3 ^ 40 * 5160754 * 2
def baseEnd_5160754 : Nat := 2649947341613406759941131

theorem tailTrace_5160754 : CollatzResearch.WordTrace tailWord_5160754 prefixEnd_5160754 2649947341613406759941131 := by
  unfold tailWord_5160754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47057040486369279864384329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125485441296984746305024877 47057040486369279864384329)
  ·
    refine ⟨35292780364776959898288247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47057040486369279864384329 35292780364776959898288247)
    ·
      refine ⟨52939170547165439847432371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35292780364776959898288247 52939170547165439847432371)
      ·
        refine ⟨79408755820748159771148557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52939170547165439847432371 79408755820748159771148557)
        ·
          refine ⟨29778283432780559914180709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79408755820748159771148557 29778283432780559914180709)
          ·
            refine ⟨5583428143646354983908883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29778283432780559914180709 5583428143646354983908883)
            ·
              refine ⟨8375142215469532475863325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5583428143646354983908883 8375142215469532475863325)
              ·
                refine ⟨3140678330801074678448747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8375142215469532475863325 3140678330801074678448747)
                ·
                  refine ⟨4711017496201612017673121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140678330801074678448747 4711017496201612017673121)
                  ·
                    refine ⟨3533263122151209013254841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4711017496201612017673121 3533263122151209013254841)
                    ·
                      refine ⟨2649947341613406759941131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533263122151209013254841 2649947341613406759941131)
                      ·
                        rfl

theorem cell23_5160754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_5160754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160754 prefixEnd_5160754 := by exact prefixLift 5160754
  have htrace : WordTrace (prefixWord ++ tailWord_5160754) baseStart_5160754 baseEnd_5160754 := by
    simpa [prefixWord, tailWord_5160754, baseEnd_5160754] using wordTrace_append hprefix tailTrace_5160754
  have hstable : (prefixWord ++ tailWord_5160754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160754).length < 2 ^ (prefixWord ++ tailWord_5160754).sum := by decide
  have hdescent : baseEnd_5160754 < baseStart_5160754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160793 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 1, 4, 2]
def baseStart_5160793 : Nat := 118140960795 + 5160793 * 2 ^ 59
def prefixEnd_5160793 : Nat := 4983230072969 + 3 ^ 40 * 5160793 * 2
def baseEnd_5160793 : Nat := 2649967367358932107353451

theorem tailTrace_5160793 : CollatzResearch.WordTrace tailWord_5160793 prefixEnd_5160793 2649967367358932107353451 := by
  unfold tailWord_5160793
  simp only [CollatzResearch.WordTrace]
  refine ⟨188229584392335829118207033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125486389594890552745471355 188229584392335829118207033)
  ·
    refine ⟨141172188294251871838655275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188229584392335829118207033 141172188294251871838655275)
    ·
      refine ⟨211758282441377807757982913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141172188294251871838655275 211758282441377807757982913)
      ·
        refine ⟨158818711831033355818487185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211758282441377807757982913 158818711831033355818487185)
        ·
          refine ⟨119114033873275016863865389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158818711831033355818487185 119114033873275016863865389)
          ·
            refine ⟨44667762702478131323949521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119114033873275016863865389 44667762702478131323949521)
            ·
              refine ⟨33500822026858598492962141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44667762702478131323949521 33500822026858598492962141)
              ·
                refine ⟨12562808260071974434860803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33500822026858598492962141 12562808260071974434860803)
                ·
                  refine ⟨18844212390107961652291205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12562808260071974434860803 18844212390107961652291205)
                  ·
                    refine ⟨3533289823145242809804601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18844212390107961652291205 3533289823145242809804601)
                    ·
                      refine ⟨2649967367358932107353451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533289823145242809804601 2649967367358932107353451)
                      ·
                        rfl

theorem cell23_5160793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_5160793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160793 prefixEnd_5160793 := by exact prefixLift 5160793
  have htrace : WordTrace (prefixWord ++ tailWord_5160793) baseStart_5160793 baseEnd_5160793 := by
    simpa [prefixWord, tailWord_5160793, baseEnd_5160793] using wordTrace_append hprefix tailTrace_5160793
  have hstable : (prefixWord ++ tailWord_5160793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160793).length < 2 ^ (prefixWord ++ tailWord_5160793).sum := by decide
  have hdescent : baseEnd_5160793 < baseStart_5160793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160814 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_5160814 : Nat := 118140960795 + 5160814 * 2 ^ 59
def prefixEnd_5160814 : Nat := 4983230072969 + 3 ^ 40 * 5160814 * 2
def baseEnd_5160814 : Nat := 2649978150452676525190855

theorem tailTrace_5160814 : CollatzResearch.WordTrace tailWord_5160814 prefixEnd_5160814 2649978150452676525190855 := by
  unfold tailWord_5160814
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528793790657468713090187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125486900216839833136480997 23528793790657468713090187)
  ·
    refine ⟨35293190685986203069635281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23528793790657468713090187 35293190685986203069635281)
    ·
      refine ⟨26469893014489652302226461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35293190685986203069635281 26469893014489652302226461)
      ·
        refine ⟨9926209880433619613334923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26469893014489652302226461 9926209880433619613334923)
        ·
          refine ⟨14889314820650429420002385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9926209880433619613334923 14889314820650429420002385)
          ·
            refine ⟨11166986115487822065001789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14889314820650429420002385 11166986115487822065001789)
            ·
              refine ⟨4187619793307933274375671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11166986115487822065001789 4187619793307933274375671)
              ·
                refine ⟨6281429689961899911563507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187619793307933274375671 6281429689961899911563507)
                ·
                  refine ⟨9422144534942849867345261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281429689961899911563507 9422144534942849867345261)
                  ·
                    refine ⟨3533304200603568700254473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9422144534942849867345261 3533304200603568700254473)
                    ·
                      refine ⟨2649978150452676525190855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533304200603568700254473 2649978150452676525190855)
                      ·
                        rfl

theorem cell23_5160814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_5160814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160814 prefixEnd_5160814 := by exact prefixLift 5160814
  have htrace : WordTrace (prefixWord ++ tailWord_5160814) baseStart_5160814 baseEnd_5160814 := by
    simpa [prefixWord, tailWord_5160814, baseEnd_5160814] using wordTrace_append hprefix tailTrace_5160814
  have hstable : (prefixWord ++ tailWord_5160814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160814).length < 2 ^ (prefixWord ++ tailWord_5160814).sum := by decide
  have hdescent : baseEnd_5160814 < baseStart_5160814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160830 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5160830 : Nat := 118140960795 + 5160830 * 2 ^ 59
def prefixEnd_5160830 : Nat := 4983230072969 + 3 ^ 40 * 5160830 * 2
def baseEnd_5160830 : Nat := 2649986366143148462590781

theorem tailTrace_5160830 : CollatzResearch.WordTrace tailWord_5160830 prefixEnd_5160830 2649986366143148462590781 := by
  unfold tailWord_5160830
  simp only [CollatzResearch.WordTrace]
  refine ⟨23528866736650223054662993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125487289262134522958202629 23528866736650223054662993)
  ·
    refine ⟨17646650052487667290997245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23528866736650223054662993 17646650052487667290997245)
    ·
      refine ⟨6617493769682875234123967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17646650052487667290997245 6617493769682875234123967)
      ·
        refine ⟨9926240654524312851185951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617493769682875234123967 9926240654524312851185951)
        ·
          refine ⟨14889360981786469276778927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9926240654524312851185951 14889360981786469276778927)
          ·
            refine ⟨22334041472679703915168391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14889360981786469276778927 22334041472679703915168391)
            ·
              refine ⟨33501062209019555872752587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22334041472679703915168391 33501062209019555872752587)
              ·
                refine ⟨50251593313529333809128881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33501062209019555872752587 50251593313529333809128881)
                ·
                  refine ⟨37688694985147000356846661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50251593313529333809128881 37688694985147000356846661)
                  ·
                    refine ⟨7066630309715062566908749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37688694985147000356846661 7066630309715062566908749)
                    ·
                      refine ⟨2649986366143148462590781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7066630309715062566908749 2649986366143148462590781)
                      ·
                        rfl

theorem cell23_5160830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5160830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160830 prefixEnd_5160830 := by exact prefixLift 5160830
  have htrace : WordTrace (prefixWord ++ tailWord_5160830) baseStart_5160830 baseEnd_5160830 := by
    simpa [prefixWord, tailWord_5160830, baseEnd_5160830] using wordTrace_append hprefix tailTrace_5160830
  have hstable : (prefixWord ++ tailWord_5160830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160830).length < 2 ^ (prefixWord ++ tailWord_5160830).sum := by decide
  have hdescent : baseEnd_5160830 < baseStart_5160830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160853 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_5160853 : Nat := 118140960795 + 5160853 * 2 ^ 59
def prefixEnd_5160853 : Nat := 4983230072969 + 3 ^ 40 * 5160853 * 2
def baseEnd_5160853 : Nat := 2649998176198201872603175

theorem tailTrace_5160853 : CollatzResearch.WordTrace tailWord_5160853 prefixEnd_5160853 2649998176198201872603175 := by
  unfold tailWord_5160853
  simp only [CollatzResearch.WordTrace]
  refine ⟨188231772772118459365391213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125487848514745639576927475 188231772772118459365391213)
  ·
    refine ⟨70586914789544422262021705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188231772772118459365391213 70586914789544422262021705)
    ·
      refine ⟨52940186092158316696516279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70586914789544422262021705 52940186092158316696516279)
      ·
        refine ⟨79410279138237475044774419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52940186092158316696516279 79410279138237475044774419)
        ·
          refine ⟨119115418707356212567161629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79410279138237475044774419 119115418707356212567161629)
          ·
            refine ⟨44668282015258579712685611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119115418707356212567161629 44668282015258579712685611)
            ·
              refine ⟨67002423022887869569028417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44668282015258579712685611 67002423022887869569028417)
              ·
                refine ⟨50251817267165902176771313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67002423022887869569028417 50251817267165902176771313)
                ·
                  refine ⟨37688862950374426632578485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50251817267165902176771313 37688862950374426632578485)
                  ·
                    refine ⟨3533330901597602496804233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37688862950374426632578485 3533330901597602496804233)
                    ·
                      refine ⟨2649998176198201872603175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533330901597602496804233 2649998176198201872603175)
                      ·
                        rfl

theorem cell23_5160853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_5160853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160853 prefixEnd_5160853 := by exact prefixLift 5160853
  have htrace : WordTrace (prefixWord ++ tailWord_5160853) baseStart_5160853 baseEnd_5160853 := by
    simpa [prefixWord, tailWord_5160853, baseEnd_5160853] using wordTrace_append hprefix tailTrace_5160853
  have hstable : (prefixWord ++ tailWord_5160853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160853).length < 2 ^ (prefixWord ++ tailWord_5160853).sum := by decide
  have hdescent : baseEnd_5160853 < baseStart_5160853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160863 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 1, 7]
def baseStart_5160863 : Nat := 118140960795 + 5160863 * 2 ^ 59
def prefixEnd_5160863 : Nat := 4983230072969 + 3 ^ 40 * 5160863 * 2
def baseEnd_5160863 : Nat := 883334437001582277826043

theorem tailTrace_5160863 : CollatzResearch.WordTrace tailWord_5160863 prefixEnd_5160863 883334437001582277826043 := by
  unfold tailWord_5160863
  simp only [CollatzResearch.WordTrace]
  refine ⟨188232137502082231073255243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125488091668054820715503495 188232137502082231073255243)
  ·
    refine ⟨282348206253123346609882865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188232137502082231073255243 282348206253123346609882865)
    ·
      refine ⟨211761154689842509957412149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282348206253123346609882865 211761154689842509957412149)
      ·
        refine ⟨19852608252172735308507389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211761154689842509957412149 19852608252172735308507389)
        ·
          refine ⟨7444728094564775740690271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19852608252172735308507389 7444728094564775740690271)
          ·
            refine ⟨11167092141847163611035407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7444728094564775740690271 11167092141847163611035407)
            ·
              refine ⟨16750638212770745416553111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11167092141847163611035407 16750638212770745416553111)
              ·
                refine ⟨25125957319156118124829667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16750638212770745416553111 25125957319156118124829667)
                ·
                  refine ⟨37688935978734177187244501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25125957319156118124829667 37688935978734177187244501)
                  ·
                    refine ⟨883334437001582277826043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37688935978734177187244501 883334437001582277826043)
                    ·
                      rfl

theorem cell23_5160863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_5160863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160863 prefixEnd_5160863 := by exact prefixLift 5160863
  have htrace : WordTrace (prefixWord ++ tailWord_5160863) baseStart_5160863 baseEnd_5160863 := by
    simpa [prefixWord, tailWord_5160863, baseEnd_5160863] using wordTrace_append hprefix tailTrace_5160863
  have hstable : (prefixWord ++ tailWord_5160863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160863).length < 2 ^ (prefixWord ++ tailWord_5160863).sum := by decide
  have hdescent : baseEnd_5160863 < baseStart_5160863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160883 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 4, 4, 2]
def baseStart_5160883 : Nat := 118140960795 + 5160883 * 2 ^ 59
def prefixEnd_5160883 : Nat := 4983230072969 + 3 ^ 40 * 5160883 * 2
def baseEnd_5160883 : Nat := 2650013580617836755228037

theorem tailTrace_5160883 : CollatzResearch.WordTrace tailWord_5160883 prefixEnd_5160883 2650013580617836755228037 := by
  unfold tailWord_5160883
  simp only [CollatzResearch.WordTrace]
  refine ⟨188232866962009774488983303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125488577974673182992655535 188232866962009774488983303)
  ·
    refine ⟨282349300443014661733474955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188232866962009774488983303 282349300443014661733474955)
    ·
      refine ⟨423523950664521992600212433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282349300443014661733474955 423523950664521992600212433)
      ·
        refine ⟨317642962998391494450159325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423523950664521992600212433 317642962998391494450159325)
        ·
          refine ⟨119116111124396810418809747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317642962998391494450159325 119116111124396810418809747)
          ·
            refine ⟨178674166686595215628214621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119116111124396810418809747 178674166686595215628214621)
            ·
              refine ⟨67002812507473205860580483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178674166686595215628214621 67002812507473205860580483)
              ·
                refine ⟨100504218761209808790870725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67002812507473205860580483 100504218761209808790870725)
                ·
                  refine ⟨18844541017726839148288261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100504218761209808790870725 18844541017726839148288261)
                  ·
                    refine ⟨3533351440823782340304049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18844541017726839148288261 3533351440823782340304049)
                    ·
                      refine ⟨2650013580617836755228037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533351440823782340304049 2650013580617836755228037)
                      ·
                        rfl

theorem cell23_5160883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4, 2].length) (baseStart_5160883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160883 prefixEnd_5160883 := by exact prefixLift 5160883
  have htrace : WordTrace (prefixWord ++ tailWord_5160883) baseStart_5160883 baseEnd_5160883 := by
    simpa [prefixWord, tailWord_5160883, baseEnd_5160883] using wordTrace_append hprefix tailTrace_5160883
  have hstable : (prefixWord ++ tailWord_5160883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160883).length < 2 ^ (prefixWord ++ tailWord_5160883).sum := by decide
  have hdescent : baseEnd_5160883 < baseStart_5160883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160896 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_5160896 : Nat := 118140960795 + 5160896 * 2 ^ 59
def prefixEnd_5160896 : Nat := 4983230072969 + 3 ^ 40 * 5160896 * 2
def baseEnd_5160896 : Nat := 2650020255866345204365477

theorem tailTrace_5160896 : CollatzResearch.WordTrace tailWord_5160896 prefixEnd_5160896 2650020255866345204365477 := by
  unfold tailWord_5160896
  simp only [CollatzResearch.WordTrace]
  refine ⟨94116670555481338854603271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125488894073975118472804361 94116670555481338854603271)
  ·
    refine ⟨141175005833222008281904907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94116670555481338854603271 141175005833222008281904907)
    ·
      refine ⟨211762508749833012422857361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141175005833222008281904907 211762508749833012422857361)
      ·
        refine ⟨158821881562374759317143021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211762508749833012422857361 158821881562374759317143021)
        ·
          refine ⟨59558205585890534743928633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158821881562374759317143021 59558205585890534743928633)
          ·
            refine ⟨44668654189417901057946475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59558205585890534743928633 44668654189417901057946475)
            ·
              refine ⟨67002981284126851586919713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44668654189417901057946475 67002981284126851586919713)
              ·
                refine ⟨50252235963095138690189785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67002981284126851586919713 50252235963095138690189785)
                ·
                  refine ⟨37689176972321354017642339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50252235963095138690189785 37689176972321354017642339)
                  ·
                    refine ⟨56533765458482031026463509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37689176972321354017642339 56533765458482031026463509)
                    ·
                      refine ⟨2650020255866345204365477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56533765458482031026463509 2650020255866345204365477)
                      ·
                        rfl

theorem cell23_5160896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_5160896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160896 prefixEnd_5160896 := by exact prefixLift 5160896
  have htrace : WordTrace (prefixWord ++ tailWord_5160896) baseStart_5160896 baseEnd_5160896 := by
    simpa [prefixWord, tailWord_5160896, baseEnd_5160896] using wordTrace_append hprefix tailTrace_5160896
  have hstable : (prefixWord ++ tailWord_5160896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160896).length < 2 ^ (prefixWord ++ tailWord_5160896).sum := by decide
  have hdescent : baseEnd_5160896 < baseStart_5160896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160927 : List Nat := [1, 1, 2, 3, 4, 1, 3, 3, 1, 4]
def baseStart_5160927 : Nat := 118140960795 + 5160927 * 2 ^ 59
def prefixEnd_5160927 : Nat := 4983230072969 + 3 ^ 40 * 5160927 * 2
def baseEnd_5160927 : Nat := 883345391255544861025945

theorem tailTrace_5160927 : CollatzResearch.WordTrace tailWord_5160927 prefixEnd_5160927 883345391255544861025945 := by
  unfold tailWord_5160927
  simp only [CollatzResearch.WordTrace]
  refine ⟨188234471773850370003585035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125489647849233580002390023 188234471773850370003585035)
  ·
    refine ⟨282351707660775555005377553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188234471773850370003585035 282351707660775555005377553)
    ·
      refine ⟨211763780745581666254033165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282351707660775555005377553 211763780745581666254033165)
      ·
        refine ⟨79411417779593124845262437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211763780745581666254033165 79411417779593124845262437)
        ·
          refine ⟨14889640833673710908486707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79411417779593124845262437 14889640833673710908486707)
          ·
            refine ⟨22334461250510566362730061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14889640833673710908486707 22334461250510566362730061)
            ·
              refine ⟨8375422968941462386023773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22334461250510566362730061 8375422968941462386023773)
              ·
                refine ⟨3140783613353048394758915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8375422968941462386023773 3140783613353048394758915)
                ·
                  refine ⟨4711175420029572592138373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140783613353048394758915 4711175420029572592138373)
                  ·
                    refine ⟨883345391255544861025945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4711175420029572592138373 883345391255544861025945)
                    ·
                      rfl

theorem cell23_5160927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 1, 4].length) (baseStart_5160927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160927 prefixEnd_5160927 := by exact prefixLift 5160927
  have htrace : WordTrace (prefixWord ++ tailWord_5160927) baseStart_5160927 baseEnd_5160927 := by
    simpa [prefixWord, tailWord_5160927, baseEnd_5160927] using wordTrace_append hprefix tailTrace_5160927
  have hstable : (prefixWord ++ tailWord_5160927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160927).length < 2 ^ (prefixWord ++ tailWord_5160927).sum := by decide
  have hdescent : baseEnd_5160927 < baseStart_5160927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5160970 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_5160970 : Nat := 118140960795 + 5160970 * 2 ^ 59
def prefixEnd_5160970 : Nat := 4983230072969 + 3 ^ 40 * 5160970 * 2
def baseEnd_5160970 : Nat := 883352751144925971613379

theorem tailTrace_5160970 : CollatzResearch.WordTrace tailWord_5160970 prefixEnd_5160970 883352751144925971613379 := by
  unfold tailWord_5160970
  simp only [CollatzResearch.WordTrace]
  refine ⟨47059010028173647086850091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125490693408463058898266909 47059010028173647086850091)
  ·
    refine ⟨70588515042260470630275137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47059010028173647086850091 70588515042260470630275137)
    ·
      refine ⟨52941386281695352972706353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70588515042260470630275137 52941386281695352972706353)
      ·
        refine ⟨39706039711271514729529765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52941386281695352972706353 39706039711271514729529765)
        ·
          refine ⟨7444882445863409011786831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39706039711271514729529765 7444882445863409011786831)
          ·
            refine ⟨11167323668795113517680247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7444882445863409011786831 11167323668795113517680247)
            ·
              refine ⟨16750985503192670276520371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11167323668795113517680247 16750985503192670276520371)
              ·
                refine ⟨25126478254789005414780557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16750985503192670276520371 25126478254789005414780557)
                ·
                  refine ⟨9422429345545877030542709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25126478254789005414780557 9422429345545877030542709)
                  ·
                    refine ⟨883352751144925971613379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9422429345545877030542709 883352751144925971613379)
                    ·
                      rfl

theorem cell23_5160970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_5160970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5160970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5160970 prefixEnd_5160970 := by exact prefixLift 5160970
  have htrace : WordTrace (prefixWord ++ tailWord_5160970) baseStart_5160970 baseEnd_5160970 := by
    simpa [prefixWord, tailWord_5160970, baseEnd_5160970] using wordTrace_append hprefix tailTrace_5160970
  have hstable : (prefixWord ++ tailWord_5160970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5160970).length < 2 ^ (prefixWord ++ tailWord_5160970).sum := by decide
  have hdescent : baseEnd_5160970 < baseStart_5160970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5160970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161010 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_5161010 : Nat := 118140960795 + 5161010 * 2 ^ 59
def prefixEnd_5161010 : Nat := 4983230072969 + 3 ^ 40 * 5161010 * 2
def baseEnd_5161010 : Nat := 2650078792660957758339953

theorem tailTrace_5161010 : CollatzResearch.WordTrace tailWord_5161010 prefixEnd_5161010 2650078792660957758339953 := by
  unfold tailWord_5161010
  simp only [CollatzResearch.WordTrace]
  refine ⟨47059374758137418794714121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125491666021699783452570989 47059374758137418794714121)
  ·
    refine ⟨35294531068603064096035591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47059374758137418794714121 35294531068603064096035591)
    ·
      refine ⟨52941796602904596144053387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35294531068603064096035591 52941796602904596144053387)
      ·
        refine ⟨79412694904356894216080081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52941796602904596144053387 79412694904356894216080081)
        ·
          refine ⟨59559521178267670662060061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79412694904356894216080081 59559521178267670662060061)
          ·
            refine ⟨22334820441850376498272523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59559521178267670662060061 22334820441850376498272523)
            ·
              refine ⟨33502230662775564747408785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22334820441850376498272523 33502230662775564747408785)
              ·
                refine ⟨25126672997081673560556589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33502230662775564747408785 25126672997081673560556589)
                ·
                  refine ⟨9422502373905627585208721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25126672997081673560556589 9422502373905627585208721)
                  ·
                    refine ⟨7066876780429220688906541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9422502373905627585208721 7066876780429220688906541)
                    ·
                      refine ⟨2650078792660957758339953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7066876780429220688906541 2650078792660957758339953)
                      ·
                        rfl

theorem cell23_5161010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_5161010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161010 prefixEnd_5161010 := by exact prefixLift 5161010
  have htrace : WordTrace (prefixWord ++ tailWord_5161010) baseStart_5161010 baseEnd_5161010 := by
    simpa [prefixWord, tailWord_5161010, baseEnd_5161010] using wordTrace_append hprefix tailTrace_5161010
  have hstable : (prefixWord ++ tailWord_5161010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161010).length < 2 ^ (prefixWord ++ tailWord_5161010).sum := by decide
  have hdescent : baseEnd_5161010 < baseStart_5161010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161013 : List Nat := [1, 3, 3, 1, 1, 1, 5, 8]
def baseStart_5161013 : Nat := 118140960795 + 5161013 * 2 ^ 59
def prefixEnd_5161013 : Nat := 4983230072969 + 3 ^ 40 * 5161013 * 2
def baseEnd_5161013 : Nat := 98151123448256342466757

theorem tailTrace_5161013 : CollatzResearch.WordTrace tailWord_5161013 prefixEnd_5161013 98151123448256342466757 := by
  unfold tailWord_5161013
  simp only [CollatzResearch.WordTrace]
  refine ⟨188237608451538806691215693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125491738967692537794143795 188237608451538806691215693)
  ·
    refine ⟨70589103169327052509205885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188237608451538806691215693 70589103169327052509205885)
    ·
      refine ⟨26470913688497644690952207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70589103169327052509205885 26470913688497644690952207)
      ·
        refine ⟨39706370532746467036428311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26470913688497644690952207 39706370532746467036428311)
        ·
          refine ⟨59559555799119700554642467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39706370532746467036428311 59559555799119700554642467)
          ·
            refine ⟨89339333698679550831963701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59559555799119700554642467 89339333698679550831963701)
            ·
              refine ⟨8375562534251207890496597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89339333698679550831963701 8375562534251207890496597)
              ·
                refine ⟨98151123448256342466757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8375562534251207890496597 98151123448256342466757)
                ·
                  rfl

theorem cell23_5161013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 8].length) (baseStart_5161013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161013 prefixEnd_5161013 := by exact prefixLift 5161013
  have htrace : WordTrace (prefixWord ++ tailWord_5161013) baseStart_5161013 baseEnd_5161013 := by
    simpa [prefixWord, tailWord_5161013, baseEnd_5161013] using wordTrace_append hprefix tailTrace_5161013
  have hstable : (prefixWord ++ tailWord_5161013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161013).length < 2 ^ (prefixWord ++ tailWord_5161013).sum := by decide
  have hdescent : baseEnd_5161013 < baseStart_5161013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161020 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_5161020 : Nat := 118140960795 + 5161020 * 2 ^ 59
def prefixEnd_5161020 : Nat := 4983230072969 + 3 ^ 40 * 5161020 * 2
def baseEnd_5161020 : Nat := 2650083927467502719214907

theorem tailTrace_5161020 : CollatzResearch.WordTrace tailWord_5161020 prefixEnd_5161020 2650083927467502719214907 := by
  unfold tailWord_5161020
  simp only [CollatzResearch.WordTrace]
  refine ⟨94118931881256723443360257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125491909175008964591147009 94118931881256723443360257)
  ·
    refine ⟨70589198910942542582520193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94118931881256723443360257 70589198910942542582520193)
    ·
      refine ⟨52941899183206906936890145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70589198910942542582520193 52941899183206906936890145)
      ·
        refine ⟨39706424387405180202667609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52941899183206906936890145 39706424387405180202667609)
        ·
          refine ⟨29779818290553885152000707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39706424387405180202667609 29779818290553885152000707)
          ·
            refine ⟨44669727435830827728001061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29779818290553885152000707 44669727435830827728001061)
            ·
              refine ⟨8375573894218280199000199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44669727435830827728001061 8375573894218280199000199)
              ·
                refine ⟨12563360841327420298500299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8375573894218280199000199 12563360841327420298500299)
                ·
                  refine ⟨18845041261991130447750449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12563360841327420298500299 18845041261991130447750449)
                  ·
                    refine ⟨14133780946493347835812837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18845041261991130447750449 14133780946493347835812837)
                    ·
                      refine ⟨2650083927467502719214907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14133780946493347835812837 2650083927467502719214907)
                      ·
                        rfl

theorem cell23_5161020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_5161020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161020 prefixEnd_5161020 := by exact prefixLift 5161020
  have htrace : WordTrace (prefixWord ++ tailWord_5161020) baseStart_5161020 baseEnd_5161020 := by
    simpa [prefixWord, tailWord_5161020, baseEnd_5161020] using wordTrace_append hprefix tailTrace_5161020
  have hstable : (prefixWord ++ tailWord_5161020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161020).length < 2 ^ (prefixWord ++ tailWord_5161020).sum := by decide
  have hdescent : baseEnd_5161020 < baseStart_5161020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161073 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 2, 6]
def baseStart_5161073 : Nat := 118140960795 + 5161073 * 2 ^ 59
def prefixEnd_5161073 : Nat := 4983230072969 + 3 ^ 40 * 5161073 * 2
def baseEnd_5161073 : Nat := 883370380647397003950721

theorem tailTrace_5161073 : CollatzResearch.WordTrace tailWord_5161073 prefixEnd_5161073 883370380647397003950721 := by
  unfold tailWord_5161073
  simp only [CollatzResearch.WordTrace]
  refine ⟨188239796831321436938399873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125493197887547624625599915 188239796831321436938399873)
  ·
    refine ⟨141179847623491077703799905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188239796831321436938399873 141179847623491077703799905)
    ·
      refine ⟨105884885717618308277849929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141179847623491077703799905 105884885717618308277849929)
      ·
        refine ⟨79413664288213731208387447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105884885717618308277849929 79413664288213731208387447)
        ·
          refine ⟨119120496432320596812581171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79413664288213731208387447 119120496432320596812581171)
          ·
            refine ⟨178680744648480895218871757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119120496432320596812581171 178680744648480895218871757)
            ·
              refine ⟨67005279243180335707076909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178680744648480895218871757 67005279243180335707076909)
              ·
                refine ⟨25126979716192625890153841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67005279243180335707076909 25126979716192625890153841)
                ·
                  refine ⟨18845234787144469417615381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25126979716192625890153841 18845234787144469417615381)
                  ·
                    refine ⟨883370380647397003950721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18845234787144469417615381 883370380647397003950721)
                    ·
                      rfl

theorem cell23_5161073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_5161073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161073 prefixEnd_5161073 := by exact prefixLift 5161073
  have htrace : WordTrace (prefixWord ++ tailWord_5161073) baseStart_5161073 baseEnd_5161073 := by
    simpa [prefixWord, tailWord_5161073, baseEnd_5161073] using wordTrace_append hprefix tailTrace_5161073
  have hstable : (prefixWord ++ tailWord_5161073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161073).length < 2 ^ (prefixWord ++ tailWord_5161073).sum := by decide
  have hdescent : baseEnd_5161073 < baseStart_5161073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161084 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_5161084 : Nat := 118140960795 + 5161084 * 2 ^ 59
def prefixEnd_5161084 : Nat := 4983230072969 + 3 ^ 40 * 5161084 * 2
def baseEnd_5161084 : Nat := 2650116790229390468814613

theorem tailTrace_5161084 : CollatzResearch.WordTrace tailWord_5161084 prefixEnd_5161084 2650116790229390468814613 := by
  unfold tailWord_5161084
  simp only [CollatzResearch.WordTrace]
  refine ⟨94120099017140792908525153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125493465356187723878033537 94120099017140792908525153)
  ·
    refine ⟨70590074262855594681393865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94120099017140792908525153 70590074262855594681393865)
    ·
      refine ⟨52942555697141696011045399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70590074262855594681393865 52942555697141696011045399)
      ·
        refine ⟨79413833545712544016568099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52942555697141696011045399 79413833545712544016568099)
        ·
          refine ⟨119120750318568816024852149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79413833545712544016568099 119120750318568816024852149)
          ·
            refine ⟨11167570342365826502329889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119120750318568816024852149 11167570342365826502329889)
            ·
              refine ⟨8375677756774369876747417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11167570342365826502329889 8375677756774369876747417)
              ·
                refine ⟨6281758317580777407560563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8375677756774369876747417 6281758317580777407560563)
                ·
                  refine ⟨9422637476371166111340845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6281758317580777407560563 9422637476371166111340845)
                  ·
                    refine ⟨3533489053639187291752817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9422637476371166111340845 3533489053639187291752817)
                    ·
                      refine ⟨2650116790229390468814613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533489053639187291752817 2650116790229390468814613)
                      ·
                        rfl

theorem cell23_5161084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_5161084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161084 prefixEnd_5161084 := by exact prefixLift 5161084
  have htrace : WordTrace (prefixWord ++ tailWord_5161084) baseStart_5161084 baseEnd_5161084 := by
    simpa [prefixWord, tailWord_5161084, baseEnd_5161084] using wordTrace_append hprefix tailTrace_5161084
  have hstable : (prefixWord ++ tailWord_5161084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161084).length < 2 ^ (prefixWord ++ tailWord_5161084).sum := by decide
  have hdescent : baseEnd_5161084 < baseStart_5161084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161097 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 6, 2, 2]
def baseStart_5161097 : Nat := 118140960795 + 5161097 * 2 ^ 59
def prefixEnd_5161097 : Nat := 4983230072969 + 3 ^ 40 * 5161097 * 2
def baseEnd_5161097 : Nat := 2650123465477898917952053

theorem tailTrace_5161097 : CollatzResearch.WordTrace tailWord_5161097 prefixEnd_5161097 2650123465477898917952053 := by
  unfold tailWord_5161097
  simp only [CollatzResearch.WordTrace]
  refine ⟨188240672183234489037273545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125493781455489659358182363 188240672183234489037273545)
  ·
    refine ⟨141180504137425866777955159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188240672183234489037273545 141180504137425866777955159)
    ·
      refine ⟨211770756206138800166932739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141180504137425866777955159 211770756206138800166932739)
      ·
        refine ⟨317656134309208200250399109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211770756206138800166932739 317656134309208200250399109)
        ·
          refine ⟨59560525182976537546949833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317656134309208200250399109 59560525182976537546949833)
          ·
            refine ⟨44670393887232403160212375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59560525182976537546949833 44670393887232403160212375)
            ·
              refine ⟨67005590830848604740318563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44670393887232403160212375 67005590830848604740318563)
              ·
                refine ⟨100508386246272907110477845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67005590830848604740318563 100508386246272907110477845)
                ·
                  refine ⟨4711330605294042520803649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100508386246272907110477845 4711330605294042520803649)
                  ·
                    refine ⟨3533497953970531890602737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4711330605294042520803649 3533497953970531890602737)
                    ·
                      refine ⟨2650123465477898917952053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533497953970531890602737 2650123465477898917952053)
                      ·
                        rfl

theorem cell23_5161097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 2, 2].length) (baseStart_5161097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161097 prefixEnd_5161097 := by exact prefixLift 5161097
  have htrace : WordTrace (prefixWord ++ tailWord_5161097) baseStart_5161097 baseEnd_5161097 := by
    simpa [prefixWord, tailWord_5161097, baseEnd_5161097] using wordTrace_append hprefix tailTrace_5161097
  have hstable : (prefixWord ++ tailWord_5161097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161097).length < 2 ^ (prefixWord ++ tailWord_5161097).sum := by decide
  have hdescent : baseEnd_5161097 < baseStart_5161097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161120 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 7]
def baseStart_5161120 : Nat := 118140960795 + 5161120 * 2 ^ 59
def prefixEnd_5161120 : Nat := 4983230072969 + 3 ^ 40 * 5161120 * 2
def baseEnd_5161120 : Nat := 294459475059216925329383

theorem tailTrace_5161120 : CollatzResearch.WordTrace tailWord_5161120 prefixEnd_5161120 294459475059216925329383 := by
  unfold tailWord_5161120
  simp only [CollatzResearch.WordTrace]
  refine ⟨94120755531075581982680407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125494340708100775976907209 94120755531075581982680407)
  ·
    refine ⟨141181133296613372974020611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94120755531075581982680407 141181133296613372974020611)
    ·
      refine ⟨211771699944920059461030917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141181133296613372974020611 211771699944920059461030917)
      ·
        refine ⟨39707193739672511148943297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211771699944920059461030917 39707193739672511148943297)
        ·
          refine ⟨29780395304754383361707473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39707193739672511148943297 29780395304754383361707473)
          ·
            refine ⟨22335296478565787521280605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29780395304754383361707473 22335296478565787521280605)
            ·
              refine ⟨8375736179462170320480227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22335296478565787521280605 8375736179462170320480227)
              ·
                refine ⟨12563604269193255480720341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8375736179462170320480227 12563604269193255480720341)
                ·
                  refine ⟨294459475059216925329383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12563604269193255480720341 294459475059216925329383)
                  ·
                    rfl

theorem cell23_5161120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 7].length) (baseStart_5161120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161120 prefixEnd_5161120 := by exact prefixLift 5161120
  have htrace : WordTrace (prefixWord ++ tailWord_5161120) baseStart_5161120 baseEnd_5161120 := by
    simpa [prefixWord, tailWord_5161120, baseEnd_5161120] using wordTrace_append hprefix tailTrace_5161120
  have hstable : (prefixWord ++ tailWord_5161120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161120).length < 2 ^ (prefixWord ++ tailWord_5161120).sum := by decide
  have hdescent : baseEnd_5161120 < baseStart_5161120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161230 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_5161230 : Nat := 118140960795 + 5161230 * 2 ^ 59
def prefixEnd_5161230 : Nat := 4983230072969 + 3 ^ 40 * 5161230 * 2
def baseEnd_5161230 : Nat := 2650191758404946897588941

theorem tailTrace_5161230 : CollatzResearch.WordTrace tailWord_5161230 prefixEnd_5161230 2650191758404946897588941 := by
  unfold tailWord_5161230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23530690386469081593983143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125497015394501768501243429 23530690386469081593983143)
  ·
    refine ⟨35296035579703622390974715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23530690386469081593983143 35296035579703622390974715)
    ·
      refine ⟨52944053369555433586462073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35296035579703622390974715 52944053369555433586462073)
      ·
        refine ⟨39708040027166575189846555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52944053369555433586462073 39708040027166575189846555)
        ·
          refine ⟨59562060040749862784769833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39708040027166575189846555 59562060040749862784769833)
          ·
            refine ⟨44671545030562397088577375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59562060040749862784769833 44671545030562397088577375)
            ·
              refine ⟨67007317545843595632866063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44671545030562397088577375 67007317545843595632866063)
              ·
                refine ⟨100510976318765393449299095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67007317545843595632866063 100510976318765393449299095)
                ·
                  refine ⟨150766464478148090173948643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100510976318765393449299095 150766464478148090173948643)
                  ·
                    refine ⟨226149696717222135260922965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150766464478148090173948643 226149696717222135260922965)
                    ·
                      refine ⟨2650191758404946897588941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226149696717222135260922965 2650191758404946897588941)
                      ·
                        rfl

theorem cell23_5161230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_5161230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161230 prefixEnd_5161230 := by exact prefixLift 5161230
  have htrace : WordTrace (prefixWord ++ tailWord_5161230) baseStart_5161230 baseEnd_5161230 := by
    simpa [prefixWord, tailWord_5161230, baseEnd_5161230] using wordTrace_append hprefix tailTrace_5161230
  have hstable : (prefixWord ++ tailWord_5161230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161230).length < 2 ^ (prefixWord ++ tailWord_5161230).sum := by decide
  have hdescent : baseEnd_5161230 < baseStart_5161230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161287 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 4, 4]
def baseStart_5161287 : Nat := 118140960795 + 5161287 * 2 ^ 59
def prefixEnd_5161287 : Nat := 4983230072969 + 3 ^ 40 * 5161287 * 2
def baseEnd_5161287 : Nat := 883407008934084391525393

theorem tailTrace_5161287 : CollatzResearch.WordTrace tailWord_5161287 prefixEnd_5161287 883407008934084391525393 := by
  unfold tailWord_5161287
  simp only [CollatzResearch.WordTrace]
  refine ⟨188247602052546151486690115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125498401368364100991126743 188247602052546151486690115)
  ·
    refine ⟨282371403078819227230035173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188247602052546151486690115 282371403078819227230035173)
    ·
      refine ⟨52944638077278605105631595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282371403078819227230035173 52944638077278605105631595)
      ·
        refine ⟨79416957115917907658447393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52944638077278605105631595 79416957115917907658447393)
        ·
          refine ⟨59562717836938430743835545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79416957115917907658447393 59562717836938430743835545)
          ·
            refine ⟨44672038377703823057876659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59562717836938430743835545 44672038377703823057876659)
            ·
              refine ⟨67008057566555734586814989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44672038377703823057876659 67008057566555734586814989)
              ·
                refine ⟨25128021587458400470055621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67008057566555734586814989 25128021587458400470055621)
                ·
                  refine ⟨4711504047648450088135429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25128021587458400470055621 4711504047648450088135429)
                  ·
                    refine ⟨883407008934084391525393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4711504047648450088135429 883407008934084391525393)
                    ·
                      rfl

theorem cell23_5161287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_5161287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161287 prefixEnd_5161287 := by exact prefixLift 5161287
  have htrace : WordTrace (prefixWord ++ tailWord_5161287) baseStart_5161287 baseEnd_5161287 := by
    simpa [prefixWord, tailWord_5161287, baseEnd_5161287] using wordTrace_append hprefix tailTrace_5161287
  have hstable : (prefixWord ++ tailWord_5161287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161287).length < 2 ^ (prefixWord ++ tailWord_5161287).sum := by decide
  have hdescent : baseEnd_5161287 < baseStart_5161287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161297 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_5161297 : Nat := 118140960795 + 5161297 * 2 ^ 59
def prefixEnd_5161297 : Nat := 4983230072969 + 3 ^ 40 * 5161297 * 2
def baseEnd_5161297 : Nat := 2650226161608798135451133

theorem tailTrace_5161297 : CollatzResearch.WordTrace tailWord_5161297 prefixEnd_5161297 2650226161608798135451133 := by
  unfold tailWord_5161297
  simp only [CollatzResearch.WordTrace]
  refine ⟨188247966782509923194554145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125498644521673282129702763 188247966782509923194554145)
  ·
    refine ⟨141185975086882442395915609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188247966782509923194554145 141185975086882442395915609)
    ·
      refine ⟨105889481315161831796936707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141185975086882442395915609 105889481315161831796936707)
      ·
        refine ⟨158834221972742747695405061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105889481315161831796936707 158834221972742747695405061)
        ·
          refine ⟨29781416619889265192888449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158834221972742747695405061 29781416619889265192888449)
          ·
            refine ⟨22336062464916948894666337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29781416619889265192888449 22336062464916948894666337)
            ·
              refine ⟨16752046848687711670999753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22336062464916948894666337 16752046848687711670999753)
              ·
                refine ⟨12564035136515783753249815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16752046848687711670999753 12564035136515783753249815)
                ·
                  refine ⟨18846052704773675629874723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12564035136515783753249815 18846052704773675629874723)
                  ·
                    refine ⟨28269079057160513444812085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18846052704773675629874723 28269079057160513444812085)
                    ·
                      refine ⟨2650226161608798135451133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28269079057160513444812085 2650226161608798135451133)
                      ·
                        rfl

theorem cell23_5161297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_5161297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161297 prefixEnd_5161297 := by exact prefixLift 5161297
  have htrace : WordTrace (prefixWord ++ tailWord_5161297) baseStart_5161297 baseEnd_5161297 := by
    simpa [prefixWord, tailWord_5161297, baseEnd_5161297] using wordTrace_append hprefix tailTrace_5161297
  have hstable : (prefixWord ++ tailWord_5161297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161297).length < 2 ^ (prefixWord ++ tailWord_5161297).sum := by decide
  have hdescent : baseEnd_5161297 < baseStart_5161297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161308 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5161308 : Nat := 118140960795 + 5161308 * 2 ^ 59
def prefixEnd_5161308 : Nat := 4983230072969 + 3 ^ 40 * 5161308 * 2
def baseEnd_5161308 : Nat := 883410603298665864137861

theorem tailTrace_5161308 : CollatzResearch.WordTrace tailWord_5161308 prefixEnd_5161308 883410603298665864137861 := by
  unfold tailWord_5161308
  simp only [CollatzResearch.WordTrace]
  refine ⟨94124183992735036036602289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125498911990313381382136385 94124183992735036036602289)
  ·
    refine ⟨70593137994551277027451717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94124183992735036036602289 70593137994551277027451717)
    ·
      refine ⟨13236213373978364442647197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70593137994551277027451717 13236213373978364442647197)
      ·
        refine ⟨4963580015241886665992699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13236213373978364442647197 4963580015241886665992699)
        ·
          refine ⟨7445370022862829998989049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963580015241886665992699 7445370022862829998989049)
          ·
            refine ⟨5584027517147122499241787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7445370022862829998989049 5584027517147122499241787)
            ·
              refine ⟨8376041275720683748862681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584027517147122499241787 8376041275720683748862681)
              ·
                refine ⟨6282030956790512811647011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8376041275720683748862681 6282030956790512811647011)
                ·
                  refine ⟨9423046435185769217470517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6282030956790512811647011 9423046435185769217470517)
                  ·
                    refine ⟨883410603298665864137861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9423046435185769217470517 883410603298665864137861)
                    ·
                      rfl

theorem cell23_5161308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5161308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161308 prefixEnd_5161308 := by exact prefixLift 5161308
  have htrace : WordTrace (prefixWord ++ tailWord_5161308) baseStart_5161308 baseEnd_5161308 := by
    simpa [prefixWord, tailWord_5161308, baseEnd_5161308] using wordTrace_append hprefix tailTrace_5161308
  have hstable : (prefixWord ++ tailWord_5161308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161308).length < 2 ^ (prefixWord ++ tailWord_5161308).sum := by decide
  have hdescent : baseEnd_5161308 < baseStart_5161308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161324 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_5161324 : Nat := 118140960795 + 5161324 * 2 ^ 59
def prefixEnd_5161324 : Nat := 4983230072969 + 3 ^ 40 * 5161324 * 2
def baseEnd_5161324 : Nat := 2650240025586469529813509

theorem tailTrace_5161324 : CollatzResearch.WordTrace tailWord_5161324 prefixEnd_5161324 2650240025586469529813509 := by
  unfold tailWord_5161324
  simp only [CollatzResearch.WordTrace]
  refine ⟨94124475776706053402893513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125499301035608071203858017 94124475776706053402893513)
  ·
    refine ⟨70593356832529540052170135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94124475776706053402893513 70593356832529540052170135)
    ·
      refine ⟨105890035248794310078255203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70593356832529540052170135 105890035248794310078255203)
      ·
        refine ⟨158835052873191465117382805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105890035248794310078255203 158835052873191465117382805)
        ·
          refine ⟨7445393103430849927377319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158835052873191465117382805 7445393103430849927377319)
          ·
            refine ⟨11168089655146274891065979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445393103430849927377319 11168089655146274891065979)
            ·
              refine ⟨16752134482719412336598969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11168089655146274891065979 16752134482719412336598969)
              ·
                refine ⟨12564100862039559252449227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16752134482719412336598969 12564100862039559252449227)
                ·
                  refine ⟨18846151293059338878673841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12564100862039559252449227 18846151293059338878673841)
                  ·
                    refine ⟨14134613469794504159005381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18846151293059338878673841 14134613469794504159005381)
                    ·
                      refine ⟨2650240025586469529813509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14134613469794504159005381 2650240025586469529813509)
                      ·
                        rfl

theorem cell23_5161324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_5161324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161324 prefixEnd_5161324 := by exact prefixLift 5161324
  have htrace : WordTrace (prefixWord ++ tailWord_5161324) baseStart_5161324 baseEnd_5161324 := by
    simpa [prefixWord, tailWord_5161324, baseEnd_5161324] using wordTrace_append hprefix tailTrace_5161324
  have hstable : (prefixWord ++ tailWord_5161324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161324).length < 2 ^ (prefixWord ++ tailWord_5161324).sum := by decide
  have hdescent : baseEnd_5161324 < baseStart_5161324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161334 : List Nat := [5, 1, 1, 4, 1, 11]
def baseStart_5161334 : Nat := 118140960795 + 5161334 * 2 ^ 59
def prefixEnd_5161334 : Nat := 4983230072969 + 3 ^ 40 * 5161334 * 2
def baseEnd_5161334 : Nat := 10906358684744915599541

theorem tailTrace_5161334 : CollatzResearch.WordTrace tailWord_5161334 prefixEnd_5161334 10906358684744915599541 := by
  unfold tailWord_5161334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765582267710992407103191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125499544188917252342434037 11765582267710992407103191)
  ·
    refine ⟨17648373401566488610654787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11765582267710992407103191 17648373401566488610654787)
    ·
      refine ⟨26472560102349732915982181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17648373401566488610654787 26472560102349732915982181)
      ·
        refine ⟨4963605019190574921746659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26472560102349732915982181 4963605019190574921746659)
        ·
          refine ⟨7445407528785862382619989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963605019190574921746659 7445407528785862382619989)
          ·
            refine ⟨10906358684744915599541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7445407528785862382619989 10906358684744915599541)
            ·
              rfl

theorem cell23_5161334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 11].length) (baseStart_5161334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161334 prefixEnd_5161334 := by exact prefixLift 5161334
  have htrace : WordTrace (prefixWord ++ tailWord_5161334) baseStart_5161334 baseEnd_5161334 := by
    simpa [prefixWord, tailWord_5161334, baseEnd_5161334] using wordTrace_append hprefix tailTrace_5161334
  have hstable : (prefixWord ++ tailWord_5161334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161334).length < 2 ^ (prefixWord ++ tailWord_5161334).sum := by decide
  have hdescent : baseEnd_5161334 < baseStart_5161334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161345 : List Nat := [1, 2, 4, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_5161345 : Nat := 118140960795 + 5161345 * 2 ^ 59
def prefixEnd_5161345 : Nat := 4983230072969 + 3 ^ 40 * 5161345 * 2
def baseEnd_5161345 : Nat := 2650250808680213947650913

theorem tailTrace_5161345 : CollatzResearch.WordTrace tailWord_5161345 prefixEnd_5161345 2650250808680213947650913 := by
  unfold tailWord_5161345
  simp only [CollatzResearch.WordTrace]
  refine ⟨188249717486336027392301489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125499811657557351594867659 188249717486336027392301489)
  ·
    refine ⟨141187288114752020544226117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188249717486336027392301489 141187288114752020544226117)
    ·
      refine ⟨26472616521516003852042397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141187288114752020544226117 26472616521516003852042397)
      ·
        refine ⟨9927231195568501444515899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26472616521516003852042397 9927231195568501444515899)
        ·
          refine ⟨14890846793352752166773849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9927231195568501444515899 14890846793352752166773849)
          ·
            refine ⟨11168135095014564125080387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14890846793352752166773849 11168135095014564125080387)
            ·
              refine ⟨16752202642521846187620581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11168135095014564125080387 16752202642521846187620581)
              ·
                refine ⟨3141037995472846160178859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16752202642521846187620581 3141037995472846160178859)
                ·
                  refine ⟨4711556993209269240268289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141037995472846160178859 4711556993209269240268289)
                  ·
                    refine ⟨3533667744906951930201217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4711556993209269240268289 3533667744906951930201217)
                    ·
                      refine ⟨2650250808680213947650913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533667744906951930201217 2650250808680213947650913)
                      ·
                        rfl

theorem cell23_5161345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_5161345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161345 prefixEnd_5161345 := by exact prefixLift 5161345
  have htrace : WordTrace (prefixWord ++ tailWord_5161345) baseStart_5161345 baseEnd_5161345 := by
    simpa [prefixWord, tailWord_5161345, baseEnd_5161345] using wordTrace_append hprefix tailTrace_5161345
  have hstable : (prefixWord ++ tailWord_5161345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161345).length < 2 ^ (prefixWord ++ tailWord_5161345).sum := by decide
  have hdescent : baseEnd_5161345 < baseStart_5161345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161444 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_5161444 : Nat := 118140960795 + 5161444 * 2 ^ 59
def prefixEnd_5161444 : Nat := 4983230072969 + 3 ^ 40 * 5161444 * 2
def baseEnd_5161444 : Nat := 2650301643265009060312957

theorem tailTrace_5161444 : CollatzResearch.WordTrace tailWord_5161444 prefixEnd_5161444 2650301643265009060312957 := by
  unfold tailWord_5161444
  simp only [CollatzResearch.WordTrace]
  refine ⟨94126664156488683650077693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125502218875318244866770257 94126664156488683650077693)
  ·
    refine ⟨35297499058683256368779135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94126664156488683650077693 35297499058683256368779135)
    ·
      refine ⟨52946248588024884553168703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35297499058683256368779135 52946248588024884553168703)
      ·
        refine ⟨79419372882037326829753055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52946248588024884553168703 79419372882037326829753055)
        ·
          refine ⟨119129059323055990244629583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79419372882037326829753055 119129059323055990244629583)
          ·
            refine ⟨178693588984583985366944375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119129059323055990244629583 178693588984583985366944375)
            ·
              refine ⟨268040383476875978050416563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178693588984583985366944375 268040383476875978050416563)
              ·
                refine ⟨402060575215313967075624845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268040383476875978050416563 402060575215313967075624845)
                ·
                  refine ⟨150772715705742737653359317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402060575215313967075624845 150772715705742737653359317)
                  ·
                    refine ⟨3533735524353345413750609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 150772715705742737653359317 3533735524353345413750609)
                    ·
                      refine ⟨2650301643265009060312957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533735524353345413750609 2650301643265009060312957)
                      ·
                        rfl

theorem cell23_5161444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_5161444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161444 prefixEnd_5161444 := by exact prefixLift 5161444
  have htrace : WordTrace (prefixWord ++ tailWord_5161444) baseStart_5161444 baseEnd_5161444 := by
    simpa [prefixWord, tailWord_5161444, baseEnd_5161444] using wordTrace_append hprefix tailTrace_5161444
  have hstable : (prefixWord ++ tailWord_5161444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161444).length < 2 ^ (prefixWord ++ tailWord_5161444).sum := by decide
  have hdescent : baseEnd_5161444 < baseStart_5161444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161454 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_5161454 : Nat := 118140960795 + 5161454 * 2 ^ 59
def prefixEnd_5161454 : Nat := 4983230072969 + 3 ^ 40 * 5161454 * 2
def baseEnd_5161454 : Nat := 883435592690518007062637

theorem tailTrace_5161454 : CollatzResearch.WordTrace tailWord_5161454 prefixEnd_5161454 883435592690518007062637 := by
  unfold tailWord_5161454
  simp only [CollatzResearch.WordTrace]
  refine ⟨23531711630367642376002427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125502462028627426005346277 23531711630367642376002427)
  ·
    refine ⟨35297567445551463564003641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23531711630367642376002427 35297567445551463564003641)
    ·
      refine ⟨26473175584163597673002731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35297567445551463564003641 26473175584163597673002731)
      ·
        refine ⟨39709763376245396509504097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26473175584163597673002731 39709763376245396509504097)
        ·
          refine ⟨29782322532184047382128073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39709763376245396509504097 29782322532184047382128073)
          ·
            refine ⟨22336741899138035536596055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29782322532184047382128073 22336741899138035536596055)
            ·
              refine ⟨33505112848707053304894083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22336741899138035536596055 33505112848707053304894083)
              ·
                refine ⟨50257669273060579957341125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33505112848707053304894083 50257669273060579957341125)
                ·
                  refine ⟨9423312988698858742001461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50257669273060579957341125 9423312988698858742001461)
                  ·
                    refine ⟨883435592690518007062637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9423312988698858742001461 883435592690518007062637)
                    ·
                      rfl

theorem cell23_5161454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_5161454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161454 prefixEnd_5161454 := by exact prefixLift 5161454
  have htrace : WordTrace (prefixWord ++ tailWord_5161454) baseStart_5161454 baseEnd_5161454 := by
    simpa [prefixWord, tailWord_5161454, baseEnd_5161454] using wordTrace_append hprefix tailTrace_5161454
  have hstable : (prefixWord ++ tailWord_5161454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161454).length < 2 ^ (prefixWord ++ tailWord_5161454).sum := by decide
  have hdescent : baseEnd_5161454 < baseStart_5161454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161458 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 7]
def baseStart_5161458 : Nat := 118140960795 + 5161458 * 2 ^ 59
def prefixEnd_5161458 : Nat := 4983230072969 + 3 ^ 40 * 5161458 * 2
def baseEnd_5161458 : Nat := 294478759110463556170877

theorem tailTrace_5161458 : CollatzResearch.WordTrace tailWord_5161458 prefixEnd_5161458 294478759110463556170877 := by
  unfold tailWord_5161458
  simp only [CollatzResearch.WordTrace]
  refine ⟨47063459733731661922791257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125502559289951098460776685 47063459733731661922791257)
  ·
    refine ⟨35297594800298746442093443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47063459733731661922791257 35297594800298746442093443)
    ·
      refine ⟨52946392200448119663140165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35297594800298746442093443 52946392200448119663140165)
      ·
        refine ⟨9927448537584022436838781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52946392200448119663140165 9927448537584022436838781)
        ·
          refine ⟨3722793201594008413814543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9927448537584022436838781 3722793201594008413814543)
          ·
            refine ⟨5584189802391012620721815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722793201594008413814543 5584189802391012620721815)
            ·
              refine ⟨8376284703586518931082723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584189802391012620721815 8376284703586518931082723)
              ·
                refine ⟨12564427055379778396624085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8376284703586518931082723 12564427055379778396624085)
                ·
                  refine ⟨294478759110463556170877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12564427055379778396624085 294478759110463556170877)
                  ·
                    rfl

theorem cell23_5161458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_5161458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161458 prefixEnd_5161458 := by exact prefixLift 5161458
  have htrace : WordTrace (prefixWord ++ tailWord_5161458) baseStart_5161458 baseEnd_5161458 := by
    simpa [prefixWord, tailWord_5161458, baseEnd_5161458] using wordTrace_append hprefix tailTrace_5161458
  have hstable : (prefixWord ++ tailWord_5161458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161458).length < 2 ^ (prefixWord ++ tailWord_5161458).sum := by decide
  have hdescent : baseEnd_5161458 < baseStart_5161458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161487 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_5161487 : Nat := 118140960795 + 5161487 * 2 ^ 59
def prefixEnd_5161487 : Nat := 4983230072969 + 3 ^ 40 * 5161487 * 2
def baseEnd_5161487 : Nat := 2650323722933152392075259

theorem tailTrace_5161487 : CollatzResearch.WordTrace tailWord_5161487 prefixEnd_5161487 2650323722933152392075259 := by
  unfold tailWord_5161487
  simp only [CollatzResearch.WordTrace]
  refine ⟨188254896651821585643970715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125503264434547723762647143 188254896651821585643970715)
  ·
    refine ⟨282382344977732378465956073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188254896651821585643970715 282382344977732378465956073)
    ·
      refine ⟨211786758733299283849467055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282382344977732378465956073 211786758733299283849467055)
      ·
        refine ⟨317680138099948925774200583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211786758733299283849467055 317680138099948925774200583)
        ·
          refine ⟨476520207149923388661300875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317680138099948925774200583 476520207149923388661300875)
          ·
            refine ⟨714780310724885082991951313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476520207149923388661300875 714780310724885082991951313)
            ·
              refine ⟨536085233043663812243963485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714780310724885082991951313 536085233043663812243963485)
              ·
                refine ⟨201031962391373929591486307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536085233043663812243963485 201031962391373929591486307)
                ·
                  refine ⟨301547943587060894387229461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201031962391373929591486307 301547943587060894387229461)
                  ·
                    refine ⟨14135059855643479424401381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 301547943587060894387229461 14135059855643479424401381)
                    ·
                      refine ⟨2650323722933152392075259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14135059855643479424401381 2650323722933152392075259)
                      ·
                        rfl

theorem cell23_5161487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_5161487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161487 prefixEnd_5161487 := by exact prefixLift 5161487
  have htrace : WordTrace (prefixWord ++ tailWord_5161487) baseStart_5161487 baseEnd_5161487 := by
    simpa [prefixWord, tailWord_5161487, baseEnd_5161487] using wordTrace_append hprefix tailTrace_5161487
  have hstable : (prefixWord ++ tailWord_5161487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161487).length < 2 ^ (prefixWord ++ tailWord_5161487).sum := by decide
  have hdescent : baseEnd_5161487 < baseStart_5161487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161541 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_5161541 : Nat := 118140960795 + 5161541 * 2 ^ 59
def prefixEnd_5161541 : Nat := 4983230072969 + 3 ^ 40 * 5161541 * 2
def baseEnd_5161541 : Nat := 2650351450888495180800011

theorem tailTrace_5161541 : CollatzResearch.WordTrace tailWord_5161541 prefixEnd_5161541 2650351450888495180800011 := by
  unfold tailWord_5161541
  simp only [CollatzResearch.WordTrace]
  refine ⟨188256866193625952866436477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125504577462417301910957651 188256866193625952866436477)
  ·
    refine ⟨70596324822609732324913679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188256866193625952866436477 70596324822609732324913679)
    ·
      refine ⟨105894487233914598487370519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70596324822609732324913679 105894487233914598487370519)
      ·
        refine ⟨158841730850871897731055779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105894487233914598487370519 158841730850871897731055779)
        ·
          refine ⟨238262596276307846596583669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158841730850871897731055779 238262596276307846596583669)
          ·
            refine ⟨22337118400903860618429719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238262596276307846596583669 22337118400903860618429719)
            ·
              refine ⟨33505677601355790927644579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22337118400903860618429719 33505677601355790927644579)
              ·
                refine ⟨50258516402033686391466869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33505677601355790927644579 50258516402033686391466869)
                ·
                  refine ⟨4711735912690658099200019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50258516402033686391466869 4711735912690658099200019)
                  ·
                    refine ⟨7067603869035987148800029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4711735912690658099200019 7067603869035987148800029)
                    ·
                      refine ⟨2650351450888495180800011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7067603869035987148800029 2650351450888495180800011)
                      ·
                        rfl

theorem cell23_5161541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_5161541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161541 prefixEnd_5161541 := by exact prefixLift 5161541
  have htrace : WordTrace (prefixWord ++ tailWord_5161541) baseStart_5161541 baseEnd_5161541 := by
    simpa [prefixWord, tailWord_5161541, baseEnd_5161541] using wordTrace_append hprefix tailTrace_5161541
  have hstable : (prefixWord ++ tailWord_5161541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161541).length < 2 ^ (prefixWord ++ tailWord_5161541).sum := by decide
  have hdescent : baseEnd_5161541 < baseStart_5161541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161591 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 2, 4]
def baseStart_5161591 : Nat := 118140960795 + 5161591 * 2 ^ 59
def prefixEnd_5161591 : Nat := 4983230072969 + 3 ^ 40 * 5161591 * 2
def baseEnd_5161591 : Nat := 883459041640406661724927

theorem tailTrace_5161591 : CollatzResearch.WordTrace tailWord_5161591 prefixEnd_5161591 883459041640406661724927 := by
  unfold tailWord_5161591
  simp only [CollatzResearch.WordTrace]
  refine ⟨188258689843444811405756627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125505793228963207603837751 188258689843444811405756627)
  ·
    refine ⟨282388034765167217108634941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188258689843444811405756627 282388034765167217108634941)
    ·
      refine ⟨105895513036937706415738103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282388034765167217108634941 105895513036937706415738103)
      ·
        refine ⟨158843269555406559623607155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105895513036937706415738103 158843269555406559623607155)
        ·
          refine ⟨238264904333109839435410733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158843269555406559623607155 238264904333109839435410733)
          ·
            refine ⟨89349339124916189788279025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238264904333109839435410733 89349339124916189788279025)
            ·
              refine ⟨67012004343687142341209269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89349339124916189788279025 67012004343687142341209269)
              ·
                refine ⟨6282375407220669594488369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67012004343687142341209269 6282375407220669594488369)
                ·
                  refine ⟨4711781555415502195866277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6282375407220669594488369 4711781555415502195866277)
                  ·
                    refine ⟨883459041640406661724927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4711781555415502195866277 883459041640406661724927)
                    ·
                      rfl

theorem cell23_5161591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_5161591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161591 prefixEnd_5161591 := by exact prefixLift 5161591
  have htrace : WordTrace (prefixWord ++ tailWord_5161591) baseStart_5161591 baseEnd_5161591 := by
    simpa [prefixWord, tailWord_5161591, baseEnd_5161591] using wordTrace_append hprefix tailTrace_5161591
  have hstable : (prefixWord ++ tailWord_5161591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161591).length < 2 ^ (prefixWord ++ tailWord_5161591).sum := by decide
  have hdescent : baseEnd_5161591 < baseStart_5161591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161618 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_5161618 : Nat := 118140960795 + 5161618 * 2 ^ 59
def prefixEnd_5161618 : Nat := 4983230072969 + 3 ^ 40 * 5161618 * 2
def baseEnd_5161618 : Nat := 2650390988898891379537157

theorem tailTrace_5161618 : CollatzResearch.WordTrace tailWord_5161618 prefixEnd_5161618 2650390988898891379537157 := by
  unfold tailWord_5161618
  simp only [CollatzResearch.WordTrace]
  refine ⟨47064918653586748754247377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125506449742897996677993005 47064918653586748754247377)
  ·
    refine ⟨35298688990190061565685533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47064918653586748754247377 35298688990190061565685533)
    ·
      refine ⟨13237008371321273087132075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35298688990190061565685533 13237008371321273087132075)
      ·
        refine ⟨19855512556981909630698113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13237008371321273087132075 19855512556981909630698113)
        ·
          refine ⟨14891634417736432223023585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19855512556981909630698113 14891634417736432223023585)
          ·
            refine ⟨11168725813302324167267689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14891634417736432223023585 11168725813302324167267689)
            ·
              refine ⟨8376544359976743125450767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11168725813302324167267689 8376544359976743125450767)
              ·
                refine ⟨12564816539965114688176151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8376544359976743125450767 12564816539965114688176151)
                ·
                  refine ⟨18847224809947672032264227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12564816539965114688176151 18847224809947672032264227)
                  ·
                    refine ⟨28270837214921508048396341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18847224809947672032264227 28270837214921508048396341)
                    ·
                      refine ⟨2650390988898891379537157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28270837214921508048396341 2650390988898891379537157)
                      ·
                        rfl

theorem cell23_5161618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_5161618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161618 prefixEnd_5161618 := by exact prefixLift 5161618
  have htrace : WordTrace (prefixWord ++ tailWord_5161618) baseStart_5161618 baseEnd_5161618 := by
    simpa [prefixWord, tailWord_5161618, baseEnd_5161618] using wordTrace_append hprefix tailTrace_5161618
  have hstable : (prefixWord ++ tailWord_5161618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161618).length < 2 ^ (prefixWord ++ tailWord_5161618).sum := by decide
  have hdescent : baseEnd_5161618 < baseStart_5161618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161632 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 3, 2, 2]
def baseStart_5161632 : Nat := 118140960795 + 5161632 * 2 ^ 59
def prefixEnd_5161632 : Nat := 4983230072969 + 3 ^ 40 * 5161632 * 2
def baseEnd_5161632 : Nat := 2650398177628054324762093

theorem tailTrace_5161632 : CollatzResearch.WordTrace tailWord_5161632 prefixEnd_5161632 2650398177628054324762093 := by
  unfold tailWord_5161632
  simp only [CollatzResearch.WordTrace]
  refine ⟨94130092618148137703999575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125506790157530850271999433 94130092618148137703999575)
  ·
    refine ⟨141195138927222206555999363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94130092618148137703999575 141195138927222206555999363)
    ·
      refine ⟨211792708390833309833999045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141195138927222206555999363 211792708390833309833999045)
      ·
        refine ⟨39711132823281245593874821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211792708390833309833999045 39711132823281245593874821)
        ·
          refine ⟨7445837404365233548851529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39711132823281245593874821 7445837404365233548851529)
          ·
            refine ⟨5584378053273925161638647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7445837404365233548851529 5584378053273925161638647)
            ·
              refine ⟨8376567079910887742457971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584378053273925161638647 8376567079910887742457971)
              ·
                refine ⟨12564850619866331613686957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8376567079910887742457971 12564850619866331613686957)
                ·
                  refine ⟨4711818982449874355132609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12564850619866331613686957 4711818982449874355132609)
                  ·
                    refine ⟨3533864236837405766349457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4711818982449874355132609 3533864236837405766349457)
                    ·
                      refine ⟨2650398177628054324762093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533864236837405766349457 2650398177628054324762093)
                      ·
                        rfl

theorem cell23_5161632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_5161632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161632 prefixEnd_5161632 := by exact prefixLift 5161632
  have htrace : WordTrace (prefixWord ++ tailWord_5161632) baseStart_5161632 baseEnd_5161632 := by
    simpa [prefixWord, tailWord_5161632, baseEnd_5161632] using wordTrace_append hprefix tailTrace_5161632
  have hstable : (prefixWord ++ tailWord_5161632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161632).length < 2 ^ (prefixWord ++ tailWord_5161632).sum := by decide
  have hdescent : baseEnd_5161632 < baseStart_5161632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161642 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5161642 : Nat := 118140960795 + 5161642 * 2 ^ 59
def prefixEnd_5161642 : Nat := 4983230072969 + 3 ^ 40 * 5161642 * 2
def baseEnd_5161642 : Nat := 883467770811533095212349

theorem tailTrace_5161642 : CollatzResearch.WordTrace tailWord_5161642 prefixEnd_5161642 883467770811533095212349 := by
  unfold tailWord_5161642
  simp only [CollatzResearch.WordTrace]
  refine ⟨47065137491565011778965795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125507033310840031410575453 47065137491565011778965795)
  ·
    refine ⟨70597706237347517668448693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47065137491565011778965795 70597706237347517668448693)
    ·
      refine ⟨6618534959751329781417065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70597706237347517668448693 6618534959751329781417065)
      ·
        refine ⟨4963901219813497336062799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6618534959751329781417065 4963901219813497336062799)
        ·
          refine ⟨7445851829720246004094199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963901219813497336062799 7445851829720246004094199)
          ·
            refine ⟨11168777744580369006141299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445851829720246004094199 11168777744580369006141299)
            ·
              refine ⟨16753166616870553509211949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11168777744580369006141299 16753166616870553509211949)
              ·
                refine ⟨6282437481326457565954481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16753166616870553509211949 6282437481326457565954481)
                ·
                  refine ⟨4711828110994843174465861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6282437481326457565954481 4711828110994843174465861)
                  ·
                    refine ⟨883467770811533095212349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4711828110994843174465861 883467770811533095212349)
                    ·
                      rfl

theorem cell23_5161642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5161642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161642 prefixEnd_5161642 := by exact prefixLift 5161642
  have htrace : WordTrace (prefixWord ++ tailWord_5161642) baseStart_5161642 baseEnd_5161642 := by
    simpa [prefixWord, tailWord_5161642, baseEnd_5161642] using wordTrace_append hprefix tailTrace_5161642
  have hstable : (prefixWord ++ tailWord_5161642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161642).length < 2 ^ (prefixWord ++ tailWord_5161642).sum := by decide
  have hdescent : baseEnd_5161642 < baseStart_5161642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161658 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2]
def baseStart_5161658 : Nat := 118140960795 + 5161658 * 2 ^ 59
def prefixEnd_5161658 : Nat := 4983230072969 + 3 ^ 40 * 5161658 * 2
def baseEnd_5161658 : Nat := 2650411528125071223036973

theorem tailTrace_5161658 : CollatzResearch.WordTrace tailWord_5161658 prefixEnd_5161658 2650411528125071223036973 := by
  unfold tailWord_5161658
  simp only [CollatzResearch.WordTrace]
  refine ⟨47065283383550520462111407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125507422356134721232297085 47065283383550520462111407)
  ·
    refine ⟨70597925075325780693167111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47065283383550520462111407 70597925075325780693167111)
    ·
      refine ⟨105896887612988671039750667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70597925075325780693167111 105896887612988671039750667)
      ·
        refine ⟨158845331419483006559626001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105896887612988671039750667 158845331419483006559626001)
        ·
          refine ⟨119133998564612254919719501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158845331419483006559626001 119133998564612254919719501)
          ·
            refine ⟨44675249461729595594894813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119133998564612254919719501 44675249461729595594894813)
            ·
              refine ⟨16753218548148598348085555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44675249461729595594894813 16753218548148598348085555)
              ·
                refine ⟨25129827822222897522128333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16753218548148598348085555 25129827822222897522128333)
                ·
                  refine ⟨9423685433333586570798125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25129827822222897522128333 9423685433333586570798125)
                  ·
                    refine ⟨3533882037500094964049297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9423685433333586570798125 3533882037500094964049297)
                    ·
                      refine ⟨2650411528125071223036973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533882037500094964049297 2650411528125071223036973)
                      ·
                        rfl

theorem cell23_5161658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_5161658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161658 prefixEnd_5161658 := by exact prefixLift 5161658
  have htrace : WordTrace (prefixWord ++ tailWord_5161658) baseStart_5161658 baseEnd_5161658 := by
    simpa [prefixWord, tailWord_5161658, baseEnd_5161658] using wordTrace_append hprefix tailTrace_5161658
  have hstable : (prefixWord ++ tailWord_5161658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161658).length < 2 ^ (prefixWord ++ tailWord_5161658).sum := by decide
  have hdescent : baseEnd_5161658 < baseStart_5161658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161682 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_5161682 : Nat := 118140960795 + 5161682 * 2 ^ 59
def prefixEnd_5161682 : Nat := 4983230072969 + 3 ^ 40 * 5161682 * 2
def baseEnd_5161682 : Nat := 2650423851660779129136863

theorem tailTrace_5161682 : CollatzResearch.WordTrace tailWord_5161682 prefixEnd_5161682 2650423851660779129136863 := by
  unfold tailWord_5161682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47065502221528783486829825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125508005924076755964879533 47065502221528783486829825)
  ·
    refine ⟨35299126666146587615122369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47065502221528783486829825 35299126666146587615122369)
    ·
      refine ⟨26474344999609940711341777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35299126666146587615122369 26474344999609940711341777)
      ·
        refine ⟨19855758749707455533506333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26474344999609940711341777 19855758749707455533506333)
        ·
          refine ⟨7445909531140295825064875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19855758749707455533506333 7445909531140295825064875)
          ·
            refine ⟨11168864296710443737597313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7445909531140295825064875 11168864296710443737597313)
            ·
              refine ⟨8376648222532832803197985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11168864296710443737597313 8376648222532832803197985)
              ·
                refine ⟨6282486166899624602398489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8376648222532832803197985 6282486166899624602398489)
                ·
                  refine ⟨4711864625174718451798867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6282486166899624602398489 4711864625174718451798867)
                  ·
                    refine ⟨7067796937762077677698301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4711864625174718451798867 7067796937762077677698301)
                    ·
                      refine ⟨2650423851660779129136863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7067796937762077677698301 2650423851660779129136863)
                      ·
                        rfl

theorem cell23_5161682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_5161682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161682 prefixEnd_5161682 := by exact prefixLift 5161682
  have htrace : WordTrace (prefixWord ++ tailWord_5161682) baseStart_5161682 baseEnd_5161682 := by
    simpa [prefixWord, tailWord_5161682, baseEnd_5161682] using wordTrace_append hprefix tailTrace_5161682
  have hstable : (prefixWord ++ tailWord_5161682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161682).length < 2 ^ (prefixWord ++ tailWord_5161682).sum := by decide
  have hdescent : baseEnd_5161682 < baseStart_5161682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161701 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_5161701 : Nat := 118140960795 + 5161701 * 2 ^ 59
def prefixEnd_5161701 : Nat := 4983230072969 + 3 ^ 40 * 5161701 * 2
def baseEnd_5161701 : Nat := 2650433607793214554799275

theorem tailTrace_5161701 : CollatzResearch.WordTrace tailWord_5161701 prefixEnd_5161701 2650433607793214554799275 := by
  unfold tailWord_5161701
  simp only [CollatzResearch.WordTrace]
  refine ⟨188262701873046300192260957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125508467915364200128173971 188262701873046300192260957)
  ·
    refine ⟨70598513202392362572097859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188262701873046300192260957 70598513202392362572097859)
    ·
      refine ⟨105897769803588543858146789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70598513202392362572097859 105897769803588543858146789)
      ·
        refine ⟨19855831838172851973402523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105897769803588543858146789 19855831838172851973402523)
        ·
          refine ⟨29783747757259277960103785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19855831838172851973402523 29783747757259277960103785)
          ·
            refine ⟨22337810817944458470077839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29783747757259277960103785 22337810817944458470077839)
            ·
              refine ⟨33506716226916687705116759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22337810817944458470077839 33506716226916687705116759)
              ·
                refine ⟨50260074340375031557675139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33506716226916687705116759 50260074340375031557675139)
                ·
                  refine ⟨75390111510562547336512709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50260074340375031557675139 75390111510562547336512709)
                  ·
                    refine ⟨14135645908230477625596133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75390111510562547336512709 14135645908230477625596133)
                    ·
                      refine ⟨2650433607793214554799275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14135645908230477625596133 2650433607793214554799275)
                      ·
                        rfl

theorem cell23_5161701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_5161701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161701 prefixEnd_5161701 := by exact prefixLift 5161701
  have htrace : WordTrace (prefixWord ++ tailWord_5161701) baseStart_5161701 baseEnd_5161701 := by
    simpa [prefixWord, tailWord_5161701, baseEnd_5161701] using wordTrace_append hprefix tailTrace_5161701
  have hstable : (prefixWord ++ tailWord_5161701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161701).length < 2 ^ (prefixWord ++ tailWord_5161701).sum := by decide
  have hdescent : baseEnd_5161701 < baseStart_5161701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161705 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 2, 2, 2]
def baseStart_5161705 : Nat := 118140960795 + 5161705 * 2 ^ 59
def prefixEnd_5161705 : Nat := 4983230072969 + 3 ^ 40 * 5161705 * 2
def baseEnd_5161705 : Nat := 2650435661715832539149257

theorem tailTrace_5161705 : CollatzResearch.WordTrace tailWord_5161705 prefixEnd_5161705 2650435661715832539149257 := by
  unfold tailWord_5161705
  simp only [CollatzResearch.WordTrace]
  refine ⟨188262847765031808875406569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125508565176687872583604379 188262847765031808875406569)
  ·
    refine ⟨141197135823773856656554927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188262847765031808875406569 141197135823773856656554927)
    ·
      refine ⟨211795703735660784984832391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141197135823773856656554927 211795703735660784984832391)
      ·
        refine ⟨317693555603491177477248587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211795703735660784984832391 317693555603491177477248587)
        ·
          refine ⟨476540333405236766215872881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317693555603491177477248587 476540333405236766215872881)
          ·
            refine ⟨357405250053927574661904661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476540333405236766215872881 357405250053927574661904661)
            ·
              refine ⟨16753371096277855062276781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 357405250053927574661904661 16753371096277855062276781)
              ·
                refine ⟨6282514161104195648353793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16753371096277855062276781 6282514161104195648353793)
                ·
                  refine ⟨4711885620828146736265345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6282514161104195648353793 4711885620828146736265345)
                  ·
                    refine ⟨3533914215621110052199009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4711885620828146736265345 3533914215621110052199009)
                    ·
                      refine ⟨2650435661715832539149257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3533914215621110052199009 2650435661715832539149257)
                      ·
                        rfl

theorem cell23_5161705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 2, 2].length) (baseStart_5161705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161705 prefixEnd_5161705 := by exact prefixLift 5161705
  have htrace : WordTrace (prefixWord ++ tailWord_5161705) baseStart_5161705 baseEnd_5161705 := by
    simpa [prefixWord, tailWord_5161705, baseEnd_5161705] using wordTrace_append hprefix tailTrace_5161705
  have hstable : (prefixWord ++ tailWord_5161705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161705).length < 2 ^ (prefixWord ++ tailWord_5161705).sum := by decide
  have hdescent : baseEnd_5161705 < baseStart_5161705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161711 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 7]
def baseStart_5161711 : Nat := 118140960795 + 5161711 * 2 ^ 59
def prefixEnd_5161711 : Nat := 4983230072969 + 3 ^ 40 * 5161711 * 2
def baseEnd_5161711 : Nat := 294493193622195501741581

theorem tailTrace_5161711 : CollatzResearch.WordTrace tailWord_5161711 prefixEnd_5161711 294493193622195501741581 := by
  unfold tailWord_5161711
  simp only [CollatzResearch.WordTrace]
  refine ⟨188263066603010071900124987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125508711068673381266749991 188263066603010071900124987)
  ·
    refine ⟨282394599904515107850187481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188263066603010071900124987 282394599904515107850187481)
    ·
      refine ⟨211795949928386330887640611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282394599904515107850187481 211795949928386330887640611)
      ·
        refine ⟨317693924892579496331460917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211795949928386330887640611 317693924892579496331460917)
        ·
          refine ⟨29783805458679327781074461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 317693924892579496331460917 29783805458679327781074461)
          ·
            refine ⟨11168927047004747917902923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29783805458679327781074461 11168927047004747917902923)
            ·
              refine ⟨16753390570507121876854385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11168927047004747917902923 16753390570507121876854385)
              ·
                refine ⟨12565042927880341407640789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16753390570507121876854385 12565042927880341407640789)
                ·
                  refine ⟨294493193622195501741581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12565042927880341407640789 294493193622195501741581)
                  ·
                    rfl

theorem cell23_5161711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 7].length) (baseStart_5161711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161711 prefixEnd_5161711 := by exact prefixLift 5161711
  have htrace : WordTrace (prefixWord ++ tailWord_5161711) baseStart_5161711 baseEnd_5161711 := by
    simpa [prefixWord, tailWord_5161711, baseEnd_5161711] using wordTrace_append hprefix tailTrace_5161711
  have hstable : (prefixWord ++ tailWord_5161711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161711).length < 2 ^ (prefixWord ++ tailWord_5161711).sum := by decide
  have hdescent : baseEnd_5161711 < baseStart_5161711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161761 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5161761 : Nat := 118140960795 + 5161761 * 2 ^ 59
def prefixEnd_5161761 : Nat := 4983230072969 + 3 ^ 40 * 5161761 * 2
def baseEnd_5161761 : Nat := 2650464416632484320048999

theorem tailTrace_5161761 : CollatzResearch.WordTrace tailWord_5161761 prefixEnd_5161761 2650464416632484320048999 := by
  unfold tailWord_5161761
  simp only [CollatzResearch.WordTrace]
  refine ⟨188264890252828930439445137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125509926835219286959630091 188264890252828930439445137)
  ·
    refine ⟨141198667689621697829583853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188264890252828930439445137 141198667689621697829583853)
    ·
      refine ⟨52949500383608136686093945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141198667689621697829583853 52949500383608136686093945)
      ·
        refine ⟨39712125287706102514570459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52949500383608136686093945 39712125287706102514570459)
        ·
          refine ⟨59568187931559153771855689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39712125287706102514570459 59568187931559153771855689)
          ·
            refine ⟨44676140948669365328891767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59568187931559153771855689 44676140948669365328891767)
            ·
              refine ⟨67014211423004047993337651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44676140948669365328891767 67014211423004047993337651)
              ·
                refine ⟨100521317134506071990006477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67014211423004047993337651 100521317134506071990006477)
                ·
                  refine ⟨37695493925439776996252429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100521317134506071990006477 37695493925439776996252429)
                  ·
                    refine ⟨14135810222039916373594661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37695493925439776996252429 14135810222039916373594661)
                    ·
                      refine ⟨2650464416632484320048999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14135810222039916373594661 2650464416632484320048999)
                      ·
                        rfl

theorem cell23_5161761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5161761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161761 prefixEnd_5161761 := by exact prefixLift 5161761
  have htrace : WordTrace (prefixWord ++ tailWord_5161761) baseStart_5161761 baseEnd_5161761 := by
    simpa [prefixWord, tailWord_5161761, baseEnd_5161761] using wordTrace_append hprefix tailTrace_5161761
  have hstable : (prefixWord ++ tailWord_5161761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161761).length < 2 ^ (prefixWord ++ tailWord_5161761).sum := by decide
  have hdescent : baseEnd_5161761 < baseStart_5161761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161778 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_5161778 : Nat := 118140960795 + 5161778 * 2 ^ 59
def prefixEnd_5161778 : Nat := 4983230072969 + 3 ^ 40 * 5161778 * 2
def baseEnd_5161778 : Nat := 2650473145803610753536421

theorem tailTrace_5161778 : CollatzResearch.WordTrace tailWord_5161778 prefixEnd_5161778 2650473145803610753536421 := by
  unfold tailWord_5161778
  simp only [CollatzResearch.WordTrace]
  refine ⟨47066377573441835585703497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125510340195844894895209325 47066377573441835585703497)
  ·
    refine ⟨35299783180081376689277623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47066377573441835585703497 35299783180081376689277623)
    ·
      refine ⟨52949674770122065033916435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35299783180081376689277623 52949674770122065033916435)
      ·
        refine ⟨79424512155183097550874653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52949674770122065033916435 79424512155183097550874653)
        ·
          refine ⟨29784192058193661581577995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79424512155183097550874653 29784192058193661581577995)
          ·
            refine ⟨44676288087290492372366993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29784192058193661581577995 44676288087290492372366993)
            ·
              refine ⟨33507216065467869279275245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44676288087290492372366993 33507216065467869279275245)
              ·
                refine ⟨12565206024550450979728217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33507216065467869279275245 12565206024550450979728217)
                ·
                  refine ⟨9423904518412838234796163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12565206024550450979728217 9423904518412838234796163)
                  ·
                    refine ⟨14135856777619257352194245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9423904518412838234796163 14135856777619257352194245)
                    ·
                      refine ⟨2650473145803610753536421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14135856777619257352194245 2650473145803610753536421)
                      ·
                        rfl

theorem cell23_5161778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_5161778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161778 prefixEnd_5161778 := by exact prefixLift 5161778
  have htrace : WordTrace (prefixWord ++ tailWord_5161778) baseStart_5161778 baseEnd_5161778 := by
    simpa [prefixWord, tailWord_5161778, baseEnd_5161778] using wordTrace_append hprefix tailTrace_5161778
  have hstable : (prefixWord ++ tailWord_5161778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161778).length < 2 ^ (prefixWord ++ tailWord_5161778).sum := by decide
  have hdescent : baseEnd_5161778 < baseStart_5161778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161801 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 8]
def baseStart_5161801 : Nat := 118140960795 + 5161801 * 2 ^ 59
def prefixEnd_5161801 : Nat := 4983230072969 + 3 ^ 40 * 5161801 * 2
def baseEnd_5161801 : Nat := 294498328428740462616535

theorem tailTrace_5161801 : CollatzResearch.WordTrace tailWord_5161801 prefixEnd_5161801 294498328428740462616535 := by
  unfold tailWord_5161801
  simp only [CollatzResearch.WordTrace]
  refine ⟨188266349172684017270901257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125510899448456011513934171 188266349172684017270901257)
  ·
    refine ⟨141199761879513012953175943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188266349172684017270901257 141199761879513012953175943)
    ·
      refine ⟨211799642819269519429763915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141199761879513012953175943 211799642819269519429763915)
      ·
        refine ⟨317699464228904279144645873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211799642819269519429763915 317699464228904279144645873)
        ·
          refine ⟨238274598171678209358484405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317699464228904279144645873 238274598171678209358484405)
          ·
            refine ⟨22338243578594832127357913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238274598171678209358484405 22338243578594832127357913)
            ·
              refine ⟨16753682683946124095518435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22338243578594832127357913 16753682683946124095518435)
              ·
                refine ⟨25130524025919186143277653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16753682683946124095518435 25130524025919186143277653)
                ·
                  refine ⟨294498328428740462616535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25130524025919186143277653 294498328428740462616535)
                  ·
                    rfl

theorem cell23_5161801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_5161801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161801 prefixEnd_5161801 := by exact prefixLift 5161801
  have htrace : WordTrace (prefixWord ++ tailWord_5161801) baseStart_5161801 baseEnd_5161801 := by
    simpa [prefixWord, tailWord_5161801, baseEnd_5161801] using wordTrace_append hprefix tailTrace_5161801
  have hstable : (prefixWord ++ tailWord_5161801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161801).length < 2 ^ (prefixWord ++ tailWord_5161801).sum := by decide
  have hdescent : baseEnd_5161801 < baseStart_5161801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161818 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 6]
def baseStart_5161818 : Nat := 118140960795 + 5161818 * 2 ^ 59
def prefixEnd_5161818 : Nat := 4983230072969 + 3 ^ 40 * 5161818 * 2
def baseEnd_5161818 : Nat := 294499298336643399670693

theorem tailTrace_5161818 : CollatzResearch.WordTrace tailWord_5161818 prefixEnd_5161818 294499298336643399670693 := by
  unfold tailWord_5161818
  simp only [CollatzResearch.WordTrace]
  refine ⟨47066742303405607293567527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125511312809081619449513405 47066742303405607293567527)
  ·
    refine ⟨70600113455108410940351291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47066742303405607293567527 70600113455108410940351291)
    ·
      refine ⟨105900170182662616410526937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70600113455108410940351291 105900170182662616410526937)
      ·
        refine ⟨79425127636996962307895203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105900170182662616410526937 79425127636996962307895203)
        ·
          refine ⟨119137691455495443461842805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79425127636996962307895203 119137691455495443461842805)
          ·
            refine ⟨11169158573952697824547763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119137691455495443461842805 11169158573952697824547763)
            ·
              refine ⟨16753737860929046736821645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11169158573952697824547763 16753737860929046736821645)
              ·
                refine ⟨6282651697848392526308117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16753737860929046736821645 6282651697848392526308117)
                ·
                  refine ⟨294499298336643399670693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6282651697848392526308117 294499298336643399670693)
                  ·
                    rfl

theorem cell23_5161818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_5161818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161818 prefixEnd_5161818 := by exact prefixLift 5161818
  have htrace : WordTrace (prefixWord ++ tailWord_5161818) baseStart_5161818 baseEnd_5161818 := by
    simpa [prefixWord, tailWord_5161818, baseEnd_5161818] using wordTrace_append hprefix tailTrace_5161818
  have hstable : (prefixWord ++ tailWord_5161818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161818).length < 2 ^ (prefixWord ++ tailWord_5161818).sum := by decide
  have hdescent : baseEnd_5161818 < baseStart_5161818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161855 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 2, 3, 2]
def baseStart_5161855 : Nat := 118140960795 + 5161855 * 2 ^ 59
def prefixEnd_5161855 : Nat := 4983230072969 + 3 ^ 40 * 5161855 * 2
def baseEnd_5161855 : Nat := 2650512683814006952273567

theorem tailTrace_5161855 : CollatzResearch.WordTrace tailWord_5161855 prefixEnd_5161855 2650512683814006952273567 := by
  unfold tailWord_5161855
  simp only [CollatzResearch.WordTrace]
  refine ⟨188268318714488384493367019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125512212476325589662244679 188268318714488384493367019)
  ·
    refine ⟨282402478071732576740050529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188268318714488384493367019 282402478071732576740050529)
    ·
      refine ⟨211801858553799432555037897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282402478071732576740050529 211801858553799432555037897)
      ·
        refine ⟨158851393915349574416278423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211801858553799432555037897 158851393915349574416278423)
        ·
          refine ⟨238277090873024361624417635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158851393915349574416278423 238277090873024361624417635)
          ·
            refine ⟨357415636309536542436626453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238277090873024361624417635 357415636309536542436626453)
            ·
              refine ⟨16753857952009525426716865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 357415636309536542436626453 16753857952009525426716865)
              ·
                refine ⟨12565393464007144070037649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16753857952009525426716865 12565393464007144070037649)
                ·
                  refine ⟨9424045098005358052528237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12565393464007144070037649 9424045098005358052528237)
                  ·
                    refine ⟨3534016911752009269698089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9424045098005358052528237 3534016911752009269698089)
                    ·
                      refine ⟨2650512683814006952273567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534016911752009269698089 2650512683814006952273567)
                      ·
                        rfl

theorem cell23_5161855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_5161855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161855 prefixEnd_5161855 := by exact prefixLift 5161855
  have htrace : WordTrace (prefixWord ++ tailWord_5161855) baseStart_5161855 baseEnd_5161855 := by
    simpa [prefixWord, tailWord_5161855, baseEnd_5161855] using wordTrace_append hprefix tailTrace_5161855
  have hstable : (prefixWord ++ tailWord_5161855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161855).length < 2 ^ (prefixWord ++ tailWord_5161855).sum := by decide
  have hdescent : baseEnd_5161855 < baseStart_5161855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161868 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_5161868 : Nat := 118140960795 + 5161868 * 2 ^ 59
def prefixEnd_5161868 : Nat := 4983230072969 + 3 ^ 40 * 5161868 * 2
def baseEnd_5161868 : Nat := 2650519359062515401411007

theorem tailTrace_5161868 : CollatzResearch.WordTrace tailWord_5161868 prefixEnd_5161868 2650519359062515401411007 := by
  unfold tailWord_5161868
  simp only [CollatzResearch.WordTrace]
  refine ⟨94134396431720643856795129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125512528575627525142393505 94134396431720643856795129)
  ·
    refine ⟨70600797323790482892596347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94134396431720643856795129 70600797323790482892596347)
    ·
      refine ⟨105901195985685724338894521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70600797323790482892596347 105901195985685724338894521)
      ·
        refine ⟨79425896989264293254170891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105901195985685724338894521 79425896989264293254170891)
        ·
          refine ⟨119138845483896439881256337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79425896989264293254170891 119138845483896439881256337)
          ·
            refine ⟨89354134112922329910942253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119138845483896439881256337 89354134112922329910942253)
            ·
              refine ⟨33507800292345873716603345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89354134112922329910942253 33507800292345873716603345)
              ·
                refine ⟨25130850219259405287452509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33507800292345873716603345 25130850219259405287452509)
                ·
                  refine ⟨9424068832222276982794691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25130850219259405287452509 9424068832222276982794691)
                  ·
                    refine ⟨14136103248333415474192037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9424068832222276982794691 14136103248333415474192037)
                    ·
                      refine ⟨2650519359062515401411007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14136103248333415474192037 2650519359062515401411007)
                      ·
                        rfl

theorem cell23_5161868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_5161868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161868 prefixEnd_5161868 := by exact prefixLift 5161868
  have htrace : WordTrace (prefixWord ++ tailWord_5161868) baseStart_5161868 baseEnd_5161868 := by
    simpa [prefixWord, tailWord_5161868, baseEnd_5161868] using wordTrace_append hprefix tailTrace_5161868
  have hstable : (prefixWord ++ tailWord_5161868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161868).length < 2 ^ (prefixWord ++ tailWord_5161868).sum := by decide
  have hdescent : baseEnd_5161868 < baseStart_5161868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161885 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_5161885 : Nat := 118140960795 + 5161885 * 2 ^ 59
def prefixEnd_5161885 : Nat := 4983230072969 + 3 ^ 40 * 5161885 * 2
def baseEnd_5161885 : Nat := 2650528088233641834898429

theorem tailTrace_5161885 : CollatzResearch.WordTrace tailWord_5161885 prefixEnd_5161885 2650528088233641834898429 := by
  unfold tailWord_5161885
  simp only [CollatzResearch.WordTrace]
  refine ⟨188269412904379699616959109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125512941936253133077972739 188269412904379699616959109)
  ·
    refine ⟨35300514919571193678179833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188269412904379699616959109 35300514919571193678179833)
    ·
      refine ⟨26475386189678395258634875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35300514919571193678179833 26475386189678395258634875)
      ·
        refine ⟨39713079284517592887952313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26475386189678395258634875 39713079284517592887952313)
        ·
          refine ⟨29784809463388194665964235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39713079284517592887952313 29784809463388194665964235)
          ·
            refine ⟨44677214195082291998946353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29784809463388194665964235 44677214195082291998946353)
            ·
              refine ⟨33507910646311718999209765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44677214195082291998946353 33507910646311718999209765)
              ·
                refine ⟨6282733246183447312351831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33507910646311718999209765 6282733246183447312351831)
                ·
                  refine ⟨9424099869275170968527747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6282733246183447312351831 9424099869275170968527747)
                  ·
                    refine ⟨14136149803912756452791621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9424099869275170968527747 14136149803912756452791621)
                    ·
                      refine ⟨2650528088233641834898429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14136149803912756452791621 2650528088233641834898429)
                      ·
                        rfl

theorem cell23_5161885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_5161885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161885 prefixEnd_5161885 := by exact prefixLift 5161885
  have htrace : WordTrace (prefixWord ++ tailWord_5161885) baseStart_5161885 baseEnd_5161885 := by
    simpa [prefixWord, tailWord_5161885, baseEnd_5161885] using wordTrace_append hprefix tailTrace_5161885
  have hstable : (prefixWord ++ tailWord_5161885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161885).length < 2 ^ (prefixWord ++ tailWord_5161885).sum := by decide
  have hdescent : baseEnd_5161885 < baseStart_5161885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161889 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5161889 : Nat := 118140960795 + 5161889 * 2 ^ 59
def prefixEnd_5161889 : Nat := 4983230072969 + 3 ^ 40 * 5161889 * 2
def baseEnd_5161889 : Nat := 2650530142156259819248411

theorem tailTrace_5161889 : CollatzResearch.WordTrace tailWord_5161889 prefixEnd_5161889 2650530142156259819248411 := by
  unfold tailWord_5161889
  simp only [CollatzResearch.WordTrace]
  refine ⟨188269558796365208300104721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125513039197576805533403147 188269558796365208300104721)
  ·
    refine ⟨141202169097273906225078541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188269558796365208300104721 141202169097273906225078541)
    ·
      refine ⟨52950813411477714834404453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141202169097273906225078541 52950813411477714834404453)
      ·
        refine ⟨9928277514652071531450835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52950813411477714834404453 9928277514652071531450835)
        ·
          refine ⟨14892416271978107297176253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9928277514652071531450835 14892416271978107297176253)
          ·
            refine ⟨5584656101991790236441095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14892416271978107297176253 5584656101991790236441095)
            ·
              refine ⟨8376984152987685354661643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584656101991790236441095 8376984152987685354661643)
              ·
                refine ⟨12565476229481528031992465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8376984152987685354661643 12565476229481528031992465)
                ·
                  refine ⟨9424107172111146023994349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12565476229481528031992465 9424107172111146023994349)
                  ·
                    refine ⟨3534040189541679758997881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9424107172111146023994349 3534040189541679758997881)
                    ·
                      refine ⟨2650530142156259819248411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534040189541679758997881 2650530142156259819248411)
                      ·
                        rfl

theorem cell23_5161889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5161889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161889 prefixEnd_5161889 := by exact prefixLift 5161889
  have htrace : WordTrace (prefixWord ++ tailWord_5161889) baseStart_5161889 baseEnd_5161889 := by
    simpa [prefixWord, tailWord_5161889, baseEnd_5161889] using wordTrace_append hprefix tailTrace_5161889
  have hstable : (prefixWord ++ tailWord_5161889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161889).length < 2 ^ (prefixWord ++ tailWord_5161889).sum := by decide
  have hdescent : baseEnd_5161889 < baseStart_5161889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161891 : List Nat := [1, 1, 1, 4, 1, 2, 2, 11]
def baseStart_5161891 : Nat := 118140960795 + 5161891 * 2 ^ 59
def prefixEnd_5161891 : Nat := 4983230072969 + 3 ^ 40 * 5161891 * 2
def baseEnd_5161891 : Nat := 98167821078428474497163

theorem tailTrace_5161891 : CollatzResearch.WordTrace tailWord_5161891 prefixEnd_5161891 98167821078428474497163 := by
  unfold tailWord_5161891
  simp only [CollatzResearch.WordTrace]
  refine ⟨188269631742357962641677527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125513087828238641761118351 188269631742357962641677527)
  ·
    refine ⟨282404447613536943962516291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188269631742357962641677527 282404447613536943962516291)
    ·
      refine ⟨423606671420305415943774437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282404447613536943962516291 423606671420305415943774437)
      ·
        refine ⟨79426250891307265489457707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 423606671420305415943774437 79426250891307265489457707)
        ·
          refine ⟨119139376336960898234186561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79426250891307265489457707 119139376336960898234186561)
          ·
            refine ⟨89354532252720673675639921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119139376336960898234186561 89354532252720673675639921)
            ·
              refine ⟨67015899189540505256729941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89354532252720673675639921 67015899189540505256729941)
              ·
                refine ⟨98167821078428474497163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 67015899189540505256729941 98167821078428474497163)
                ·
                  rfl

theorem cell23_5161891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 11].length) (baseStart_5161891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161891 prefixEnd_5161891 := by exact prefixLift 5161891
  have htrace : WordTrace (prefixWord ++ tailWord_5161891) baseStart_5161891 baseEnd_5161891 := by
    simpa [prefixWord, tailWord_5161891, baseEnd_5161891] using wordTrace_append hprefix tailTrace_5161891
  have hstable : (prefixWord ++ tailWord_5161891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161891).length < 2 ^ (prefixWord ++ tailWord_5161891).sum := by decide
  have hdescent : baseEnd_5161891 < baseStart_5161891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161912 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 2, 4]
def baseStart_5161912 : Nat := 118140960795 + 5161912 * 2 ^ 59
def prefixEnd_5161912 : Nat := 4983230072969 + 3 ^ 40 * 5161912 * 2
def baseEnd_5161912 : Nat := 883513984070437743086935

theorem tailTrace_5161912 : CollatzResearch.WordTrace tailWord_5161912 prefixEnd_5161912 883513984070437743086935 := by
  unfold tailWord_5161912
  simp only [CollatzResearch.WordTrace]
  refine ⟨94135198837640941614095995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125513598450187922152127993 94135198837640941614095995)
  ·
    refine ⟨141202798256461412421143993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94135198837640941614095995 141202798256461412421143993)
    ·
      refine ⟨105902098692346059315857995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141202798256461412421143993 105902098692346059315857995)
      ·
        refine ⟨158853148038519088973786993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105902098692346059315857995 158853148038519088973786993)
        ·
          refine ⟨119139861028889316730340245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158853148038519088973786993 119139861028889316730340245)
          ·
            refine ⟨5584680985729186721734699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119139861028889316730340245 5584680985729186721734699)
            ·
              refine ⟨8377021478593780082602049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584680985729186721734699 8377021478593780082602049)
              ·
                refine ⟨6282766108945335061951537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8377021478593780082602049 6282766108945335061951537)
                ·
                  refine ⟨4712074581709001296463653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6282766108945335061951537 4712074581709001296463653)
                  ·
                    refine ⟨883513984070437743086935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712074581709001296463653 883513984070437743086935)
                    ·
                      rfl

theorem cell23_5161912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_5161912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161912 prefixEnd_5161912 := by exact prefixLift 5161912
  have htrace : WordTrace (prefixWord ++ tailWord_5161912) baseStart_5161912 baseEnd_5161912 := by
    simpa [prefixWord, tailWord_5161912, baseEnd_5161912] using wordTrace_append hprefix tailTrace_5161912
  have hstable : (prefixWord ++ tailWord_5161912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161912).length < 2 ^ (prefixWord ++ tailWord_5161912).sum := by decide
  have hdescent : baseEnd_5161912 < baseStart_5161912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161935 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 3]
def baseStart_5161935 : Nat := 118140960795 + 5161935 * 2 ^ 59
def prefixEnd_5161935 : Nat := 4983230072969 + 3 ^ 40 * 5161935 * 2
def baseEnd_5161935 : Nat := 2650553762266366639273199

theorem tailTrace_5161935 : CollatzResearch.WordTrace tailWord_5161935 prefixEnd_5161935 2650553762266366639273199 := by
  unfold tailWord_5161935
  simp only [CollatzResearch.WordTrace]
  refine ⟨188271236554198558156279259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125514157702799038770852839 188271236554198558156279259)
  ·
    refine ⟨282406854831297837234418889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188271236554198558156279259 282406854831297837234418889)
    ·
      refine ⟨211805141123473377925814167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282406854831297837234418889 211805141123473377925814167)
      ·
        refine ⟨317707711685210066888721251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211805141123473377925814167 317707711685210066888721251)
        ·
          refine ⟨476561567527815100333081877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317707711685210066888721251 476561567527815100333081877)
          ·
            refine ⟨22338823477866332828113213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 476561567527815100333081877 22338823477866332828113213)
            ·
              refine ⟨8377058804199874810542455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22338823477866332828113213 8377058804199874810542455)
              ·
                refine ⟨12565588206299812215813683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377058804199874810542455 12565588206299812215813683)
                ·
                  refine ⟨18848382309449718323720525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12565588206299812215813683 18848382309449718323720525)
                  ·
                    refine ⟨7068143366043644371395197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18848382309449718323720525 7068143366043644371395197)
                    ·
                      refine ⟨2650553762266366639273199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7068143366043644371395197 2650553762266366639273199)
                      ·
                        rfl

theorem cell23_5161935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_5161935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161935 prefixEnd_5161935 := by exact prefixLift 5161935
  have htrace : WordTrace (prefixWord ++ tailWord_5161935) baseStart_5161935 baseEnd_5161935 := by
    simpa [prefixWord, tailWord_5161935, baseEnd_5161935] using wordTrace_append hprefix tailTrace_5161935
  have hstable : (prefixWord ++ tailWord_5161935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161935).length < 2 ^ (prefixWord ++ tailWord_5161935).sum := by decide
  have hdescent : baseEnd_5161935 < baseStart_5161935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161942 : List Nat := [5, 2, 1, 1, 2, 1, 4, 7]
def baseStart_5161942 : Nat := 118140960795 + 5161942 * 2 ^ 59
def prefixEnd_5161942 : Nat := 4983230072969 + 3 ^ 40 * 5161942 * 2
def baseEnd_5161942 : Nat := 98168790986331411551321

theorem tailTrace_5161942 : CollatzResearch.WordTrace tailWord_5161942 prefixEnd_5161942 98168790986331411551321 := by
  unfold tailWord_5161942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766968241573324896986505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125514327910115465567856053 11766968241573324896986505)
  ·
    refine ⟨8825226181179993672739879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11766968241573324896986505 8825226181179993672739879)
    ·
      refine ⟨13237839271769990509109819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8825226181179993672739879 13237839271769990509109819)
      ·
        refine ⟨19856758907654985763664729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13237839271769990509109819 19856758907654985763664729)
        ·
          refine ⟨14892569180741239322748547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19856758907654985763664729 14892569180741239322748547)
          ·
            refine ⟨22338853771111858984122821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14892569180741239322748547 22338853771111858984122821)
            ·
              refine ⟨4188535082083473559523029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22338853771111858984122821 4188535082083473559523029)
              ·
                refine ⟨98168790986331411551321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4188535082083473559523029 98168790986331411551321)
                ·
                  rfl

theorem cell23_5161942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_5161942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161942 prefixEnd_5161942 := by exact prefixLift 5161942
  have htrace : WordTrace (prefixWord ++ tailWord_5161942) baseStart_5161942 baseEnd_5161942 := by
    simpa [prefixWord, tailWord_5161942, baseEnd_5161942] using wordTrace_append hprefix tailTrace_5161942
  have hstable : (prefixWord ++ tailWord_5161942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161942).length < 2 ^ (prefixWord ++ tailWord_5161942).sum := by decide
  have hdescent : baseEnd_5161942 < baseStart_5161942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5161970 : List Nat := [3, 2, 1, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5161970 : Nat := 118140960795 + 5161970 * 2 ^ 59
def prefixEnd_5161970 : Nat := 4983230072969 + 3 ^ 40 * 5161970 * 2
def baseEnd_5161970 : Nat := 2650571734089274002335539

theorem tailTrace_5161970 : CollatzResearch.WordTrace tailWord_5161970 prefixEnd_5161970 2650571734089274002335539 := by
  unfold tailWord_5161970
  simp only [CollatzResearch.WordTrace]
  refine ⟨47068128277267939783450841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125515008739381172755868909 47068128277267939783450841)
  ·
    refine ⟨35301096207950954837588131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47068128277267939783450841 35301096207950954837588131)
    ·
      refine ⟨52951644311926432256382197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35301096207950954837588131 52951644311926432256382197)
      ·
        refine ⟨4964216654243103024035831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52951644311926432256382197 4964216654243103024035831)
        ·
          refine ⟨7446324981364654536053747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964216654243103024035831 7446324981364654536053747)
          ·
            refine ⟨11169487472046981804080621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446324981364654536053747 11169487472046981804080621)
            ·
              refine ⟨4188557802017618176530233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11169487472046981804080621 4188557802017618176530233)
              ·
                refine ⟨3141418351513213632397675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4188557802017618176530233 3141418351513213632397675)
                ·
                  refine ⟨4712127527269820448596513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141418351513213632397675 4712127527269820448596513)
                  ·
                    refine ⟨3534095645452365336447385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4712127527269820448596513 3534095645452365336447385)
                    ·
                      refine ⟨2650571734089274002335539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534095645452365336447385 2650571734089274002335539)
                      ·
                        rfl

theorem cell23_5161970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5161970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5161970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5161970 prefixEnd_5161970 := by exact prefixLift 5161970
  have htrace : WordTrace (prefixWord ++ tailWord_5161970) baseStart_5161970 baseEnd_5161970 := by
    simpa [prefixWord, tailWord_5161970, baseEnd_5161970] using wordTrace_append hprefix tailTrace_5161970
  have hstable : (prefixWord ++ tailWord_5161970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5161970).length < 2 ^ (prefixWord ++ tailWord_5161970).sum := by decide
  have hdescent : baseEnd_5161970 < baseStart_5161970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5161970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162092 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_5162092 : Nat := 118140960795 + 5162092 * 2 ^ 59
def prefixEnd_5162092 : Nat := 4983230072969 + 3 ^ 40 * 5162092 * 2
def baseEnd_5162092 : Nat := 883544792909707508336659

theorem tailTrace_5162092 : CollatzResearch.WordTrace tailWord_5162092 prefixEnd_5162092 883544792909707508336659 := by
  unfold tailWord_5162092
  simp only [CollatzResearch.WordTrace]
  refine ⟨94138481407314886984872265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125517975209753182646496353 94138481407314886984872265)
  ·
    refine ⟨70603861055486165238654199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94138481407314886984872265 70603861055486165238654199)
    ·
      refine ⟨105905791583229247857981299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70603861055486165238654199 105905791583229247857981299)
      ·
        refine ⟨158858687374843871786971949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105905791583229247857981299 158858687374843871786971949)
        ·
          refine ⟨59572007765566451920114481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158858687374843871786971949 59572007765566451920114481)
          ·
            refine ⟨44679005824174838940085861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59572007765566451920114481 44679005824174838940085861)
            ·
              refine ⟨8377313592032782301266099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44679005824174838940085861 8377313592032782301266099)
              ·
                refine ⟨12565970388049173451899149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377313592032782301266099 12565970388049173451899149)
                ·
                  refine ⟨4712238895518440044462181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12565970388049173451899149 4712238895518440044462181)
                  ·
                    refine ⟨883544792909707508336659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712238895518440044462181 883544792909707508336659)
                    ·
                      rfl

theorem cell23_5162092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_5162092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162092 prefixEnd_5162092 := by exact prefixLift 5162092
  have htrace : WordTrace (prefixWord ++ tailWord_5162092) baseStart_5162092 baseEnd_5162092 := by
    simpa [prefixWord, tailWord_5162092, baseEnd_5162092] using wordTrace_append hprefix tailTrace_5162092
  have hstable : (prefixWord ++ tailWord_5162092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162092).length < 2 ^ (prefixWord ++ tailWord_5162092).sum := by decide
  have hdescent : baseEnd_5162092 < baseStart_5162092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162102 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5162102 : Nat := 118140960795 + 5162102 * 2 ^ 59
def prefixEnd_5162102 : Nat := 4983230072969 + 3 ^ 40 * 5162102 * 2
def baseEnd_5162102 : Nat := 2650639513535667485884931

theorem tailTrace_5162102 : CollatzResearch.WordTrace tailWord_5162102 prefixEnd_5162102 2650639513535667485884931 := by
  unfold tailWord_5162102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11767332971537096604850535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125518218363062363785072373 11767332971537096604850535)
  ·
    refine ⟨17650999457305644907275803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11767332971537096604850535 17650999457305644907275803)
    ·
      refine ⟨26476499185958467360913705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17650999457305644907275803 26476499185958467360913705)
      ·
        refine ⟨19857374389468850520685279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26476499185958467360913705 19857374389468850520685279)
        ·
          refine ⟨29786061584203275781027919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19857374389468850520685279 29786061584203275781027919)
          ·
            refine ⟨44679092376304913671541879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29786061584203275781027919 44679092376304913671541879)
            ·
              refine ⟨67018638564457370507312819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44679092376304913671541879 67018638564457370507312819)
              ·
                refine ⟨100527957846686055760969229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67018638564457370507312819 100527957846686055760969229)
                ·
                  refine ⟨37697984192507270910363461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100527957846686055760969229 37697984192507270910363461)
                  ·
                    refine ⟨7068372036095113295693149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37697984192507270910363461 7068372036095113295693149)
                    ·
                      refine ⟨2650639513535667485884931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7068372036095113295693149 2650639513535667485884931)
                      ·
                        rfl

theorem cell23_5162102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5162102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162102 prefixEnd_5162102 := by exact prefixLift 5162102
  have htrace : WordTrace (prefixWord ++ tailWord_5162102) baseStart_5162102 baseEnd_5162102 := by
    simpa [prefixWord, tailWord_5162102, baseEnd_5162102] using wordTrace_append hprefix tailTrace_5162102
  have hstable : (prefixWord ++ tailWord_5162102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162102).length < 2 ^ (prefixWord ++ tailWord_5162102).sum := by decide
  have hdescent : baseEnd_5162102 < baseStart_5162102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162115 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 3]
def baseStart_5162115 : Nat := 118140960795 + 5162115 * 2 ^ 59
def prefixEnd_5162115 : Nat := 4983230072969 + 3 ^ 40 * 5162115 * 2
def baseEnd_5162115 : Nat := 2650646188784175935022371

theorem tailTrace_5162115 : CollatzResearch.WordTrace tailWord_5162115 prefixEnd_5162115 2650646188784175935022371 := by
  unfold tailWord_5162115
  simp only [CollatzResearch.WordTrace]
  refine ⟨188277801693546448897831799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125518534462364299265221199 188277801693546448897831799)
  ·
    refine ⟨282416702540319673346747699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188277801693546448897831799 282416702540319673346747699)
    ·
      refine ⟨423625053810479510020121549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282416702540319673346747699 423625053810479510020121549)
      ·
        refine ⟨158859395178929816257545581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423625053810479510020121549 158859395178929816257545581)
        ·
          refine ⟨59572273192098681096579593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158859395178929816257545581 59572273192098681096579593)
          ·
            refine ⟨44679204894074010822434695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59572273192098681096579593 44679204894074010822434695)
            ·
              refine ⟨67018807341111016233652043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44679204894074010822434695 67018807341111016233652043)
              ·
                refine ⟨100528211011666524350478065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67018807341111016233652043 100528211011666524350478065)
                ·
                  refine ⟨75396158258749893262858549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100528211011666524350478065 75396158258749893262858549)
                  ·
                    refine ⟨7068389836757802493392989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75396158258749893262858549 7068389836757802493392989)
                    ·
                      refine ⟨2650646188784175935022371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7068389836757802493392989 2650646188784175935022371)
                      ·
                        rfl

theorem cell23_5162115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_5162115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162115 prefixEnd_5162115 := by exact prefixLift 5162115
  have htrace : WordTrace (prefixWord ++ tailWord_5162115) baseStart_5162115 baseEnd_5162115 := by
    simpa [prefixWord, tailWord_5162115, baseEnd_5162115] using wordTrace_append hprefix tailTrace_5162115
  have hstable : (prefixWord ++ tailWord_5162115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162115).length < 2 ^ (prefixWord ++ tailWord_5162115).sum := by decide
  have hdescent : baseEnd_5162115 < baseStart_5162115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162126 : List Nat := [4, 1, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_5162126 : Nat := 118140960795 + 5162126 * 2 ^ 59
def prefixEnd_5162126 : Nat := 4983230072969 + 3 ^ 40 * 5162126 * 2
def baseEnd_5162126 : Nat := 883550612357125130661607

theorem tailTrace_5162126 : CollatzResearch.WordTrace tailWord_5162126 prefixEnd_5162126 883550612357125130661607 := by
  unfold tailWord_5162126
  simp only [CollatzResearch.WordTrace]
  refine ⟨23534775362063324722060279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125518801931004398517654821 23534775362063324722060279)
  ·
    refine ⟨35302163043094987083090419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23534775362063324722060279 35302163043094987083090419)
    ·
      refine ⟨52953244564642480624635629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35302163043094987083090419 52953244564642480624635629)
      ·
        refine ⟨19857466711740930234238361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52953244564642480624635629 19857466711740930234238361)
        ·
          refine ⟨14893100033805697675678771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19857466711740930234238361 14893100033805697675678771)
          ·
            refine ⟨22339650050708546513518157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14893100033805697675678771 22339650050708546513518157)
            ·
              refine ⟨8377368769015704942569309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22339650050708546513518157 8377368769015704942569309)
              ·
                refine ⟨3141513288380889353463491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8377368769015704942569309 3141513288380889353463491)
                ·
                  refine ⟨4712269932571334030195237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141513288380889353463491 4712269932571334030195237)
                  ·
                    refine ⟨883550612357125130661607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712269932571334030195237 883550612357125130661607)
                    ·
                      rfl

theorem cell23_5162126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_5162126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162126 prefixEnd_5162126 := by exact prefixLift 5162126
  have htrace : WordTrace (prefixWord ++ tailWord_5162126) baseStart_5162126 baseEnd_5162126 := by
    simpa [prefixWord, tailWord_5162126, baseEnd_5162126] using wordTrace_append hprefix tailTrace_5162126
  have hstable : (prefixWord ++ tailWord_5162126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162126).length < 2 ^ (prefixWord ++ tailWord_5162126).sum := by decide
  have hdescent : baseEnd_5162126 < baseStart_5162126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162143 : List Nat := [1, 1, 2, 6, 2, 1, 3, 2, 1, 4]
def baseStart_5162143 : Nat := 118140960795 + 5162143 * 2 ^ 59
def prefixEnd_5162143 : Nat := 4983230072969 + 3 ^ 40 * 5162143 * 2
def baseEnd_5162143 : Nat := 883553522080833941824081

theorem tailTrace_5162143 : CollatzResearch.WordTrace tailWord_5162143 prefixEnd_5162143 883553522080833941824081 := by
  unfold tailWord_5162143
  simp only [CollatzResearch.WordTrace]
  refine ⟨188278822937445009679851083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125519215291630006453234055 188278822937445009679851083)
  ·
    refine ⟨282418234406167514519776625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188278822937445009679851083 282418234406167514519776625)
    ·
      refine ⟨211813675804625635889832469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282418234406167514519776625 211813675804625635889832469)
      ·
        refine ⟨9928766053341826682335897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 211813675804625635889832469 9928766053341826682335897)
        ·
          refine ⟨7446574540006370011751923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9928766053341826682335897 7446574540006370011751923)
          ·
            refine ⟨11169861810009555017627885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446574540006370011751923 11169861810009555017627885)
            ·
              refine ⟨4188698178753583131610457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11169861810009555017627885 4188698178753583131610457)
              ·
                refine ⟨3141523634065187348707843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4188698178753583131610457 3141523634065187348707843)
                ·
                  refine ⟨4712285451097781023061765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141523634065187348707843 4712285451097781023061765)
                  ·
                    refine ⟨883553522080833941824081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712285451097781023061765 883553522080833941824081)
                    ·
                      rfl

theorem cell23_5162143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 1, 4].length) (baseStart_5162143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162143 prefixEnd_5162143 := by exact prefixLift 5162143
  have htrace : WordTrace (prefixWord ++ tailWord_5162143) baseStart_5162143 baseEnd_5162143 := by
    simpa [prefixWord, tailWord_5162143, baseEnd_5162143] using wordTrace_append hprefix tailTrace_5162143
  have hstable : (prefixWord ++ tailWord_5162143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162143).length < 2 ^ (prefixWord ++ tailWord_5162143).sum := by decide
  have hdescent : baseEnd_5162143 < baseStart_5162143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162149 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_5162149 : Nat := 118140960795 + 5162149 * 2 ^ 59
def prefixEnd_5162149 : Nat := 4983230072969 + 3 ^ 40 * 5162149 * 2
def baseEnd_5162149 : Nat := 2650663647126428801997215

theorem tailTrace_5162149 : CollatzResearch.WordTrace tailWord_5162149 prefixEnd_5162149 2650663647126428801997215 := by
  unfold tailWord_5162149
  simp only [CollatzResearch.WordTrace]
  refine ⟨188279041775423272704569501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125519361183615515136379667 188279041775423272704569501)
  ·
    refine ⟨70604640665783727264213563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188279041775423272704569501 70604640665783727264213563)
    ·
      refine ⟨105906960998675590896320345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70604640665783727264213563 105906960998675590896320345)
      ·
        refine ⟨79430220749006693172240259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105906960998675590896320345 79430220749006693172240259)
        ·
          refine ⟨119145331123510039758360389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79430220749006693172240259 119145331123510039758360389)
          ·
            refine ⟨22339749585658132454692573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119145331123510039758360389 22339749585658132454692573)
            ·
              refine ⟨8377406094621799670509715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22339749585658132454692573 8377406094621799670509715)
              ·
                refine ⟨12566109141932699505764573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377406094621799670509715 12566109141932699505764573)
                ·
                  refine ⟨4712290928224762314661715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12566109141932699505764573 4712290928224762314661715)
                  ·
                    refine ⟨7068436392337143471992573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4712290928224762314661715 7068436392337143471992573)
                    ·
                      refine ⟨2650663647126428801997215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7068436392337143471992573 2650663647126428801997215)
                      ·
                        rfl

theorem cell23_5162149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_5162149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162149 prefixEnd_5162149 := by exact prefixLift 5162149
  have htrace : WordTrace (prefixWord ++ tailWord_5162149) baseStart_5162149 baseEnd_5162149 := by
    simpa [prefixWord, tailWord_5162149, baseEnd_5162149] using wordTrace_append hprefix tailTrace_5162149
  have hstable : (prefixWord ++ tailWord_5162149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162149).length < 2 ^ (prefixWord ++ tailWord_5162149).sum := by decide
  have hdescent : baseEnd_5162149 < baseStart_5162149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162169 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 1, 5]
def baseStart_5162169 : Nat := 118140960795 + 5162169 * 2 ^ 59
def prefixEnd_5162169 : Nat := 4983230072969 + 3 ^ 40 * 5162169 * 2
def baseEnd_5162169 : Nat := 883557972246506241249041

theorem tailTrace_5162169 : CollatzResearch.WordTrace tailWord_5162169 prefixEnd_5162169 883557972246506241249041 := by
  unfold tailWord_5162169
  simp only [CollatzResearch.WordTrace]
  refine ⟨188279771235350816120297561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125519847490233877413531707 188279771235350816120297561)
  ·
    refine ⟨141209828426513112090223171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188279771235350816120297561 141209828426513112090223171)
    ·
      refine ⟨211814742639769668135334757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141209828426513112090223171 211814742639769668135334757)
      ·
        refine ⟨39715264244956812775375267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211814742639769668135334757 39715264244956812775375267)
        ·
          refine ⟨59572896367435219163062901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39715264244956812775375267 59572896367435219163062901)
          ·
            refine ⟨5584959034447051796537147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59572896367435219163062901 5584959034447051796537147)
            ·
              refine ⟨8377438551670577694805721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584959034447051796537147 8377438551670577694805721)
              ·
                refine ⟨6283078913752933271104291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8377438551670577694805721 6283078913752933271104291)
                ·
                  refine ⟨9424618370629399906656437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6283078913752933271104291 9424618370629399906656437)
                  ·
                    refine ⟨883557972246506241249041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9424618370629399906656437 883557972246506241249041)
                    ·
                      rfl

theorem cell23_5162169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_5162169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162169 prefixEnd_5162169 := by exact prefixLift 5162169
  have htrace : WordTrace (prefixWord ++ tailWord_5162169) baseStart_5162169 baseEnd_5162169 := by
    simpa [prefixWord, tailWord_5162169, baseEnd_5162169] using wordTrace_append hprefix tailTrace_5162169
  have hstable : (prefixWord ++ tailWord_5162169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162169).length < 2 ^ (prefixWord ++ tailWord_5162169).sum := by decide
  have hdescent : baseEnd_5162169 < baseStart_5162169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162175 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_5162175 : Nat := 118140960795 + 5162175 * 2 ^ 59
def prefixEnd_5162175 : Nat := 4983230072969 + 3 ^ 40 * 5162175 * 2
def baseEnd_5162175 : Nat := 2650676997623445700272095

theorem tailTrace_5162175 : CollatzResearch.WordTrace tailWord_5162175 prefixEnd_5162175 2650676997623445700272095 := by
  unfold tailWord_5162175
  simp only [CollatzResearch.WordTrace]
  refine ⟨188279990073329079145015979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125519993382219386096677319 188279990073329079145015979)
  ·
    refine ⟨282419985109993618717523969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188279990073329079145015979 282419985109993618717523969)
    ·
      refine ⟨211814988832495214038142977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282419985109993618717523969 211814988832495214038142977)
      ·
        refine ⟨158861241624371410528607233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211814988832495214038142977 158861241624371410528607233)
        ·
          refine ⟨119145931218278557896455425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158861241624371410528607233 119145931218278557896455425)
          ·
            refine ⟨89359448413708918422341569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119145931218278557896455425 89359448413708918422341569)
            ·
              refine ⟨67019586310281688816756177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89359448413708918422341569 67019586310281688816756177)
              ·
                refine ⟨50264689732711266612567133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67019586310281688816756177 50264689732711266612567133)
                ·
                  refine ⟨18849258649766724979712675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50264689732711266612567133 18849258649766724979712675)
                  ·
                    refine ⟨28273887974650087469569013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18849258649766724979712675 28273887974650087469569013)
                    ·
                      refine ⟨2650676997623445700272095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28273887974650087469569013 2650676997623445700272095)
                      ·
                        rfl

theorem cell23_5162175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_5162175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162175 prefixEnd_5162175 := by exact prefixLift 5162175
  have htrace : WordTrace (prefixWord ++ tailWord_5162175) baseStart_5162175 baseEnd_5162175 := by
    simpa [prefixWord, tailWord_5162175, baseEnd_5162175] using wordTrace_append hprefix tailTrace_5162175
  have hstable : (prefixWord ++ tailWord_5162175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162175).length < 2 ^ (prefixWord ++ tailWord_5162175).sum := by decide
  have hdescent : baseEnd_5162175 < baseStart_5162175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162176 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 2, 3, 2]
def baseStart_5162176 : Nat := 118140960795 + 5162176 * 2 ^ 59
def prefixEnd_5162176 : Nat := 4983230072969 + 3 ^ 40 * 5162176 * 2
def baseEnd_5162176 : Nat := 2650677511104100196359591

theorem tailTrace_5162176 : CollatzResearch.WordTrace tailWord_5162176 prefixEnd_5162176 2650677511104100196359591 := by
  unfold tailWord_5162176
  simp only [CollatzResearch.WordTrace]
  refine ⟨94140013273162728157901191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125520017697550304210534921 94140013273162728157901191)
  ·
    refine ⟨141210019909744092236851787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94140013273162728157901191 141210019909744092236851787)
    ·
      refine ⟨211815029864616138355277681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141210019909744092236851787 211815029864616138355277681)
      ·
        refine ⟨158861272398462103766458261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211815029864616138355277681 158861272398462103766458261)
        ·
          refine ⟨7446622143677911114052731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158861272398462103766458261 7446622143677911114052731)
          ·
            refine ⟨11169933215516866671079097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7446622143677911114052731 11169933215516866671079097)
            ·
              refine ⟨8377449911637650003309323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11169933215516866671079097 8377449911637650003309323)
              ·
                refine ⟨12566174867456475004963985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377449911637650003309323 12566174867456475004963985)
                ·
                  refine ⟨9424631150592356253722989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12566174867456475004963985 9424631150592356253722989)
                  ·
                    refine ⟨3534236681472133595146121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9424631150592356253722989 3534236681472133595146121)
                    ·
                      refine ⟨2650677511104100196359591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534236681472133595146121 2650677511104100196359591)
                      ·
                        rfl

theorem cell23_5162176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_5162176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162176 prefixEnd_5162176 := by exact prefixLift 5162176
  have htrace : WordTrace (prefixWord ++ tailWord_5162176) baseStart_5162176 baseEnd_5162176 := by
    simpa [prefixWord, tailWord_5162176, baseEnd_5162176] using wordTrace_append hprefix tailTrace_5162176
  have hstable : (prefixWord ++ tailWord_5162176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162176).length < 2 ^ (prefixWord ++ tailWord_5162176).sum := by decide
  have hdescent : baseEnd_5162176 < baseStart_5162176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162200 : List Nat := [2, 1, 2, 2, 5, 2, 2, 2, 1, 1, 3]
def baseStart_5162200 : Nat := 118140960795 + 5162200 * 2 ^ 59
def prefixEnd_5162200 : Nat := 4983230072969 + 3 ^ 40 * 5162200 * 2
def baseEnd_5162200 : Nat := 2650689834639808102459481

theorem tailTrace_5162200 : CollatzResearch.WordTrace tailWord_5162200 prefixEnd_5162200 2650689834639808102459481 := by
  unfold tailWord_5162200
  simp only [CollatzResearch.WordTrace]
  refine ⟨94140450949119254207338027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125520601265492338943117369 94140450949119254207338027)
  ·
    refine ⟨141210676423678881311007041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94140450949119254207338027 141210676423678881311007041)
    ·
      refine ⟨105908007317759160983255281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141210676423678881311007041 105908007317759160983255281)
      ·
        refine ⟨79431005488319370737441461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105908007317759160983255281 79431005488319370737441461)
        ·
          refine ⟨7446656764529941006635137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79431005488319370737441461 7446656764529941006635137)
          ·
            refine ⟨5584992573397455754976353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7446656764529941006635137 5584992573397455754976353)
            ·
              refine ⟨4188744430048091816232265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5584992573397455754976353 4188744430048091816232265)
              ·
                refine ⟨3141558322536068862174199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4188744430048091816232265 3141558322536068862174199)
                ·
                  refine ⟨4712337483804103293261299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141558322536068862174199 4712337483804103293261299)
                  ·
                    refine ⟨7068506225706154939891949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4712337483804103293261299 7068506225706154939891949)
                    ·
                      refine ⟨2650689834639808102459481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7068506225706154939891949 2650689834639808102459481)
                      ·
                        rfl

theorem cell23_5162200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_5162200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162200 prefixEnd_5162200 := by exact prefixLift 5162200
  have htrace : WordTrace (prefixWord ++ tailWord_5162200) baseStart_5162200 baseEnd_5162200 := by
    simpa [prefixWord, tailWord_5162200, baseEnd_5162200] using wordTrace_append hprefix tailTrace_5162200
  have hstable : (prefixWord ++ tailWord_5162200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162200).length < 2 ^ (prefixWord ++ tailWord_5162200).sum := by decide
  have hdescent : baseEnd_5162200 < baseStart_5162200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162225 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 4, 7]
def baseStart_5162225 : Nat := 118140960795 + 5162225 * 2 ^ 59
def prefixEnd_5162225 : Nat := 4983230072969 + 3 ^ 40 * 5162225 * 2
def baseEnd_5162225 : Nat := 883567557218723501548955

theorem tailTrace_5162225 : CollatzResearch.WordTrace tailWord_5162225 prefixEnd_5162225 883567557218723501548955 := by
  unfold tailWord_5162225
  simp only [CollatzResearch.WordTrace]
  refine ⟨188281813723147937684336129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125521209148765291789557419 188281813723147937684336129)
  ·
    refine ⟨141211360292360953263252097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188281813723147937684336129 141211360292360953263252097)
    ·
      refine ⟨105908520219270714947439073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141211360292360953263252097 105908520219270714947439073)
      ·
        refine ⟨79431390164453036210579305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105908520219270714947439073 79431390164453036210579305)
        ·
          refine ⟨59573542623339777157934479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79431390164453036210579305 59573542623339777157934479)
          ·
            refine ⟨89360313935009665736901719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59573542623339777157934479 89360313935009665736901719)
            ·
              refine ⟨134040470902514498605352579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89360313935009665736901719 134040470902514498605352579)
              ·
                refine ⟨201060706353771747908028869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134040470902514498605352579 201060706353771747908028869)
                ·
                  refine ⟨37698882441332202732755413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201060706353771747908028869 37698882441332202732755413)
                  ·
                    refine ⟨883567557218723501548955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37698882441332202732755413 883567557218723501548955)
                    ·
                      rfl

theorem cell23_5162225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_5162225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162225 prefixEnd_5162225 := by exact prefixLift 5162225
  have htrace : WordTrace (prefixWord ++ tailWord_5162225) baseStart_5162225 baseEnd_5162225 := by
    simpa [prefixWord, tailWord_5162225, baseEnd_5162225] using wordTrace_append hprefix tailTrace_5162225
  have hstable : (prefixWord ++ tailWord_5162225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162225).length < 2 ^ (prefixWord ++ tailWord_5162225).sum := by decide
  have hdescent : baseEnd_5162225 < baseStart_5162225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162270 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5162270 : Nat := 118140960795 + 5162270 * 2 ^ 59
def prefixEnd_5162270 : Nat := 4983230072969 + 3 ^ 40 * 5162270 * 2
def baseEnd_5162270 : Nat := 2650725778285622828584159

theorem tailTrace_5162270 : CollatzResearch.WordTrace tailWord_5162270 prefixEnd_5162270 2650725778285622828584159 := by
  unfold tailWord_5162270
  simp only [CollatzResearch.WordTrace]
  refine ⟨23535431875998113796215533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125522303338656606913149509 23535431875998113796215533)
  ·
    refine ⟨8825786953499292673580825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23535431875998113796215533 8825786953499292673580825)
    ·
      refine ⟨6619340215124469505185619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8825786953499292673580825 6619340215124469505185619)
      ·
        refine ⟨9929010322686704257778429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6619340215124469505185619 9929010322686704257778429)
        ·
          refine ⟨3723378871007514096666911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9929010322686704257778429 3723378871007514096666911)
          ·
            refine ⟨5585068306511271145000367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723378871007514096666911 5585068306511271145000367)
            ·
              refine ⟨8377602459766906717500551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585068306511271145000367 8377602459766906717500551)
              ·
                refine ⟨12566403689650360076250827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8377602459766906717500551 12566403689650360076250827)
                ·
                  refine ⟨18849605534475540114376241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12566403689650360076250827 18849605534475540114376241)
                  ·
                    refine ⟨14137204150856655085782181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18849605534475540114376241 14137204150856655085782181)
                    ·
                      refine ⟨2650725778285622828584159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14137204150856655085782181 2650725778285622828584159)
                      ·
                        rfl

theorem cell23_5162270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5162270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162270 prefixEnd_5162270 := by exact prefixLift 5162270
  have htrace : WordTrace (prefixWord ++ tailWord_5162270) baseStart_5162270 baseEnd_5162270 := by
    simpa [prefixWord, tailWord_5162270, baseEnd_5162270] using wordTrace_append hprefix tailTrace_5162270
  have hstable : (prefixWord ++ tailWord_5162270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162270).length < 2 ^ (prefixWord ++ tailWord_5162270).sum := by decide
  have hdescent : baseEnd_5162270 < baseStart_5162270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162349 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_5162349 : Nat := 118140960795 + 5162349 * 2 ^ 59
def prefixEnd_5162349 : Nat := 4983230072969 + 3 ^ 40 * 5162349 * 2
def baseEnd_5162349 : Nat := 883588781085776006498765

theorem tailTrace_5162349 : CollatzResearch.WordTrace tailWord_5162349 prefixEnd_5162349 883588781085776006498765 := by
  unfold tailWord_5162349
  simp only [CollatzResearch.WordTrace]
  refine ⟨188286336374698706861850101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125524224249799137907900067 188286336374698706861850101)
  ·
    refine ⟨17651844035128003768298447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188286336374698706861850101 17651844035128003768298447)
    ·
      refine ⟨26477766052692005652447671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17651844035128003768298447 26477766052692005652447671)
      ·
        refine ⟨39716649079038008478671507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26477766052692005652447671 39716649079038008478671507)
        ·
          refine ⟨59574973618557012718007261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39716649079038008478671507 59574973618557012718007261)
          ·
            refine ⟨22340615106958879769252723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59574973618557012718007261 22340615106958879769252723)
            ·
              refine ⟨33510922660438319653879085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22340615106958879769252723 33510922660438319653879085)
              ·
                refine ⟨12566595997664369870204657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33510922660438319653879085 12566595997664369870204657)
                ·
                  refine ⟨9424946998248277402653493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12566595997664369870204657 9424946998248277402653493)
                  ·
                    refine ⟨883588781085776006498765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9424946998248277402653493 883588781085776006498765)
                    ·
                      rfl

theorem cell23_5162349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_5162349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162349 prefixEnd_5162349 := by exact prefixLift 5162349
  have htrace : WordTrace (prefixWord ++ tailWord_5162349) baseStart_5162349 baseEnd_5162349 := by
    simpa [prefixWord, tailWord_5162349, baseEnd_5162349] using wordTrace_append hprefix tailTrace_5162349
  have hstable : (prefixWord ++ tailWord_5162349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162349).length < 2 ^ (prefixWord ++ tailWord_5162349).sum := by decide
  have hdescent : baseEnd_5162349 < baseStart_5162349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162370 : List Nat := [3, 4, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5162370 : Nat := 118140960795 + 5162370 * 2 ^ 59
def prefixEnd_5162370 : Nat := 4983230072969 + 3 ^ 40 * 5162370 * 2
def baseEnd_5162370 : Nat := 294530791816785826370411

theorem tailTrace_5162370 : CollatzResearch.WordTrace tailWord_5162370 prefixEnd_5162370 294530791816785826370411 := by
  unfold tailWord_5162370
  simp only [CollatzResearch.WordTrace]
  refine ⟨47071775576905656862091141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125524734871748418298909709 47071775576905656862091141)
  ·
    refine ⟨8825957920669810661642089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47071775576905656862091141 8825957920669810661642089)
    ·
      refine ⟨6619468440502357996231567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8825957920669810661642089 6619468440502357996231567)
      ·
        refine ⟨9929202660753536994347351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6619468440502357996231567 9929202660753536994347351)
        ·
          refine ⟨14893803991130305491521027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9929202660753536994347351 14893803991130305491521027)
          ·
            refine ⟨22340705986695458237281541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14893803991130305491521027 22340705986695458237281541)
            ·
              refine ⟨4188882372505398419490289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22340705986695458237281541 4188882372505398419490289)
              ·
                refine ⟨3141661779379048814617717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4188882372505398419490289 3141661779379048814617717)
                ·
                  refine ⟨294530791816785826370411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141661779379048814617717 294530791816785826370411)
                  ·
                    rfl

theorem cell23_5162370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5162370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162370 prefixEnd_5162370 := by exact prefixLift 5162370
  have htrace : WordTrace (prefixWord ++ tailWord_5162370) baseStart_5162370 baseEnd_5162370 := by
    simpa [prefixWord, tailWord_5162370, baseEnd_5162370] using wordTrace_append hprefix tailTrace_5162370
  have hstable : (prefixWord ++ tailWord_5162370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162370).length < 2 ^ (prefixWord ++ tailWord_5162370).sum := by decide
  have hdescent : baseEnd_5162370 < baseStart_5162370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162379 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 3, 4]
def baseStart_5162379 : Nat := 118140960795 + 5162379 * 2 ^ 59
def prefixEnd_5162379 : Nat := 4983230072969 + 3 ^ 40 * 5162379 * 2
def baseEnd_5162379 : Nat := 883593915892320967373719

theorem tailTrace_5162379 : CollatzResearch.WordTrace tailWord_5162379 prefixEnd_5162379 883593915892320967373719 := by
  unfold tailWord_5162379
  simp only [CollatzResearch.WordTrace]
  refine ⟨188287430564590021985442191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125524953709726681323628127 188287430564590021985442191)
  ·
    refine ⟨282431145846885032978163287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188287430564590021985442191 282431145846885032978163287)
    ·
      refine ⟨423646718770327549467244931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282431145846885032978163287 423646718770327549467244931)
      ·
        refine ⟨635470078155491324200867397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423646718770327549467244931 635470078155491324200867397)
        ·
          refine ⟨119150639654154623287662637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 635470078155491324200867397 119150639654154623287662637)
          ·
            refine ⟨44681489870307983732873489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119150639654154623287662637 44681489870307983732873489)
            ·
              refine ⟨33511117402730987799655117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44681489870307983732873489 33511117402730987799655117)
              ·
                refine ⟨12566669026024120424870669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33511117402730987799655117 12566669026024120424870669)
                ·
                  refine ⟨4712500884759045159326501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12566669026024120424870669 4712500884759045159326501)
                  ·
                    refine ⟨883593915892320967373719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712500884759045159326501 883593915892320967373719)
                    ·
                      rfl

theorem cell23_5162379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 4].length) (baseStart_5162379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162379 prefixEnd_5162379 := by exact prefixLift 5162379
  have htrace : WordTrace (prefixWord ++ tailWord_5162379) baseStart_5162379 baseEnd_5162379 := by
    simpa [prefixWord, tailWord_5162379, baseEnd_5162379] using wordTrace_append hprefix tailTrace_5162379
  have hstable : (prefixWord ++ tailWord_5162379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162379).length < 2 ^ (prefixWord ++ tailWord_5162379).sum := by decide
  have hdescent : baseEnd_5162379 < baseStart_5162379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162389 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_5162389 : Nat := 118140960795 + 5162389 * 2 ^ 59
def prefixEnd_5162389 : Nat := 4983230072969 + 3 ^ 40 * 5162389 * 2
def baseEnd_5162389 : Nat := 2650786882483507862996111

theorem tailTrace_5162389 : CollatzResearch.WordTrace tailWord_5162389 prefixEnd_5162389 2650786882483507862996111 := by
  unfold tailWord_5162389
  simp only [CollatzResearch.WordTrace]
  refine ⟨188287795294553793693306221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125525196863035862462204147 188287795294553793693306221)
  ·
    refine ⟨70607923235457672634989833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188287795294553793693306221 70607923235457672634989833)
    ·
      refine ⟨52955942426593254476242375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70607923235457672634989833 52955942426593254476242375)
      ·
        refine ⟨79433913639889881714363563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52955942426593254476242375 79433913639889881714363563)
        ·
          refine ⟨119150870459834822571545345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79433913639889881714363563 119150870459834822571545345)
          ·
            refine ⟨89363152844876116928659009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119150870459834822571545345 89363152844876116928659009)
            ·
              refine ⟨67022364633657087696494257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89363152844876116928659009 67022364633657087696494257)
              ·
                refine ⟨50266773475242815772370693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67022364633657087696494257 50266773475242815772370693)
                ·
                  refine ⟨9425020026608027957319505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50266773475242815772370693 9425020026608027957319505)
                  ·
                    refine ⟨7068765019956020967989629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9425020026608027957319505 7068765019956020967989629)
                    ·
                      refine ⟨2650786882483507862996111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7068765019956020967989629 2650786882483507862996111)
                      ·
                        rfl

theorem cell23_5162389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_5162389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162389 prefixEnd_5162389 := by exact prefixLift 5162389
  have htrace : WordTrace (prefixWord ++ tailWord_5162389) baseStart_5162389 baseEnd_5162389 := by
    simpa [prefixWord, tailWord_5162389, baseEnd_5162389] using wordTrace_append hprefix tailTrace_5162389
  have hstable : (prefixWord ++ tailWord_5162389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162389).length < 2 ^ (prefixWord ++ tailWord_5162389).sum := by decide
  have hdescent : baseEnd_5162389 < baseStart_5162389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162446 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_5162446 : Nat := 118140960795 + 5162446 * 2 ^ 59
def prefixEnd_5162446 : Nat := 4983230072969 + 3 ^ 40 * 5162446 * 2
def baseEnd_5162446 : Nat := 2650816150880814139983349

theorem tailTrace_5162446 : CollatzResearch.WordTrace tailWord_5162446 prefixEnd_5162446 2650816150880814139983349 := by
  unfold tailWord_5162446
  simp only [CollatzResearch.WordTrace]
  refine ⟨23536234281918411553516399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125526582836898194952087461 23536234281918411553516399)
  ·
    refine ⟨35304351422877617330274599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23536234281918411553516399 35304351422877617330274599)
    ·
      refine ⟨52956527134316425995411899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35304351422877617330274599 52956527134316425995411899)
      ·
        refine ⟨79434790701474638993117849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52956527134316425995411899 79434790701474638993117849)
        ·
          refine ⟨59576093026105979244838387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79434790701474638993117849 59576093026105979244838387)
          ·
            refine ⟨89364139539158968867257581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59576093026105979244838387 89364139539158968867257581)
            ·
              refine ⟨33511552327184613325221593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89364139539158968867257581 33511552327184613325221593)
              ·
                refine ⟨25133664245388459993916195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33511552327184613325221593 25133664245388459993916195)
                ·
                  refine ⟨37700496368082689990874293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25133664245388459993916195 37700496368082689990874293)
                  ·
                    refine ⟨3534421534507752186644465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37700496368082689990874293 3534421534507752186644465)
                    ·
                      refine ⟨2650816150880814139983349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534421534507752186644465 2650816150880814139983349)
                      ·
                        rfl

theorem cell23_5162446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_5162446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162446 prefixEnd_5162446 := by exact prefixLift 5162446
  have htrace : WordTrace (prefixWord ++ tailWord_5162446) baseStart_5162446 baseEnd_5162446 := by
    simpa [prefixWord, tailWord_5162446, baseEnd_5162446] using wordTrace_append hprefix tailTrace_5162446
  have hstable : (prefixWord ++ tailWord_5162446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162446).length < 2 ^ (prefixWord ++ tailWord_5162446).sum := by decide
  have hdescent : baseEnd_5162446 < baseStart_5162446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162479 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_5162479 : Nat := 118140960795 + 5162479 * 2 ^ 59
def prefixEnd_5162479 : Nat := 4983230072969 + 3 ^ 40 * 5162479 * 2
def baseEnd_5162479 : Nat := 2650833095742412510870697

theorem tailTrace_5162479 : CollatzResearch.WordTrace tailWord_5162479 prefixEnd_5162479 2650833095742412510870697 := by
  unfold tailWord_5162479
  simp only [CollatzResearch.WordTrace]
  refine ⟨188291077864227739064082491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125527385242818492709388327 188291077864227739064082491)
  ·
    refine ⟨282436616796341608596123737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188291077864227739064082491 282436616796341608596123737)
    ·
      refine ⟨211827462597256206447092803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282436616796341608596123737 211827462597256206447092803)
      ·
        refine ⟨317741193895884309670639205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211827462597256206447092803 317741193895884309670639205)
        ·
          refine ⟨59576473855478308063244851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317741193895884309670639205 59576473855478308063244851)
          ·
            refine ⟨89364710783217462094867277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59576473855478308063244851 89364710783217462094867277)
            ·
              refine ⟨33511766543706548285575229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89364710783217462094867277 33511766543706548285575229)
              ·
                refine ⟨12566912453889955607090711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33511766543706548285575229 12566912453889955607090711)
                ·
                  refine ⟨18850368680834933410636067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12566912453889955607090711 18850368680834933410636067)
                  ·
                    refine ⟨28275553021252400115954101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18850368680834933410636067 28275553021252400115954101)
                    ·
                      refine ⟨2650833095742412510870697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28275553021252400115954101 2650833095742412510870697)
                      ·
                        rfl

theorem cell23_5162479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_5162479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162479 prefixEnd_5162479 := by exact prefixLift 5162479
  have htrace : WordTrace (prefixWord ++ tailWord_5162479) baseStart_5162479 baseEnd_5162479 := by
    simpa [prefixWord, tailWord_5162479, baseEnd_5162479] using wordTrace_append hprefix tailTrace_5162479
  have hstable : (prefixWord ++ tailWord_5162479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162479).length < 2 ^ (prefixWord ++ tailWord_5162479).sum := by decide
  have hdescent : baseEnd_5162479 < baseStart_5162479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162503 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 2, 4]
def baseStart_5162503 : Nat := 118140960795 + 5162503 * 2 ^ 59
def prefixEnd_5162503 : Nat := 4983230072969 + 3 ^ 40 * 5162503 * 2
def baseEnd_5162503 : Nat := 883615139759373472323529

theorem tailTrace_5162503 : CollatzResearch.WordTrace tailWord_5162503 prefixEnd_5162503 883615139759373472323529 := by
  unfold tailWord_5162503
  simp only [CollatzResearch.WordTrace]
  refine ⟨188291953216140791162956163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125527968810760527441970775 188291953216140791162956163)
  ·
    refine ⟨282437929824211186744434245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188291953216140791162956163 282437929824211186744434245)
    ·
      refine ⟨52957111842039597514581421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282437929824211186744434245 52957111842039597514581421)
      ·
        refine ⟨19858916940764849067968033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52957111842039597514581421 19858916940764849067968033)
        ·
          refine ⟨14894187705573636800976025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19858916940764849067968033 14894187705573636800976025)
          ·
            refine ⟨11170640779180227600732019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14894187705573636800976025 11170640779180227600732019)
            ·
              refine ⟨16755961168770341401098029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11170640779180227600732019 16755961168770341401098029)
              ·
                refine ⟨6283485438288878025411761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16755961168770341401098029 6283485438288878025411761)
                ·
                  refine ⟨4712614078716658519058821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283485438288878025411761 4712614078716658519058821)
                  ·
                    refine ⟨883615139759373472323529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4712614078716658519058821 883615139759373472323529)
                    ·
                      rfl

theorem cell23_5162503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_5162503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162503 prefixEnd_5162503 := by exact prefixLift 5162503
  have htrace : WordTrace (prefixWord ++ tailWord_5162503) baseStart_5162503 baseEnd_5162503 := by
    simpa [prefixWord, tailWord_5162503, baseEnd_5162503] using wordTrace_append hprefix tailTrace_5162503
  have hstable : (prefixWord ++ tailWord_5162503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162503).length < 2 ^ (prefixWord ++ tailWord_5162503).sum := by decide
  have hdescent : baseEnd_5162503 < baseStart_5162503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162510 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_5162510 : Nat := 118140960795 + 5162510 * 2 ^ 59
def prefixEnd_5162510 : Nat := 4983230072969 + 3 ^ 40 * 5162510 * 2
def baseEnd_5162510 : Nat := 2650849013642701889583055

theorem tailTrace_5162510 : CollatzResearch.WordTrace tailWord_5162510 prefixEnd_5162510 2650849013642701889583055 := by
  unfold tailWord_5162510
  simp only [CollatzResearch.WordTrace]
  refine ⟨23536526065889428919807623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125528139018076954238973989 23536526065889428919807623)
  ·
    refine ⟨35304789098834143379711435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23536526065889428919807623 35304789098834143379711435)
    ·
      refine ⟨52957183648251215069567153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35304789098834143379711435 52957183648251215069567153)
      ·
        refine ⟨39717887736188411302175365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52957183648251215069567153 39717887736188411302175365)
        ·
          refine ⟨7447103950535327119157881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39717887736188411302175365 7447103950535327119157881)
          ·
            refine ⟨5585327962901495339368411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7447103950535327119157881 5585327962901495339368411)
            ·
              refine ⟨8377991944352243009052617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585327962901495339368411 8377991944352243009052617)
              ·
                refine ⟨6283493958264182256789463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8377991944352243009052617 6283493958264182256789463)
                ·
                  refine ⟨9425240937396273385184195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6283493958264182256789463 9425240937396273385184195)
                  ·
                    refine ⟨14137861406094410077776293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9425240937396273385184195 14137861406094410077776293)
                    ·
                      refine ⟨2650849013642701889583055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14137861406094410077776293 2650849013642701889583055)
                      ·
                        rfl

theorem cell23_5162510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_5162510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162510 prefixEnd_5162510 := by exact prefixLift 5162510
  have htrace : WordTrace (prefixWord ++ tailWord_5162510) baseStart_5162510 baseEnd_5162510 := by
    simpa [prefixWord, tailWord_5162510, baseEnd_5162510] using wordTrace_append hprefix tailTrace_5162510
  have hstable : (prefixWord ++ tailWord_5162510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162510).length < 2 ^ (prefixWord ++ tailWord_5162510).sum := by decide
  have hdescent : baseEnd_5162510 < baseStart_5162510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162550 : List Nat := [5, 1, 2, 1, 4, 1, 1, 8]
def baseStart_5162550 : Nat := 118140960795 + 5162550 * 2 ^ 59
def prefixEnd_5162550 : Nat := 4983230072969 + 3 ^ 40 * 5162550 * 2
def baseEnd_5162550 : Nat := 98180353809958582706773

theorem tailTrace_5162550 : CollatzResearch.WordTrace tailWord_5162550 prefixEnd_5162550 98180353809958582706773 := by
  unfold tailWord_5162550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768354215435657386869819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125529111631313678793278069 11768354215435657386869819)
  ·
    refine ⟨17652531323153486080304729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11768354215435657386869819 17652531323153486080304729)
    ·
      refine ⟨13239398492365114560228547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17652531323153486080304729 13239398492365114560228547)
      ·
        refine ⟨19859097738547671840342821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13239398492365114560228547 19859097738547671840342821)
        ·
          refine ⟨3723580825977688470064279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19859097738547671840342821 3723580825977688470064279)
          ·
            refine ⟨5585371238966532705096419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723580825977688470064279 5585371238966532705096419)
            ·
              refine ⟨8378056858449799057644629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585371238966532705096419 8378056858449799057644629)
              ·
                refine ⟨98180353809958582706773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8378056858449799057644629 98180353809958582706773)
                ·
                  rfl

theorem cell23_5162550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_5162550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162550 prefixEnd_5162550 := by exact prefixLift 5162550
  have htrace : WordTrace (prefixWord ++ tailWord_5162550) baseStart_5162550 baseEnd_5162550 := by
    simpa [prefixWord, tailWord_5162550, baseEnd_5162550] using wordTrace_append hprefix tailTrace_5162550
  have hstable : (prefixWord ++ tailWord_5162550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162550).length < 2 ^ (prefixWord ++ tailWord_5162550).sum := by decide
  have hdescent : baseEnd_5162550 < baseStart_5162550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162553 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5162553 : Nat := 118140960795 + 5162553 * 2 ^ 59
def prefixEnd_5162553 : Nat := 4983230072969 + 3 ^ 40 * 5162553 * 2
def baseEnd_5162553 : Nat := 2650871093310845221345357

theorem tailTrace_5162553 : CollatzResearch.WordTrace tailWord_5162553 prefixEnd_5162553 2650871093310845221345357 := by
  unfold tailWord_5162553
  simp only [CollatzResearch.WordTrace]
  refine ⟨188293776865959649702276313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125529184577306433134850875 188293776865959649702276313)
  ·
    refine ⟨141220332649469737276707235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188293776865959649702276313 141220332649469737276707235)
    ·
      refine ⟨211830498974204605915060853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141220332649469737276707235 211830498974204605915060853)
      ·
        refine ⟨19859109278831681804536955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 211830498974204605915060853 19859109278831681804536955)
        ·
          refine ⟨29788663918247522706805433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19859109278831681804536955 29788663918247522706805433)
          ·
            refine ⟨22341497938685642030104075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29788663918247522706805433 22341497938685642030104075)
            ·
              refine ⟨33512246908028463045156113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22341497938685642030104075 33512246908028463045156113)
              ·
                refine ⟨25134185181021347283867085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33512246908028463045156113 25134185181021347283867085)
                ·
                  refine ⟨9425319442883005231450157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25134185181021347283867085 9425319442883005231450157)
                  ·
                    refine ⟨3534494791081126961793809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9425319442883005231450157 3534494791081126961793809)
                    ·
                      refine ⟨2650871093310845221345357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534494791081126961793809 2650871093310845221345357)
                      ·
                        rfl

theorem cell23_5162553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5162553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162553 prefixEnd_5162553 := by exact prefixLift 5162553
  have htrace : WordTrace (prefixWord ++ tailWord_5162553) baseStart_5162553 baseEnd_5162553 := by
    simpa [prefixWord, tailWord_5162553, baseEnd_5162553] using wordTrace_append hprefix tailTrace_5162553
  have hstable : (prefixWord ++ tailWord_5162553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162553).length < 2 ^ (prefixWord ++ tailWord_5162553).sum := by decide
  have hdescent : baseEnd_5162553 < baseStart_5162553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162559 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 1, 8]
def baseStart_5162559 : Nat := 118140960795 + 5162559 * 2 ^ 59
def prefixEnd_5162559 : Nat := 4983230072969 + 3 ^ 40 * 5162559 * 2
def baseEnd_5162559 : Nat := 883624724731590732623443

theorem tailTrace_5162559 : CollatzResearch.WordTrace tailWord_5162559 prefixEnd_5162559 883624724731590732623443 := by
  unfold tailWord_5162559
  simp only [CollatzResearch.WordTrace]
  refine ⟨188293995703937912726994731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125529330469291941817996487 188293995703937912726994731)
  ·
    refine ⟨282440993555906869090492097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188293995703937912726994731 282440993555906869090492097)
    ·
      refine ⟨211830745166930151817869073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282440993555906869090492097 211830745166930151817869073)
      ·
        refine ⟨158873058875197613863401805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211830745166930151817869073 158873058875197613863401805)
        ·
          refine ⟨59577397078199105198775677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158873058875197613863401805 59577397078199105198775677)
          ·
            refine ⟨22341523904324664449540879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59577397078199105198775677 22341523904324664449540879)
            ·
              refine ⟨33512285856486996674311319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22341523904324664449540879 33512285856486996674311319)
              ·
                refine ⟨50268428784730495011466979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33512285856486996674311319 50268428784730495011466979)
                ·
                  refine ⟨75402643177095742517200469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50268428784730495011466979 75402643177095742517200469)
                  ·
                    refine ⟨883624724731590732623443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75402643177095742517200469 883624724731590732623443)
                    ·
                      rfl

theorem cell23_5162559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_5162559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162559 prefixEnd_5162559 := by exact prefixLift 5162559
  have htrace : WordTrace (prefixWord ++ tailWord_5162559) baseStart_5162559 baseEnd_5162559 := by
    simpa [prefixWord, tailWord_5162559, baseEnd_5162559] using wordTrace_append hprefix tailTrace_5162559
  have hstable : (prefixWord ++ tailWord_5162559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162559).length < 2 ^ (prefixWord ++ tailWord_5162559).sum := by decide
  have hdescent : baseEnd_5162559 < baseStart_5162559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162569 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_5162569 : Nat := 118140960795 + 5162569 * 2 ^ 59
def prefixEnd_5162569 : Nat := 4983230072969 + 3 ^ 40 * 5162569 * 2
def baseEnd_5162569 : Nat := 2650879309001317158745283

theorem tailTrace_5162569 : CollatzResearch.WordTrace tailWord_5162569 prefixEnd_5162569 2650879309001317158745283 := by
  unfold tailWord_5162569
  simp only [CollatzResearch.WordTrace]
  refine ⟨188294360433901684434858761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125529573622601122956572507 188294360433901684434858761)
  ·
    refine ⟨141220770325426263326144071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188294360433901684434858761 141220770325426263326144071)
    ·
      refine ⟨211831155488139394989216107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141220770325426263326144071 211831155488139394989216107)
      ·
        refine ⟨317746733232209092483824161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211831155488139394989216107 317746733232209092483824161)
        ·
          refine ⟨238310049924156819362868121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317746733232209092483824161 238310049924156819362868121)
          ·
            refine ⟨178732537443117614522151091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238310049924156819362868121 178732537443117614522151091)
            ·
              refine ⟨268098806164676421783226637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178732537443117614522151091 268098806164676421783226637)
              ·
                refine ⟨100537052311753658168709989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268098806164676421783226637 100537052311753658168709989)
                ·
                  refine ⟨18850697308453810906633123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100537052311753658168709989 18850697308453810906633123)
                  ·
                    refine ⟨28276045962680716359949685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18850697308453810906633123 28276045962680716359949685)
                    ·
                      refine ⟨2650879309001317158745283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28276045962680716359949685 2650879309001317158745283)
                      ·
                        rfl

theorem cell23_5162569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_5162569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162569 prefixEnd_5162569 := by exact prefixLift 5162569
  have htrace : WordTrace (prefixWord ++ tailWord_5162569) baseStart_5162569 baseEnd_5162569 := by
    simpa [prefixWord, tailWord_5162569, baseEnd_5162569] using wordTrace_append hprefix tailTrace_5162569
  have hstable : (prefixWord ++ tailWord_5162569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162569).length < 2 ^ (prefixWord ++ tailWord_5162569).sum := by decide
  have hdescent : baseEnd_5162569 < baseStart_5162569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162583 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 1, 4, 2]
def baseStart_5162583 : Nat := 118140960795 + 5162583 * 2 ^ 59
def prefixEnd_5162583 : Nat := 4983230072969 + 3 ^ 40 * 5162583 * 2
def baseEnd_5162583 : Nat := 2650886497730480103970219

theorem tailTrace_5162583 : CollatzResearch.WordTrace tailWord_5162583 prefixEnd_5162583 2650886497730480103970219 := by
  unfold tailWord_5162583
  simp only [CollatzResearch.WordTrace]
  refine ⟨188294871055850964825868403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125529914037233976550578935 188294871055850964825868403)
  ·
    refine ⟨282442306583776447238802605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188294871055850964825868403 282442306583776447238802605)
    ·
      refine ⟨105915864968916167714550977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282442306583776447238802605 105915864968916167714550977)
      ·
        refine ⟨79436898726687125785913233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105915864968916167714550977 79436898726687125785913233)
        ·
          refine ⟨59577674045015344339434925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79436898726687125785913233 59577674045015344339434925)
          ·
            refine ⟨22341627766880754127288097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59577674045015344339434925 22341627766880754127288097)
            ·
              refine ⟨16756220825160565595466073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22341627766880754127288097 16756220825160565595466073)
              ·
                refine ⟨12567165618870424196599555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16756220825160565595466073 12567165618870424196599555)
                ·
                  refine ⟨18850748428305636294899333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12567165618870424196599555 18850748428305636294899333)
                  ·
                    refine ⟨3534515330307306805293625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18850748428305636294899333 3534515330307306805293625)
                    ·
                      refine ⟨2650886497730480103970219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534515330307306805293625 2650886497730480103970219)
                      ·
                        rfl

theorem cell23_5162583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_5162583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162583 prefixEnd_5162583 := by exact prefixLift 5162583
  have htrace : WordTrace (prefixWord ++ tailWord_5162583) baseStart_5162583 baseEnd_5162583 := by
    simpa [prefixWord, tailWord_5162583, baseEnd_5162583] using wordTrace_append hprefix tailTrace_5162583
  have hstable : (prefixWord ++ tailWord_5162583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162583).length < 2 ^ (prefixWord ++ tailWord_5162583).sum := by decide
  have hdescent : baseEnd_5162583 < baseStart_5162583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162596 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_5162596 : Nat := 118140960795 + 5162596 * 2 ^ 59
def prefixEnd_5162596 : Nat := 4983230072969 + 3 ^ 40 * 5162596 * 2
def baseEnd_5162596 : Nat := 2650893172978988553107659

theorem tailTrace_5162596 : CollatzResearch.WordTrace tailWord_5162596 prefixEnd_5162596 2650893172978988553107659 := by
  unfold tailWord_5162596
  simp only [CollatzResearch.WordTrace]
  refine ⟨94147672602401934023045821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125530230136535912030727761 94147672602401934023045821)
  ·
    refine ⟨35305377225900725258642183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94147672602401934023045821 35305377225900725258642183)
    ·
      refine ⟨52958065838851087887963275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35305377225900725258642183 52958065838851087887963275)
      ·
        refine ⟨79437098758276631831944913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52958065838851087887963275 79437098758276631831944913)
        ·
          refine ⟨59577824068707473873958685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79437098758276631831944913 59577824068707473873958685)
          ·
            refine ⟨22341684025765302702734507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59577824068707473873958685 22341684025765302702734507)
            ·
              refine ⟨33512526038647954054101761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22341684025765302702734507 33512526038647954054101761)
              ·
                refine ⟨25134394528985965540576321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33512526038647954054101761 25134394528985965540576321)
                ·
                  refine ⟨18850795896739474155432241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25134394528985965540576321 18850795896739474155432241)
                  ·
                    refine ⟨14138096922554605616574181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18850795896739474155432241 14138096922554605616574181)
                    ·
                      refine ⟨2650893172978988553107659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14138096922554605616574181 2650893172978988553107659)
                      ·
                        rfl

theorem cell23_5162596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_5162596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162596 prefixEnd_5162596 := by exact prefixLift 5162596
  have htrace : WordTrace (prefixWord ++ tailWord_5162596) baseStart_5162596 baseEnd_5162596 := by
    simpa [prefixWord, tailWord_5162596, baseEnd_5162596] using wordTrace_append hprefix tailTrace_5162596
  have hstable : (prefixWord ++ tailWord_5162596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162596).length < 2 ^ (prefixWord ++ tailWord_5162596).sum := by decide
  have hdescent : baseEnd_5162596 < baseStart_5162596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162613 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5162613 : Nat := 118140960795 + 5162613 * 2 ^ 59
def prefixEnd_5162613 : Nat := 4983230072969 + 3 ^ 40 * 5162613 * 2
def baseEnd_5162613 : Nat := 2650901902150114986595081

theorem tailTrace_5162613 : CollatzResearch.WordTrace tailWord_5162613 prefixEnd_5162613 2650901902150114986595081 := by
  unfold tailWord_5162613
  simp only [CollatzResearch.WordTrace]
  refine ⟨188295965245742279949460493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125530643497161519966306995 188295965245742279949460493)
  ·
    refine ⟨70610986967153354981047685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188295965245742279949460493 70610986967153354981047685)
    ·
      refine ⟨13239560056341254058946441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70610986967153354981047685 13239560056341254058946441)
      ·
        refine ⟨9929670042255940544209831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13239560056341254058946441 9929670042255940544209831)
        ·
          refine ⟨14894505063383910816314747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9929670042255940544209831 14894505063383910816314747)
          ·
            refine ⟨22341757595075866224472121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14894505063383910816314747 22341757595075866224472121)
            ·
              refine ⟨16756318196306899668354091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22341757595075866224472121 16756318196306899668354091)
              ·
                refine ⟨25134477294460349502531137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16756318196306899668354091 25134477294460349502531137)
                ·
                  refine ⟨18850857970845262126898353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25134477294460349502531137 18850857970845262126898353)
                  ·
                    refine ⟨14138143478133946595173765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18850857970845262126898353 14138143478133946595173765)
                    ·
                      refine ⟨2650901902150114986595081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14138143478133946595173765 2650901902150114986595081)
                      ·
                        rfl

theorem cell23_5162613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5162613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162613 prefixEnd_5162613 := by exact prefixLift 5162613
  have htrace : WordTrace (prefixWord ++ tailWord_5162613) baseStart_5162613 baseEnd_5162613 := by
    simpa [prefixWord, tailWord_5162613, baseEnd_5162613] using wordTrace_append hprefix tailTrace_5162613
  have hstable : (prefixWord ++ tailWord_5162613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162613).length < 2 ^ (prefixWord ++ tailWord_5162613).sum := by decide
  have hdescent : baseEnd_5162613 < baseStart_5162613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162617 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 2, 2, 2]
def baseStart_5162617 : Nat := 118140960795 + 5162617 * 2 ^ 59
def prefixEnd_5162617 : Nat := 4983230072969 + 3 ^ 40 * 5162617 * 2
def baseEnd_5162617 : Nat := 2650903956072732970945063

theorem tailTrace_5162617 : CollatzResearch.WordTrace tailWord_5162617 prefixEnd_5162617 2650903956072732970945063 := by
  unfold tailWord_5162617
  simp only [CollatzResearch.WordTrace]
  refine ⟨188296111137727788632606105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125530740758485192421737403 188296111137727788632606105)
  ·
    refine ⟨141222083353295841474454579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188296111137727788632606105 141222083353295841474454579)
    ·
      refine ⟨211833125029943762211681869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141222083353295841474454579 211833125029943762211681869)
      ·
        refine ⟨79437421886228910829380701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211833125029943762211681869 79437421886228910829380701)
        ·
          refine ⟨29789033207335841561017763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79437421886228910829380701 29789033207335841561017763)
          ·
            refine ⟨44683549811003762341526645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29789033207335841561017763 44683549811003762341526645)
            ·
              refine ⟨4189082794781602719518123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44683549811003762341526645 4189082794781602719518123)
              ·
                refine ⟨6283624192172404079277185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4189082794781602719518123 6283624192172404079277185)
                ·
                  refine ⟨4712718144129303059457889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283624192172404079277185 4712718144129303059457889)
                  ·
                    refine ⟨3534538608096977294593417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4712718144129303059457889 3534538608096977294593417)
                    ·
                      refine ⟨2650903956072732970945063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534538608096977294593417 2650903956072732970945063)
                      ·
                        rfl

theorem cell23_5162617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_5162617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162617 prefixEnd_5162617 := by exact prefixLift 5162617
  have htrace : WordTrace (prefixWord ++ tailWord_5162617) baseStart_5162617 baseEnd_5162617 := by
    simpa [prefixWord, tailWord_5162617, baseEnd_5162617] using wordTrace_append hprefix tailTrace_5162617
  have hstable : (prefixWord ++ tailWord_5162617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162617).length < 2 ^ (prefixWord ++ tailWord_5162617).sum := by decide
  have hdescent : baseEnd_5162617 < baseStart_5162617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162619 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 3, 7]
def baseStart_5162619 : Nat := 118140960795 + 5162619 * 2 ^ 59
def prefixEnd_5162619 : Nat := 4983230072969 + 3 ^ 40 * 5162619 * 2
def baseEnd_5162619 : Nat := 883634994344680654373351

theorem tailTrace_5162619 : CollatzResearch.WordTrace tailWord_5162619 prefixEnd_5162619 883634994344680654373351 := by
  unfold tailWord_5162619
  simp only [CollatzResearch.WordTrace]
  refine ⟨188296184083720542974178911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125530789389147028649452607 188296184083720542974178911)
  ·
    refine ⟨282444276125580814461268367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188296184083720542974178911 282444276125580814461268367)
    ·
      refine ⟨423666414188371221691902551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282444276125580814461268367 423666414188371221691902551)
      ·
        refine ⟨635499621282556832537853827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423666414188371221691902551 635499621282556832537853827)
        ·
          refine ⟨953249431923835248806780741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635499621282556832537853827 953249431923835248806780741)
          ·
            refine ⟨178734268485719109151271389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 953249431923835248806780741 178734268485719109151271389)
            ·
              refine ⟨67025350682144665931726771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178734268485719109151271389 67025350682144665931726771)
              ·
                refine ⟨100538026023216998897590157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67025350682144665931726771 100538026023216998897590157)
                ·
                  refine ⟨37701759758706374586596309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100538026023216998897590157 37701759758706374586596309)
                  ·
                    refine ⟨883634994344680654373351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37701759758706374586596309 883634994344680654373351)
                    ·
                      rfl

theorem cell23_5162619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_5162619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162619 prefixEnd_5162619 := by exact prefixLift 5162619
  have htrace : WordTrace (prefixWord ++ tailWord_5162619) baseStart_5162619 baseEnd_5162619 := by
    simpa [prefixWord, tailWord_5162619, baseEnd_5162619] using wordTrace_append hprefix tailTrace_5162619
  have hstable : (prefixWord ++ tailWord_5162619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162619).length < 2 ^ (prefixWord ++ tailWord_5162619).sum := by decide
  have hdescent : baseEnd_5162619 < baseStart_5162619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162636 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_5162636 : Nat := 118140960795 + 5162636 * 2 ^ 59
def prefixEnd_5162636 : Nat := 4983230072969 + 3 ^ 40 * 5162636 * 2
def baseEnd_5162636 : Nat := 883637904068389465535825

theorem tailTrace_5162636 : CollatzResearch.WordTrace tailWord_5162636 prefixEnd_5162636 883637904068389465535825 := by
  unfold tailWord_5162636
  simp only [CollatzResearch.WordTrace]
  refine ⟨94148402062329477438773881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125531202749772636585031841 94148402062329477438773881)
  ·
    refine ⟨70611301546747108079080411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94148402062329477438773881 70611301546747108079080411)
    ·
      refine ⟨105916952320120662118620617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70611301546747108079080411 105916952320120662118620617)
      ·
        refine ⟨79437714240090496588965463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105916952320120662118620617 79437714240090496588965463)
        ·
          refine ⟨119156571360135744883448195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79437714240090496588965463 119156571360135744883448195)
          ·
            refine ⟨178734857040203617325172293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119156571360135744883448195 178734857040203617325172293)
            ·
              refine ⟨33512785695038178248469805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178734857040203617325172293 33512785695038178248469805)
              ·
                refine ⟨12567294635639316843176177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33512785695038178248469805 12567294635639316843176177)
                ·
                  refine ⟨9425470976729487632382133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12567294635639316843176177 9425470976729487632382133)
                  ·
                    refine ⟨883637904068389465535825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9425470976729487632382133 883637904068389465535825)
                    ·
                      rfl

theorem cell23_5162636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_5162636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162636 prefixEnd_5162636 := by exact prefixLift 5162636
  have htrace : WordTrace (prefixWord ++ tailWord_5162636) baseStart_5162636 baseEnd_5162636 := by
    simpa [prefixWord, tailWord_5162636, baseEnd_5162636] using wordTrace_append hprefix tailTrace_5162636
  have hstable : (prefixWord ++ tailWord_5162636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162636).length < 2 ^ (prefixWord ++ tailWord_5162636).sum := by decide
  have hdescent : baseEnd_5162636 < baseStart_5162636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162713 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 6]
def baseStart_5162713 : Nat := 118140960795 + 5162713 * 2 ^ 59
def prefixEnd_5162713 : Nat := 4983230072969 + 3 ^ 40 * 5162713 * 2
def baseEnd_5162713 : Nat := 294550361135062732816069

theorem tailTrace_5162713 : CollatzResearch.WordTrace tailWord_5162713 prefixEnd_5162713 294550361135062732816069 := by
  unfold tailWord_5162713
  simp only [CollatzResearch.WordTrace]
  refine ⟨188299612545379997028100793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125533075030253331352067195 188299612545379997028100793)
  ·
    refine ⟨141224709409034997771075595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188299612545379997028100793 141224709409034997771075595)
    ·
      refine ⟨211837064113552496656613393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141224709409034997771075595 211837064113552496656613393)
      ·
        refine ⟨158877798085164372492460045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211837064113552496656613393 158877798085164372492460045)
        ·
          refine ⟨59579174281936639684672517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158877798085164372492460045 59579174281936639684672517)
          ·
            refine ⟨11171095177863119940876097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59579174281936639684672517 11171095177863119940876097)
            ·
              refine ⟨8378321383397339955657073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11171095177863119940876097 8378321383397339955657073)
              ·
                refine ⟨6283741037548004966742805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8378321383397339955657073 6283741037548004966742805)
                ·
                  refine ⟨294550361135062732816069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6283741037548004966742805 294550361135062732816069)
                  ·
                    rfl

theorem cell23_5162713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 6].length) (baseStart_5162713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162713 prefixEnd_5162713 := by exact prefixLift 5162713
  have htrace : WordTrace (prefixWord ++ tailWord_5162713) baseStart_5162713 baseEnd_5162713 := by
    simpa [prefixWord, tailWord_5162713, baseEnd_5162713] using wordTrace_append hprefix tailTrace_5162713
  have hstable : (prefixWord ++ tailWord_5162713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162713).length < 2 ^ (prefixWord ++ tailWord_5162713).sum := by decide
  have hdescent : baseEnd_5162713 < baseStart_5162713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162783 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_5162783 : Nat := 118140960795 + 5162783 * 2 ^ 59
def prefixEnd_5162783 : Nat := 4983230072969 + 3 ^ 40 * 5162783 * 2
def baseEnd_5162783 : Nat := 2650989193861379321469299

theorem tailTrace_5162783 : CollatzResearch.WordTrace tailWord_5162783 prefixEnd_5162783 2650989193861379321469299 := by
  unfold tailWord_5162783
  simp only [CollatzResearch.WordTrace]
  refine ⟨188302165655126398983149003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125534777103417599322099335 188302165655126398983149003)
  ·
    refine ⟨282453248482689598474723505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188302165655126398983149003 282453248482689598474723505)
    ·
      refine ⟨211839936362017198856042629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282453248482689598474723505 211839936362017198856042629)
      ·
        refine ⟨39719988067878224785507993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211839936362017198856042629 39719988067878224785507993)
        ·
          refine ⟨29789991050908668589130995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39719988067878224785507993 29789991050908668589130995)
          ·
            refine ⟨44684986576363002883696493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29789991050908668589130995 44684986576363002883696493)
            ·
              refine ⟨16756869966136126081386185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44684986576363002883696493 16756869966136126081386185)
              ·
                refine ⟨12567652474602094561039639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16756869966136126081386185 12567652474602094561039639)
                ·
                  refine ⟨18851478711903141841559459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12567652474602094561039639 18851478711903141841559459)
                  ·
                    refine ⟨28277218067854712762339189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18851478711903141841559459 28277218067854712762339189)
                    ·
                      refine ⟨2650989193861379321469299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28277218067854712762339189 2650989193861379321469299)
                      ·
                        rfl

theorem cell23_5162783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_5162783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162783 prefixEnd_5162783 := by exact prefixLift 5162783
  have htrace : WordTrace (prefixWord ++ tailWord_5162783) baseStart_5162783 baseEnd_5162783 := by
    simpa [prefixWord, tailWord_5162783, baseEnd_5162783] using wordTrace_append hprefix tailTrace_5162783
  have hstable : (prefixWord ++ tailWord_5162783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162783).length < 2 ^ (prefixWord ++ tailWord_5162783).sum := by decide
  have hdescent : baseEnd_5162783 < baseStart_5162783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162803 : List Nat := [1, 1, 1, 2, 7, 1, 1, 9]
def baseStart_5162803 : Nat := 118140960795 + 5162803 * 2 ^ 59
def prefixEnd_5162803 : Nat := 4983230072969 + 3 ^ 40 * 5162803 * 2
def baseEnd_5162803 : Nat := 98185165313869231230341

theorem tailTrace_5162803 : CollatzResearch.WordTrace tailWord_5162803 prefixEnd_5162803 98185165313869231230341 := by
  unfold tailWord_5162803
  simp only [CollatzResearch.WordTrace]
  refine ⟨188302895115053942398877063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125535263410035961599251375 188302895115053942398877063)
  ·
    refine ⟨282454342672580913598315595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188302895115053942398877063 282454342672580913598315595)
    ·
      refine ⟨423681514008871370397473393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282454342672580913598315595 423681514008871370397473393)
      ·
        refine ⟨317761135506653527798105045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423681514008871370397473393 317761135506653527798105045)
        ·
          refine ⟨7447526613437192057768087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 317761135506653527798105045 7447526613437192057768087)
          ·
            refine ⟨11171289920155788086652131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447526613437192057768087 11171289920155788086652131)
            ·
              refine ⟨16756934880233682129978197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11171289920155788086652131 16756934880233682129978197)
              ·
                refine ⟨98185165313869231230341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16756934880233682129978197 98185165313869231230341)
                ·
                  rfl

theorem cell23_5162803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 9].length) (baseStart_5162803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162803 prefixEnd_5162803 := by exact prefixLift 5162803
  have htrace : WordTrace (prefixWord ++ tailWord_5162803) baseStart_5162803 baseEnd_5162803 := by
    simpa [prefixWord, tailWord_5162803, baseEnd_5162803] using wordTrace_append hprefix tailTrace_5162803
  have hstable : (prefixWord ++ tailWord_5162803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162803).length < 2 ^ (prefixWord ++ tailWord_5162803).sum := by decide
  have hdescent : baseEnd_5162803 < baseStart_5162803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162816 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 9]
def baseStart_5162816 : Nat := 118140960795 + 5162816 * 2 ^ 59
def prefixEnd_5162816 : Nat := 4983230072969 + 3 ^ 40 * 5162816 * 2
def baseEnd_5162816 : Nat := 883668712907659230785549

theorem tailTrace_5162816 : CollatzResearch.WordTrace tailWord_5162816 prefixEnd_5162816 883668712907659230785549 := by
  unfold tailWord_5162816
  simp only [CollatzResearch.WordTrace]
  refine ⟨94151684632003422809550151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125535579509337897079400201 94151684632003422809550151)
  ·
    refine ⟨141227526948005134214325227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94151684632003422809550151 141227526948005134214325227)
    ·
      refine ⟨211841290422007701321487841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141227526948005134214325227 211841290422007701321487841)
      ·
        refine ⟨158880967816505775991115881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211841290422007701321487841 158880967816505775991115881)
        ·
          refine ⟨119160725862379331993336911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158880967816505775991115881 119160725862379331993336911)
          ·
            refine ⟨178741088793568997990005367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119160725862379331993336911 178741088793568997990005367)
            ·
              refine ⟨268111633190353496985008051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178741088793568997990005367 268111633190353496985008051)
              ·
                refine ⟨402167449785530245477512077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268111633190353496985008051 402167449785530245477512077)
                ·
                  refine ⟨150812793669573842054067029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402167449785530245477512077 150812793669573842054067029)
                  ·
                    refine ⟨883668712907659230785549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 150812793669573842054067029 883668712907659230785549)
                    ·
                      rfl

theorem cell23_5162816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_5162816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162816 prefixEnd_5162816 := by exact prefixLift 5162816
  have htrace : WordTrace (prefixWord ++ tailWord_5162816) baseStart_5162816 baseEnd_5162816 := by
    simpa [prefixWord, tailWord_5162816, baseEnd_5162816] using wordTrace_append hprefix tailTrace_5162816
  have hstable : (prefixWord ++ tailWord_5162816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162816).length < 2 ^ (prefixWord ++ tailWord_5162816).sum := by decide
  have hdescent : baseEnd_5162816 < baseStart_5162816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162847 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 3]
def baseStart_5162847 : Nat := 118140960795 + 5162847 * 2 ^ 59
def prefixEnd_5162847 : Nat := 4983230072969 + 3 ^ 40 * 5162847 * 2
def baseEnd_5162847 : Nat := 2651022056623267071069005

theorem tailTrace_5162847 : CollatzResearch.WordTrace tailWord_5162847 prefixEnd_5162847 2651022056623267071069005 := by
  unfold tailWord_5162847
  simp only [CollatzResearch.WordTrace]
  refine ⟨188304499926894537913478795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125536333284596358608985863 188304499926894537913478795)
  ·
    refine ⟨282456749890341806870218193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188304499926894537913478795 282456749890341806870218193)
    ·
      refine ⟨211842562417756355152663645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282456749890341806870218193 211842562417756355152663645)
      ·
        refine ⟨79440960906658633182248867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211842562417756355152663645 79440960906658633182248867)
        ·
          refine ⟨119161441359987949773373301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79440960906658633182248867 119161441359987949773373301)
          ·
            refine ⟨11171385127498870291253747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119161441359987949773373301 11171385127498870291253747)
            ·
              refine ⟨16757077691248305436880621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11171385127498870291253747 16757077691248305436880621)
              ·
                refine ⟨6283904134218114538830233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16757077691248305436880621 6283904134218114538830233)
                ·
                  refine ⟨4712928100663585904122675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283904134218114538830233 4712928100663585904122675)
                  ·
                    refine ⟨7069392150995378856184013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4712928100663585904122675 7069392150995378856184013)
                    ·
                      refine ⟨2651022056623267071069005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7069392150995378856184013 2651022056623267071069005)
                      ·
                        rfl

theorem cell23_5162847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_5162847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162847 prefixEnd_5162847 := by exact prefixLift 5162847
  have htrace : WordTrace (prefixWord ++ tailWord_5162847) baseStart_5162847 baseEnd_5162847 := by
    simpa [prefixWord, tailWord_5162847, baseEnd_5162847] using wordTrace_append hprefix tailTrace_5162847
  have hstable : (prefixWord ++ tailWord_5162847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162847).length < 2 ^ (prefixWord ++ tailWord_5162847).sum := by decide
  have hdescent : baseEnd_5162847 < baseStart_5162847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162873 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_5162873 : Nat := 118140960795 + 5162873 * 2 ^ 59
def prefixEnd_5162873 : Nat := 4983230072969 + 3 ^ 40 * 5162873 * 2
def baseEnd_5162873 : Nat := 2651035407120283969343885

theorem tailTrace_5162873 : CollatzResearch.WordTrace tailWord_5162873 prefixEnd_5162873 2651035407120283969343885 := by
  unfold tailWord_5162873
  simp only [CollatzResearch.WordTrace]
  refine ⟨188305448224800344353925273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125536965483200229569283515 188305448224800344353925273)
  ·
    refine ⟨141229086168600258265443955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188305448224800344353925273 141229086168600258265443955)
    ·
      refine ⟨211843629252900387398165933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141229086168600258265443955 211843629252900387398165933)
      ·
        refine ⟨79441360969837645274312225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211843629252900387398165933 79441360969837645274312225)
        ·
          refine ⟨59581020727378233955734169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79441360969837645274312225 59581020727378233955734169)
          ·
            refine ⟨44685765545533675466800627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59581020727378233955734169 44685765545533675466800627)
            ·
              refine ⟨67028648318300513200200941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44685765545533675466800627 67028648318300513200200941)
              ·
                refine ⟨25135743119362692450075353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67028648318300513200200941 25135743119362692450075353)
                ·
                  refine ⟨18851807339522019337556515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25135743119362692450075353 18851807339522019337556515)
                  ·
                    refine ⟨28277711009283029006334773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18851807339522019337556515 28277711009283029006334773)
                    ·
                      refine ⟨2651035407120283969343885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28277711009283029006334773 2651035407120283969343885)
                      ·
                        rfl

theorem cell23_5162873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_5162873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162873 prefixEnd_5162873 := by exact prefixLift 5162873
  have htrace : WordTrace (prefixWord ++ tailWord_5162873) baseStart_5162873 baseEnd_5162873 := by
    simpa [prefixWord, tailWord_5162873, baseEnd_5162873] using wordTrace_append hprefix tailTrace_5162873
  have hstable : (prefixWord ++ tailWord_5162873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162873).length < 2 ^ (prefixWord ++ tailWord_5162873).sum := by decide
  have hdescent : baseEnd_5162873 < baseStart_5162873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162881 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5162881 : Nat := 118140960795 + 5162881 * 2 ^ 59
def prefixEnd_5162881 : Nat := 4983230072969 + 3 ^ 40 * 5162881 * 2
def baseEnd_5162881 : Nat := 2651039514965519938043849

theorem tailTrace_5162881 : CollatzResearch.WordTrace tailWord_5162881 prefixEnd_5162881 2651039514965519938043849 := by
  unfold tailWord_5162881
  simp only [CollatzResearch.WordTrace]
  refine ⟨188305740008771361720216497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125537160005847574480144331 188305740008771361720216497)
  ·
    refine ⟨141229305006578521290162373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188305740008771361720216497 141229305006578521290162373)
    ·
      refine ⟨26480494688733472741905445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141229305006578521290162373 26480494688733472741905445)
      ·
        refine ⟨4965092754137526139107271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26480494688733472741905445 4965092754137526139107271)
        ·
          refine ⟨7447639131206289208660907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965092754137526139107271 7447639131206289208660907)
          ·
            refine ⟨11171458696809433812991361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7447639131206289208660907 11171458696809433812991361)
            ·
              refine ⟨8378594022607075359743521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11171458696809433812991361 8378594022607075359743521)
              ·
                refine ⟨6283945516955306519807641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8378594022607075359743521 6283945516955306519807641)
                ·
                  refine ⟨4712959137716479889855731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283945516955306519807641 4712959137716479889855731)
                  ·
                    refine ⟨7069438706574719834783597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4712959137716479889855731 7069438706574719834783597)
                    ·
                      refine ⟨2651039514965519938043849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7069438706574719834783597 2651039514965519938043849)
                      ·
                        rfl

theorem cell23_5162881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5162881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162881 prefixEnd_5162881 := by exact prefixLift 5162881
  have htrace : WordTrace (prefixWord ++ tailWord_5162881) baseStart_5162881 baseEnd_5162881 := by
    simpa [prefixWord, tailWord_5162881, baseEnd_5162881] using wordTrace_append hprefix tailTrace_5162881
  have hstable : (prefixWord ++ tailWord_5162881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162881).length < 2 ^ (prefixWord ++ tailWord_5162881).sum := by decide
  have hdescent : baseEnd_5162881 < baseStart_5162881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162900 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_5162900 : Nat := 118140960795 + 5162900 * 2 ^ 59
def prefixEnd_5162900 : Nat := 4983230072969 + 3 ^ 40 * 5162900 * 2
def baseEnd_5162900 : Nat := 2651049271097955363706261

theorem tailTrace_5162900 : CollatzResearch.WordTrace tailWord_5162900 prefixEnd_5162900 2651049271097955363706261 := by
  unfold tailWord_5162900
  simp only [CollatzResearch.WordTrace]
  refine ⟨94153216497851263982579077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125537621997135018643438769 94153216497851263982579077)
  ·
    refine ⟨17653728093347111996733577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94153216497851263982579077 17653728093347111996733577)
    ·
      refine ⟨13240296070010333997550183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17653728093347111996733577 13240296070010333997550183)
      ·
        refine ⟨19860444105015500996325275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13240296070010333997550183 19860444105015500996325275)
        ·
          refine ⟨29790666157523251494487913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19860444105015500996325275 29790666157523251494487913)
          ·
            refine ⟨22342999618142438620865935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29790666157523251494487913 22342999618142438620865935)
            ·
              refine ⟨33514499427213657931298903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22342999618142438620865935 33514499427213657931298903)
              ·
                refine ⟨50271749140820486896948355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33514499427213657931298903 50271749140820486896948355)
                ·
                  refine ⟨75407623711230730345422533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50271749140820486896948355 75407623711230730345422533)
                  ·
                    refine ⟨14138929445855761939766725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75407623711230730345422533 14138929445855761939766725)
                    ·
                      refine ⟨2651049271097955363706261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14138929445855761939766725 2651049271097955363706261)
                      ·
                        rfl

theorem cell23_5162900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_5162900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162900 prefixEnd_5162900 := by exact prefixLift 5162900
  have htrace : WordTrace (prefixWord ++ tailWord_5162900) baseStart_5162900 baseEnd_5162900 := by
    simpa [prefixWord, tailWord_5162900, baseEnd_5162900] using wordTrace_append hprefix tailTrace_5162900
  have hstable : (prefixWord ++ tailWord_5162900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162900).length < 2 ^ (prefixWord ++ tailWord_5162900).sum := by decide
  have hdescent : baseEnd_5162900 < baseStart_5162900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162978 : List Nat := [3, 3, 3, 1, 3, 1, 1, 3, 5]
def baseStart_5162978 : Nat := 118140960795 + 5162978 * 2 ^ 59
def prefixEnd_5162978 : Nat := 4983230072969 + 3 ^ 40 * 5162978 * 2
def baseEnd_5162978 : Nat := 294565480287667339836767

theorem tailTrace_5162978 : CollatzResearch.WordTrace tailWord_5162978 prefixEnd_5162978 294565480287667339836767 := by
  unfold tailWord_5162978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47077319472354986821624397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125539518592946631524331725 47077319472354986821624397)
  ·
    refine ⟨17653994802133120058109149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47077319472354986821624397 17653994802133120058109149)
    ·
      refine ⟨6620248050799920021790931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17653994802133120058109149 6620248050799920021790931)
      ·
        refine ⟨9930372076199880032686397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6620248050799920021790931 9930372076199880032686397)
        ·
          refine ⟨3723889528574955012257399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9930372076199880032686397 3723889528574955012257399)
          ·
            refine ⟨5585834292862432518386099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723889528574955012257399 5585834292862432518386099)
            ·
              refine ⟨8378751439293648777579149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5585834292862432518386099 8378751439293648777579149)
              ·
                refine ⟨3142031789735118291592181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8378751439293648777579149 3142031789735118291592181)
                ·
                  refine ⟨294565480287667339836767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3142031789735118291592181 294565480287667339836767)
                  ·
                    rfl

theorem cell23_5162978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_5162978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162978 prefixEnd_5162978 := by exact prefixLift 5162978
  have htrace : WordTrace (prefixWord ++ tailWord_5162978) baseStart_5162978 baseEnd_5162978 := by
    simpa [prefixWord, tailWord_5162978, baseEnd_5162978] using wordTrace_append hprefix tailTrace_5162978
  have hstable : (prefixWord ++ tailWord_5162978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162978).length < 2 ^ (prefixWord ++ tailWord_5162978).sum := by decide
  have hdescent : baseEnd_5162978 < baseStart_5162978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5162980 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_5162980 : Nat := 118140960795 + 5162980 * 2 ^ 59
def prefixEnd_5162980 : Nat := 4983230072969 + 3 ^ 40 * 5162980 * 2
def baseEnd_5162980 : Nat := 2651090349550315050705893

theorem tailTrace_5162980 : CollatzResearch.WordTrace tailWord_5162980 prefixEnd_5162980 2651090349550315050705893 := by
  unfold tailWord_5162980
  simp only [CollatzResearch.WordTrace]
  refine ⟨94154675417706350814035197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125539567223608467752046929 94154675417706350814035197)
  ·
    refine ⟨35308003281639881555263199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94154675417706350814035197 35308003281639881555263199)
    ·
      refine ⟨52962004922459822332894799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35308003281639881555263199 52962004922459822332894799)
      ·
        refine ⟨79443007383689733499342199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52962004922459822332894799 79443007383689733499342199)
        ·
          refine ⟨119164511075534600249013299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79443007383689733499342199 119164511075534600249013299)
          ·
            refine ⟨178746766613301900373519949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119164511075534600249013299 178746766613301900373519949)
            ·
              refine ⟨67030037479988212640069981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178746766613301900373519949 67030037479988212640069981)
              ·
                refine ⟨25136264054995579740026243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67030037479988212640069981 25136264054995579740026243)
                ·
                  refine ⟨37704396082493369610039365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25136264054995579740026243 37704396082493369610039365)
                  ·
                    refine ⟨7069574265467506801882381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37704396082493369610039365 7069574265467506801882381)
                    ·
                      refine ⟨2651090349550315050705893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7069574265467506801882381 2651090349550315050705893)
                      ·
                        rfl

theorem cell23_5162980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_5162980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5162980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5162980 prefixEnd_5162980 := by exact prefixLift 5162980
  have htrace : WordTrace (prefixWord ++ tailWord_5162980) baseStart_5162980 baseEnd_5162980 := by
    simpa [prefixWord, tailWord_5162980, baseEnd_5162980] using wordTrace_append hprefix tailTrace_5162980
  have hstable : (prefixWord ++ tailWord_5162980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5162980).length < 2 ^ (prefixWord ++ tailWord_5162980).sum := by decide
  have hdescent : baseEnd_5162980 < baseStart_5162980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5162980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163003 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8]
def baseStart_5163003 : Nat := 118140960795 + 5163003 * 2 ^ 59
def prefixEnd_5163003 : Nat := 4983230072969 + 3 ^ 40 * 5163003 * 2
def baseEnd_5163003 : Nat := 2651102159605368460718287

theorem tailTrace_5163003 : CollatzResearch.WordTrace tailWord_5163003 prefixEnd_5163003 2651102159605368460718287 := by
  unfold tailWord_5163003
  simp only [CollatzResearch.WordTrace]
  refine ⟨188310189714329376556157663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125540126476219584370771775 188310189714329376556157663)
  ·
    refine ⟨282465284571494064834236495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188310189714329376556157663 282465284571494064834236495)
    ·
      refine ⟨423697926857241097251354743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282465284571494064834236495 423697926857241097251354743)
      ·
        refine ⟨635546890285861645877032115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423697926857241097251354743 635546890285861645877032115)
        ·
          refine ⟨953320335428792468815548173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635546890285861645877032115 953320335428792468815548173)
          ·
            refine ⟨357495125785797175805830565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 953320335428792468815548173 357495125785797175805830565)
            ·
              refine ⟨67030336084836970463593231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 357495125785797175805830565 67030336084836970463593231)
              ·
                refine ⟨100545504127255455695389847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67030336084836970463593231 100545504127255455695389847)
                ·
                  refine ⟨150818256190883183543084771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100545504127255455695389847 150818256190883183543084771)
                  ·
                    refine ⟨226227384286324775314627157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150818256190883183543084771 226227384286324775314627157)
                    ·
                      refine ⟨2651102159605368460718287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226227384286324775314627157 2651102159605368460718287)
                      ·
                        rfl

theorem cell23_5163003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_5163003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163003 prefixEnd_5163003 := by exact prefixLift 5163003
  have htrace : WordTrace (prefixWord ++ tailWord_5163003) baseStart_5163003 baseEnd_5163003 := by
    simpa [prefixWord, tailWord_5163003, baseEnd_5163003] using wordTrace_append hprefix tailTrace_5163003
  have hstable : (prefixWord ++ tailWord_5163003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163003).length < 2 ^ (prefixWord ++ tailWord_5163003).sum := by decide
  have hdescent : baseEnd_5163003 < baseStart_5163003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163027 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 3]
def baseStart_5163027 : Nat := 118140960795 + 5163027 * 2 ^ 59
def prefixEnd_5163027 : Nat := 4983230072969 + 3 ^ 40 * 5163027 * 2
def baseEnd_5163027 : Nat := 2651114483141076366818177

theorem tailTrace_5163027 : CollatzResearch.WordTrace tailWord_5163027 prefixEnd_5163027 2651114483141076366818177 := by
  unfold tailWord_5163027
  simp only [CollatzResearch.WordTrace]
  refine ⟨188311065066242428655031335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125540710044161619103354223 188311065066242428655031335)
  ·
    refine ⟨282466597599363642982547003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188311065066242428655031335 282466597599363642982547003)
    ·
      refine ⟨423699896399045464473820505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282466597599363642982547003 423699896399045464473820505)
      ·
        refine ⟨317774922299284098355365379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423699896399045464473820505 317774922299284098355365379)
        ·
          refine ⟨476662383448926147533048069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317774922299284098355365379 476662383448926147533048069)
          ·
            refine ⟨89374196896673652662446513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 476662383448926147533048069 89374196896673652662446513)
            ·
              refine ⟨67030647672505239496834885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89374196896673652662446513 67030647672505239496834885)
              ·
                refine ⟨12568246438594732405656541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67030647672505239496834885 12568246438594732405656541)
                ·
                  refine ⟨4713092414473024652121203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12568246438594732405656541 4713092414473024652121203)
                  ·
                    refine ⟨7069638621709536978181805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4713092414473024652121203 7069638621709536978181805)
                    ·
                      refine ⟨2651114483141076366818177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7069638621709536978181805 2651114483141076366818177)
                      ·
                        rfl

theorem cell23_5163027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 1, 3].length) (baseStart_5163027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163027 prefixEnd_5163027 := by exact prefixLift 5163027
  have htrace : WordTrace (prefixWord ++ tailWord_5163027) baseStart_5163027 baseEnd_5163027 := by
    simpa [prefixWord, tailWord_5163027, baseEnd_5163027] using wordTrace_append hprefix tailTrace_5163027
  have hstable : (prefixWord ++ tailWord_5163027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163027).length < 2 ^ (prefixWord ++ tailWord_5163027).sum := by decide
  have hdescent : baseEnd_5163027 < baseStart_5163027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163084 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 5, 2, 2]
def baseStart_5163084 : Nat := 118140960795 + 5163084 * 2 ^ 59
def prefixEnd_5163084 : Nat := 4983230072969 + 3 ^ 40 * 5163084 * 2
def baseEnd_5163084 : Nat := 2651143751538382643805415

theorem tailTrace_5163084 : CollatzResearch.WordTrace tailWord_5163084 prefixEnd_5163084 2651143751538382643805415 := by
  unfold tailWord_5163084
  simp only [CollatzResearch.WordTrace]
  refine ⟨94156572013517963694928153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125542096018023951593237537 94156572013517963694928153)
  ·
    refine ⟨70617429010138472771196115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94156572013517963694928153 70617429010138472771196115)
    ·
      refine ⟨105926143515207709156794173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70617429010138472771196115 105926143515207709156794173)
      ·
        refine ⟨39722303818202890933797815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105926143515207709156794173 39722303818202890933797815)
        ·
          refine ⟨59583455727304336400696723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39722303818202890933797815 59583455727304336400696723)
          ·
            refine ⟨89375183590956504601045085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59583455727304336400696723 89375183590956504601045085)
            ·
              refine ⟨33515693846608689225391907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89375183590956504601045085 33515693846608689225391907)
              ·
                refine ⟨50273540769913033838087861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33515693846608689225391907 50273540769913033838087861)
                ·
                  refine ⟨4713144447179346922320737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50273540769913033838087861 4713144447179346922320737)
                  ·
                    refine ⟨3534858335384510191740553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4713144447179346922320737 3534858335384510191740553)
                    ·
                      refine ⟨2651143751538382643805415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534858335384510191740553 2651143751538382643805415)
                      ·
                        rfl

theorem cell23_5163084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_5163084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163084 prefixEnd_5163084 := by exact prefixLift 5163084
  have htrace : WordTrace (prefixWord ++ tailWord_5163084) baseStart_5163084 baseEnd_5163084 := by
    simpa [prefixWord, tailWord_5163084, baseEnd_5163084] using wordTrace_append hprefix tailTrace_5163084
  have hstable : (prefixWord ++ tailWord_5163084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163084).length < 2 ^ (prefixWord ++ tailWord_5163084).sum := by decide
  have hdescent : baseEnd_5163084 < baseStart_5163084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163101 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5163101 : Nat := 118140960795 + 5163101 * 2 ^ 59
def prefixEnd_5163101 : Nat := 4983230072969 + 3 ^ 40 * 5163101 * 2
def baseEnd_5163101 : Nat := 2651152480709509077292837

theorem tailTrace_5163101 : CollatzResearch.WordTrace tailWord_5163101 prefixEnd_5163101 2651152480709509077292837 := by
  unfold tailWord_5163101
  simp only [CollatzResearch.WordTrace]
  refine ⟨188313764067974339293225157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125542509378649559528816771 188313764067974339293225157)
  ·
    refine ⟨35308830762745188617479717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188313764067974339293225157 35308830762745188617479717)
    ·
      refine ⟨6620405768014722865777447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35308830762745188617479717 6620405768014722865777447)
      ·
        refine ⟨9930608652022084298666171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6620405768014722865777447 9930608652022084298666171)
        ·
          refine ⟨14895912978033126447999257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9930608652022084298666171 14895912978033126447999257)
          ·
            refine ⟨11171934733524844835999443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14895912978033126447999257 11171934733524844835999443)
            ·
              refine ⟨16757902100287267253999165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11171934733524844835999443 16757902100287267253999165)
              ·
                refine ⟨6284213287607725220249687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16757902100287267253999165 6284213287607725220249687)
                ·
                  refine ⟨9426319931411587830374531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6284213287607725220249687 9426319931411587830374531)
                  ·
                    refine ⟨14139479897117381745561797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9426319931411587830374531 14139479897117381745561797)
                    ·
                      refine ⟨2651152480709509077292837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14139479897117381745561797 2651152480709509077292837)
                      ·
                        rfl

theorem cell23_5163101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5163101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163101 prefixEnd_5163101 := by exact prefixLift 5163101
  have htrace : WordTrace (prefixWord ++ tailWord_5163101) baseStart_5163101 baseEnd_5163101 := by
    simpa [prefixWord, tailWord_5163101, baseEnd_5163101] using wordTrace_append hprefix tailTrace_5163101
  have hstable : (prefixWord ++ tailWord_5163101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163101).length < 2 ^ (prefixWord ++ tailWord_5163101).sum := by decide
  have hdescent : baseEnd_5163101 < baseStart_5163101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163104 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3]
def baseStart_5163104 : Nat := 118140960795 + 5163104 * 2 ^ 59
def prefixEnd_5163104 : Nat := 4983230072969 + 3 ^ 40 * 5163104 * 2
def baseEnd_5163104 : Nat := 2651154021151472565555323

theorem tailTrace_5163104 : CollatzResearch.WordTrace tailWord_5163104 prefixEnd_5163104 2651154021151472565555323 := by
  unfold tailWord_5163104
  simp only [CollatzResearch.WordTrace]
  refine ⟨94156936743481735402792183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125542582324642313870389577 94156936743481735402792183)
  ·
    refine ⟨141235405115222603104188275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94156936743481735402792183 141235405115222603104188275)
    ·
      refine ⟨211853107672833904656282413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141235405115222603104188275 211853107672833904656282413)
      ·
        refine ⟨79444915377312714246105905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211853107672833904656282413 79444915377312714246105905)
        ·
          refine ⟨59583686532984535684579429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79444915377312714246105905 59583686532984535684579429)
          ·
            refine ⟨11171941224934600440858643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59583686532984535684579429 11171941224934600440858643)
            ·
              refine ⟨16757911837401900661287965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11171941224934600440858643 16757911837401900661287965)
              ·
                refine ⟨6284216939025712747982987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16757911837401900661287965 6284216939025712747982987)
                ·
                  refine ⟨9426325408538569121974481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6284216939025712747982987 9426325408538569121974481)
                  ·
                    refine ⟨7069744056403926841480861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9426325408538569121974481 7069744056403926841480861)
                    ·
                      refine ⟨2651154021151472565555323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7069744056403926841480861 2651154021151472565555323)
                      ·
                        rfl

theorem cell23_5163104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_5163104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163104 prefixEnd_5163104 := by exact prefixLift 5163104
  have htrace : WordTrace (prefixWord ++ tailWord_5163104) baseStart_5163104 baseEnd_5163104 := by
    simpa [prefixWord, tailWord_5163104, baseEnd_5163104] using wordTrace_append hprefix tailTrace_5163104
  have hstable : (prefixWord ++ tailWord_5163104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163104).length < 2 ^ (prefixWord ++ tailWord_5163104).sum := by decide
  have hdescent : baseEnd_5163104 < baseStart_5163104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163118 : List Nat := [4, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_5163118 : Nat := 118140960795 + 5163118 * 2 ^ 59
def prefixEnd_5163118 : Nat := 4983230072969 + 3 ^ 40 * 5163118 * 2
def baseEnd_5163118 : Nat := 2651161209880635510780259

theorem tailTrace_5163118 : CollatzResearch.WordTrace tailWord_5163118 prefixEnd_5163118 2651161209880635510780259 := by
  unfold tailWord_5163118
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539298013614093899574251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125542922739275167464396005 23539298013614093899574251)
  ·
    refine ⟨35308947020421140849361377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23539298013614093899574251 35308947020421140849361377)
    ·
      refine ⟨26481710265315855637021033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35308947020421140849361377 26481710265315855637021033)
      ·
        refine ⟨19861282698986891727765775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26481710265315855637021033 19861282698986891727765775)
        ·
          refine ⟨29791924048480337591648663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19861282698986891727765775 29791924048480337591648663)
          ·
            refine ⟨44687886072720506387472995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29791924048480337591648663 44687886072720506387472995)
            ·
              refine ⟨67031829109080759581209493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44687886072720506387472995 67031829109080759581209493)
              ·
                refine ⟨3142116989488160605369195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67031829109080759581209493 3142116989488160605369195)
                ·
                  refine ⟨4713175484232240908053793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142116989488160605369195 4713175484232240908053793)
                  ·
                    refine ⟨3534881613174180681040345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4713175484232240908053793 3534881613174180681040345)
                    ·
                      refine ⟨2651161209880635510780259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3534881613174180681040345 2651161209880635510780259)
                      ·
                        rfl

theorem cell23_5163118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_5163118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163118 prefixEnd_5163118 := by exact prefixLift 5163118
  have htrace : WordTrace (prefixWord ++ tailWord_5163118) baseStart_5163118 baseEnd_5163118 := by
    simpa [prefixWord, tailWord_5163118, baseEnd_5163118] using wordTrace_append hprefix tailTrace_5163118
  have hstable : (prefixWord ++ tailWord_5163118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163118).length < 2 ^ (prefixWord ++ tailWord_5163118).sum := by decide
  have hdescent : baseEnd_5163118 < baseStart_5163118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163130 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_5163130 : Nat := 118140960795 + 5163130 * 2 ^ 59
def prefixEnd_5163130 : Nat := 4983230072969 + 3 ^ 40 * 5163130 * 2
def baseEnd_5163130 : Nat := 2651167371648489463830203

theorem tailTrace_5163130 : CollatzResearch.WordTrace tailWord_5163130 prefixEnd_5163130 2651167371648489463830203 := by
  unfold tailWord_5163130
  simp only [CollatzResearch.WordTrace]
  refine ⟨47078705446217319311507711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125543214523246184830687229 47078705446217319311507711)
  ·
    refine ⟨70618058169325978967261567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47078705446217319311507711 70618058169325978967261567)
    ·
      refine ⟨105927087253988968450892351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70618058169325978967261567 105927087253988968450892351)
      ·
        refine ⟨158890630880983452676338527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105927087253988968450892351 158890630880983452676338527)
        ·
          refine ⟨238335946321475179014507791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158890630880983452676338527 238335946321475179014507791)
          ·
            refine ⟨357503919482212768521761687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238335946321475179014507791 357503919482212768521761687)
            ·
              refine ⟨536255879223319152782642531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357503919482212768521761687 536255879223319152782642531)
              ·
                refine ⟨804383818834978729173963797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536255879223319152782642531 804383818834978729173963797)
                ·
                  refine ⟨37705491507889627930029553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 804383818834978729173963797 37705491507889627930029553)
                  ·
                    refine ⟨28279118630917220947522165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37705491507889627930029553 28279118630917220947522165)
                    ·
                      refine ⟨2651167371648489463830203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28279118630917220947522165 2651167371648489463830203)
                      ·
                        rfl

theorem cell23_5163130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_5163130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163130 prefixEnd_5163130 := by exact prefixLift 5163130
  have htrace : WordTrace (prefixWord ++ tailWord_5163130) baseStart_5163130 baseEnd_5163130 := by
    simpa [prefixWord, tailWord_5163130, baseEnd_5163130] using wordTrace_append hprefix tailTrace_5163130
  have hstable : (prefixWord ++ tailWord_5163130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163130).length < 2 ^ (prefixWord ++ tailWord_5163130).sum := by decide
  have hdescent : baseEnd_5163130 < baseStart_5163130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163185 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5163185 : Nat := 118140960795 + 5163185 * 2 ^ 59
def prefixEnd_5163185 : Nat := 4983230072969 + 3 ^ 40 * 5163185 * 2
def baseEnd_5163185 : Nat := 2651195613084486748642451

theorem tailTrace_5163185 : CollatzResearch.WordTrace tailWord_5163185 prefixEnd_5163185 2651195613084486748642451 := by
  unfold tailWord_5163185
  simp only [CollatzResearch.WordTrace]
  refine ⟨188316827799670021639283009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125544551866446681092855339 188316827799670021639283009)
  ·
    refine ⟨141237620849752516229462257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188316827799670021639283009 141237620849752516229462257)
    ·
      refine ⟨105928215637314387172096693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141237620849752516229462257 105928215637314387172096693)
      ·
        refine ⟨9930770215998223797384065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105928215637314387172096693 9930770215998223797384065)
        ·
          refine ⟨7448077661998667848038049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9930770215998223797384065 7448077661998667848038049)
          ·
            refine ⟨5586058246499000886028537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7448077661998667848038049 5586058246499000886028537)
            ·
              refine ⟨4189543684874250664521403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5586058246499000886028537 4189543684874250664521403)
              ·
                refine ⟨6284315527311375996782105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4189543684874250664521403 6284315527311375996782105)
                ·
                  refine ⟨4713236645483531997586579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6284315527311375996782105 4713236645483531997586579)
                  ·
                    refine ⟨7069854968225297996379869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4713236645483531997586579 7069854968225297996379869)
                    ·
                      refine ⟨2651195613084486748642451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7069854968225297996379869 2651195613084486748642451)
                      ·
                        rfl

theorem cell23_5163185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5163185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163185 prefixEnd_5163185 := by exact prefixLift 5163185
  have htrace : WordTrace (prefixWord ++ tailWord_5163185) baseStart_5163185 baseEnd_5163185 := by
    simpa [prefixWord, tailWord_5163185, baseEnd_5163185] using wordTrace_append hprefix tailTrace_5163185
  have hstable : (prefixWord ++ tailWord_5163185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163185).length < 2 ^ (prefixWord ++ tailWord_5163185).sum := by decide
  have hdescent : baseEnd_5163185 < baseStart_5163185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163207 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_5163207 : Nat := 118140960795 + 5163207 * 2 ^ 59
def prefixEnd_5163207 : Nat := 4983230072969 + 3 ^ 40 * 5163207 * 2
def baseEnd_5163207 : Nat := 2651206909658885662567349

theorem tailTrace_5163207 : CollatzResearch.WordTrace tailWord_5163207 prefixEnd_5163207 2651206909658885662567349 := by
  unfold tailWord_5163207
  simp only [CollatzResearch.WordTrace]
  refine ⟨188317630205590319396583875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125545086803726879597722583 188317630205590319396583875)
  ·
    refine ⟨282476445308385479094875813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188317630205590319396583875 282476445308385479094875813)
    ·
      refine ⟨52964333495322277330289215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282476445308385479094875813 52964333495322277330289215)
      ·
        refine ⟨79446500242983415995433823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52964333495322277330289215 79446500242983415995433823)
        ·
          refine ⟨119169750364475123993150735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79446500242983415995433823 119169750364475123993150735)
          ·
            refine ⟨178754625546712685989726103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119169750364475123993150735 178754625546712685989726103)
            ·
              refine ⟨268131938320069028984589155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178754625546712685989726103 268131938320069028984589155)
              ·
                refine ⟨402197907480103543476883733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268131938320069028984589155 402197907480103543476883733)
                ·
                  refine ⟨18853026913129853600478925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 402197907480103543476883733 18853026913129853600478925)
                  ·
                    refine ⟨7069885092423695100179597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18853026913129853600478925 7069885092423695100179597)
                    ·
                      refine ⟨2651206909658885662567349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7069885092423695100179597 2651206909658885662567349)
                      ·
                        rfl

theorem cell23_5163207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_5163207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163207 prefixEnd_5163207 := by exact prefixLift 5163207
  have htrace : WordTrace (prefixWord ++ tailWord_5163207) baseStart_5163207 baseEnd_5163207 := by
    simpa [prefixWord, tailWord_5163207, baseEnd_5163207] using wordTrace_append hprefix tailTrace_5163207
  have hstable : (prefixWord ++ tailWord_5163207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163207).length < 2 ^ (prefixWord ++ tailWord_5163207).sum := by decide
  have hdescent : baseEnd_5163207 < baseStart_5163207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163264 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4]
def baseStart_5163264 : Nat := 118140960795 + 5163264 * 2 ^ 59
def prefixEnd_5163264 : Nat := 4983230072969 + 3 ^ 40 * 5163264 * 2
def baseEnd_5163264 : Nat := 2651236178056191939554587

theorem tailTrace_5163264 : CollatzResearch.WordTrace tailWord_5163264 prefixEnd_5163264 2651236178056191939554587 := by
  unfold tailWord_5163264
  simp only [CollatzResearch.WordTrace]
  refine ⟨94159854583191909065704423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125546472777589212087605897 94159854583191909065704423)
  ·
    refine ⟨141239781874787863598556635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94159854583191909065704423 141239781874787863598556635)
    ·
      refine ⟨211859672812181795397834953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141239781874787863598556635 211859672812181795397834953)
      ·
        refine ⟨158894754609136346548376215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211859672812181795397834953 158894754609136346548376215)
        ·
          refine ⟨238342131913704519822564323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158894754609136346548376215 238342131913704519822564323)
          ·
            refine ⟨357513197870556779733846485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238342131913704519822564323 357513197870556779733846485)
            ·
              refine ⟨8379215575091174525012027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 357513197870556779733846485 8379215575091174525012027)
              ·
                refine ⟨12568823362636761787518041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8379215575091174525012027 12568823362636761787518041)
                ·
                  refine ⟨9426617521977571340638531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12568823362636761787518041 9426617521977571340638531)
                  ·
                    refine ⟨14139926282966357010957797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9426617521977571340638531 14139926282966357010957797)
                    ·
                      refine ⟨2651236178056191939554587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14139926282966357010957797 2651236178056191939554587)
                      ·
                        rfl

theorem cell23_5163264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_5163264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163264 prefixEnd_5163264 := by exact prefixLift 5163264
  have htrace : WordTrace (prefixWord ++ tailWord_5163264) baseStart_5163264 baseEnd_5163264 := by
    simpa [prefixWord, tailWord_5163264, baseEnd_5163264] using wordTrace_append hprefix tailTrace_5163264
  have hstable : (prefixWord ++ tailWord_5163264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163264).length < 2 ^ (prefixWord ++ tailWord_5163264).sum := by decide
  have hdescent : baseEnd_5163264 < baseStart_5163264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163291 : List Nat := [1, 1, 1, 1, 1, 1, 8, 4, 1, 4]
def baseStart_5163291 : Nat := 118140960795 + 5163291 * 2 ^ 59
def prefixEnd_5163291 : Nat := 4983230072969 + 3 ^ 40 * 5163291 * 2
def baseEnd_5163291 : Nat := 883750014011287777972321

theorem tailTrace_5163291 : CollatzResearch.WordTrace tailWord_5163291 prefixEnd_5163291 883750014011287777972321 := by
  unfold tailWord_5163291
  simp only [CollatzResearch.WordTrace]
  refine ⟨188320693937286001742641727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125547129291524001161761151 188320693937286001742641727)
  ·
    refine ⟨282481040905929002613962591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188320693937286001742641727 282481040905929002613962591)
    ·
      refine ⟨423721561358893503920943887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282481040905929002613962591 423721561358893503920943887)
      ·
        refine ⟨635582342038340255881415831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423721561358893503920943887 635582342038340255881415831)
        ·
          refine ⟨953373513057510383822123747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635582342038340255881415831 953373513057510383822123747)
          ·
            refine ⟨1430060269586265575733185621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953373513057510383822123747 1430060269586265575733185621)
            ·
              refine ⟨16758518784214049715623269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1430060269586265575733185621 16758518784214049715623269)
              ·
                refine ⟨3142222272040134321679363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16758518784214049715623269 3142222272040134321679363)
                ·
                  refine ⟨4713333408060201482519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142222272040134321679363 4713333408060201482519045)
                  ·
                    refine ⟨883750014011287777972321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4713333408060201482519045 883750014011287777972321)
                    ·
                      rfl

theorem cell23_5163291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 1, 4].length) (baseStart_5163291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163291 prefixEnd_5163291 := by exact prefixLift 5163291
  have htrace : WordTrace (prefixWord ++ tailWord_5163291) baseStart_5163291 baseEnd_5163291 := by
    simpa [prefixWord, tailWord_5163291, baseEnd_5163291] using wordTrace_append hprefix tailTrace_5163291
  have hstable : (prefixWord ++ tailWord_5163291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163291).length < 2 ^ (prefixWord ++ tailWord_5163291).sum := by decide
  have hdescent : baseEnd_5163291 < baseStart_5163291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163347 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 5, 6]
def baseStart_5163347 : Nat := 118140960795 + 5163347 * 2 ^ 59
def prefixEnd_5163347 : Nat := 4983230072969 + 3 ^ 40 * 5163347 * 2
def baseEnd_5163347 : Nat := 883759598983505038272235

theorem tailTrace_5163347 : CollatzResearch.WordTrace tailWord_5163347 prefixEnd_5163347 883759598983505038272235 := by
  unfold tailWord_5163347
  simp only [CollatzResearch.WordTrace]
  refine ⟨188322736425083123306680295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125548490950055415537786863 188322736425083123306680295)
  ·
    refine ⟨282484104637624684960020443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188322736425083123306680295 282484104637624684960020443)
    ·
      refine ⟨423726156956437027440030665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282484104637624684960020443 423726156956437027440030665)
      ·
        refine ⟨317794617717327770580022999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423726156956437027440030665 317794617717327770580022999)
        ·
          refine ⟨476691926575991655870034499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317794617717327770580022999 476691926575991655870034499)
          ·
            refine ⟨715037889863987483805051749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476691926575991655870034499 715037889863987483805051749)
            ·
              refine ⟨134069604349497653213447203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 715037889863987483805051749 134069604349497653213447203)
              ·
                refine ⟨201104406524246479820170805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134069604349497653213447203 201104406524246479820170805)
                ·
                  refine ⟨18853538111648107483141013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201104406524246479820170805 18853538111648107483141013)
                  ·
                    refine ⟨883759598983505038272235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18853538111648107483141013 883759598983505038272235)
                    ·
                      rfl

theorem cell23_5163347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 6].length) (baseStart_5163347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163347 prefixEnd_5163347 := by exact prefixLift 5163347
  have htrace : WordTrace (prefixWord ++ tailWord_5163347) baseStart_5163347 baseEnd_5163347 := by
    simpa [prefixWord, tailWord_5163347, baseEnd_5163347] using wordTrace_append hprefix tailTrace_5163347
  have hstable : (prefixWord ++ tailWord_5163347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163347).length < 2 ^ (prefixWord ++ tailWord_5163347).sum := by decide
  have hdescent : baseEnd_5163347 < baseStart_5163347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163348 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_5163348 : Nat := 118140960795 + 5163348 * 2 ^ 59
def prefixEnd_5163348 : Nat := 4983230072969 + 3 ^ 40 * 5163348 * 2
def baseEnd_5163348 : Nat := 2651279310431169610904201

theorem tailTrace_5163348 : CollatzResearch.WordTrace tailWord_5163348 prefixEnd_5163348 2651279310431169610904201 := by
  unfold tailWord_5163348
  simp only [CollatzResearch.WordTrace]
  refine ⟨94161386449039750238733349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125548515265386333651644465 94161386449039750238733349)
  ·
    refine ⟨17655259959194953169762503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94161386449039750238733349 17655259959194953169762503)
    ·
      refine ⟨26482889938792429754643755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17655259959194953169762503 26482889938792429754643755)
      ·
        refine ⟨39724334908188644631965633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26482889938792429754643755 39724334908188644631965633)
        ·
          refine ⟨29793251181141483473974225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39724334908188644631965633 29793251181141483473974225)
          ·
            refine ⟨22344938385856112605480669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29793251181141483473974225 22344938385856112605480669)
            ·
              refine ⟨8379351894696042227055251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22344938385856112605480669 8379351894696042227055251)
              ·
                refine ⟨12569027842044063340582877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8379351894696042227055251 12569027842044063340582877)
                ·
                  refine ⟨4713385440766523752718579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12569027842044063340582877 4713385440766523752718579)
                  ·
                    refine ⟨7070078161149785629077869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4713385440766523752718579 7070078161149785629077869)
                    ·
                      refine ⟨2651279310431169610904201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7070078161149785629077869 2651279310431169610904201)
                      ·
                        rfl

theorem cell23_5163348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_5163348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163348 prefixEnd_5163348 := by exact prefixLift 5163348
  have htrace : WordTrace (prefixWord ++ tailWord_5163348) baseStart_5163348 baseEnd_5163348 := by
    simpa [prefixWord, tailWord_5163348, baseEnd_5163348] using wordTrace_append hprefix tailTrace_5163348
  have hstable : (prefixWord ++ tailWord_5163348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163348).length < 2 ^ (prefixWord ++ tailWord_5163348).sum := by decide
  have hdescent : baseEnd_5163348 < baseStart_5163348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163354 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_5163354 : Nat := 118140960795 + 5163354 * 2 ^ 59
def prefixEnd_5163354 : Nat := 4983230072969 + 3 ^ 40 * 5163354 * 2
def baseEnd_5163354 : Nat := 2651282391315096587429173

theorem tailTrace_5163354 : CollatzResearch.WordTrace tailWord_5163354 prefixEnd_5163354 2651282391315096587429173 := by
  unfold tailWord_5163354
  simp only [CollatzResearch.WordTrace]
  refine ⟨47080747934014440875546279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125548661157371842334790077 47080747934014440875546279)
  ·
    refine ⟨70621121901021661313319419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47080747934014440875546279 70621121901021661313319419)
    ·
      refine ⟨105931682851532491969979129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70621121901021661313319419 105931682851532491969979129)
      ·
        refine ⟨79448762138649368977484347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105931682851532491969979129 79448762138649368977484347)
        ·
          refine ⟨119173143207974053466226521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79448762138649368977484347 119173143207974053466226521)
          ·
            refine ⟨89379857405980540099669891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119173143207974053466226521 89379857405980540099669891)
            ·
              refine ⟨134069786108970810149504837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89379857405980540099669891 134069786108970810149504837)
              ·
                refine ⟨25138084895432026903032157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134069786108970810149504837 25138084895432026903032157)
                ·
                  refine ⟨9426781835787010088637059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25138084895432026903032157 9426781835787010088637059)
                  ·
                    refine ⟨14140172753680515132955589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9426781835787010088637059 14140172753680515132955589)
                    ·
                      refine ⟨2651282391315096587429173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14140172753680515132955589 2651282391315096587429173)
                      ·
                        rfl

theorem cell23_5163354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_5163354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163354 prefixEnd_5163354 := by exact prefixLift 5163354
  have htrace : WordTrace (prefixWord ++ tailWord_5163354) baseStart_5163354 baseEnd_5163354 := by
    simpa [prefixWord, tailWord_5163354, baseEnd_5163354] using wordTrace_append hprefix tailTrace_5163354
  have hstable : (prefixWord ++ tailWord_5163354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163354).length < 2 ^ (prefixWord ++ tailWord_5163354).sum := by decide
  have hdescent : baseEnd_5163354 < baseStart_5163354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163364 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_5163364 : Nat := 118140960795 + 5163364 * 2 ^ 59
def prefixEnd_5163364 : Nat := 4983230072969 + 3 ^ 40 * 5163364 * 2
def baseEnd_5163364 : Nat := 883762508707213849434709

theorem tailTrace_5163364 : CollatzResearch.WordTrace tailWord_5163364 prefixEnd_5163364 883762508707213849434709 := by
  unfold tailWord_5163364
  simp only [CollatzResearch.WordTrace]
  refine ⟨94161678233010767605024573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125548904310681023473366097 94161678233010767605024573)
  ·
    refine ⟨35310629337379037851884215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94161678233010767605024573 35310629337379037851884215)
    ·
      refine ⟨52965944006068556777826323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35310629337379037851884215 52965944006068556777826323)
      ·
        refine ⟨79448916009102835166739485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52965944006068556777826323 79448916009102835166739485)
        ·
          refine ⟨29793343503413563187527307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79448916009102835166739485 29793343503413563187527307)
          ·
            refine ⟨44690015255120344781290961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29793343503413563187527307 44690015255120344781290961)
            ·
              refine ⟨33517511441340258585968221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44690015255120344781290961 33517511441340258585968221)
              ·
                refine ⟨12569066790502596969738083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33517511441340258585968221 12569066790502596969738083)
                ·
                  refine ⟨18853600185753895454607125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12569066790502596969738083 18853600185753895454607125)
                  ·
                    refine ⟨883762508707213849434709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18853600185753895454607125 883762508707213849434709)
                    ·
                      rfl

theorem cell23_5163364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_5163364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163364 prefixEnd_5163364 := by exact prefixLift 5163364
  have htrace : WordTrace (prefixWord ++ tailWord_5163364) baseStart_5163364 baseEnd_5163364 := by
    simpa [prefixWord, tailWord_5163364, baseEnd_5163364] using wordTrace_append hprefix tailTrace_5163364
  have hstable : (prefixWord ++ tailWord_5163364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163364).length < 2 ^ (prefixWord ++ tailWord_5163364).sum := by decide
  have hdescent : baseEnd_5163364 < baseStart_5163364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163368 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 1, 5]
def baseStart_5163368 : Nat := 118140960795 + 5163368 * 2 ^ 59
def prefixEnd_5163368 : Nat := 4983230072969 + 3 ^ 40 * 5163368 * 2
def baseEnd_5163368 : Nat := 883763193348086510884703

theorem tailTrace_5163368 : CollatzResearch.WordTrace tailWord_5163368 prefixEnd_5163368 883763193348086510884703 := by
  unfold tailWord_5163368
  simp only [CollatzResearch.WordTrace]
  refine ⟨94161751179003521946597379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125549001572004695928796505 94161751179003521946597379)
  ·
    refine ⟨141242626768505282919896069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94161751179003521946597379 141242626768505282919896069)
    ·
      refine ⟨26482992519094740547480513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141242626768505282919896069 26482992519094740547480513)
      ·
        refine ⟨19862244389321055410610385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26482992519094740547480513 19862244389321055410610385)
        ·
          refine ⟨14896683291990791557957789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19862244389321055410610385 14896683291990791557957789)
          ·
            refine ⟨5586256234496546834234171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14896683291990791557957789 5586256234496546834234171)
            ·
              refine ⟨8379384351744820251351257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586256234496546834234171 8379384351744820251351257)
              ·
                refine ⟨6284538263808615188513443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8379384351744820251351257 6284538263808615188513443)
                ·
                  refine ⟨9426807395712922782770165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6284538263808615188513443 9426807395712922782770165)
                  ·
                    refine ⟨883763193348086510884703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9426807395712922782770165 883763193348086510884703)
                    ·
                      rfl

theorem cell23_5163368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_5163368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163368 prefixEnd_5163368 := by exact prefixLift 5163368
  have htrace : WordTrace (prefixWord ++ tailWord_5163368) baseStart_5163368 baseEnd_5163368 := by
    simpa [prefixWord, tailWord_5163368, baseEnd_5163368] using wordTrace_append hprefix tailTrace_5163368
  have hstable : (prefixWord ++ tailWord_5163368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163368).length < 2 ^ (prefixWord ++ tailWord_5163368).sum := by decide
  have hdescent : baseEnd_5163368 < baseStart_5163368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163381 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_5163381 : Nat := 118140960795 + 5163381 * 2 ^ 59
def prefixEnd_5163381 : Nat := 4983230072969 + 3 ^ 40 * 5163381 * 2
def baseEnd_5163381 : Nat := 883765418430922660597183

theorem tailTrace_5163381 : CollatzResearch.WordTrace tailWord_5163381 prefixEnd_5163381 883765418430922660597183 := by
  unfold tailWord_5163381
  simp only [CollatzResearch.WordTrace]
  refine ⟨188323976506959947113417997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125549317671306631408945331 188323976506959947113417997)
  ·
    refine ⟨70621491190109980167531749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188323976506959947113417997 70621491190109980167531749)
    ·
      refine ⟨13241529598145621281412203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70621491190109980167531749 13241529598145621281412203)
      ·
        refine ⟨19862294397218431922118305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13241529598145621281412203 19862294397218431922118305)
        ·
          refine ⟨14896720797913823941588729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19862294397218431922118305 14896720797913823941588729)
          ·
            refine ⟨11172540598435367956191547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14896720797913823941588729 11172540598435367956191547)
            ·
              refine ⟨16758810897653051934287321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11172540598435367956191547 16758810897653051934287321)
              ·
                refine ⟨12569108173239788950715491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16758810897653051934287321 12569108173239788950715491)
                ·
                  refine ⟨18853662259859683426073237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12569108173239788950715491 18853662259859683426073237)
                  ·
                    refine ⟨883765418430922660597183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18853662259859683426073237 883765418430922660597183)
                    ·
                      rfl

theorem cell23_5163381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_5163381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163381 prefixEnd_5163381 := by exact prefixLift 5163381
  have htrace : WordTrace (prefixWord ++ tailWord_5163381) baseStart_5163381 baseEnd_5163381 := by
    simpa [prefixWord, tailWord_5163381, baseEnd_5163381] using wordTrace_append hprefix tailTrace_5163381
  have hstable : (prefixWord ++ tailWord_5163381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163381).length < 2 ^ (prefixWord ++ tailWord_5163381).sum := by decide
  have hdescent : baseEnd_5163381 < baseStart_5163381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163422 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5163422 : Nat := 118140960795 + 5163422 * 2 ^ 59
def prefixEnd_5163422 : Nat := 4983230072969 + 3 ^ 40 * 5163422 * 2
def baseEnd_5163422 : Nat := 2651317307999602321378861

theorem tailTrace_5163422 : CollatzResearch.WordTrace tailWord_5163422 prefixEnd_5163422 2651317307999602321378861 := by
  unfold tailWord_5163422
  simp only [CollatzResearch.WordTrace]
  refine ⟨23540683987476426389457565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125550314599874274077107013 23540683987476426389457565)
  ·
    refine ⟨8827756495303659896046587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23540683987476426389457565 8827756495303659896046587)
    ·
      refine ⟨13241634742955489844069881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8827756495303659896046587 13241634742955489844069881)
      ·
        refine ⟨9931226057216617383052411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13241634742955489844069881 9931226057216617383052411)
        ·
          refine ⟨14896839085824926074578617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9931226057216617383052411 14896839085824926074578617)
          ·
            refine ⟨11172629314368694555933963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14896839085824926074578617 11172629314368694555933963)
            ·
              refine ⟨16758943971553041833900945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11172629314368694555933963 16758943971553041833900945)
              ·
                refine ⟨12569207978664781375425709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16758943971553041833900945 12569207978664781375425709)
                ·
                  refine ⟨4713452991999293015784641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12569207978664781375425709 4713452991999293015784641)
                  ·
                    refine ⟨3535089743999469761838481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4713452991999293015784641 3535089743999469761838481)
                    ·
                      refine ⟨2651317307999602321378861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535089743999469761838481 2651317307999602321378861)
                      ·
                        rfl

theorem cell23_5163422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5163422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163422 prefixEnd_5163422 := by exact prefixLift 5163422
  have htrace : WordTrace (prefixWord ++ tailWord_5163422) baseStart_5163422 baseEnd_5163422 := by
    simpa [prefixWord, tailWord_5163422, baseEnd_5163422] using wordTrace_append hprefix tailTrace_5163422
  have hstable : (prefixWord ++ tailWord_5163422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163422).length < 2 ^ (prefixWord ++ tailWord_5163422).sum := by decide
  have hdescent : baseEnd_5163422 < baseStart_5163422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163514 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_5163514 : Nat := 118140960795 + 5163514 * 2 ^ 59
def prefixEnd_5163514 : Nat := 4983230072969 + 3 ^ 40 * 5163514 * 2
def baseEnd_5163514 : Nat := 883788182739938653809479

theorem tailTrace_5163514 : CollatzResearch.WordTrace tailWord_5163514 prefixEnd_5163514 883788182739938653809479 := by
  unfold tailWord_5163514
  simp only [CollatzResearch.WordTrace]
  refine ⟨47082206853869527707002399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125552551610318740552006397 47082206853869527707002399)
  ·
    refine ⟨70623310280804291560503599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47082206853869527707002399 70623310280804291560503599)
    ·
      refine ⟨105934965421206437340755399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70623310280804291560503599 105934965421206437340755399)
      ·
        refine ⟨158902448131809656011133099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105934965421206437340755399 158902448131809656011133099)
        ·
          refine ⟨238353672197714484016699649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158902448131809656011133099 238353672197714484016699649)
          ·
            refine ⟨178765254148285863012524737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238353672197714484016699649 178765254148285863012524737)
            ·
              refine ⟨134073940611214397259393553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178765254148285863012524737 134073940611214397259393553)
              ·
                refine ⟨100555455458410797944545165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134073940611214397259393553 100555455458410797944545165)
                ·
                  refine ⟨37708295796904049229204437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100555455458410797944545165 37708295796904049229204437)
                  ·
                    refine ⟨883788182739938653809479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37708295796904049229204437 883788182739938653809479)
                    ·
                      rfl

theorem cell23_5163514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_5163514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163514 prefixEnd_5163514 := by exact prefixLift 5163514
  have htrace : WordTrace (prefixWord ++ tailWord_5163514) baseStart_5163514 baseEnd_5163514 := by
    simpa [prefixWord, tailWord_5163514, baseEnd_5163514] using wordTrace_append hprefix tailTrace_5163514
  have hstable : (prefixWord ++ tailWord_5163514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163514).length < 2 ^ (prefixWord ++ tailWord_5163514).sum := by decide
  have hdescent : baseEnd_5163514 < baseStart_5163514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163548 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_5163548 : Nat := 118140960795 + 5163548 * 2 ^ 59
def prefixEnd_5163548 : Nat := 4983230072969 + 3 ^ 40 * 5163548 * 2
def baseEnd_5163548 : Nat := 883794002187356276134427

theorem tailTrace_5163548 : CollatzResearch.WordTrace tailWord_5163548 prefixEnd_5163548 883794002187356276134427 := by
  unfold tailWord_5163548
  simp only [CollatzResearch.WordTrace]
  refine ⟨94165033748677467317373649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125553378331569956423164865 94165033748677467317373649)
  ·
    refine ⟨70623775311508100488030237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94165033748677467317373649 70623775311508100488030237)
    ·
      refine ⟨26483915741815537683011339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70623775311508100488030237 26483915741815537683011339)
      ·
        refine ⟨39725873612723306524517009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26483915741815537683011339 39725873612723306524517009)
        ·
          refine ⟨29794405209542479893387757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39725873612723306524517009 29794405209542479893387757)
          ·
            refine ⟨11172901953578429960020409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29794405209542479893387757 11172901953578429960020409)
            ·
              refine ⟨8379676465183822470015307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11172901953578429960020409 8379676465183822470015307)
              ·
                refine ⟨12569514697775733705022961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8379676465183822470015307 12569514697775733705022961)
                ·
                  refine ⟨9427136023331800278767221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12569514697775733705022961 9427136023331800278767221)
                  ·
                    refine ⟨883794002187356276134427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9427136023331800278767221 883794002187356276134427)
                    ·
                      rfl

theorem cell23_5163548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_5163548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163548 prefixEnd_5163548 := by exact prefixLift 5163548
  have htrace : WordTrace (prefixWord ++ tailWord_5163548) baseStart_5163548 baseEnd_5163548 := by
    simpa [prefixWord, tailWord_5163548, baseEnd_5163548] using wordTrace_append hprefix tailTrace_5163548
  have hstable : (prefixWord ++ tailWord_5163548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163548).length < 2 ^ (prefixWord ++ tailWord_5163548).sum := by decide
  have hdescent : baseEnd_5163548 < baseStart_5163548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163585 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5163585 : Nat := 118140960795 + 5163585 * 2 ^ 59
def prefixEnd_5163585 : Nat := 4983230072969 + 3 ^ 40 * 5163585 * 2
def baseEnd_5163585 : Nat := 2651401005346285183640611

theorem tailTrace_5163585 : CollatzResearch.WordTrace tailWord_5163585 prefixEnd_5163585 2651401005346285183640611 := by
  unfold tailWord_5163585
  simp only [CollatzResearch.WordTrace]
  refine ⟨188331416998220889953844209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125554277998813926635896139 188331416998220889953844209)
  ·
    refine ⟨141248562748665667465383157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188331416998220889953844209 141248562748665667465383157)
    ·
      refine ⟨13242052757687406324879671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141248562748665667465383157 13242052757687406324879671)
      ·
        refine ⟨19863079136531109487319507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13242052757687406324879671 19863079136531109487319507)
        ·
          refine ⟨29794618704796664230979261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19863079136531109487319507 29794618704796664230979261)
          ·
            refine ⟨11172982014298749086617223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29794618704796664230979261 11172982014298749086617223)
            ·
              refine ⟨16759473021448123629925835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11172982014298749086617223 16759473021448123629925835)
              ·
                refine ⟨25139209532172185444888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16759473021448123629925835 25139209532172185444888753)
                ·
                  refine ⟨18854407149129139083666565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25139209532172185444888753 18854407149129139083666565)
                  ·
                    refine ⟨3535201340461713578187481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18854407149129139083666565 3535201340461713578187481)
                    ·
                      refine ⟨2651401005346285183640611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535201340461713578187481 2651401005346285183640611)
                      ·
                        rfl

theorem cell23_5163585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5163585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163585 prefixEnd_5163585 := by exact prefixLift 5163585
  have htrace : WordTrace (prefixWord ++ tailWord_5163585) baseStart_5163585 baseEnd_5163585 := by
    simpa [prefixWord, tailWord_5163585, baseEnd_5163585] using wordTrace_append hprefix tailTrace_5163585
  have hstable : (prefixWord ++ tailWord_5163585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163585).length < 2 ^ (prefixWord ++ tailWord_5163585).sum := by decide
  have hdescent : baseEnd_5163585 < baseStart_5163585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163712 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3]
def baseStart_5163712 : Nat := 118140960795 + 5163712 * 2 ^ 59
def prefixEnd_5163712 : Nat := 4983230072969 + 3 ^ 40 * 5163712 * 2
def baseEnd_5163712 : Nat := 2651466217389406186752527

theorem tailTrace_5163712 : CollatzResearch.WordTrace tailWord_5163712 prefixEnd_5163712 2651466217389406186752527 := by
  unfold tailWord_5163712
  simp only [CollatzResearch.WordTrace]
  refine ⟨94168024534380395321858695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125557366045840527095811593 94168024534380395321858695)
  ·
    refine ⟨141252036801570592982788043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94168024534380395321858695 141252036801570592982788043)
    ·
      refine ⟨211878055202355889474182065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141252036801570592982788043 211878055202355889474182065)
      ·
        refine ⟨158908541401766917105636549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211878055202355889474182065 158908541401766917105636549)
        ·
          refine ⟨29795351512831296957306853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158908541401766917105636549 29795351512831296957306853)
          ·
            refine ⟨5586628408655868179495035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29795351512831296957306853 5586628408655868179495035)
            ·
              refine ⟨8379942612983802269242553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586628408655868179495035 8379942612983802269242553)
              ·
                refine ⟨6284956959737851701931915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8379942612983802269242553 6284956959737851701931915)
                ·
                  refine ⟨9427435439606777552897873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6284956959737851701931915 9427435439606777552897873)
                  ·
                    refine ⟨7070576579705083164673405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9427435439606777552897873 7070576579705083164673405)
                    ·
                      refine ⟨2651466217389406186752527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7070576579705083164673405 2651466217389406186752527)
                      ·
                        rfl

theorem cell23_5163712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_5163712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163712 prefixEnd_5163712 := by exact prefixLift 5163712
  have htrace : WordTrace (prefixWord ++ tailWord_5163712) baseStart_5163712 baseEnd_5163712 := by
    simpa [prefixWord, tailWord_5163712, baseEnd_5163712] using wordTrace_append hprefix tailTrace_5163712
  have hstable : (prefixWord ++ tailWord_5163712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163712).length < 2 ^ (prefixWord ++ tailWord_5163712).sum := by decide
  have hdescent : baseEnd_5163712 < baseStart_5163712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163748 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_5163748 : Nat := 118140960795 + 5163748 * 2 ^ 59
def prefixEnd_5163748 : Nat := 4983230072969 + 3 ^ 40 * 5163748 * 2
def baseEnd_5163748 : Nat := 2651484702692968045902361

theorem tailTrace_5163748 : CollatzResearch.WordTrace tailWord_5163748 prefixEnd_5163748 2651484702692968045902361 := by
  unfold tailWord_5163748
  simp only [CollatzResearch.WordTrace]
  refine ⟨94168681048315184396013949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125558241397753579194685265 94168681048315184396013949)
  ·
    refine ⟨35313255393118194148505231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94168681048315184396013949 35313255393118194148505231)
    ·
      refine ⟨52969883089677291222757847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35313255393118194148505231 52969883089677291222757847)
      ·
        refine ⟨79454824634515936834136771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52969883089677291222757847 79454824634515936834136771)
        ·
          refine ⟨119182236951773905251205157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79454824634515936834136771 119182236951773905251205157)
          ·
            refine ⟨22346669428457607234600967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119182236951773905251205157 22346669428457607234600967)
            ·
              refine ⟨33520004142686410851901451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22346669428457607234600967 33520004142686410851901451)
              ·
                refine ⟨50280006214029616277852177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33520004142686410851901451 50280006214029616277852177)
                ·
                  refine ⟨37710004660522212208389133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50280006214029616277852177 37710004660522212208389133)
                  ·
                    refine ⟨14141251747695829578145925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37710004660522212208389133 14141251747695829578145925)
                    ·
                      refine ⟨2651484702692968045902361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14141251747695829578145925 2651484702692968045902361)
                      ·
                        rfl

theorem cell23_5163748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_5163748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163748 prefixEnd_5163748 := by exact prefixLift 5163748
  have htrace : WordTrace (prefixWord ++ tailWord_5163748) baseStart_5163748 baseEnd_5163748 := by
    simpa [prefixWord, tailWord_5163748, baseEnd_5163748] using wordTrace_append hprefix tailTrace_5163748
  have hstable : (prefixWord ++ tailWord_5163748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163748).length < 2 ^ (prefixWord ++ tailWord_5163748).sum := by decide
  have hdescent : baseEnd_5163748 < baseStart_5163748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163758 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_5163758 : Nat := 118140960795 + 5163758 * 2 ^ 59
def prefixEnd_5163758 : Nat := 4983230072969 + 3 ^ 40 * 5163758 * 2
def baseEnd_5163758 : Nat := 883829945833171002259105

theorem tailTrace_5163758 : CollatzResearch.WordTrace tailWord_5163758 prefixEnd_5163758 883829945833171002259105 := by
  unfold tailWord_5163758
  simp only [CollatzResearch.WordTrace]
  refine ⟨23542215853324267562486491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125558484551062760333261285 23542215853324267562486491)
  ·
    refine ⟨35313323779986401343729737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23542215853324267562486491 35313323779986401343729737)
    ·
      refine ⟨26484992834989801007797303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35313323779986401343729737 26484992834989801007797303)
      ·
        refine ⟨39727489252484701511695955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26484992834989801007797303 39727489252484701511695955)
        ·
          refine ⟨59591233878727052267543933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39727489252484701511695955 59591233878727052267543933)
          ·
            refine ⟨22346712704522644600328975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59591233878727052267543933 22346712704522644600328975)
            ·
              refine ⟨33520069056783966900493463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22346712704522644600328975 33520069056783966900493463)
              ·
                refine ⟨50280103585175950350740195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33520069056783966900493463 50280103585175950350740195)
                ·
                  refine ⟨75420155377763925526110293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50280103585175950350740195 75420155377763925526110293)
                  ·
                    refine ⟨883829945833171002259105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75420155377763925526110293 883829945833171002259105)
                    ·
                      rfl

theorem cell23_5163758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_5163758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163758 prefixEnd_5163758 := by exact prefixLift 5163758
  have htrace : WordTrace (prefixWord ++ tailWord_5163758) baseStart_5163758 baseEnd_5163758 := by
    simpa [prefixWord, tailWord_5163758, baseEnd_5163758] using wordTrace_append hprefix tailTrace_5163758
  have hstable : (prefixWord ++ tailWord_5163758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163758).length < 2 ^ (prefixWord ++ tailWord_5163758).sum := by decide
  have hdescent : baseEnd_5163758 < baseStart_5163758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163768 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_5163768 : Nat := 118140960795 + 5163768 * 2 ^ 59
def prefixEnd_5163768 : Nat := 4983230072969 + 3 ^ 40 * 5163768 * 2
def baseEnd_5163768 : Nat := 2651494972306057967652269

theorem tailTrace_5163768 : CollatzResearch.WordTrace tailWord_5163768 prefixEnd_5163768 2651494972306057967652269 := by
  unfold tailWord_5163768
  simp only [CollatzResearch.WordTrace]
  refine ⟨94169045778278956103877979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125558727704371941471837305 94169045778278956103877979)
  ·
    refine ⟨141253568667418434155816969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94169045778278956103877979 141253568667418434155816969)
    ·
      refine ⟨105940176500563825616862727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141253568667418434155816969 105940176500563825616862727)
      ·
        refine ⟨158910264750845738425294091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105940176500563825616862727 158910264750845738425294091)
        ·
          refine ⟨238365397126268607637941137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158910264750845738425294091 238365397126268607637941137)
          ·
            refine ⟨178774047844701455728455853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238365397126268607637941137 178774047844701455728455853)
            ·
              refine ⟨67040267941763045898170945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178774047844701455728455853 67040267941763045898170945)
              ·
                refine ⟨50280200956322284423628209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67040267941763045898170945 50280200956322284423628209)
                ·
                  refine ⟨37710150717241713317721157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50280200956322284423628209 37710150717241713317721157)
                  ·
                    refine ⟨7070653259482821247072717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37710150717241713317721157 7070653259482821247072717)
                    ·
                      refine ⟨2651494972306057967652269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7070653259482821247072717 2651494972306057967652269)
                      ·
                        rfl

theorem cell23_5163768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_5163768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163768 prefixEnd_5163768 := by exact prefixLift 5163768
  have htrace : WordTrace (prefixWord ++ tailWord_5163768) baseStart_5163768 baseEnd_5163768 := by
    simpa [prefixWord, tailWord_5163768, baseEnd_5163768] using wordTrace_append hprefix tailTrace_5163768
  have hstable : (prefixWord ++ tailWord_5163768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163768).length < 2 ^ (prefixWord ++ tailWord_5163768).sum := by decide
  have hdescent : baseEnd_5163768 < baseStart_5163768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163799 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 4, 2, 2]
def baseStart_5163799 : Nat := 118140960795 + 5163799 * 2 ^ 59
def prefixEnd_5163799 : Nat := 4983230072969 + 3 ^ 40 * 5163799 * 2
def baseEnd_5163799 : Nat := 2651510890206347346364627

theorem tailTrace_5163799 : CollatzResearch.WordTrace tailWord_5163799 prefixEnd_5163799 2651510890206347346364627 := by
  unfold tailWord_5163799
  simp only [CollatzResearch.WordTrace]
  refine ⟨188339222219445604502134451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125559481479630403001422967 188339222219445604502134451)
  ·
    refine ⟨282508833329168406753201677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188339222219445604502134451 282508833329168406753201677)
    ·
      refine ⟨105940812498438152532450629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282508833329168406753201677 105940812498438152532450629)
      ·
        refine ⟨19863902343457153599834493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105940812498438152532450629 19863902343457153599834493)
        ·
          refine ⟨7448963378796432599937935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19863902343457153599834493 7448963378796432599937935)
          ·
            refine ⟨11173445068194648899906903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7448963378796432599937935 11173445068194648899906903)
            ·
              refine ⟨16760167602291973349860355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11173445068194648899906903 16760167602291973349860355)
              ·
                refine ⟨25140251403437960024790533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16760167602291973349860355 25140251403437960024790533)
                ·
                  refine ⟨4713797138144617504648225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25140251403437960024790533 4713797138144617504648225)
                  ·
                    refine ⟨3535347853608463128486169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4713797138144617504648225 3535347853608463128486169)
                    ·
                      refine ⟨2651510890206347346364627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535347853608463128486169 2651510890206347346364627)
                      ·
                        rfl

theorem cell23_5163799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_5163799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163799 prefixEnd_5163799 := by exact prefixLift 5163799
  have htrace : WordTrace (prefixWord ++ tailWord_5163799) baseStart_5163799 baseEnd_5163799 := by
    simpa [prefixWord, tailWord_5163799, baseEnd_5163799] using wordTrace_append hprefix tailTrace_5163799
  have hstable : (prefixWord ++ tailWord_5163799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163799).length < 2 ^ (prefixWord ++ tailWord_5163799).sum := by decide
  have hdescent : baseEnd_5163799 < baseStart_5163799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163816 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_5163816 : Nat := 118140960795 + 5163816 * 2 ^ 59
def prefixEnd_5163816 : Nat := 4983230072969 + 3 ^ 40 * 5163816 * 2
def baseEnd_5163816 : Nat := 2651519619377473779852049

theorem tailTrace_5163816 : CollatzResearch.WordTrace tailWord_5163816 prefixEnd_5163816 2651519619377473779852049 := by
  unfold tailWord_5163816
  simp only [CollatzResearch.WordTrace]
  refine ⟨94169921130192008202751651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125559894840256010937002201 94169921130192008202751651)
  ·
    refine ⟨141254881695288012304127477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94169921130192008202751651 141254881695288012304127477)
    ·
      refine ⟨13242645158933251153511951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141254881695288012304127477 13242645158933251153511951)
      ·
        refine ⟨19863967738399876730267927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13242645158933251153511951 19863967738399876730267927)
        ·
          refine ⟨29795951607599815095401891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19863967738399876730267927 29795951607599815095401891)
          ·
            refine ⟨44693927411399722643102837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29795951607599815095401891 44693927411399722643102837)
            ·
              refine ⟨4190055694818723997790891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44693927411399722643102837 4190055694818723997790891)
              ·
                refine ⟨6285083542228085996686337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4190055694818723997790891 6285083542228085996686337)
                ·
                  refine ⟨4713812656671064497514753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6285083542228085996686337 4713812656671064497514753)
                  ·
                    refine ⟨3535359492503298373136065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4713812656671064497514753 3535359492503298373136065)
                    ·
                      refine ⟨2651519619377473779852049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535359492503298373136065 2651519619377473779852049)
                      ·
                        rfl

theorem cell23_5163816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_5163816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163816 prefixEnd_5163816 := by exact prefixLift 5163816
  have htrace : WordTrace (prefixWord ++ tailWord_5163816) baseStart_5163816 baseEnd_5163816 := by
    simpa [prefixWord, tailWord_5163816, baseEnd_5163816] using wordTrace_append hprefix tailTrace_5163816
  have hstable : (prefixWord ++ tailWord_5163816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163816).length < 2 ^ (prefixWord ++ tailWord_5163816).sum := by decide
  have hdescent : baseEnd_5163816 < baseStart_5163816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163898 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_5163898 : Nat := 118140960795 + 5163898 * 2 ^ 59
def prefixEnd_5163898 : Nat := 4983230072969 + 3 ^ 40 * 5163898 * 2
def baseEnd_5163898 : Nat := 2651561724791142459026671

theorem tailTrace_5163898 : CollatzResearch.WordTrace tailWord_5163898 prefixEnd_5163898 2651561724791142459026671 := by
  unfold tailWord_5163898
  simp only [CollatzResearch.WordTrace]
  refine ⟨47085708261521736102497087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125561888697391296273325565 47085708261521736102497087)
  ·
    refine ⟨70628562392282604153745631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47085708261521736102497087 70628562392282604153745631)
    ·
      refine ⟨105942843588423906230618447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70628562392282604153745631 105942843588423906230618447)
      ·
        refine ⟨158914265382635859345927671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105942843588423906230618447 158914265382635859345927671)
        ·
          refine ⟨238371398073953789018891507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158914265382635859345927671 238371398073953789018891507)
          ·
            refine ⟨357557097110930683528337261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238371398073953789018891507 357557097110930683528337261)
            ·
              refine ⟨134083911416599006323126473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357557097110930683528337261 134083911416599006323126473)
              ·
                refine ⟨100562933562449254742344855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134083911416599006323126473 100562933562449254742344855)
                ·
                  refine ⟨150844400343673882113517283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100562933562449254742344855 150844400343673882113517283)
                  ·
                    refine ⟨226266600515510823170275925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150844400343673882113517283 226266600515510823170275925)
                    ·
                      refine ⟨2651561724791142459026671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226266600515510823170275925 2651561724791142459026671)
                      ·
                        rfl

theorem cell23_5163898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_5163898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163898 prefixEnd_5163898 := by exact prefixLift 5163898
  have htrace : WordTrace (prefixWord ++ tailWord_5163898) baseStart_5163898 baseEnd_5163898 := by
    simpa [prefixWord, tailWord_5163898, baseEnd_5163898] using wordTrace_append hprefix tailTrace_5163898
  have hstable : (prefixWord ++ tailWord_5163898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163898).length < 2 ^ (prefixWord ++ tailWord_5163898).sum := by decide
  have hdescent : baseEnd_5163898 < baseStart_5163898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163912 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 6]
def baseStart_5163912 : Nat := 118140960795 + 5163912 * 2 ^ 59
def prefixEnd_5163912 : Nat := 4983230072969 + 3 ^ 40 * 5163912 * 2
def baseEnd_5163912 : Nat := 294618768168922822694623

theorem tailTrace_5163912 : CollatzResearch.WordTrace tailWord_5163912 prefixEnd_5163912 294618768168922822694623 := by
  unfold tailWord_5163912
  simp only [CollatzResearch.WordTrace]
  refine ⟨94171671834018112400498995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125562229112024149867331993 94171671834018112400498995)
  ·
    refine ⟨141257507751027168600748493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94171671834018112400498995 141257507751027168600748493)
    ·
      refine ⟨52971565406635188225280685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141257507751027168600748493 52971565406635188225280685)
      ·
        refine ⟨19864337027488195584480257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52971565406635188225280685 19864337027488195584480257)
        ·
          refine ⟨14898252770616146688360193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19864337027488195584480257 14898252770616146688360193)
          ·
            refine ⟨11173689577962110016270145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14898252770616146688360193 11173689577962110016270145)
            ·
              refine ⟨8380267183471582512202609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11173689577962110016270145 8380267183471582512202609)
              ·
                refine ⟨6285200387603686884151957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8380267183471582512202609 6285200387603686884151957)
                ·
                  refine ⟨294618768168922822694623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6285200387603686884151957 294618768168922822694623)
                  ·
                    rfl

theorem cell23_5163912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 6].length) (baseStart_5163912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163912 prefixEnd_5163912 := by exact prefixLift 5163912
  have htrace : WordTrace (prefixWord ++ tailWord_5163912) baseStart_5163912 baseEnd_5163912 := by
    simpa [prefixWord, tailWord_5163912, baseEnd_5163912] using wordTrace_append hprefix tailTrace_5163912
  have hstable : (prefixWord ++ tailWord_5163912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163912).length < 2 ^ (prefixWord ++ tailWord_5163912).sum := by decide
  have hdescent : baseEnd_5163912 < baseStart_5163912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163925 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_5163925 : Nat := 118140960795 + 5163925 * 2 ^ 59
def prefixEnd_5163925 : Nat := 4983230072969 + 3 ^ 40 * 5163925 * 2
def baseEnd_5163925 : Nat := 883858529589604617796349

theorem tailTrace_5163925 : CollatzResearch.WordTrace tailWord_5163925 prefixEnd_5163925 883858529589604617796349 := by
  unfold tailWord_5163925
  simp only [CollatzResearch.WordTrace]
  refine ⟨188343817816989128021221229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125562545211326085347480819 188343817816989128021221229)
  ·
    refine ⟨70628931681370923007957961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188343817816989128021221229 70628931681370923007957961)
    ·
      refine ⟨52971698761028192255968471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70628931681370923007957961 52971698761028192255968471)
      ·
        refine ⟨79457548141542288383952707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52971698761028192255968471 79457548141542288383952707)
        ·
          refine ⟨119186322212313432575929061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79457548141542288383952707 119186322212313432575929061)
          ·
            refine ⟨22347435414808768607986699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119186322212313432575929061 22347435414808768607986699)
            ·
              refine ⟨33521153122213152911980049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22347435414808768607986699 33521153122213152911980049)
              ·
                refine ⟨25140864841659864683985037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33521153122213152911980049 25140864841659864683985037)
                ·
                  refine ⟨9427824315622449256494389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25140864841659864683985037 9427824315622449256494389)
                  ·
                    refine ⟨883858529589604617796349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9427824315622449256494389 883858529589604617796349)
                    ·
                      rfl

theorem cell23_5163925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_5163925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163925 prefixEnd_5163925 := by exact prefixLift 5163925
  have htrace : WordTrace (prefixWord ++ tailWord_5163925) baseStart_5163925 baseEnd_5163925 := by
    simpa [prefixWord, tailWord_5163925, baseEnd_5163925] using wordTrace_append hprefix tailTrace_5163925
  have hstable : (prefixWord ++ tailWord_5163925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163925).length < 2 ^ (prefixWord ++ tailWord_5163925).sum := by decide
  have hdescent : baseEnd_5163925 < baseStart_5163925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163945 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_5163945 : Nat := 118140960795 + 5163945 * 2 ^ 59
def prefixEnd_5163945 : Nat := 4983230072969 + 3 ^ 40 * 5163945 * 2
def baseEnd_5163945 : Nat := 2651585858381903775138955

theorem tailTrace_5163945 : CollatzResearch.WordTrace tailWord_5163945 prefixEnd_5163945 2651585858381903775138955 := by
  unfold tailWord_5163945
  simp only [CollatzResearch.WordTrace]
  refine ⟨188344547276916671436949289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125563031517944447624632859 188344547276916671436949289)
  ·
    refine ⟨141258410457687503577711967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188344547276916671436949289 141258410457687503577711967)
    ·
      refine ⟨211887615686531255366567951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141258410457687503577711967 211887615686531255366567951)
      ·
        refine ⟨317831423529796883049851927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211887615686531255366567951 317831423529796883049851927)
        ·
          refine ⟨476747135294695324574777891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317831423529796883049851927 476747135294695324574777891)
          ·
            refine ⟨715120702942042986862166837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476747135294695324574777891 715120702942042986862166837)
            ·
              refine ⟨67042565900816530018328141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 715120702942042986862166837 67042565900816530018328141)
              ·
                refine ⟨25140962212806198756873053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67042565900816530018328141 25140962212806198756873053)
                ·
                  refine ⟨9427860829802324533827395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25140962212806198756873053 9427860829802324533827395)
                  ·
                    refine ⟨14141791244703486800741093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9427860829802324533827395 14141791244703486800741093)
                    ·
                      refine ⟨2651585858381903775138955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14141791244703486800741093 2651585858381903775138955)
                      ·
                        rfl

theorem cell23_5163945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_5163945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163945 prefixEnd_5163945 := by exact prefixLift 5163945
  have htrace : WordTrace (prefixWord ++ tailWord_5163945) baseStart_5163945 baseEnd_5163945 := by
    simpa [prefixWord, tailWord_5163945, baseEnd_5163945] using wordTrace_append hprefix tailTrace_5163945
  have hstable : (prefixWord ++ tailWord_5163945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163945).length < 2 ^ (prefixWord ++ tailWord_5163945).sum := by decide
  have hdescent : baseEnd_5163945 < baseStart_5163945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163962 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_5163962 : Nat := 118140960795 + 5163962 * 2 ^ 59
def prefixEnd_5163962 : Nat := 4983230072969 + 3 ^ 40 * 5163962 * 2
def baseEnd_5163962 : Nat := 2651594587553030208626377

theorem tailTrace_5163962 : CollatzResearch.WordTrace tailWord_5163962 prefixEnd_5163962 2651594587553030208626377 := by
  unfold tailWord_5163962
  simp only [CollatzResearch.WordTrace]
  refine ⟨47086291829463770835079535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125563444878570055560212093 47086291829463770835079535)
  ·
    refine ⟨70629437744195656252619303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47086291829463770835079535 70629437744195656252619303)
    ·
      refine ⟨105944156616293484378928955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70629437744195656252619303 105944156616293484378928955)
      ·
        refine ⟨158916234924440226568393433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105944156616293484378928955 158916234924440226568393433)
        ·
          refine ⟨119187176193330169926295075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158916234924440226568393433 119187176193330169926295075)
          ·
            refine ⟨178780764289995254889442613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119187176193330169926295075 178780764289995254889442613)
            ·
              refine ⟨16760696652187055145885245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178780764289995254889442613 16760696652187055145885245)
              ·
                refine ⟨6285261244570145679706967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16760696652187055145885245 6285261244570145679706967)
                ·
                  refine ⟨9427891866855218519560451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6285261244570145679706967 9427891866855218519560451)
                  ·
                    refine ⟨14141837800282827779340677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9427891866855218519560451 14141837800282827779340677)
                    ·
                      refine ⟨2651594587553030208626377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14141837800282827779340677 2651594587553030208626377)
                      ·
                        rfl

theorem cell23_5163962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_5163962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163962 prefixEnd_5163962 := by exact prefixLift 5163962
  have htrace : WordTrace (prefixWord ++ tailWord_5163962) baseStart_5163962 baseEnd_5163962 := by
    simpa [prefixWord, tailWord_5163962, baseEnd_5163962] using wordTrace_append hprefix tailTrace_5163962
  have hstable : (prefixWord ++ tailWord_5163962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163962).length < 2 ^ (prefixWord ++ tailWord_5163962).sum := by decide
  have hdescent : baseEnd_5163962 < baseStart_5163962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163975 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_5163975 : Nat := 118140960795 + 5163975 * 2 ^ 59
def prefixEnd_5163975 : Nat := 4983230072969 + 3 ^ 40 * 5163975 * 2
def baseEnd_5163975 : Nat := 2651601262801538657763817

theorem tailTrace_5163975 : CollatzResearch.WordTrace tailWord_5163975 prefixEnd_5163975 2651601262801538657763817 := by
  unfold tailWord_5163975
  simp only [CollatzResearch.WordTrace]
  refine ⟨188345641466807986560541379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125563760977871991040360919 188345641466807986560541379)
  ·
    refine ⟨282518462200211979840812069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188345641466807986560541379 282518462200211979840812069)
    ·
      refine ⟨52972211662539746220152263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282518462200211979840812069 52972211662539746220152263)
      ·
        refine ⟨79458317493809619330228395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52972211662539746220152263 79458317493809619330228395)
        ·
          refine ⟨119187476240714428995342593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79458317493809619330228395 119187476240714428995342593)
          ·
            refine ⟨89390607180535821746506945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119187476240714428995342593 89390607180535821746506945)
            ·
              refine ⟨67042955385401866309880209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89390607180535821746506945 67042955385401866309880209)
              ·
                refine ⟨50282216539051399732410157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67042955385401866309880209 50282216539051399732410157)
                ·
                  refine ⟨18855831202144274899653809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50282216539051399732410157 18855831202144274899653809)
                  ·
                    refine ⟨14141873401608206174740357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18855831202144274899653809 14141873401608206174740357)
                    ·
                      refine ⟨2651601262801538657763817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14141873401608206174740357 2651601262801538657763817)
                      ·
                        rfl

theorem cell23_5163975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_5163975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163975 prefixEnd_5163975 := by exact prefixLift 5163975
  have htrace : WordTrace (prefixWord ++ tailWord_5163975) baseStart_5163975 baseEnd_5163975 := by
    simpa [prefixWord, tailWord_5163975, baseEnd_5163975] using wordTrace_append hprefix tailTrace_5163975
  have hstable : (prefixWord ++ tailWord_5163975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163975).length < 2 ^ (prefixWord ++ tailWord_5163975).sum := by decide
  have hdescent : baseEnd_5163975 < baseStart_5163975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163979 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 3, 2, 2]
def baseStart_5163979 : Nat := 118140960795 + 5163979 * 2 ^ 59
def prefixEnd_5163979 : Nat := 4983230072969 + 3 ^ 40 * 5163979 * 2
def baseEnd_5163979 : Nat := 2651603316724156642113799

theorem tailTrace_5163979 : CollatzResearch.WordTrace tailWord_5163979 prefixEnd_5163979 2651603316724156642113799 := by
  unfold tailWord_5163979
  simp only [CollatzResearch.WordTrace]
  refine ⟨188345787358793495243686991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125563858239195663495791327 188345787358793495243686991)
  ·
    refine ⟨282518681038190242865530487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188345787358793495243686991 282518681038190242865530487)
    ·
      refine ⟨423778021557285364298295731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282518681038190242865530487 423778021557285364298295731)
      ·
        refine ⟨635667032335928046447443597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423778021557285364298295731 635667032335928046447443597)
        ·
          refine ⟨238375137125973017417791349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 635667032335928046447443597 238375137125973017417791349)
          ·
            refine ⟨22347669105559970382917939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238375137125973017417791349 22347669105559970382917939)
            ·
              refine ⟨33521503658339955574376909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22347669105559970382917939 33521503658339955574376909)
              ·
                refine ⟨12570563871877483340391341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33521503658339955574376909 12570563871877483340391341)
                ·
                  refine ⟨4713961451954056252646753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12570563871877483340391341 4713961451954056252646753)
                  ·
                    refine ⟨3535471088965542189485065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4713961451954056252646753 3535471088965542189485065)
                    ·
                      refine ⟨2651603316724156642113799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535471088965542189485065 2651603316724156642113799)
                      ·
                        rfl

theorem cell23_5163979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 2, 2].length) (baseStart_5163979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163979 prefixEnd_5163979 := by exact prefixLift 5163979
  have htrace : WordTrace (prefixWord ++ tailWord_5163979) baseStart_5163979 baseEnd_5163979 := by
    simpa [prefixWord, tailWord_5163979, baseEnd_5163979] using wordTrace_append hprefix tailTrace_5163979
  have hstable : (prefixWord ++ tailWord_5163979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163979).length < 2 ^ (prefixWord ++ tailWord_5163979).sum := by decide
  have hdescent : baseEnd_5163979 < baseStart_5163979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163982 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_5163982 : Nat := 118140960795 + 5163982 * 2 ^ 59
def prefixEnd_5163982 : Nat := 4983230072969 + 3 ^ 40 * 5163982 * 2
def baseEnd_5163982 : Nat := 2651604857166120130376285

theorem tailTrace_5163982 : CollatzResearch.WordTrace tailWord_5163982 prefixEnd_5163982 2651604857166120130376285 := by
  unfold tailWord_5163982
  simp only [CollatzResearch.WordTrace]
  refine ⟨23543237097222828344505775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125563931185188417837364133 23543237097222828344505775)
  ·
    refine ⟨35314855645834242516758663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23543237097222828344505775 35314855645834242516758663)
    ·
      refine ⟨52972283468751363775137995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35314855645834242516758663 52972283468751363775137995)
      ·
        refine ⟨79458425203127045662706993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52972283468751363775137995 79458425203127045662706993)
        ·
          refine ⟨59593818902345284247030245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79458425203127045662706993 59593818902345284247030245)
          ·
            refine ⟨11173841044189740796318171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59593818902345284247030245 11173841044189740796318171)
            ·
              refine ⟨16760761566284611194477257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11173841044189740796318171 16760761566284611194477257)
              ·
                refine ⟨12570571174713458395857943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16760761566284611194477257 12570571174713458395857943)
                ·
                  refine ⟨18855856762070187593786915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12570571174713458395857943 18855856762070187593786915)
                  ·
                    refine ⟨28283785143105281390680373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18855856762070187593786915 28283785143105281390680373)
                    ·
                      refine ⟨2651604857166120130376285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28283785143105281390680373 2651604857166120130376285)
                      ·
                        rfl

theorem cell23_5163982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_5163982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163982 prefixEnd_5163982 := by exact prefixLift 5163982
  have htrace : WordTrace (prefixWord ++ tailWord_5163982) baseStart_5163982 baseEnd_5163982 := by
    simpa [prefixWord, tailWord_5163982, baseEnd_5163982] using wordTrace_append hprefix tailTrace_5163982
  have hstable : (prefixWord ++ tailWord_5163982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163982).length < 2 ^ (prefixWord ++ tailWord_5163982).sum := by decide
  have hdescent : baseEnd_5163982 < baseStart_5163982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163989 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_5163989 : Nat := 118140960795 + 5163989 * 2 ^ 59
def prefixEnd_5163989 : Nat := 4983230072969 + 3 ^ 40 * 5163989 * 2
def baseEnd_5163989 : Nat := 883869483843567200996251

theorem tailTrace_5163989 : CollatzResearch.WordTrace tailWord_5163989 prefixEnd_5163989 883869483843567200996251 := by
  unfold tailWord_5163989
  simp only [CollatzResearch.WordTrace]
  refine ⟨188346152088757266951551021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125564101392504844634367347 188346152088757266951551021)
  ·
    refine ⟨70629807033283975106831633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188346152088757266951551021 70629807033283975106831633)
    ·
      refine ⟨52972355274962981330123725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70629807033283975106831633 52972355274962981330123725)
      ·
        refine ⟨19864633228111117998796397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52972355274962981330123725 19864633228111117998796397)
        ·
          refine ⟨7449237460541669249548649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19864633228111117998796397 7449237460541669249548649)
          ·
            refine ⟨5586928095406251937161487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7449237460541669249548649 5586928095406251937161487)
            ·
              refine ⟨8380392143109377905742231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586928095406251937161487 8380392143109377905742231)
              ·
                refine ⟨12570588214664066858613347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8380392143109377905742231 12570588214664066858613347)
                ·
                  refine ⟨18855882321996100287920021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12570588214664066858613347 18855882321996100287920021)
                  ·
                    refine ⟨883869483843567200996251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18855882321996100287920021 883869483843567200996251)
                    ·
                      rfl

theorem cell23_5163989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_5163989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163989 prefixEnd_5163989 := by exact prefixLift 5163989
  have htrace : WordTrace (prefixWord ++ tailWord_5163989) baseStart_5163989 baseEnd_5163989 := by
    simpa [prefixWord, tailWord_5163989, baseEnd_5163989] using wordTrace_append hprefix tailTrace_5163989
  have hstable : (prefixWord ++ tailWord_5163989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163989).length < 2 ^ (prefixWord ++ tailWord_5163989).sum := by decide
  have hdescent : baseEnd_5163989 < baseStart_5163989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5163992 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_5163992 : Nat := 118140960795 + 5163992 * 2 ^ 59
def prefixEnd_5163992 : Nat := 4983230072969 + 3 ^ 40 * 5163992 * 2
def baseEnd_5163992 : Nat := 2651609991972665091251239

theorem tailTrace_5163992 : CollatzResearch.WordTrace tailWord_5163992 prefixEnd_5163992 2651609991972665091251239 := by
  unfold tailWord_5163992
  simp only [CollatzResearch.WordTrace]
  refine ⟨94173130753873199231955115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125564174338497598975940153 94173130753873199231955115)
  ·
    refine ⟨141259696130809798847932673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94173130753873199231955115 141259696130809798847932673)
    ·
      refine ⟨105944772098107349135949505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141259696130809798847932673 105944772098107349135949505)
      ·
        refine ⟨79458579073580511851962129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105944772098107349135949505 79458579073580511851962129)
        ·
          refine ⟨59593934305185383888971597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79458579073580511851962129 59593934305185383888971597)
          ·
            refine ⟨22347725364444518958364349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59593934305185383888971597 22347725364444518958364349)
            ·
              refine ⟨8380397011666694609386631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22347725364444518958364349 8380397011666694609386631)
              ·
                refine ⟨12570595517500041914079947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8380397011666694609386631 12570595517500041914079947)
                ·
                  refine ⟨18855893276250062871119921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12570595517500041914079947 18855893276250062871119921)
                  ·
                    refine ⟨14141919957187547153339941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18855893276250062871119921 14141919957187547153339941)
                    ·
                      refine ⟨2651609991972665091251239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14141919957187547153339941 2651609991972665091251239)
                      ·
                        rfl

theorem cell23_5163992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_5163992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5163992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5163992 prefixEnd_5163992 := by exact prefixLift 5163992
  have htrace : WordTrace (prefixWord ++ tailWord_5163992) baseStart_5163992 baseEnd_5163992 := by
    simpa [prefixWord, tailWord_5163992, baseEnd_5163992] using wordTrace_append hprefix tailTrace_5163992
  have hstable : (prefixWord ++ tailWord_5163992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5163992).length < 2 ^ (prefixWord ++ tailWord_5163992).sum := by decide
  have hdescent : baseEnd_5163992 < baseStart_5163992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5163992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164025 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_5164025 : Nat := 118140960795 + 5164025 * 2 ^ 59
def prefixEnd_5164025 : Nat := 4983230072969 + 3 ^ 40 * 5164025 * 2
def baseEnd_5164025 : Nat := 2651626936834263462138587

theorem tailTrace_5164025 : CollatzResearch.WordTrace tailWord_5164025 prefixEnd_5164025 2651626936834263462138587 := by
  unfold tailWord_5164025
  simp only [CollatzResearch.WordTrace]
  refine ⟨188347465116626845099861529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125564976744417896733241019 188347465116626845099861529)
  ·
    refine ⟨141260598837470133824896147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188347465116626845099861529 141260598837470133824896147)
    ·
      refine ⟨211890898256205200737344221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141260598837470133824896147 211890898256205200737344221)
      ·
        refine ⟨79459086846076950276504083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211890898256205200737344221 79459086846076950276504083)
        ·
          refine ⟨119188630269115425414756125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79459086846076950276504083 119188630269115425414756125)
          ·
            refine ⟨44695736350918284530533547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119188630269115425414756125 44695736350918284530533547)
            ·
              refine ⟨67043604526377426795800321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44695736350918284530533547 67043604526377426795800321)
              ·
                refine ⟨50282703394783070096850241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67043604526377426795800321 50282703394783070096850241)
                ·
                  refine ⟨37712027546087302572637681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50282703394783070096850241 37712027546087302572637681)
                  ·
                    refine ⟨28284020659565476929478261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37712027546087302572637681 28284020659565476929478261)
                    ·
                      refine ⟨2651626936834263462138587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28284020659565476929478261 2651626936834263462138587)
                      ·
                        rfl

theorem cell23_5164025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_5164025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164025 prefixEnd_5164025 := by exact prefixLift 5164025
  have htrace : WordTrace (prefixWord ++ tailWord_5164025) baseStart_5164025 baseEnd_5164025 := by
    simpa [prefixWord, tailWord_5164025, baseEnd_5164025] using wordTrace_append hprefix tailTrace_5164025
  have hstable : (prefixWord ++ tailWord_5164025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164025).length < 2 ^ (prefixWord ++ tailWord_5164025).sum := by decide
  have hdescent : baseEnd_5164025 < baseStart_5164025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164029 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_5164029 : Nat := 118140960795 + 5164029 * 2 ^ 59
def prefixEnd_5164029 : Nat := 4983230072969 + 3 ^ 40 * 5164029 * 2
def baseEnd_5164029 : Nat := 2651628990756881446488569

theorem tailTrace_5164029 : CollatzResearch.WordTrace tailWord_5164029 prefixEnd_5164029 2651628990756881446488569 := by
  unfold tailWord_5164029
  simp only [CollatzResearch.WordTrace]
  refine ⟨188347611008612353783007141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125565074005741569188671427 188347611008612353783007141)
  ·
    refine ⟨35315177064114816334313839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188347611008612353783007141 35315177064114816334313839)
    ·
      refine ⟨52972765596172224501470759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35315177064114816334313839 52972765596172224501470759)
      ·
        refine ⟨79459148394258336752206139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52972765596172224501470759 79459148394258336752206139)
        ·
          refine ⟨119188722591387505128309209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79459148394258336752206139 119188722591387505128309209)
          ·
            refine ⟨89391541943540628846231907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119188722591387505128309209 89391541943540628846231907)
            ·
              refine ⟨134087312915310943269347861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89391541943540628846231907 134087312915310943269347861)
              ·
                refine ⟨6285342792905200465750681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134087312915310943269347861 6285342792905200465750681)
                ·
                  refine ⟨4714007094678900349313011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6285342792905200465750681 4714007094678900349313011)
                  ·
                    refine ⟨7071010642018350523969517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4714007094678900349313011 7071010642018350523969517)
                    ·
                      refine ⟨2651628990756881446488569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7071010642018350523969517 2651628990756881446488569)
                      ·
                        rfl

theorem cell23_5164029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_5164029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164029 prefixEnd_5164029 := by exact prefixLift 5164029
  have htrace : WordTrace (prefixWord ++ tailWord_5164029) baseStart_5164029 baseEnd_5164029 := by
    simpa [prefixWord, tailWord_5164029, baseEnd_5164029] using wordTrace_append hprefix tailTrace_5164029
  have hstable : (prefixWord ++ tailWord_5164029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164029).length < 2 ^ (prefixWord ++ tailWord_5164029).sum := by decide
  have hdescent : baseEnd_5164029 < baseStart_5164029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164030 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5164030 : Nat := 118140960795 + 5164030 * 2 ^ 59
def prefixEnd_5164030 : Nat := 4983230072969 + 3 ^ 40 * 5164030 * 2
def baseEnd_5164030 : Nat := 2651629504237535942576065

theorem tailTrace_5164030 : CollatzResearch.WordTrace tailWord_5164030 prefixEnd_5164030 2651629504237535942576065 := by
  unfold tailWord_5164030
  simp only [CollatzResearch.WordTrace]
  refine ⟨23543455935201091369224193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125565098321072487302529029 23543455935201091369224193)
  ·
    refine ⟨17657591951400818526918145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23543455935201091369224193 17657591951400818526918145)
    ·
      refine ⟨13243193963550613895188609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17657591951400818526918145 13243193963550613895188609)
      ·
        refine ⟨9932395472662960421391457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13243193963550613895188609 9932395472662960421391457)
        ·
          refine ⟨7449296604497220316043593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9932395472662960421391457 7449296604497220316043593)
          ·
            refine ⟨5586972453372915237032695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7449296604497220316043593 5586972453372915237032695)
            ·
              refine ⟨8380458680059372855549043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5586972453372915237032695 8380458680059372855549043)
              ·
                refine ⟨12570688020089059283323565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8380458680059372855549043 12570688020089059283323565)
                ·
                  refine ⟨4714008007533397231246337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12570688020089059283323565 4714008007533397231246337)
                  ·
                    refine ⟨3535506005650047923434753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714008007533397231246337 3535506005650047923434753)
                    ·
                      refine ⟨2651629504237535942576065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535506005650047923434753 2651629504237535942576065)
                      ·
                        rfl

theorem cell23_5164030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5164030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164030 prefixEnd_5164030 := by exact prefixLift 5164030
  have htrace : WordTrace (prefixWord ++ tailWord_5164030) baseStart_5164030 baseEnd_5164030 := by
    simpa [prefixWord, tailWord_5164030, baseEnd_5164030] using wordTrace_append hprefix tailTrace_5164030
  have hstable : (prefixWord ++ tailWord_5164030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164030).length < 2 ^ (prefixWord ++ tailWord_5164030).sum := by decide
  have hdescent : baseEnd_5164030 < baseStart_5164030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164039 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_5164039 : Nat := 118140960795 + 5164039 * 2 ^ 59
def prefixEnd_5164039 : Nat := 4983230072969 + 3 ^ 40 * 5164039 * 2
def baseEnd_5164039 : Nat := 2651634125563426407363523

theorem tailTrace_5164039 : CollatzResearch.WordTrace tailWord_5164039 prefixEnd_5164039 2651634125563426407363523 := by
  unfold tailWord_5164039
  simp only [CollatzResearch.WordTrace]
  refine ⟨188347975738576125490871171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125565317159050750327247447 188347975738576125490871171)
  ·
    refine ⟨282521963607864188236306757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188347975738576125490871171 282521963607864188236306757)
    ·
      refine ⟨52972868176474535294307517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282521963607864188236306757 52972868176474535294307517)
      ·
        refine ⟨19864825566177950735365319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52972868176474535294307517 19864825566177950735365319)
        ·
          refine ⟨29797238349266926103047979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19864825566177950735365319 29797238349266926103047979)
          ·
            refine ⟨44695857523900389154571969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29797238349266926103047979 44695857523900389154571969)
            ·
              refine ⟨33521893142925291865928977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44695857523900389154571969 33521893142925291865928977)
              ·
                refine ⟨25141419857193968899446733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33521893142925291865928977 25141419857193968899446733)
                ·
                  refine ⟨9428032446447738337292525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25141419857193968899446733 9428032446447738337292525)
                  ·
                    refine ⟨3535512167417901876484697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9428032446447738337292525 3535512167417901876484697)
                    ·
                      refine ⟨2651634125563426407363523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535512167417901876484697 2651634125563426407363523)
                      ·
                        rfl

theorem cell23_5164039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_5164039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164039 prefixEnd_5164039 := by exact prefixLift 5164039
  have htrace : WordTrace (prefixWord ++ tailWord_5164039) baseStart_5164039 baseEnd_5164039 := by
    simpa [prefixWord, tailWord_5164039, baseEnd_5164039] using wordTrace_append hprefix tailTrace_5164039
  have hstable : (prefixWord ++ tailWord_5164039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164039).length < 2 ^ (prefixWord ++ tailWord_5164039).sum := by decide
  have hdescent : baseEnd_5164039 < baseStart_5164039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164046 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_5164046 : Nat := 118140960795 + 5164046 * 2 ^ 59
def prefixEnd_5164046 : Nat := 4983230072969 + 3 ^ 40 * 5164046 * 2
def baseEnd_5164046 : Nat := 2651637719928007879975991

theorem tailTrace_5164046 : CollatzResearch.WordTrace tailWord_5164046 prefixEnd_5164046 2651637719928007879975991 := by
  unfold tailWord_5164046
  simp only [CollatzResearch.WordTrace]
  refine ⟨23543528881193845710796999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125565487366367177124250661 23543528881193845710796999)
  ·
    refine ⟨35315293321790768566195499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23543528881193845710796999 35315293321790768566195499)
    ·
      refine ⟨52972939982686152849293249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35315293321790768566195499 52972939982686152849293249)
      ·
        refine ⟨39729704987014614636969937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52972939982686152849293249 39729704987014614636969937)
        ·
          refine ⟨29797278740260960977727453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39729704987014614636969937 29797278740260960977727453)
          ·
            refine ⟨11173979527597860366647795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29797278740260960977727453 11173979527597860366647795)
            ·
              refine ⟨16760969291396790549971693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11173979527597860366647795 16760969291396790549971693)
              ·
                refine ⟨6285363484273796456239385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16760969291396790549971693 6285363484273796456239385)
                ·
                  refine ⟨4714022613205347342179539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6285363484273796456239385 4714022613205347342179539)
                  ·
                    refine ⟨7071033919808021013269309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4714022613205347342179539 7071033919808021013269309)
                    ·
                      refine ⟨2651637719928007879975991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7071033919808021013269309 2651637719928007879975991)
                      ·
                        rfl

theorem cell23_5164046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_5164046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164046 prefixEnd_5164046 := by exact prefixLift 5164046
  have htrace : WordTrace (prefixWord ++ tailWord_5164046) baseStart_5164046 baseEnd_5164046 := by
    simpa [prefixWord, tailWord_5164046, baseEnd_5164046] using wordTrace_append hprefix tailTrace_5164046
  have hstable : (prefixWord ++ tailWord_5164046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164046).length < 2 ^ (prefixWord ++ tailWord_5164046).sum := by decide
  have hdescent : baseEnd_5164046 < baseStart_5164046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164056 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 1, 3, 2]
def baseStart_5164056 : Nat := 118140960795 + 5164056 * 2 ^ 59
def prefixEnd_5164056 : Nat := 4983230072969 + 3 ^ 40 * 5164056 * 2
def baseEnd_5164056 : Nat := 2651642854734552840850945

theorem tailTrace_5164056 : CollatzResearch.WordTrace tailWord_5164056 prefixEnd_5164056 2651642854734552840850945 := by
  unfold tailWord_5164056
  simp only [CollatzResearch.WordTrace]
  refine ⟨94174297889757268697120011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125565730519676358262826681 94174297889757268697120011)
  ·
    refine ⟨141261446834635903045680017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94174297889757268697120011 141261446834635903045680017)
    ·
      refine ⟨105946085125976927284260013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141261446834635903045680017 105946085125976927284260013)
      ·
        refine ⟨39729781922241347731597505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105946085125976927284260013 39729781922241347731597505)
        ·
          refine ⟨29797336441681010798698129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39729781922241347731597505 29797336441681010798698129)
          ·
            refine ⟨22348002331260758099023597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29797336441681010798698129 22348002331260758099023597)
            ·
              refine ⟨8380500874222784287133849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22348002331260758099023597 8380500874222784287133849)
              ·
                refine ⟨6285375655667088215350387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8380500874222784287133849 6285375655667088215350387)
                ·
                  refine ⟨9428063483500632323025581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6285375655667088215350387 9428063483500632323025581)
                  ·
                    refine ⟨3535523806312737121134593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9428063483500632323025581 3535523806312737121134593)
                    ·
                      refine ⟨2651642854734552840850945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535523806312737121134593 2651642854734552840850945)
                      ·
                        rfl

theorem cell23_5164056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_5164056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164056 prefixEnd_5164056 := by exact prefixLift 5164056
  have htrace : WordTrace (prefixWord ++ tailWord_5164056) baseStart_5164056 baseEnd_5164056 := by
    simpa [prefixWord, tailWord_5164056, baseEnd_5164056] using wordTrace_append hprefix tailTrace_5164056
  have hstable : (prefixWord ++ tailWord_5164056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164056).length < 2 ^ (prefixWord ++ tailWord_5164056).sum := by decide
  have hdescent : baseEnd_5164056 < baseStart_5164056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164069 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 1, 4, 2]
def baseStart_5164069 : Nat := 118140960795 + 5164069 * 2 ^ 59
def prefixEnd_5164069 : Nat := 4983230072969 + 3 ^ 40 * 5164069 * 2
def baseEnd_5164069 : Nat := 2651649529983061289988385

theorem tailTrace_5164069 : CollatzResearch.WordTrace tailWord_5164069 prefixEnd_5164069 2651649529983061289988385 := by
  unfold tailWord_5164069
  simp only [CollatzResearch.WordTrace]
  refine ⟨188349069928467440614463261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125566046618978293742975507 188349069928467440614463261)
  ·
    refine ⟨70630901223175290230423723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188349069928467440614463261 70630901223175290230423723)
    ·
      refine ⟨105946351834762935345635585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70630901223175290230423723 105946351834762935345635585)
      ·
        refine ⟨79459763876072201509226689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105946351834762935345635585 79459763876072201509226689)
        ·
          refine ⟨59594822907054151131920017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79459763876072201509226689 59594822907054151131920017)
          ·
            refine ⟨44696117180290613348940013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59594822907054151131920017 44696117180290613348940013)
            ·
              refine ⟨16761043942608980005852505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44696117180290613348940013 16761043942608980005852505)
              ·
                refine ⟨12570782956956735004389379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16761043942608980005852505 12570782956956735004389379)
                ·
                  refine ⟨18856174435435102506584069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12570782956956735004389379 18856174435435102506584069)
                  ·
                    refine ⟨3535532706644081719984513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18856174435435102506584069 3535532706644081719984513)
                    ·
                      refine ⟨2651649529983061289988385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535532706644081719984513 2651649529983061289988385)
                      ·
                        rfl

theorem cell23_5164069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_5164069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164069 prefixEnd_5164069 := by exact prefixLift 5164069
  have htrace : WordTrace (prefixWord ++ tailWord_5164069) baseStart_5164069 baseEnd_5164069 := by
    simpa [prefixWord, tailWord_5164069, baseEnd_5164069] using wordTrace_append hprefix tailTrace_5164069
  have hstable : (prefixWord ++ tailWord_5164069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164069).length < 2 ^ (prefixWord ++ tailWord_5164069).sum := by decide
  have hdescent : baseEnd_5164069 < baseStart_5164069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164082 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_5164082 : Nat := 118140960795 + 5164082 * 2 ^ 59
def prefixEnd_5164082 : Nat := 4983230072969 + 3 ^ 40 * 5164082 * 2
def baseEnd_5164082 : Nat := 2651656205231569739125825

theorem tailTrace_5164082 : CollatzResearch.WordTrace tailWord_5164082 prefixEnd_5164082 2651656205231569739125825 := by
  unfold tailWord_5164082
  simp only [CollatzResearch.WordTrace]
  refine ⟨47087386019355085958671625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125566362718280229223124333 47087386019355085958671625)
  ·
    refine ⟨35315539514516314469003719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47087386019355085958671625 35315539514516314469003719)
    ·
      refine ⟨52973309271774471703505579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35315539514516314469003719 52973309271774471703505579)
      ·
        refine ⟨79459963907661707555258369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52973309271774471703505579 79459963907661707555258369)
        ·
          refine ⟨59594972930746280666443777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79459963907661707555258369 59594972930746280666443777)
          ·
            refine ⟨44696229698059710499832833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59594972930746280666443777 44696229698059710499832833)
            ·
              refine ⟨33522172273544782874874625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44696229698059710499832833 33522172273544782874874625)
              ·
                refine ⟨25141629205158587156155969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33522172273544782874874625 25141629205158587156155969)
                ·
                  refine ⟨18856221903868940367116977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25141629205158587156155969 18856221903868940367116977)
                  ·
                    refine ⟨14142166427901705275337733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18856221903868940367116977 14142166427901705275337733)
                    ·
                      refine ⟨2651656205231569739125825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14142166427901705275337733 2651656205231569739125825)
                      ·
                        rfl

theorem cell23_5164082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_5164082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164082 prefixEnd_5164082 := by exact prefixLift 5164082
  have htrace : WordTrace (prefixWord ++ tailWord_5164082) baseStart_5164082 baseEnd_5164082 := by
    simpa [prefixWord, tailWord_5164082, baseEnd_5164082] using wordTrace_append hprefix tailTrace_5164082
  have hstable : (prefixWord ++ tailWord_5164082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164082).length < 2 ^ (prefixWord ++ tailWord_5164082).sum := by decide
  have hdescent : baseEnd_5164082 < baseStart_5164082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164095 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_5164095 : Nat := 118140960795 + 5164095 * 2 ^ 59
def prefixEnd_5164095 : Nat := 4983230072969 + 3 ^ 40 * 5164095 * 2
def baseEnd_5164095 : Nat := 2651662880480078188263265

theorem tailTrace_5164095 : CollatzResearch.WordTrace tailWord_5164095 prefixEnd_5164095 2651662880480078188263265 := by
  unfold tailWord_5164095
  simp only [CollatzResearch.WordTrace]
  refine ⟨188350018226373247054909739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125566678817582164703273159 188350018226373247054909739)
  ·
    refine ⟨282525027339559870582364609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188350018226373247054909739 282525027339559870582364609)
    ·
      refine ⟨211893770504669902936773457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282525027339559870582364609 211893770504669902936773457)
      ·
        refine ⟨158920327878502427202580093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211893770504669902936773457 158920327878502427202580093)
        ·
          refine ⟨59595122954438410200967535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158920327878502427202580093 59595122954438410200967535)
          ·
            refine ⟨89392684431657615301451303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59595122954438410200967535 89392684431657615301451303)
            ·
              refine ⟨134089026647486422952176955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89392684431657615301451303 134089026647486422952176955)
              ·
                refine ⟨201133539971229634428265433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134089026647486422952176955 201133539971229634428265433)
                ·
                  refine ⟨150850154978422225821199075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201133539971229634428265433 150850154978422225821199075)
                  ·
                    refine ⟨226275232467633338731798613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150850154978422225821199075 226275232467633338731798613)
                    ·
                      refine ⟨2651662880480078188263265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226275232467633338731798613 2651662880480078188263265)
                      ·
                        rfl

theorem cell23_5164095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_5164095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164095 prefixEnd_5164095 := by exact prefixLift 5164095
  have htrace : WordTrace (prefixWord ++ tailWord_5164095) baseStart_5164095 baseEnd_5164095 := by
    simpa [prefixWord, tailWord_5164095, baseEnd_5164095] using wordTrace_append hprefix tailTrace_5164095
  have hstable : (prefixWord ++ tailWord_5164095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164095).length < 2 ^ (prefixWord ++ tailWord_5164095).sum := by decide
  have hdescent : baseEnd_5164095 < baseStart_5164095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164109 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 7]
def baseStart_5164109 : Nat := 118140960795 + 5164109 * 2 ^ 59
def prefixEnd_5164109 : Nat := 4983230072969 + 3 ^ 40 * 5164109 * 2
def baseEnd_5164109 : Nat := 294630007689915681498689

theorem tailTrace_5164109 : CollatzResearch.WordTrace tailWord_5164109 prefixEnd_5164109 294630007689915681498689 := by
  unfold tailWord_5164109
  simp only [CollatzResearch.WordTrace]
  refine ⟨188350528848322527445919381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125567019232215018297279587 188350528848322527445919381)
  ·
    refine ⟨8828931039765118474027471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 188350528848322527445919381 8828931039765118474027471)
    ·
      refine ⟨13243396559647677711041207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8828931039765118474027471 13243396559647677711041207)
      ·
        refine ⟨19865094839471516566561811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13243396559647677711041207 19865094839471516566561811)
        ·
          refine ⟨29797642259207274849842717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19865094839471516566561811 29797642259207274849842717)
          ·
            refine ⟨11174115847202728068691019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29797642259207274849842717 11174115847202728068691019)
            ·
              refine ⟨16761173770804092103036529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11174115847202728068691019 16761173770804092103036529)
              ·
                refine ⟨12570880328103069077277397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16761173770804092103036529 12570880328103069077277397)
                ·
                  refine ⟨294630007689915681498689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12570880328103069077277397 294630007689915681498689)
                  ·
                    rfl

theorem cell23_5164109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_5164109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164109 prefixEnd_5164109 := by exact prefixLift 5164109
  have htrace : WordTrace (prefixWord ++ tailWord_5164109) baseStart_5164109 baseEnd_5164109 := by
    simpa [prefixWord, tailWord_5164109, baseEnd_5164109] using wordTrace_append hprefix tailTrace_5164109
  have hstable : (prefixWord ++ tailWord_5164109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164109).length < 2 ^ (prefixWord ++ tailWord_5164109).sum := by decide
  have hdescent : baseEnd_5164109 < baseStart_5164109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164115 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7]
def baseStart_5164115 : Nat := 118140960795 + 5164115 * 2 ^ 59
def prefixEnd_5164115 : Nat := 4983230072969 + 3 ^ 40 * 5164115 * 2
def baseEnd_5164115 : Nat := 2651673150093168110013173

theorem tailTrace_5164115 : CollatzResearch.WordTrace tailWord_5164115 prefixEnd_5164115 2651673150093168110013173 := by
  unfold tailWord_5164115
  simp only [CollatzResearch.WordTrace]
  refine ⟨188350747686300790470637799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125567165124200526980425199 188350747686300790470637799)
  ·
    refine ⟨282526121529451185705956699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188350747686300790470637799 282526121529451185705956699)
    ·
      refine ⟨423789182294176778558935049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282526121529451185705956699 423789182294176778558935049)
      ·
        refine ⟨317841886720632583919201287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423789182294176778558935049 317841886720632583919201287)
        ·
          refine ⟨476762830080948875878801931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317841886720632583919201287 476762830080948875878801931)
          ·
            refine ⟨715144245121423313818202897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476762830080948875878801931 715144245121423313818202897)
            ·
              refine ⟨536358183841067485363652173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715144245121423313818202897 536358183841067485363652173)
              ·
                refine ⟨201134318940400307011369565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536358183841067485363652173 201134318940400307011369565)
                ·
                  refine ⟨75425369602650115129263587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201134318940400307011369565 75425369602650115129263587)
                  ·
                    refine ⟨113138054403975172693895381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75425369602650115129263587 113138054403975172693895381)
                    ·
                      refine ⟨2651673150093168110013173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113138054403975172693895381 2651673150093168110013173)
                      ·
                        rfl

theorem cell23_5164115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_5164115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164115 prefixEnd_5164115 := by exact prefixLift 5164115
  have htrace : WordTrace (prefixWord ++ tailWord_5164115) baseStart_5164115 baseEnd_5164115 := by
    simpa [prefixWord, tailWord_5164115, baseEnd_5164115] using wordTrace_append hprefix tailTrace_5164115
  have hstable : (prefixWord ++ tailWord_5164115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164115).length < 2 ^ (prefixWord ++ tailWord_5164115).sum := by decide
  have hdescent : baseEnd_5164115 < baseStart_5164115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164122 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_5164122 : Nat := 118140960795 + 5164122 * 2 ^ 59
def prefixEnd_5164122 : Nat := 4983230072969 + 3 ^ 40 * 5164122 * 2
def baseEnd_5164122 : Nat := 883892248152583194208547

theorem tailTrace_5164122 : CollatzResearch.WordTrace tailWord_5164122 prefixEnd_5164122 883892248152583194208547 := by
  unfold tailWord_5164122
  simp only [CollatzResearch.WordTrace]
  refine ⟨47087750749318857666535655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125567335331516953777428413 47087750749318857666535655)
  ·
    refine ⟨70631626123978286499803483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47087750749318857666535655 70631626123978286499803483)
    ·
      refine ⟨105947439185967429749705225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70631626123978286499803483 105947439185967429749705225)
      ·
        refine ⟨79460579389475572312278919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105947439185967429749705225 79460579389475572312278919)
        ·
          refine ⟨119190869084213358468418379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79460579389475572312278919 119190869084213358468418379)
          ·
            refine ⟨178786303626320037702627569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119190869084213358468418379 178786303626320037702627569)
            ·
              refine ⟨134089727719740028276970677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178786303626320037702627569 134089727719740028276970677)
              ·
                refine ⟨12570911973725627650966001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134089727719740028276970677 12570911973725627650966001)
                ·
                  refine ⟨9428183980294220738224501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12570911973725627650966001 9428183980294220738224501)
                  ·
                    refine ⟨883892248152583194208547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9428183980294220738224501 883892248152583194208547)
                    ·
                      rfl

theorem cell23_5164122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_5164122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164122 prefixEnd_5164122 := by exact prefixLift 5164122
  have htrace : WordTrace (prefixWord ++ tailWord_5164122) baseStart_5164122 baseEnd_5164122 := by
    simpa [prefixWord, tailWord_5164122, baseEnd_5164122] using wordTrace_append hprefix tailTrace_5164122
  have hstable : (prefixWord ++ tailWord_5164122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164122).length < 2 ^ (prefixWord ++ tailWord_5164122).sum := by decide
  have hdescent : baseEnd_5164122 < baseStart_5164122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164169 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 3, 4]
def baseStart_5164169 : Nat := 118140960795 + 5164169 * 2 ^ 59
def prefixEnd_5164169 : Nat := 4983230072969 + 3 ^ 40 * 5164169 * 2
def baseEnd_5164169 : Nat := 883900292682836966245975

theorem tailTrace_5164169 : CollatzResearch.WordTrace tailWord_5164169 prefixEnd_5164169 883900292682836966245975 := by
  unfold tailWord_5164169
  simp only [CollatzResearch.WordTrace]
  refine ⟨188352717228105157693103561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125568478152070105128735707 188352717228105157693103561)
  ·
    refine ⟨141264537921078868269827671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188352717228105157693103561 141264537921078868269827671)
    ·
      refine ⟨211896806881618302404741507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141264537921078868269827671 211896806881618302404741507)
      ·
        refine ⟨317845210322427453607112261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211896806881618302404741507 317845210322427453607112261)
        ·
          refine ⟨59595976935455147551333549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 317845210322427453607112261 59595976935455147551333549)
          ·
            refine ⟨22348491350795680331750081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59595976935455147551333549 22348491350795680331750081)
            ·
              refine ⟨16761368513096760248812561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22348491350795680331750081 16761368513096760248812561)
              ·
                refine ⟨12571026384822570186609421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16761368513096760248812561 12571026384822570186609421)
                ·
                  refine ⟨4714134894308463819978533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12571026384822570186609421 4714134894308463819978533)
                  ·
                    refine ⟨883900292682836966245975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4714134894308463819978533 883900292682836966245975)
                    ·
                      rfl

theorem cell23_5164169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_5164169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164169 prefixEnd_5164169 := by exact prefixLift 5164169
  have htrace : WordTrace (prefixWord ++ tailWord_5164169) baseStart_5164169 baseEnd_5164169 := by
    simpa [prefixWord, tailWord_5164169, baseEnd_5164169] using wordTrace_append hprefix tailTrace_5164169
  have hstable : (prefixWord ++ tailWord_5164169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164169).length < 2 ^ (prefixWord ++ tailWord_5164169).sum := by decide
  have hdescent : baseEnd_5164169 < baseStart_5164169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164196 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_5164196 : Nat := 118140960795 + 5164196 * 2 ^ 59
def prefixEnd_5164196 : Nat := 4983230072969 + 3 ^ 40 * 5164196 * 2
def baseEnd_5164196 : Nat := 2651714742026182293100301

theorem tailTrace_5164196 : CollatzResearch.WordTrace tailWord_5164196 prefixEnd_5164196 2651714742026182293100301 := by
  unfold tailWord_5164196
  simp only [CollatzResearch.WordTrace]
  refine ⟨94176850999503670652168221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125569134666004894202890961 94176850999503670652168221)
  ·
    refine ⟨35316319124813876494563083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94176850999503670652168221 35316319124813876494563083)
    ·
      refine ⟨52974478687220814741844625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35316319124813876494563083 52974478687220814741844625)
      ·
        refine ⟨39730859015415611056383469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52974478687220814741844625 39730859015415611056383469)
        ·
          refine ⟨14899072130780854146143801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39730859015415611056383469 14899072130780854146143801)
          ·
            refine ⟨11174304098085640609607851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14899072130780854146143801 11174304098085640609607851)
            ·
              refine ⟨16761456147128460914411777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11174304098085640609607851 16761456147128460914411777)
              ·
                refine ⟨12571092110346345685808833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16761456147128460914411777 12571092110346345685808833)
                ·
                  refine ⟨9428319082759759264356625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12571092110346345685808833 9428319082759759264356625)
                  ·
                    refine ⟨7071239312069819448267469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9428319082759759264356625 7071239312069819448267469)
                    ·
                      refine ⟨2651714742026182293100301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7071239312069819448267469 2651714742026182293100301)
                      ·
                        rfl

theorem cell23_5164196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_5164196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164196 prefixEnd_5164196 := by exact prefixLift 5164196
  have htrace : WordTrace (prefixWord ++ tailWord_5164196) baseStart_5164196 baseEnd_5164196 := by
    simpa [prefixWord, tailWord_5164196, baseEnd_5164196] using wordTrace_append hprefix tailTrace_5164196
  have hstable : (prefixWord ++ tailWord_5164196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164196).length < 2 ^ (prefixWord ++ tailWord_5164196).sum := by decide
  have hdescent : baseEnd_5164196 < baseStart_5164196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164199 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 8]
def baseStart_5164199 : Nat := 118140960795 + 5164199 * 2 ^ 59
def prefixEnd_5164199 : Nat := 4983230072969 + 3 ^ 40 * 5164199 * 2
def baseEnd_5164199 : Nat := 294635142496460642373643

theorem tailTrace_5164199 : CollatzResearch.WordTrace tailWord_5164199 prefixEnd_5164199 294635142496460642373643 := by
  unfold tailWord_5164199
  simp only [CollatzResearch.WordTrace]
  refine ⟨188353811417996472816695651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125569207611997648544463767 188353811417996472816695651)
  ·
    refine ⟨282530717126994709225043477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188353811417996472816695651 282530717126994709225043477)
    ·
      refine ⟨13243627365327876994923913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 282530717126994709225043477 13243627365327876994923913)
      ·
        refine ⟨9932720523995907746192935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13243627365327876994923913 9932720523995907746192935)
        ·
          refine ⟨14899080785993861619289403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9932720523995907746192935 14899080785993861619289403)
          ·
            refine ⟨22348621178990792428934105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14899080785993861619289403 22348621178990792428934105)
            ·
              refine ⟨16761465884243094321700579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22348621178990792428934105 16761465884243094321700579)
              ·
                refine ⟨25142198826364641482550869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16761465884243094321700579 25142198826364641482550869)
                ·
                  refine ⟨294635142496460642373643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25142198826364641482550869 294635142496460642373643)
                  ·
                    rfl

theorem cell23_5164199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 8].length) (baseStart_5164199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164199 prefixEnd_5164199 := by exact prefixLift 5164199
  have htrace : WordTrace (prefixWord ++ tailWord_5164199) baseStart_5164199 baseEnd_5164199 := by
    simpa [prefixWord, tailWord_5164199, baseEnd_5164199] using wordTrace_append hprefix tailTrace_5164199
  have hstable : (prefixWord ++ tailWord_5164199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164199).length < 2 ^ (prefixWord ++ tailWord_5164199).sum := by decide
  have hdescent : baseEnd_5164199 < baseStart_5164199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164219 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 1, 5, 2]
def baseStart_5164219 : Nat := 118140960795 + 5164219 * 2 ^ 59
def prefixEnd_5164219 : Nat := 4983230072969 + 3 ^ 40 * 5164219 * 2
def baseEnd_5164219 : Nat := 2651726552081235703112695

theorem tailTrace_5164219 : CollatzResearch.WordTrace tailWord_5164219 prefixEnd_5164219 2651726552081235703112695 := by
  unfold tailWord_5164219
  simp only [CollatzResearch.WordTrace]
  refine ⟨188354540877924016232423711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125569693918616010821615807 188354540877924016232423711)
  ·
    refine ⟨282531811316886024348635567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188354540877924016232423711 282531811316886024348635567)
    ·
      refine ⟨423797716975329036522953351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282531811316886024348635567 423797716975329036522953351)
      ·
        refine ⟨635696575462993554784430027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423797716975329036522953351 635696575462993554784430027)
        ·
          refine ⟨953544863194490332176645041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635696575462993554784430027 953544863194490332176645041)
          ·
            refine ⟨715158647395867749132483781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953544863194490332176645041 715158647395867749132483781)
            ·
              refine ⟨134092246386725202962340709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 715158647395867749132483781 134092246386725202962340709)
              ·
                refine ⟨25142296197510975555438883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134092246386725202962340709 25142296197510975555438883)
                ·
                  refine ⟨37713444296266463333158325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25142296197510975555438883 37713444296266463333158325)
                  ·
                    refine ⟨3535635402774980937483593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37713444296266463333158325 3535635402774980937483593)
                    ·
                      refine ⟨2651726552081235703112695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535635402774980937483593 2651726552081235703112695)
                      ·
                        rfl

theorem cell23_5164219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5, 2].length) (baseStart_5164219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164219 prefixEnd_5164219 := by exact prefixLift 5164219
  have htrace : WordTrace (prefixWord ++ tailWord_5164219) baseStart_5164219 baseEnd_5164219 := by
    simpa [prefixWord, tailWord_5164219, baseEnd_5164219] using wordTrace_append hprefix tailTrace_5164219
  have hstable : (prefixWord ++ tailWord_5164219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164219).length < 2 ^ (prefixWord ++ tailWord_5164219).sum := by decide
  have hdescent : baseEnd_5164219 < baseStart_5164219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164260 : List Nat := [2, 3, 1, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_5164260 : Nat := 118140960795 + 5164260 * 2 ^ 59
def prefixEnd_5164260 : Nat := 4983230072969 + 3 ^ 40 * 5164260 * 2
def baseEnd_5164260 : Nat := 2651747604788070042700007

theorem tailTrace_5164260 : CollatzResearch.WordTrace tailWord_5164260 prefixEnd_5164260 2651747604788070042700007 := by
  unfold tailWord_5164260
  simp only [CollatzResearch.WordTrace]
  refine ⟨94178018135387740117333117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125570690847183653489777489 94178018135387740117333117)
  ·
    refine ⟨35316756800770402543999919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94178018135387740117333117 35316756800770402543999919)
    ·
      refine ⟨52975135201155603815999879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35316756800770402543999919 52975135201155603815999879)
      ·
        refine ⟨79462702801733405723999819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52975135201155603815999879 79462702801733405723999819)
        ·
          refine ⟨119194054202600108585999729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79462702801733405723999819 119194054202600108585999729)
          ·
            refine ⟨89395540651950081439499797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119194054202600108585999729 89395540651950081439499797)
            ·
              refine ⟨4190415968060160067476553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89395540651950081439499797 4190415968060160067476553)
              ·
                refine ⟨3142811976045120050607415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4190415968060160067476553 3142811976045120050607415)
                ·
                  refine ⟨4714217964067680075911123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142811976045120050607415 4714217964067680075911123)
                  ·
                    refine ⟨7071326946101520113866685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4714217964067680075911123 7071326946101520113866685)
                    ·
                      refine ⟨2651747604788070042700007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7071326946101520113866685 2651747604788070042700007)
                      ·
                        rfl

theorem cell23_5164260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_5164260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164260 prefixEnd_5164260 := by exact prefixLift 5164260
  have htrace : WordTrace (prefixWord ++ tailWord_5164260) baseStart_5164260 baseEnd_5164260 := by
    simpa [prefixWord, tailWord_5164260, baseEnd_5164260] using wordTrace_append hprefix tailTrace_5164260
  have hstable : (prefixWord ++ tailWord_5164260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164260).length < 2 ^ (prefixWord ++ tailWord_5164260).sum := by decide
  have hdescent : baseEnd_5164260 < baseStart_5164260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164300 : List Nat := [2, 2, 1, 2, 2, 3, 1, 5, 1, 2, 2]
def baseStart_5164300 : Nat := 118140960795 + 5164300 * 2 ^ 59
def prefixEnd_5164300 : Nat := 4983230072969 + 3 ^ 40 * 5164300 * 2
def baseEnd_5164300 : Nat := 2651768144014249886199823

theorem tailTrace_5164300 : CollatzResearch.WordTrace tailWord_5164300 prefixEnd_5164300 2651768144014249886199823 := by
  unfold tailWord_5164300
  simp only [CollatzResearch.WordTrace]
  refine ⟨94178747595315283533061177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125571663460420378044081569 94178747595315283533061177)
  ·
    refine ⟨70634060696486462649795883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94178747595315283533061177 70634060696486462649795883)
    ·
      refine ⟨105951091044729693974693825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70634060696486462649795883 105951091044729693974693825)
      ·
        refine ⟨79463318283547270481020369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105951091044729693974693825 79463318283547270481020369)
        ·
          refine ⟨59597488712660452860765277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79463318283547270481020369 59597488712660452860765277)
          ·
            refine ⟨22349058267247669822786979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59597488712660452860765277 22349058267247669822786979)
            ·
              refine ⟨33523587400871504734180469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22349058267247669822786979 33523587400871504734180469)
              ·
                refine ⟨3142836318831703568829419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33523587400871504734180469 3142836318831703568829419)
                ·
                  refine ⟨4714254478247555353244129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142836318831703568829419 4714254478247555353244129)
                  ·
                    refine ⟨3535690858685666514933097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714254478247555353244129 3535690858685666514933097)
                    ·
                      refine ⟨2651768144014249886199823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535690858685666514933097 2651768144014249886199823)
                      ·
                        rfl

theorem cell23_5164300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_5164300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164300 prefixEnd_5164300 := by exact prefixLift 5164300
  have htrace : WordTrace (prefixWord ++ tailWord_5164300) baseStart_5164300 baseEnd_5164300 := by
    simpa [prefixWord, tailWord_5164300, baseEnd_5164300] using wordTrace_append hprefix tailTrace_5164300
  have hstable : (prefixWord ++ tailWord_5164300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164300).length < 2 ^ (prefixWord ++ tailWord_5164300).sum := by decide
  have hdescent : baseEnd_5164300 < baseStart_5164300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164317 : List Nat := [1, 4, 2, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5164317 : Nat := 118140960795 + 5164317 * 2 ^ 59
def prefixEnd_5164317 : Nat := 4983230072969 + 3 ^ 40 * 5164317 * 2
def baseEnd_5164317 : Nat := 2651776873185376319687245

theorem tailTrace_5164317 : CollatzResearch.WordTrace tailWord_5164317 prefixEnd_5164317 2651776873185376319687245 := by
  unfold tailWord_5164317
  simp only [CollatzResearch.WordTrace]
  refine ⟨188358115231568978969491205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125572076821045985979660803 188358115231568978969491205)
  ·
    refine ⟨35317146605919183556779601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188358115231568978969491205 35317146605919183556779601)
    ·
      refine ⟨26487859954439387667584701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35317146605919183556779601 26487859954439387667584701)
      ·
        refine ⟨9932947482914770375344263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26487859954439387667584701 9932947482914770375344263)
        ·
          refine ⟨14899421224372155563016395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9932947482914770375344263 14899421224372155563016395)
          ·
            refine ⟨22349131836558233344524593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14899421224372155563016395 22349131836558233344524593)
            ·
              refine ⟨16761848877418675008393445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22349131836558233344524593 16761848877418675008393445)
              ·
                refine ⟨3142846664516001564073771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16761848877418675008393445 3142846664516001564073771)
                ·
                  refine ⟨4714269996774002346110657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142846664516001564073771 4714269996774002346110657)
                  ·
                    refine ⟨3535702497580501759582993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714269996774002346110657 3535702497580501759582993)
                    ·
                      refine ⟨2651776873185376319687245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535702497580501759582993 2651776873185376319687245)
                      ·
                        rfl

theorem cell23_5164317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5164317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164317 prefixEnd_5164317 := by exact prefixLift 5164317
  have htrace : WordTrace (prefixWord ++ tailWord_5164317) baseStart_5164317 baseEnd_5164317 := by
    simpa [prefixWord, tailWord_5164317, baseEnd_5164317] using wordTrace_append hprefix tailTrace_5164317
  have hstable : (prefixWord ++ tailWord_5164317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164317).length < 2 ^ (prefixWord ++ tailWord_5164317).sum := by decide
  have hdescent : baseEnd_5164317 < baseStart_5164317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164359 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_5164359 : Nat := 118140960795 + 5164359 * 2 ^ 59
def prefixEnd_5164359 : Nat := 4983230072969 + 3 ^ 40 * 5164359 * 2
def baseEnd_5164359 : Nat := 2651798439372865155362051

theorem tailTrace_5164359 : CollatzResearch.WordTrace tailWord_5164359 prefixEnd_5164359 2651798439372865155362051 := by
  unfold tailWord_5164359
  simp only [CollatzResearch.WordTrace]
  refine ⟨188359647097416820142520131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125573098064944546761680087 188359647097416820142520131)
  ·
    refine ⟨282539470646125230213780197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188359647097416820142520131 282539470646125230213780197)
    ·
      refine ⟨52976150746148480665083787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282539470646125230213780197 52976150746148480665083787)
      ·
        refine ⟨79464226119222720997625681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52976150746148480665083787 79464226119222720997625681)
        ·
          refine ⟨59598169589417040748219261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79464226119222720997625681 59598169589417040748219261)
          ·
            refine ⟨22349313596031390280582223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59598169589417040748219261 22349313596031390280582223)
            ·
              refine ⟨33523970394047085420873335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22349313596031390280582223 33523970394047085420873335)
              ·
                refine ⟨50285955591070628131310003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33523970394047085420873335 50285955591070628131310003)
                ·
                  refine ⟨75428933386605942196965005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50285955591070628131310003 75428933386605942196965005)
                  ·
                    refine ⟨28285850019977228323861877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75428933386605942196965005 28285850019977228323861877)
                    ·
                      refine ⟨2651798439372865155362051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28285850019977228323861877 2651798439372865155362051)
                      ·
                        rfl

theorem cell23_5164359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_5164359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164359 prefixEnd_5164359 := by exact prefixLift 5164359
  have htrace : WordTrace (prefixWord ++ tailWord_5164359) baseStart_5164359 baseEnd_5164359 := by
    simpa [prefixWord, tailWord_5164359, baseEnd_5164359] using wordTrace_append hprefix tailTrace_5164359
  have hstable : (prefixWord ++ tailWord_5164359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164359).length < 2 ^ (prefixWord ++ tailWord_5164359).sum := by decide
  have hdescent : baseEnd_5164359 < baseStart_5164359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164386 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5164386 : Nat := 118140960795 + 5164386 * 2 ^ 59
def prefixEnd_5164386 : Nat := 4983230072969 + 3 ^ 40 * 5164386 * 2
def baseEnd_5164386 : Nat := 2651812303350536549724427

theorem tailTrace_5164386 : CollatzResearch.WordTrace tailWord_5164386 prefixEnd_5164386 2651812303350536549724427 := by
  unfold tailWord_5164386
  simp only [CollatzResearch.WordTrace]
  refine ⟨47090157967079750938438253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125573754578879335835835341 47090157967079750938438253)
  ·
    refine ⟨17658809237654906601914345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47090157967079750938438253 17658809237654906601914345)
    ·
      refine ⟨13244106928241179951435759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17658809237654906601914345 13244106928241179951435759)
      ·
        refine ⟨19866160392361769927153639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13244106928241179951435759 19866160392361769927153639)
        ·
          refine ⟨29799240588542654890730459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19866160392361769927153639 29799240588542654890730459)
          ·
            refine ⟨44698860882813982336095689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29799240588542654890730459 44698860882813982336095689)
            ·
              refine ⟨33524145662110486752071767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44698860882813982336095689 33524145662110486752071767)
              ·
                refine ⟨50286218493165730128107651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33524145662110486752071767 50286218493165730128107651)
                ·
                  refine ⟨75429327739748595192161477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50286218493165730128107651 75429327739748595192161477)
                  ·
                    refine ⟨14142998951202861598530277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75429327739748595192161477 14142998951202861598530277)
                    ·
                      refine ⟨2651812303350536549724427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14142998951202861598530277 2651812303350536549724427)
                      ·
                        rfl

theorem cell23_5164386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5164386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164386 prefixEnd_5164386 := by exact prefixLift 5164386
  have htrace : WordTrace (prefixWord ++ tailWord_5164386) baseStart_5164386 baseEnd_5164386 := by
    simpa [prefixWord, tailWord_5164386, baseEnd_5164386] using wordTrace_append hprefix tailTrace_5164386
  have hstable : (prefixWord ++ tailWord_5164386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164386).length < 2 ^ (prefixWord ++ tailWord_5164386).sum := by decide
  have hdescent : baseEnd_5164386 < baseStart_5164386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164394 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5164394 : Nat := 118140960795 + 5164394 * 2 ^ 59
def prefixEnd_5164394 : Nat := 4983230072969 + 3 ^ 40 * 5164394 * 2
def baseEnd_5164394 : Nat := 2651816411195772518424391

theorem tailTrace_5164394 : CollatzResearch.WordTrace tailWord_5164394 prefixEnd_5164394 2651816411195772518424391 := by
  unfold tailWord_5164394
  simp only [CollatzResearch.WordTrace]
  refine ⟨47090230913072505280011059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125573949101526680746696157 47090230913072505280011059)
  ·
    refine ⟨70635346369608757920016589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47090230913072505280011059 70635346369608757920016589)
    ·
      refine ⟨26488254888603284220006221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70635346369608757920016589 26488254888603284220006221)
      ·
        refine ⟨9933095583226231582502333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26488254888603284220006221 9933095583226231582502333)
        ·
          refine ⟨3724910843709836843438375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9933095583226231582502333 3724910843709836843438375)
          ·
            refine ⟨5587366265564755265157563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724910843709836843438375 5587366265564755265157563)
            ·
              refine ⟨8381049398347132897736345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587366265564755265157563 8381049398347132897736345)
              ·
                refine ⟨6285787048760349673302259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8381049398347132897736345 6285787048760349673302259)
                ·
                  refine ⟨9428680573140524509953389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6285787048760349673302259 9428680573140524509953389)
                  ·
                    refine ⟨3535755214927696691232521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9428680573140524509953389 3535755214927696691232521)
                    ·
                      refine ⟨2651816411195772518424391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535755214927696691232521 2651816411195772518424391)
                      ·
                        rfl

theorem cell23_5164394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5164394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164394 prefixEnd_5164394 := by exact prefixLift 5164394
  have htrace : WordTrace (prefixWord ++ tailWord_5164394) baseStart_5164394 baseEnd_5164394 := by
    simpa [prefixWord, tailWord_5164394, baseEnd_5164394] using wordTrace_append hprefix tailTrace_5164394
  have hstable : (prefixWord ++ tailWord_5164394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164394).length < 2 ^ (prefixWord ++ tailWord_5164394).sum := by decide
  have hdescent : baseEnd_5164394 < baseStart_5164394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164409 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 1, 7]
def baseStart_5164409 : Nat := 118140960795 + 5164409 * 2 ^ 59
def prefixEnd_5164409 : Nat := 4983230072969 + 3 ^ 40 * 5164409 * 2
def baseEnd_5164409 : Nat := 883941371135196653245607

theorem tailTrace_5164409 : CollatzResearch.WordTrace tailWord_5164409 prefixEnd_5164409 883941371135196653245607 := by
  unfold tailWord_5164409
  simp only [CollatzResearch.WordTrace]
  refine ⟨188361470747235678681840281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125574313831490452454560187 188361470747235678681840281)
  ·
    refine ⟨141271103060426759011380211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188361470747235678681840281 141271103060426759011380211)
    ·
      refine ⟨211906654590640138517070317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141271103060426759011380211 211906654590640138517070317)
      ·
        refine ⟨79464995471490051943901369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211906654590640138517070317 79464995471490051943901369)
        ·
          refine ⟨59598746603617538957926027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79464995471490051943901369 59598746603617538957926027)
          ·
            refine ⟨89398119905426308436889041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59598746603617538957926027 89398119905426308436889041)
            ·
              refine ⟨67048589929069731327666781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89398119905426308436889041 67048589929069731327666781)
              ·
                refine ⟨25143221223401149247875043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67048589929069731327666781 25143221223401149247875043)
                ·
                  refine ⟨37714831835101723871812565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25143221223401149247875043 37714831835101723871812565)
                  ·
                    refine ⟨883941371135196653245607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37714831835101723871812565 883941371135196653245607)
                    ·
                      rfl

theorem cell23_5164409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_5164409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164409 prefixEnd_5164409 := by exact prefixLift 5164409
  have htrace : WordTrace (prefixWord ++ tailWord_5164409) baseStart_5164409 baseEnd_5164409 := by
    simpa [prefixWord, tailWord_5164409, baseEnd_5164409] using wordTrace_append hprefix tailTrace_5164409
  have hstable : (prefixWord ++ tailWord_5164409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164409).length < 2 ^ (prefixWord ++ tailWord_5164409).sum := by decide
  have hdescent : baseEnd_5164409 < baseStart_5164409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164416 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 4, 5, 2]
def baseStart_5164416 : Nat := 118140960795 + 5164416 * 2 ^ 59
def prefixEnd_5164416 : Nat := 4983230072969 + 3 ^ 40 * 5164416 * 2
def baseEnd_5164416 : Nat := 2651827707770171432349289

theorem tailTrace_5164416 : CollatzResearch.WordTrace tailWord_5164416 prefixEnd_5164416 2651827707770171432349289 := by
  unfold tailWord_5164416
  simp only [CollatzResearch.WordTrace]
  refine ⟨94180863029105159438672551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125574484038806879251563401 94180863029105159438672551)
  ·
    refine ⟨141271294543657739158008827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94180863029105159438672551 141271294543657739158008827)
    ·
      refine ⟨211906941815486608737013241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141271294543657739158008827 211906941815486608737013241)
      ·
        refine ⟨158930206361614956552759931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211906941815486608737013241 158930206361614956552759931)
        ·
          refine ⟨238395309542422434829139897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158930206361614956552759931 238395309542422434829139897)
          ·
            refine ⟨178796482156816826121854923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238395309542422434829139897 178796482156816826121854923)
            ·
              refine ⟨268194723235225239182782385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178796482156816826121854923 268194723235225239182782385)
              ·
                refine ⟨201146042426418929387086789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268194723235225239182782385 201146042426418929387086789)
                ·
                  refine ⟨37714882954953549260078773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201146042426418929387086789 37714882954953549260078773)
                  ·
                    refine ⟨3535770277026895243132385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37714882954953549260078773 3535770277026895243132385)
                    ·
                      refine ⟨2651827707770171432349289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535770277026895243132385 2651827707770171432349289)
                      ·
                        rfl

theorem cell23_5164416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_5164416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164416 prefixEnd_5164416 := by exact prefixLift 5164416
  have htrace : WordTrace (prefixWord ++ tailWord_5164416) baseStart_5164416 baseEnd_5164416 := by
    simpa [prefixWord, tailWord_5164416, baseEnd_5164416] using wordTrace_append hprefix tailTrace_5164416
  have hstable : (prefixWord ++ tailWord_5164416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164416).length < 2 ^ (prefixWord ++ tailWord_5164416).sum := by decide
  have hdescent : baseEnd_5164416 < baseStart_5164416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164430 : List Nat := [4, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_5164430 : Nat := 118140960795 + 5164430 * 2 ^ 59
def prefixEnd_5164430 : Nat := 4983230072969 + 3 ^ 40 * 5164430 * 2
def baseEnd_5164430 : Nat := 294648321833259375286025

theorem tailTrace_5164430 : CollatzResearch.WordTrace tailWord_5164430 prefixEnd_5164430 294648321833259375286025 := by
  unfold tailWord_5164430
  simp only [CollatzResearch.WordTrace]
  refine ⟨23545279585019949908544343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125574824453439732845569829 23545279585019949908544343)
  ·
    refine ⟨35317919377529924862816515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23545279585019949908544343 35317919377529924862816515)
    ·
      refine ⟨52976879066294887294224773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35317919377529924862816515 52976879066294887294224773)
      ·
        refine ⟨9933164824930291367667145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52976879066294887294224773 9933164824930291367667145)
        ·
          refine ⟨7449873618697718525750359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9933164824930291367667145 7449873618697718525750359)
          ·
            refine ⟨11174810428046577788625539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7449873618697718525750359 11174810428046577788625539)
            ·
              refine ⟨16762215642069866682938309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11174810428046577788625539 16762215642069866682938309)
              ·
                refine ⟨3142915432888100003050933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16762215642069866682938309 3142915432888100003050933)
                ·
                  refine ⟨294648321833259375286025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3142915432888100003050933 294648321833259375286025)
                  ·
                    rfl

theorem cell23_5164430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_5164430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164430 prefixEnd_5164430 := by exact prefixLift 5164430
  have htrace : WordTrace (prefixWord ++ tailWord_5164430) baseStart_5164430 baseEnd_5164430 := by
    simpa [prefixWord, tailWord_5164430, baseEnd_5164430] using wordTrace_append hprefix tailTrace_5164430
  have hstable : (prefixWord ++ tailWord_5164430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164430).length < 2 ^ (prefixWord ++ tailWord_5164430).sum := by decide
  have hdescent : baseEnd_5164430 < baseStart_5164430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164439 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 2, 8]
def baseStart_5164439 : Nat := 118140960795 + 5164439 * 2 ^ 59
def prefixEnd_5164439 : Nat := 4983230072969 + 3 ^ 40 * 5164439 * 2
def baseEnd_5164439 : Nat := 883946505941741614120561

theorem tailTrace_5164439 : CollatzResearch.WordTrace tailWord_5164439 prefixEnd_5164439 883946505941741614120561 := by
  unfold tailWord_5164439
  simp only [CollatzResearch.WordTrace]
  refine ⟨188362564937126993805432371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125575043291417995870288247 188362564937126993805432371)
  ·
    refine ⟨282543847405690490708148557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188362564937126993805432371 282543847405690490708148557)
    ·
      refine ⟨105953942777133934015555709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282543847405690490708148557 105953942777133934015555709)
      ·
        refine ⟨39732728541425225255833391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105953942777133934015555709 39732728541425225255833391)
        ·
          refine ⟨59599092812137837883750087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39732728541425225255833391 59599092812137837883750087)
          ·
            refine ⟨89398639218206756825625131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59599092812137837883750087 89398639218206756825625131)
            ·
              refine ⟨134097958827310135238437697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89398639218206756825625131 134097958827310135238437697)
              ·
                refine ⟨100573469120482601428828273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134097958827310135238437697 100573469120482601428828273)
                ·
                  refine ⟨75430101840361951071621205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100573469120482601428828273 75430101840361951071621205)
                  ·
                    refine ⟨883946505941741614120561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75430101840361951071621205 883946505941741614120561)
                    ·
                      rfl

theorem cell23_5164439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_5164439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164439 prefixEnd_5164439 := by exact prefixLift 5164439
  have htrace : WordTrace (prefixWord ++ tailWord_5164439) baseStart_5164439 baseEnd_5164439 := by
    simpa [prefixWord, tailWord_5164439, baseEnd_5164439] using wordTrace_append hprefix tailTrace_5164439
  have hstable : (prefixWord ++ tailWord_5164439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164439).length < 2 ^ (prefixWord ++ tailWord_5164439).sum := by decide
  have hdescent : baseEnd_5164439 < baseStart_5164439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164490 : List Nat := [3, 1, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_5164490 : Nat := 118140960795 + 5164490 * 2 ^ 59
def prefixEnd_5164490 : Nat := 4983230072969 + 3 ^ 40 * 5164490 * 2
def baseEnd_5164490 : Nat := 883955235112868047607983

theorem tailTrace_5164490 : CollatzResearch.WordTrace tailWord_5164490 prefixEnd_5164490 883955235112868047607983 := by
  unfold tailWord_5164490
  simp only [CollatzResearch.WordTrace]
  refine ⟨47091106264985557378884731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125576283373294819677025949 47091106264985557378884731)
  ·
    refine ⟨70636659397478336068327097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47091106264985557378884731 70636659397478336068327097)
    ·
      refine ⟨52977494548108752051245323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70636659397478336068327097 52977494548108752051245323)
      ·
        refine ⟨79466241822163128076867985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52977494548108752051245323 79466241822163128076867985)
        ·
          refine ⟨59599681366622346057650989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79466241822163128076867985 59599681366622346057650989)
          ·
            refine ⟨22349880512483379771619121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59599681366622346057650989 22349880512483379771619121)
            ·
              refine ⟨16762410384362534828714341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22349880512483379771619121 16762410384362534828714341)
              ·
                refine ⟨3142951947067975280383939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16762410384362534828714341 3142951947067975280383939)
                ·
                  refine ⟨4714427920601962920575909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3142951947067975280383939 4714427920601962920575909)
                  ·
                    refine ⟨883955235112868047607983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4714427920601962920575909 883955235112868047607983)
                    ·
                      rfl

theorem cell23_5164490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_5164490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164490 prefixEnd_5164490 := by exact prefixLift 5164490
  have htrace : WordTrace (prefixWord ++ tailWord_5164490) baseStart_5164490 baseEnd_5164490 := by
    simpa [prefixWord, tailWord_5164490, baseEnd_5164490] using wordTrace_append hprefix tailTrace_5164490
  have hstable : (prefixWord ++ tailWord_5164490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164490).length < 2 ^ (prefixWord ++ tailWord_5164490).sum := by decide
  have hdescent : baseEnd_5164490 < baseStart_5164490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164516 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_5164516 : Nat := 118140960795 + 5164516 * 2 ^ 59
def prefixEnd_5164516 : Nat := 4983230072969 + 3 ^ 40 * 5164516 * 2
def baseEnd_5164516 : Nat := 883959685278540347032943

theorem tailTrace_5164516 : CollatzResearch.WordTrace tailWord_5164516 prefixEnd_5164516 883959685278540347032943 := by
  unfold tailWord_5164516
  simp only [CollatzResearch.WordTrace]
  refine ⟨94182686678924017977992701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125576915571898690637323601 94182686678924017977992701)
  ·
    refine ⟨35318507504596506741747263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94182686678924017977992701 35318507504596506741747263)
    ·
      refine ⟨52977761256894760112620895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35318507504596506741747263 52977761256894760112620895)
      ·
        refine ⟨79466641885342140168931343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52977761256894760112620895 79466641885342140168931343)
        ·
          refine ⟨119199962828013210253397015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79466641885342140168931343 119199962828013210253397015)
          ·
            refine ⟨178799944242019815380095523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119199962828013210253397015 178799944242019815380095523)
            ·
              refine ⟨268199916363029723070143285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178799944242019815380095523 268199916363029723070143285)
              ·
                refine ⟨25143742159034036537825933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268199916363029723070143285 25143742159034036537825933)
                ·
                  refine ⟨9428903309637763701684725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25143742159034036537825933 9428903309637763701684725)
                  ·
                    refine ⟨883959685278540347032943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9428903309637763701684725 883959685278540347032943)
                    ·
                      rfl

theorem cell23_5164516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_5164516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164516 prefixEnd_5164516 := by exact prefixLift 5164516
  have htrace : WordTrace (prefixWord ++ tailWord_5164516) baseStart_5164516 baseEnd_5164516 := by
    simpa [prefixWord, tailWord_5164516, baseEnd_5164516] using wordTrace_append hprefix tailTrace_5164516
  have hstable : (prefixWord ++ tailWord_5164516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164516).length < 2 ^ (prefixWord ++ tailWord_5164516).sum := by decide
  have hdescent : baseEnd_5164516 < baseStart_5164516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164570 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2]
def baseStart_5164570 : Nat := 118140960795 + 5164570 * 2 ^ 59
def prefixEnd_5164570 : Nat := 4983230072969 + 3 ^ 40 * 5164570 * 2
def baseEnd_5164570 : Nat := 2651906783790963829823581

theorem tailTrace_5164570 : CollatzResearch.WordTrace tailWord_5164570 prefixEnd_5164570 2651906783790963829823581 := by
  unfold tailWord_5164570
  simp only [CollatzResearch.WordTrace]
  refine ⟨47091835724913100794612791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125578228599768268785634109 47091835724913100794612791)
  ·
    refine ⟨70637753587369651191919187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47091835724913100794612791 70637753587369651191919187)
    ·
      refine ⟨105956630381054476787878781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70637753587369651191919187 105956630381054476787878781)
      ·
        refine ⟨39733736392895428795454543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105956630381054476787878781 39733736392895428795454543)
        ·
          refine ⟨59600604589343143193181815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39733736392895428795454543 59600604589343143193181815)
          ·
            refine ⟨89400906884014714789772723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59600604589343143193181815 89400906884014714789772723)
            ·
              refine ⟨134101360326022072184659085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89400906884014714789772723 134101360326022072184659085)
              ·
                refine ⟨50288010122258277069247157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134101360326022072184659085 50288010122258277069247157)
                ·
                  refine ⟨4714500948961713475241921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50288010122258277069247157 4714500948961713475241921)
                  ·
                    refine ⟨3535875711721285106431441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4714500948961713475241921 3535875711721285106431441)
                    ·
                      refine ⟨2651906783790963829823581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3535875711721285106431441 2651906783790963829823581)
                      ·
                        rfl

theorem cell23_5164570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_5164570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164570 prefixEnd_5164570 := by exact prefixLift 5164570
  have htrace : WordTrace (prefixWord ++ tailWord_5164570) baseStart_5164570 baseEnd_5164570 := by
    simpa [prefixWord, tailWord_5164570, baseEnd_5164570] using wordTrace_append hprefix tailTrace_5164570
  have hstable : (prefixWord ++ tailWord_5164570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164570).length < 2 ^ (prefixWord ++ tailWord_5164570).sum := by decide
  have hdescent : baseEnd_5164570 < baseStart_5164570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164590 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_5164590 : Nat := 118140960795 + 5164590 * 2 ^ 59
def prefixEnd_5164590 : Nat := 4983230072969 + 3 ^ 40 * 5164590 * 2
def baseEnd_5164590 : Nat := 2651917053404053751573489

theorem tailTrace_5164590 : CollatzResearch.WordTrace tailWord_5164590 prefixEnd_5164590 2651917053404053751573489 := by
  unfold tailWord_5164590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23546009044947493324272403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125578714906386631062786149 23546009044947493324272403)
  ·
    refine ⟨35319013567421239986408605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23546009044947493324272403 35319013567421239986408605)
    ·
      refine ⟨13244630087782964994903227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35319013567421239986408605 13244630087782964994903227)
      ·
        refine ⟨19866945131674447492354841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13244630087782964994903227 19866945131674447492354841)
        ·
          refine ⟨14900208848755835619266131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19866945131674447492354841 14900208848755835619266131)
          ·
            refine ⟨22350313273133753428899197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14900208848755835619266131 22350313273133753428899197)
            ·
              refine ⟨8381367477425157535837199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22350313273133753428899197 8381367477425157535837199)
              ·
                refine ⟨12572051216137736303755799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381367477425157535837199 12572051216137736303755799)
                ·
                  refine ⟨18858076824206604455633699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12572051216137736303755799 18858076824206604455633699)
                  ·
                    refine ⟨28287115236309906683450549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18858076824206604455633699 28287115236309906683450549)
                    ·
                      refine ⟨2651917053404053751573489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28287115236309906683450549 2651917053404053751573489)
                      ·
                        rfl

theorem cell23_5164590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_5164590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164590 prefixEnd_5164590 := by exact prefixLift 5164590
  have htrace : WordTrace (prefixWord ++ tailWord_5164590) baseStart_5164590 baseEnd_5164590 := by
    simpa [prefixWord, tailWord_5164590, baseEnd_5164590] using wordTrace_append hprefix tailTrace_5164590
  have hstable : (prefixWord ++ tailWord_5164590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164590).length < 2 ^ (prefixWord ++ tailWord_5164590).sum := by decide
  have hdescent : baseEnd_5164590 < baseStart_5164590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164598 : List Nat := [5, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_5164598 : Nat := 118140960795 + 5164598 * 2 ^ 59
def prefixEnd_5164598 : Nat := 4983230072969 + 3 ^ 40 * 5164598 * 2
def baseEnd_5164598 : Nat := 2651921161249289720273453

theorem tailTrace_5164598 : CollatzResearch.WordTrace tailWord_5164598 prefixEnd_5164598 2651921161249289720273453 := by
  unfold tailWord_5164598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773022758971935247529403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125578909429033975973646965 11773022758971935247529403)
  ·
    refine ⟨17659534138457902871294105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11773022758971935247529403 17659534138457902871294105)
    ·
      refine ⟨13244650603843427153470579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17659534138457902871294105 13244650603843427153470579)
      ·
        refine ⟨19866975905765140730205869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13244650603843427153470579 19866975905765140730205869)
        ·
          refine ⟨7450115964661927773827201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19866975905765140730205869 7450115964661927773827201)
          ·
            refine ⟨5587586973496445830370401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7450115964661927773827201 5587586973496445830370401)
            ·
              refine ⟨4190690230122334372777801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5587586973496445830370401 4190690230122334372777801)
              ·
                refine ⟨3143017672591750779583351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4190690230122334372777801 3143017672591750779583351)
                ·
                  refine ⟨4714526508887626169375027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143017672591750779583351 4714526508887626169375027)
                  ·
                    refine ⟨7071789763331439254062541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4714526508887626169375027 7071789763331439254062541)
                    ·
                      refine ⟨2651921161249289720273453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7071789763331439254062541 2651921161249289720273453)
                      ·
                        rfl

theorem cell23_5164598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_5164598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164598 prefixEnd_5164598 := by exact prefixLift 5164598
  have htrace : WordTrace (prefixWord ++ tailWord_5164598) baseStart_5164598 baseEnd_5164598 := by
    simpa [prefixWord, tailWord_5164598, baseEnd_5164598] using wordTrace_append hprefix tailTrace_5164598
  have hstable : (prefixWord ++ tailWord_5164598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164598).length < 2 ^ (prefixWord ++ tailWord_5164598).sum := by decide
  have hdescent : baseEnd_5164598 < baseStart_5164598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164616 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_5164616 : Nat := 118140960795 + 5164616 * 2 ^ 59
def prefixEnd_5164616 : Nat := 4983230072969 + 3 ^ 40 * 5164616 * 2
def baseEnd_5164616 : Nat := 2651930403901070649848369

theorem tailTrace_5164616 : CollatzResearch.WordTrace tailWord_5164616 prefixEnd_5164616 2651930403901070649848369 := by
  unfold tailWord_5164616
  simp only [CollatzResearch.WordTrace]
  refine ⟨94184510328742876517312851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125579347104990502023083801 94184510328742876517312851)
  ·
    refine ⟨141276765493114314775969277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94184510328742876517312851 141276765493114314775969277)
    ·
      refine ⟨52978787059917868040988479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141276765493114314775969277 52978787059917868040988479)
      ·
        refine ⟨79468180589876802061482719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52978787059917868040988479 79468180589876802061482719)
        ·
          refine ⟨119202270884815203092224079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79468180589876802061482719 119202270884815203092224079)
          ·
            refine ⟨178803406327222804638336119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119202270884815203092224079 178803406327222804638336119)
            ·
              refine ⟨268205109490834206957504179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178803406327222804638336119 268205109490834206957504179)
              ·
                refine ⟨402307664236251310436256269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268205109490834206957504179 402307664236251310436256269)
                ·
                  refine ⟨150865374088594241413596101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402307664236251310436256269 150865374088594241413596101)
                  ·
                    refine ⟨28287257641611420265049269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150865374088594241413596101 28287257641611420265049269)
                    ·
                      refine ⟨2651930403901070649848369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28287257641611420265049269 2651930403901070649848369)
                      ·
                        rfl

theorem cell23_5164616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_5164616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164616 prefixEnd_5164616 := by exact prefixLift 5164616
  have htrace : WordTrace (prefixWord ++ tailWord_5164616) baseStart_5164616 baseEnd_5164616 := by
    simpa [prefixWord, tailWord_5164616, baseEnd_5164616] using wordTrace_append hprefix tailTrace_5164616
  have hstable : (prefixWord ++ tailWord_5164616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164616).length < 2 ^ (prefixWord ++ tailWord_5164616).sum := by decide
  have hdescent : baseEnd_5164616 < baseStart_5164616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164620 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_5164620 : Nat := 118140960795 + 5164620 * 2 ^ 59
def prefixEnd_5164620 : Nat := 4983230072969 + 3 ^ 40 * 5164620 * 2
def baseEnd_5164620 : Nat := 2651932457823688634198351

theorem tailTrace_5164620 : CollatzResearch.WordTrace tailWord_5164620 prefixEnd_5164620 2651932457823688634198351 := by
  unfold tailWord_5164620
  simp only [CollatzResearch.WordTrace]
  refine ⟨94184583274735630858885657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125579444366314174478514209 94184583274735630858885657)
  ·
    refine ⟨70638437456051723144164243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94184583274735630858885657 70638437456051723144164243)
    ·
      refine ⟨105957656184077584716246365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70638437456051723144164243 105957656184077584716246365)
      ·
        refine ⟨39734121069029094268592387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105957656184077584716246365 39734121069029094268592387)
        ·
          refine ⟨59601181603543641402888581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39734121069029094268592387 59601181603543641402888581)
          ·
            refine ⟨11175221550664432763041609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59601181603543641402888581 11175221550664432763041609)
            ·
              refine ⟨8381416162998324572281207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11175221550664432763041609 8381416162998324572281207)
              ·
                refine ⟨12572124244497486858421811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381416162998324572281207 12572124244497486858421811)
                ·
                  refine ⟨18858186366746230287632717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12572124244497486858421811 18858186366746230287632717)
                  ·
                    refine ⟨7071819887529836357862269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18858186366746230287632717 7071819887529836357862269)
                    ·
                      refine ⟨2651932457823688634198351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7071819887529836357862269 2651932457823688634198351)
                      ·
                        rfl

theorem cell23_5164620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_5164620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164620 prefixEnd_5164620 := by exact prefixLift 5164620
  have htrace : WordTrace (prefixWord ++ tailWord_5164620) baseStart_5164620 baseEnd_5164620 := by
    simpa [prefixWord, tailWord_5164620, baseEnd_5164620] using wordTrace_append hprefix tailTrace_5164620
  have hstable : (prefixWord ++ tailWord_5164620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164620).length < 2 ^ (prefixWord ++ tailWord_5164620).sum := by decide
  have hdescent : baseEnd_5164620 < baseStart_5164620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164693 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_5164693 : Nat := 118140960795 + 5164693 * 2 ^ 59
def prefixEnd_5164693 : Nat := 4983230072969 + 3 ^ 40 * 5164693 * 2
def baseEnd_5164693 : Nat := 2651969941911466848585515

theorem tailTrace_5164693 : CollatzResearch.WordTrace tailWord_5164693 prefixEnd_5164693 2651969941911466848585515 := by
  unfold tailWord_5164693
  simp only [CollatzResearch.WordTrace]
  refine ⟨188371829078206795185178733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125581219385471196790119155 188371829078206795185178733)
  ·
    refine ⟨70639435904327548194442025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188371829078206795185178733 70639435904327548194442025)
    ·
      refine ⟨52979576928245661145831519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70639435904327548194442025 52979576928245661145831519)
      ·
        refine ⟨79469365392368491718747279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52979576928245661145831519 79469365392368491718747279)
        ·
          refine ⟨119204048088552737578120919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79469365392368491718747279 119204048088552737578120919)
          ·
            refine ⟨178806072132829106367181379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119204048088552737578120919 178806072132829106367181379)
            ·
              refine ⟨268209108199243659550772069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178806072132829106367181379 268209108199243659550772069)
              ·
                refine ⟨50289207787358186165769763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268209108199243659550772069 50289207787358186165769763)
                ·
                  refine ⟨75433811681037279248654645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50289207787358186165769763 75433811681037279248654645)
                  ·
                    refine ⟨7071919845097244929561373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75433811681037279248654645 7071919845097244929561373)
                    ·
                      refine ⟨2651969941911466848585515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7071919845097244929561373 2651969941911466848585515)
                      ·
                        rfl

theorem cell23_5164693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_5164693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164693 prefixEnd_5164693 := by exact prefixLift 5164693
  have htrace : WordTrace (prefixWord ++ tailWord_5164693) baseStart_5164693 baseEnd_5164693 := by
    simpa [prefixWord, tailWord_5164693, baseEnd_5164693] using wordTrace_append hprefix tailTrace_5164693
  have hstable : (prefixWord ++ tailWord_5164693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164693).length < 2 ^ (prefixWord ++ tailWord_5164693).sum := by decide
  have hdescent : baseEnd_5164693 < baseStart_5164693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164723 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5]
def baseStart_5164723 : Nat := 118140960795 + 5164723 * 2 ^ 59
def prefixEnd_5164723 : Nat := 4983230072969 + 3 ^ 40 * 5164723 * 2
def baseEnd_5164723 : Nat := 2651985346331101731210377

theorem tailTrace_5164723 : CollatzResearch.WordTrace tailWord_5164723 prefixEnd_5164723 2651985346331101731210377 := by
  unfold tailWord_5164723
  simp only [CollatzResearch.WordTrace]
  refine ⟨188372923268098110308770823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125581948845398740205847215 188372923268098110308770823)
  ·
    refine ⟨282559384902147165463156235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188372923268098110308770823 282559384902147165463156235)
    ·
      refine ⟨423839077353220748194734353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282559384902147165463156235 423839077353220748194734353)
      ·
        refine ⟨317879308014915561146050765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423839077353220748194734353 317879308014915561146050765)
        ·
          refine ⟨119204740505593335429769037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317879308014915561146050765 119204740505593335429769037)
          ·
            refine ⟨44701777689597500786163389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119204740505593335429769037 44701777689597500786163389)
            ·
              refine ⟨16763166633599062794811271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44701777689597500786163389 16763166633599062794811271)
              ·
                refine ⟨25144749950398594192216907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16763166633599062794811271 25144749950398594192216907)
                ·
                  refine ⟨37717124925597891288325361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25144749950398594192216907 37717124925597891288325361)
                  ·
                    refine ⟨28287843694198418466244021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37717124925597891288325361 28287843694198418466244021)
                    ·
                      refine ⟨2651985346331101731210377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28287843694198418466244021 2651985346331101731210377)
                      ·
                        rfl

theorem cell23_5164723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_5164723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164723 prefixEnd_5164723 := by exact prefixLift 5164723
  have htrace : WordTrace (prefixWord ++ tailWord_5164723) baseStart_5164723 baseEnd_5164723 := by
    simpa [prefixWord, tailWord_5164723, baseEnd_5164723] using wordTrace_append hprefix tailTrace_5164723
  have hstable : (prefixWord ++ tailWord_5164723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164723).length < 2 ^ (prefixWord ++ tailWord_5164723).sum := by decide
  have hdescent : baseEnd_5164723 < baseStart_5164723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164804 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_5164804 : Nat := 118140960795 + 5164804 * 2 ^ 59
def prefixEnd_5164804 : Nat := 4983230072969 + 3 ^ 40 * 5164804 * 2
def baseEnd_5164804 : Nat := 2652026938264115914297505

theorem tailTrace_5164804 : CollatzResearch.WordTrace tailWord_5164804 prefixEnd_5164804 2652026938264115914297505 := by
  unfold tailWord_5164804
  simp only [CollatzResearch.WordTrace]
  refine ⟨94187938790402330571234733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125583918387203107428312977 94187938790402330571234733)
  ·
    refine ⟨35320477046400873964213025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94187938790402330571234733 35320477046400873964213025)
    ·
      refine ⟨26490357784800655473159769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35320477046400873964213025 26490357784800655473159769)
      ·
        refine ⟨19867768338600491604869827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26490357784800655473159769 19867768338600491604869827)
        ·
          refine ⟨29801652507900737407304741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19867768338600491604869827 29801652507900737407304741)
          ·
            refine ⟨5587809845231388263869639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29801652507900737407304741 5587809845231388263869639)
            ·
              refine ⟨8381714767847082395804459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5587809845231388263869639 8381714767847082395804459)
              ·
                refine ⟨12572572151770623593706689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381714767847082395804459 12572572151770623593706689)
                ·
                  refine ⟨9429429113827967695280017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12572572151770623593706689 9429429113827967695280017)
                  ·
                    refine ⟨7072071835370975771460013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9429429113827967695280017 7072071835370975771460013)
                    ·
                      refine ⟨2652026938264115914297505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7072071835370975771460013 2652026938264115914297505)
                      ·
                        rfl

theorem cell23_5164804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_5164804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164804 prefixEnd_5164804 := by exact prefixLift 5164804
  have htrace : WordTrace (prefixWord ++ tailWord_5164804) baseStart_5164804 baseEnd_5164804 := by
    simpa [prefixWord, tailWord_5164804, baseEnd_5164804] using wordTrace_append hprefix tailTrace_5164804
  have hstable : (prefixWord ++ tailWord_5164804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164804).length < 2 ^ (prefixWord ++ tailWord_5164804).sum := by decide
  have hdescent : baseEnd_5164804 < baseStart_5164804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164834 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_5164834 : Nat := 118140960795 + 5164834 * 2 ^ 59
def prefixEnd_5164834 : Nat := 4983230072969 + 3 ^ 40 * 5164834 * 2
def baseEnd_5164834 : Nat := 2652042342683750796922367

theorem tailTrace_5164834 : CollatzResearch.WordTrace tailWord_5164834 prefixEnd_5164834 2652042342683750796922367 := by
  unfold tailWord_5164834
  simp only [CollatzResearch.WordTrace]
  refine ⟨47094242942673994066515389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125584647847130650844041037 47094242942673994066515389)
  ·
    refine ⟨17660341103502747774943271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47094242942673994066515389 17660341103502747774943271)
    ·
      refine ⟨26490511655254121662414907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17660341103502747774943271 26490511655254121662414907)
      ·
        refine ⟨39735767482881182493622361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26490511655254121662414907 39735767482881182493622361)
        ·
          refine ⟨29801825612160886870216771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39735767482881182493622361 29801825612160886870216771)
          ·
            refine ⟨44702738418241330305325157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29801825612160886870216771 44702738418241330305325157)
            ·
              refine ⟨8381763453420249432248467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44702738418241330305325157 8381763453420249432248467)
              ·
                refine ⟨12572645180130374148372701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381763453420249432248467 12572645180130374148372701)
                ·
                  refine ⟨4714741942548890305639763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12572645180130374148372701 4714741942548890305639763)
                  ·
                    refine ⟨7072112913823335458459645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4714741942548890305639763 7072112913823335458459645)
                    ·
                      refine ⟨2652042342683750796922367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7072112913823335458459645 2652042342683750796922367)
                      ·
                        rfl

theorem cell23_5164834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_5164834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164834 prefixEnd_5164834 := by exact prefixLift 5164834
  have htrace : WordTrace (prefixWord ++ tailWord_5164834) baseStart_5164834 baseEnd_5164834 := by
    simpa [prefixWord, tailWord_5164834, baseEnd_5164834] using wordTrace_append hprefix tailTrace_5164834
  have hstable : (prefixWord ++ tailWord_5164834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164834).length < 2 ^ (prefixWord ++ tailWord_5164834).sum := by decide
  have hdescent : baseEnd_5164834 < baseStart_5164834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164843 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5]
def baseStart_5164843 : Nat := 118140960795 + 5164843 * 2 ^ 59
def prefixEnd_5164843 : Nat := 4983230072969 + 3 ^ 40 * 5164843 * 2
def baseEnd_5164843 : Nat := 2652046964009641261709825

theorem tailTrace_5164843 : CollatzResearch.WordTrace tailWord_5164843 prefixEnd_5164843 2652046964009641261709825 := by
  unfold tailWord_5164843
  simp only [CollatzResearch.WordTrace]
  refine ⟨188377300027663370803139183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125584866685108913868759455 188377300027663370803139183)
  ·
    refine ⟨282565950041495056204708775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188377300027663370803139183 282565950041495056204708775)
    ·
      refine ⟨423848925062242584307063163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282565950041495056204708775 423848925062242584307063163)
      ·
        refine ⟨635773387593363876460594745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423848925062242584307063163 635773387593363876460594745)
        ·
          refine ⟨476830040695022907345446059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 635773387593363876460594745 476830040695022907345446059)
          ·
            refine ⟨715245061042534361018169089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476830040695022907345446059 715245061042534361018169089)
            ·
              refine ⟨536433795781900770763626817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715245061042534361018169089 536433795781900770763626817)
              ·
                refine ⟨402325346836425578072720113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536433795781900770763626817 402325346836425578072720113)
                ·
                  refine ⟨301744010127319183554540085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402325346836425578072720113 301744010127319183554540085)
                  ·
                    refine ⟨28288500949436173458238133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 301744010127319183554540085 28288500949436173458238133)
                    ·
                      refine ⟨2652046964009641261709825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28288500949436173458238133 2652046964009641261709825)
                      ·
                        rfl

theorem cell23_5164843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_5164843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164843 prefixEnd_5164843 := by exact prefixLift 5164843
  have htrace : WordTrace (prefixWord ++ tailWord_5164843) baseStart_5164843 baseEnd_5164843 := by
    simpa [prefixWord, tailWord_5164843, baseEnd_5164843] using wordTrace_append hprefix tailTrace_5164843
  have hstable : (prefixWord ++ tailWord_5164843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164843).length < 2 ^ (prefixWord ++ tailWord_5164843).sum := by decide
  have hdescent : baseEnd_5164843 < baseStart_5164843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164854 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_5164854 : Nat := 118140960795 + 5164854 * 2 ^ 59
def prefixEnd_5164854 : Nat := 4983230072969 + 3 ^ 40 * 5164854 * 2
def baseEnd_5164854 : Nat := 884017537432280239557425

theorem tailTrace_5164854 : CollatzResearch.WordTrace tailWord_5164854 prefixEnd_5164854 884017537432280239557425 := by
  unfold tailWord_5164854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773606326913969980111851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125585134153749013121193077 11773606326913969980111851)
  ·
    refine ⟨17660409490370954970167777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11773606326913969980111851 17660409490370954970167777)
    ·
      refine ⟨13245307117778216227625833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17660409490370954970167777 13245307117778216227625833)
      ·
        refine ⟨9933980338333662170719375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13245307117778216227625833 9933980338333662170719375)
        ·
          refine ⟨14900970507500493256079063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933980338333662170719375 14900970507500493256079063)
          ·
            refine ⟨22351455761250739884118595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14900970507500493256079063 22351455761250739884118595)
            ·
              refine ⟨33527183641876109826177893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22351455761250739884118595 33527183641876109826177893)
              ·
                refine ⟨6286346932851770592408355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33527183641876109826177893 6286346932851770592408355)
                ·
                  refine ⟨9429520399277655888612533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6286346932851770592408355 9429520399277655888612533)
                  ·
                    refine ⟨884017537432280239557425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9429520399277655888612533 884017537432280239557425)
                    ·
                      rfl

theorem cell23_5164854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_5164854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164854 prefixEnd_5164854 := by exact prefixLift 5164854
  have htrace : WordTrace (prefixWord ++ tailWord_5164854) baseStart_5164854 baseEnd_5164854 := by
    simpa [prefixWord, tailWord_5164854, baseEnd_5164854] using wordTrace_append hprefix tailTrace_5164854
  have hstable : (prefixWord ++ tailWord_5164854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164854).length < 2 ^ (prefixWord ++ tailWord_5164854).sum := by decide
  have hdescent : baseEnd_5164854 < baseStart_5164854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164940 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_5164940 : Nat := 118140960795 + 5164940 * 2 ^ 59
def prefixEnd_5164940 : Nat := 4983230072969 + 3 ^ 40 * 5164940 * 2
def baseEnd_5164940 : Nat := 884032257211042460732293

theorem tailTrace_5164940 : CollatzResearch.WordTrace tailWord_5164940 prefixEnd_5164940 884032257211042460732293 := by
  unfold tailWord_5164940
  simp only [CollatzResearch.WordTrace]
  refine ⟨94190418954155978184710137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125587225272207970912946849 94190418954155978184710137)
  ·
    refine ⟨70642814215616983638532603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94190418954155978184710137 70642814215616983638532603)
    ·
      refine ⟨105964221323425475457798905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70642814215616983638532603 105964221323425475457798905)
      ·
        refine ⟨79473165992569106593349179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105964221323425475457798905 79473165992569106593349179)
        ·
          refine ⟨119209748988853659890023769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79473165992569106593349179 119209748988853659890023769)
          ·
            refine ⟨89407311741640244917517827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119209748988853659890023769 89407311741640244917517827)
            ·
              refine ⟨134110967612460367376276741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89407311741640244917517827 134110967612460367376276741)
              ·
                refine ⟨25145806427336318883051889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134110967612460367376276741 25145806427336318883051889)
                ·
                  refine ⟨18859354820502239162288917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25145806427336318883051889 18859354820502239162288917)
                  ·
                    refine ⟨884032257211042460732293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18859354820502239162288917 884032257211042460732293)
                    ·
                      rfl

theorem cell23_5164940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_5164940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164940 prefixEnd_5164940 := by exact prefixLift 5164940
  have htrace : WordTrace (prefixWord ++ tailWord_5164940) baseStart_5164940 baseEnd_5164940 := by
    simpa [prefixWord, tailWord_5164940, baseEnd_5164940] using wordTrace_append hprefix tailTrace_5164940
  have hstable : (prefixWord ++ tailWord_5164940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164940).length < 2 ^ (prefixWord ++ tailWord_5164940).sum := by decide
  have hdescent : baseEnd_5164940 < baseStart_5164940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164957 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_5164957 : Nat := 118140960795 + 5164957 * 2 ^ 59
def prefixEnd_5164957 : Nat := 4983230072969 + 3 ^ 40 * 5164957 * 2
def baseEnd_5164957 : Nat := 884035166934751271894767

theorem tailTrace_5164957 : CollatzResearch.WordTrace tailWord_5164957 prefixEnd_5164957 884035166934751271894767 := by
  unfold tailWord_5164957
  simp only [CollatzResearch.WordTrace]
  refine ⟨188381457949250368272789125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125587638632833578848526083 188381457949250368272789125)
  ·
    refine ⟨35321523365484444051147961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188381457949250368272789125 35321523365484444051147961)
    ·
      refine ⟨26491142524113333038360971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35321523365484444051147961 26491142524113333038360971)
      ·
        refine ⟨39736713786169999557541457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26491142524113333038360971 39736713786169999557541457)
        ·
          refine ⟨29802535339627499668156093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39736713786169999557541457 29802535339627499668156093)
          ·
            refine ⟨11175950752360312375558535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29802535339627499668156093 11175950752360312375558535)
            ·
              refine ⟨16763926128540468563337803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11175950752360312375558535 16763926128540468563337803)
              ·
                refine ⟨25145889192810702845006705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16763926128540468563337803 25145889192810702845006705)
                ·
                  refine ⟨18859416894608027133755029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25145889192810702845006705 18859416894608027133755029)
                  ·
                    refine ⟨884035166934751271894767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18859416894608027133755029 884035166934751271894767)
                    ·
                      rfl

theorem cell23_5164957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_5164957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164957 prefixEnd_5164957 := by exact prefixLift 5164957
  have htrace : WordTrace (prefixWord ++ tailWord_5164957) baseStart_5164957 baseEnd_5164957 := by
    simpa [prefixWord, tailWord_5164957, baseEnd_5164957] using wordTrace_append hprefix tailTrace_5164957
  have hstable : (prefixWord ++ tailWord_5164957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164957).length < 2 ^ (prefixWord ++ tailWord_5164957).sum := by decide
  have hdescent : baseEnd_5164957 < baseStart_5164957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164958 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5164958 : Nat := 118140960795 + 5164958 * 2 ^ 59
def prefixEnd_5164958 : Nat := 4983230072969 + 3 ^ 40 * 5164958 * 2
def baseEnd_5164958 : Nat := 2652106014284908311771797

theorem tailTrace_5164958 : CollatzResearch.WordTrace tailWord_5164958 prefixEnd_5164958 2652106014284908311771797 := by
  unfold tailWord_5164958
  simp only [CollatzResearch.WordTrace]
  refine ⟨23547686802780843180446941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125587662948164496962383685 23547686802780843180446941)
  ·
    refine ⟨8830382551042816192667603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23547686802780843180446941 8830382551042816192667603)
    ·
      refine ⟨13245573826564224289001405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8830382551042816192667603 13245573826564224289001405)
      ·
        refine ⟨4967090184961584108375527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13245573826564224289001405 4967090184961584108375527)
        ·
          refine ⟨7450635277442376162563291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967090184961584108375527 7450635277442376162563291)
          ·
            refine ⟨11175952916163564243844937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450635277442376162563291 11175952916163564243844937)
            ·
              refine ⟨8381964687122673182883703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11175952916163564243844937 8381964687122673182883703)
              ·
                refine ⟨12572947030684009774325555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381964687122673182883703 12572947030684009774325555)
                ·
                  refine ⟨18859420546026014661488333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12572947030684009774325555 18859420546026014661488333)
                  ·
                    refine ⟨7072282704759755498058125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18859420546026014661488333 7072282704759755498058125)
                    ·
                      refine ⟨2652106014284908311771797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7072282704759755498058125 2652106014284908311771797)
                      ·
                        rfl

theorem cell23_5164958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5164958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164958 prefixEnd_5164958 := by exact prefixLift 5164958
  have htrace : WordTrace (prefixWord ++ tailWord_5164958) baseStart_5164958 baseEnd_5164958 := by
    simpa [prefixWord, tailWord_5164958, baseEnd_5164958] using wordTrace_append hprefix tailTrace_5164958
  have hstable : (prefixWord ++ tailWord_5164958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164958).length < 2 ^ (prefixWord ++ tailWord_5164958).sum := by decide
  have hdescent : baseEnd_5164958 < baseStart_5164958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164964 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_5164964 : Nat := 118140960795 + 5164964 * 2 ^ 59
def prefixEnd_5164964 : Nat := 4983230072969 + 3 ^ 40 * 5164964 * 2
def baseEnd_5164964 : Nat := 2652109095168835288296769

theorem tailTrace_5164964 : CollatzResearch.WordTrace tailWord_5164964 prefixEnd_5164964 2652109095168835288296769 := by
  unfold tailWord_5164964
  simp only [CollatzResearch.WordTrace]
  refine ⟨94190856630112504234146973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125587808840150005645529297 94190856630112504234146973)
  ·
    refine ⟨35321571236292189087805115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94190856630112504234146973 35321571236292189087805115)
    ·
      refine ⟨52982356854438283631707673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35321571236292189087805115 52982356854438283631707673)
      ·
        refine ⟨39736767640828712723780755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52982356854438283631707673 39736767640828712723780755)
        ·
          refine ⟨59605151461243069085671133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39736767640828712723780755 59605151461243069085671133)
          ·
            refine ⟨22351931797966150907126675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59605151461243069085671133 22351931797966150907126675)
            ·
              refine ⟨33527897696949226360690013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22351931797966150907126675 33527897696949226360690013)
              ·
                refine ⟨12572961636355959885258755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33527897696949226360690013 12572961636355959885258755)
                ·
                  refine ⟨18859442454533939827888133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12572961636355959885258755 18859442454533939827888133)
                  ·
                    refine ⟨3536145460225113717729025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18859442454533939827888133 3536145460225113717729025)
                    ·
                      refine ⟨2652109095168835288296769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536145460225113717729025 2652109095168835288296769)
                      ·
                        rfl

theorem cell23_5164964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_5164964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164964 prefixEnd_5164964 := by exact prefixLift 5164964
  have htrace : WordTrace (prefixWord ++ tailWord_5164964) baseStart_5164964 baseEnd_5164964 := by
    simpa [prefixWord, tailWord_5164964, baseEnd_5164964] using wordTrace_append hprefix tailTrace_5164964
  have hstable : (prefixWord ++ tailWord_5164964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164964).length < 2 ^ (prefixWord ++ tailWord_5164964).sum := by decide
  have hdescent : baseEnd_5164964 < baseStart_5164964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5164987 : List Nat := [1, 1, 1, 1, 1, 2, 2, 9, 5]
def baseStart_5164987 : Nat := 118140960795 + 5164987 * 2 ^ 59
def prefixEnd_5164987 : Nat := 4983230072969 + 3 ^ 40 * 5164987 * 2
def baseEnd_5164987 : Nat := 294680100580432077589907

theorem tailTrace_5164987 : CollatzResearch.WordTrace tailWord_5164987 prefixEnd_5164987 294680100580432077589907 := by
  unfold tailWord_5164987
  simp only [CollatzResearch.WordTrace]
  refine ⟨188382552139141683396381215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125588368092761122264254143 188382552139141683396381215)
  ·
    refine ⟨282573828208712525094571823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188382552139141683396381215 282573828208712525094571823)
    ·
      refine ⟨423860742313068787641857735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282573828208712525094571823 423860742313068787641857735)
      ·
        refine ⟨635791113469603181462786603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423860742313068787641857735 635791113469603181462786603)
        ·
          refine ⟨953686670204404772194179905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635791113469603181462786603 953686670204404772194179905)
          ·
            refine ⟨715265002653303579145634929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953686670204404772194179905 715265002653303579145634929)
            ·
              refine ⟨536448751989977684359226197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715265002653303579145634929 536448751989977684359226197)
              ·
                refine ⟨3143254406191275494292341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 536448751989977684359226197 3143254406191275494292341)
                ·
                  refine ⟨294680100580432077589907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3143254406191275494292341 294680100580432077589907)
                  ·
                    rfl

theorem cell23_5164987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 5].length) (baseStart_5164987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5164987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5164987 prefixEnd_5164987 := by exact prefixLift 5164987
  have htrace : WordTrace (prefixWord ++ tailWord_5164987) baseStart_5164987 baseEnd_5164987 := by
    simpa [prefixWord, tailWord_5164987, baseEnd_5164987] using wordTrace_append hprefix tailTrace_5164987
  have hstable : (prefixWord ++ tailWord_5164987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5164987).length < 2 ^ (prefixWord ++ tailWord_5164987).sum := by decide
  have hdescent : baseEnd_5164987 < baseStart_5164987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5164987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165004 : List Nat := [2, 2, 1, 4, 1, 2, 2, 4, 5]
def baseStart_5165004 : Nat := 118140960795 + 5165004 * 2 ^ 59
def prefixEnd_5165004 : Nat := 4983230072969 + 3 ^ 40 * 5165004 * 2
def baseEnd_5165004 : Nat := 294681070488335014644065

theorem tailTrace_5165004 : CollatzResearch.WordTrace tailWord_5165004 prefixEnd_5165004 294681070488335014644065 := by
  unfold tailWord_5165004
  simp only [CollatzResearch.WordTrace]
  refine ⟨94191586090040047649875033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125588781453386730199833377 94191586090040047649875033)
  ·
    refine ⟨70643689567530035737406275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94191586090040047649875033 70643689567530035737406275)
    ·
      refine ⟨105965534351295053606109413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70643689567530035737406275 105965534351295053606109413)
      ·
        refine ⟨19868537690867822551145515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105965534351295053606109413 19868537690867822551145515)
        ·
          refine ⟨29802806536301733826718273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19868537690867822551145515 29802806536301733826718273)
          ·
            refine ⟨22352104902226300370038705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29802806536301733826718273 22352104902226300370038705)
            ·
              refine ⟨16764078676669725277529029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22352104902226300370038705 16764078676669725277529029)
              ·
                refine ⟨3143264751875573489536693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16764078676669725277529029 3143264751875573489536693)
                ·
                  refine ⟨294681070488335014644065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3143264751875573489536693 294681070488335014644065)
                  ·
                    rfl

theorem cell23_5165004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_5165004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165004 prefixEnd_5165004 := by exact prefixLift 5165004
  have htrace : WordTrace (prefixWord ++ tailWord_5165004) baseStart_5165004 baseEnd_5165004 := by
    simpa [prefixWord, tailWord_5165004, baseEnd_5165004] using wordTrace_append hprefix tailTrace_5165004
  have hstable : (prefixWord ++ tailWord_5165004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165004).length < 2 ^ (prefixWord ++ tailWord_5165004).sum := by decide
  have hdescent : baseEnd_5165004 < baseStart_5165004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165114 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2]
def baseStart_5165114 : Nat := 118140960795 + 5165114 * 2 ^ 59
def prefixEnd_5165114 : Nat := 4983230072969 + 3 ^ 40 * 5165114 * 2
def baseEnd_5165114 : Nat := 2652186117267009701421079

theorem tailTrace_5165114 : CollatzResearch.WordTrace tailWord_5165114 prefixEnd_5165114 2652186117267009701421079 := by
  unfold tailWord_5165114
  simp only [CollatzResearch.WordTrace]
  refine ⟨47096796052420396021563599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125591456139787722724169597 47096796052420396021563599)
  ·
    refine ⟨70645194078630594032345399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47096796052420396021563599 70645194078630594032345399)
    ·
      refine ⟨105967791117945891048518099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70645194078630594032345399 105967791117945891048518099)
      ·
        refine ⟨158951686676918836572777149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105967791117945891048518099 158951686676918836572777149)
        ·
          refine ⟨59606882503844563714791431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158951686676918836572777149 59606882503844563714791431)
          ·
            refine ⟨89410323755766845572187147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59606882503844563714791431 89410323755766845572187147)
            ·
              refine ⟨134115485633650268358280721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89410323755766845572187147 134115485633650268358280721)
              ·
                refine ⟨100586614225237701268710541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134115485633650268358280721 100586614225237701268710541)
                ·
                  refine ⟨37719980334464137975766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100586614225237701268710541 37719980334464137975766453)
                  ·
                    refine ⟨3536248156356012935228105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37719980334464137975766453 3536248156356012935228105)
                    ·
                      refine ⟨2652186117267009701421079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536248156356012935228105 2652186117267009701421079)
                      ·
                        rfl

theorem cell23_5165114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_5165114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165114 prefixEnd_5165114 := by exact prefixLift 5165114
  have htrace : WordTrace (prefixWord ++ tailWord_5165114) baseStart_5165114 baseEnd_5165114 := by
    simpa [prefixWord, tailWord_5165114, baseEnd_5165114] using wordTrace_append hprefix tailTrace_5165114
  have hstable : (prefixWord ++ tailWord_5165114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165114).length < 2 ^ (prefixWord ++ tailWord_5165114).sum := by decide
  have hdescent : baseEnd_5165114 < baseStart_5165114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165138 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_5165138 : Nat := 118140960795 + 5165138 * 2 ^ 59
def prefixEnd_5165138 : Nat := 4983230072969 + 3 ^ 40 * 5165138 * 2
def baseEnd_5165138 : Nat := 2652198440802717607520969

theorem tailTrace_5165138 : CollatzResearch.WordTrace tailWord_5165138 prefixEnd_5165138 2652198440802717607520969 := by
  unfold tailWord_5165138
  simp only [CollatzResearch.WordTrace]
  refine ⟨47097014890398659046282017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125592039707729757456752045 47097014890398659046282017)
  ·
    refine ⟨35322761167798994284711513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47097014890398659046282017 35322761167798994284711513)
    ·
      refine ⟨26492070875849245713533635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35322761167798994284711513 26492070875849245713533635)
      ·
        refine ⟨39738106313773868570300453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26492070875849245713533635 39738106313773868570300453)
        ·
          refine ⟨7450894933832600356931335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39738106313773868570300453 7450894933832600356931335)
          ·
            refine ⟨11176342400748900535397003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450894933832600356931335 11176342400748900535397003)
            ·
              refine ⟨16764513601123350803095505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11176342400748900535397003 16764513601123350803095505)
              ·
                refine ⟨12573385200842513102321629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16764513601123350803095505 12573385200842513102321629)
                ·
                  refine ⟨4715019450315942413370611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12573385200842513102321629 4715019450315942413370611)
                  ·
                    refine ⟨7072529175473913620055917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4715019450315942413370611 7072529175473913620055917)
                    ·
                      refine ⟨2652198440802717607520969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7072529175473913620055917 2652198440802717607520969)
                      ·
                        rfl

theorem cell23_5165138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_5165138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165138 prefixEnd_5165138 := by exact prefixLift 5165138
  have htrace : WordTrace (prefixWord ++ tailWord_5165138) baseStart_5165138 baseEnd_5165138 := by
    simpa [prefixWord, tailWord_5165138, baseEnd_5165138] using wordTrace_append hprefix tailTrace_5165138
  have hstable : (prefixWord ++ tailWord_5165138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165138).length < 2 ^ (prefixWord ++ tailWord_5165138).sum := by decide
  have hdescent : baseEnd_5165138 < baseStart_5165138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165144 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_5165144 : Nat := 118140960795 + 5165144 * 2 ^ 59
def prefixEnd_5165144 : Nat := 4983230072969 + 3 ^ 40 * 5165144 * 2
def baseEnd_5165144 : Nat := 2652201521686644584045941

theorem tailTrace_5165144 : CollatzResearch.WordTrace tailWord_5165144 prefixEnd_5165144 2652201521686644584045941 := by
  unfold tailWord_5165144
  simp only [CollatzResearch.WordTrace]
  refine ⟨94194139199786449604923243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125592185599715266139897657 94194139199786449604923243)
  ·
    refine ⟨141291208799679674407384865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94194139199786449604923243 141291208799679674407384865)
    ·
      refine ⟨105968406599759755805538649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141291208799679674407384865 105968406599759755805538649)
      ·
        refine ⟨79476304949819816854153987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105968406599759755805538649 79476304949819816854153987)
        ·
          refine ⟨119214457424729725281230981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79476304949819816854153987 119214457424729725281230981)
          ·
            refine ⟨22352710767136823490230809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119214457424729725281230981 22352710767136823490230809)
            ·
              refine ⟨16764533075352617617673107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22352710767136823490230809 16764533075352617617673107)
              ·
                refine ⟨25146799613028926426509661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16764533075352617617673107 25146799613028926426509661)
                ·
                  refine ⟨9430049854885847409941123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25146799613028926426509661 9430049854885847409941123)
                  ·
                    refine ⟨14145074782328771114911685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9430049854885847409941123 14145074782328771114911685)
                    ·
                      refine ⟨2652201521686644584045941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14145074782328771114911685 2652201521686644584045941)
                      ·
                        rfl

theorem cell23_5165144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_5165144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165144 prefixEnd_5165144 := by exact prefixLift 5165144
  have htrace : WordTrace (prefixWord ++ tailWord_5165144) baseStart_5165144 baseEnd_5165144 := by
    simpa [prefixWord, tailWord_5165144, baseEnd_5165144] using wordTrace_append hprefix tailTrace_5165144
  have hstable : (prefixWord ++ tailWord_5165144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165144).length < 2 ^ (prefixWord ++ tailWord_5165144).sum := by decide
  have hdescent : baseEnd_5165144 < baseStart_5165144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165148 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_5165148 : Nat := 118140960795 + 5165148 * 2 ^ 59
def prefixEnd_5165148 : Nat := 4983230072969 + 3 ^ 40 * 5165148 * 2
def baseEnd_5165148 : Nat := 2652203575609262568395923

theorem tailTrace_5165148 : CollatzResearch.WordTrace tailWord_5165148 prefixEnd_5165148 2652203575609262568395923 := by
  unfold tailWord_5165148
  simp only [CollatzResearch.WordTrace]
  refine ⟨94194212145779203946496049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125592282861038938595328065 94194212145779203946496049)
  ·
    refine ⟨70645659109334402959872037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94194212145779203946496049 70645659109334402959872037)
    ·
      refine ⟨13246061083000200554976007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70645659109334402959872037 13246061083000200554976007)
      ·
        refine ⟨19869091624500300832464011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13246061083000200554976007 19869091624500300832464011)
        ·
          refine ⟨29803637436750451248696017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19869091624500300832464011 29803637436750451248696017)
          ·
            refine ⟨22352728077562838436522013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29803637436750451248696017 22352728077562838436522013)
            ·
              refine ⟨8382273029086064413695755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22352728077562838436522013 8382273029086064413695755)
              ·
                refine ⟨12573409543629096620543633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8382273029086064413695755 12573409543629096620543633)
                ·
                  refine ⟨9430057157721822465407725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12573409543629096620543633 9430057157721822465407725)
                  ·
                    refine ⟨3536271434145683424527897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9430057157721822465407725 3536271434145683424527897)
                    ·
                      refine ⟨2652203575609262568395923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536271434145683424527897 2652203575609262568395923)
                      ·
                        rfl

theorem cell23_5165148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_5165148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165148 prefixEnd_5165148 := by exact prefixLift 5165148
  have htrace : WordTrace (prefixWord ++ tailWord_5165148) baseStart_5165148 baseEnd_5165148 := by
    simpa [prefixWord, tailWord_5165148, baseEnd_5165148] using wordTrace_append hprefix tailTrace_5165148
  have hstable : (prefixWord ++ tailWord_5165148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165148).length < 2 ^ (prefixWord ++ tailWord_5165148).sum := by decide
  have hdescent : baseEnd_5165148 < baseStart_5165148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165161 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 5, 2, 2]
def baseStart_5165161 : Nat := 118140960795 + 5165161 * 2 ^ 59
def prefixEnd_5165161 : Nat := 4983230072969 + 3 ^ 40 * 5165161 * 2
def baseEnd_5165161 : Nat := 2652210250857771017533363

theorem tailTrace_5165161 : CollatzResearch.WordTrace tailWord_5165161 prefixEnd_5165161 2652210250857771017533363 := by
  unfold tailWord_5165161
  simp only [CollatzResearch.WordTrace]
  refine ⟨188388898440511311113215337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125592598960340874075476891 188388898440511311113215337)
  ·
    refine ⟨141291673830383483334911503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188388898440511311113215337 141291673830383483334911503)
    ·
      refine ⟨211937510745575225002367255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141291673830383483334911503 211937510745575225002367255)
      ·
        refine ⟨317906266118362837503550883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211937510745575225002367255 317906266118362837503550883)
        ·
          refine ⟨476859399177544256255326325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317906266118362837503550883 476859399177544256255326325)
          ·
            refine ⟨44705568672894774023936843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 476859399177544256255326325 44705568672894774023936843)
            ·
              refine ⟨67058353009342161035905265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44705568672894774023936843 67058353009342161035905265)
              ·
                refine ⟨50293764757006620776928949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67058353009342161035905265 50293764757006620776928949)
                ·
                  refine ⟨4715040445969370697837089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50293764757006620776928949 4715040445969370697837089)
                  ·
                    refine ⟨3536280334477028023377817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715040445969370697837089 3536280334477028023377817)
                    ·
                      refine ⟨2652210250857771017533363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536280334477028023377817 2652210250857771017533363)
                      ·
                        rfl

theorem cell23_5165161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 2, 2].length) (baseStart_5165161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165161 prefixEnd_5165161 := by exact prefixLift 5165161
  have htrace : WordTrace (prefixWord ++ tailWord_5165161) baseStart_5165161 baseEnd_5165161 := by
    simpa [prefixWord, tailWord_5165161, baseEnd_5165161] using wordTrace_append hprefix tailTrace_5165161
  have hstable : (prefixWord ++ tailWord_5165161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165161).length < 2 ^ (prefixWord ++ tailWord_5165161).sum := by decide
  have hdescent : baseEnd_5165161 < baseStart_5165161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165167 : List Nat := [1, 1, 2, 1, 3, 5, 10]
def baseStart_5165167 : Nat := 118140960795 + 5165167 * 2 ^ 59
def prefixEnd_5165167 : Nat := 4983230072969 + 3 ^ 40 * 5165167 * 2
def baseEnd_5165167 : Nat := 32743374465946888815535

theorem tailTrace_5165167 : CollatzResearch.WordTrace tailWord_5165167 prefixEnd_5165167 32743374465946888815535 := by
  unfold tailWord_5165167
  simp only [CollatzResearch.WordTrace]
  refine ⟨188389117278489574137933755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125592744852326382758622503 188389117278489574137933755)
  ·
    refine ⟨282583675917734361206900633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188389117278489574137933755 282583675917734361206900633)
    ·
      refine ⟨211937756938300770905175475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282583675917734361206900633 211937756938300770905175475)
      ·
        refine ⟨317906635407451156357763213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211937756938300770905175475 317906635407451156357763213)
        ·
          refine ⟨119214988277794183634161205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317906635407451156357763213 119214988277794183634161205)
          ·
            refine ⟨11176405151043204715702613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119214988277794183634161205 11176405151043204715702613)
            ·
              refine ⟨32743374465946888815535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11176405151043204715702613 32743374465946888815535)
              ·
                rfl

theorem cell23_5165167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 10].length) (baseStart_5165167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165167 prefixEnd_5165167 := by exact prefixLift 5165167
  have htrace : WordTrace (prefixWord ++ tailWord_5165167) baseStart_5165167 baseEnd_5165167 := by
    simpa [prefixWord, tailWord_5165167, baseEnd_5165167] using wordTrace_append hprefix tailTrace_5165167
  have hstable : (prefixWord ++ tailWord_5165167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165167).length < 2 ^ (prefixWord ++ tailWord_5165167).sum := by decide
  have hdescent : baseEnd_5165167 < baseStart_5165167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165188 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_5165188 : Nat := 118140960795 + 5165188 * 2 ^ 59
def prefixEnd_5165188 : Nat := 4983230072969 + 3 ^ 40 * 5165188 * 2
def baseEnd_5165188 : Nat := 884074704945147470631913

theorem tailTrace_5165188 : CollatzResearch.WordTrace tailWord_5165188 prefixEnd_5165188 884074704945147470631913 := by
  unfold tailWord_5165188
  simp only [CollatzResearch.WordTrace]
  refine ⟨94194941605706747362224109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125593255474275663149632145 94194941605706747362224109)
  ·
    refine ⟨35323103102140030260834041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94194941605706747362224109 35323103102140030260834041)
    ·
      refine ⟨26492327326605022695625531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35323103102140030260834041 26492327326605022695625531)
      ·
        refine ⟨39738490989907534043438297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26492327326605022695625531 39738490989907534043438297)
        ·
          refine ⟨29803868242430650532578723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39738490989907534043438297 29803868242430650532578723)
          ·
            refine ⟨44705802363645975798868085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29803868242430650532578723 44705802363645975798868085)
            ·
              refine ⟨4191168971591810231143883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44705802363645975798868085 4191168971591810231143883)
              ·
                refine ⟨6286753457387715346715825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191168971591810231143883 6286753457387715346715825)
                ·
                  refine ⟨4715065093040786510036869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6286753457387715346715825 4715065093040786510036869)
                  ·
                    refine ⟨884074704945147470631913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4715065093040786510036869 884074704945147470631913)
                    ·
                      rfl

theorem cell23_5165188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_5165188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165188 prefixEnd_5165188 := by exact prefixLift 5165188
  have htrace : WordTrace (prefixWord ++ tailWord_5165188) baseStart_5165188 baseEnd_5165188 := by
    simpa [prefixWord, tailWord_5165188, baseEnd_5165188] using wordTrace_append hprefix tailTrace_5165188
  have hstable : (prefixWord ++ tailWord_5165188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165188).length < 2 ^ (prefixWord ++ tailWord_5165188).sum := by decide
  have hdescent : baseEnd_5165188 < baseStart_5165188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165229 : List Nat := [1, 5, 2, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_5165229 : Nat := 118140960795 + 5165229 * 2 ^ 59
def prefixEnd_5165229 : Nat := 4983230072969 + 3 ^ 40 * 5165229 * 2
def baseEnd_5165229 : Nat := 2652245167542276751483051

theorem tailTrace_5165229 : CollatzResearch.WordTrace tailWord_5165229 prefixEnd_5165229 2652245167542276751483051 := by
  unfold tailWord_5165229
  simp only [CollatzResearch.WordTrace]
  refine ⟨188391378604264958726690741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125594252402843305817793827 188391378604264958726690741)
  ·
    refine ⟨17661691744149839880627257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188391378604264958726690741 17661691744149839880627257)
    ·
      refine ⟨13246268808112379910470443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17661691744149839880627257 13246268808112379910470443)
      ·
        refine ⟨19869403212168569865705665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13246268808112379910470443 19869403212168569865705665)
        ·
          refine ⟨14902052409126427399279249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19869403212168569865705665 14902052409126427399279249)
          ·
            refine ⟨11176539306844820549459437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14902052409126427399279249 11176539306844820549459437)
            ·
              refine ⟨4191202240066807706047289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11176539306844820549459437 4191202240066807706047289)
              ·
                refine ⟨3143401680050105779535467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4191202240066807706047289 3143401680050105779535467)
                ·
                  refine ⟨4715102520075158669303201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143401680050105779535467 4715102520075158669303201)
                  ·
                    refine ⟨3536326890056369001977401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715102520075158669303201 3536326890056369001977401)
                    ·
                      refine ⟨2652245167542276751483051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536326890056369001977401 2652245167542276751483051)
                      ·
                        rfl

theorem cell23_5165229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_5165229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165229 prefixEnd_5165229 := by exact prefixLift 5165229
  have htrace : WordTrace (prefixWord ++ tailWord_5165229) baseStart_5165229 baseEnd_5165229 := by
    simpa [prefixWord, tailWord_5165229, baseEnd_5165229] using wordTrace_append hprefix tailTrace_5165229
  have hstable : (prefixWord ++ tailWord_5165229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165229).length < 2 ^ (prefixWord ++ tailWord_5165229).sum := by decide
  have hdescent : baseEnd_5165229 < baseStart_5165229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165234 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_5165234 : Nat := 118140960795 + 5165234 * 2 ^ 59
def prefixEnd_5165234 : Nat := 4983230072969 + 3 ^ 40 * 5165234 * 2
def baseEnd_5165234 : Nat := 2652247734945549231920527

theorem tailTrace_5165234 : CollatzResearch.WordTrace tailWord_5165234 prefixEnd_5165234 2652247734945549231920527 := by
  unfold tailWord_5165234
  simp only [CollatzResearch.WordTrace]
  refine ⟨47097890242311711145155689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125594373979497896387081837 47097890242311711145155689)
  ·
    refine ⟨35323417681733783358866767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47097890242311711145155689 35323417681733783358866767)
    ·
      refine ⟨52985126522600675038300151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35323417681733783358866767 52985126522600675038300151)
      ·
        refine ⟨79477689783901012557450227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52985126522600675038300151 79477689783901012557450227)
        ·
          refine ⟨119216534675851518836175341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79477689783901012557450227 119216534675851518836175341)
          ·
            refine ⟨44706200503444319563565753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119216534675851518836175341 44706200503444319563565753)
            ·
              refine ⟨33529650377583239672674315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44706200503444319563565753 33529650377583239672674315)
              ·
                refine ⟨50294475566374859509011473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33529650377583239672674315 50294475566374859509011473)
                ·
                  refine ⟨37720856674781144631758605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50294475566374859509011473 37720856674781144631758605)
                  ·
                    refine ⟨14145321253042929236909477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37720856674781144631758605 14145321253042929236909477)
                    ·
                      refine ⟨2652247734945549231920527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14145321253042929236909477 2652247734945549231920527)
                      ·
                        rfl

theorem cell23_5165234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_5165234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165234 prefixEnd_5165234 := by exact prefixLift 5165234
  have htrace : WordTrace (prefixWord ++ tailWord_5165234) baseStart_5165234 baseEnd_5165234 := by
    simpa [prefixWord, tailWord_5165234, baseEnd_5165234] using wordTrace_append hprefix tailTrace_5165234
  have hstable : (prefixWord ++ tailWord_5165234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165234).length < 2 ^ (prefixWord ++ tailWord_5165234).sum := by decide
  have hdescent : baseEnd_5165234 < baseStart_5165234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165285 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 2, 2, 2]
def baseStart_5165285 : Nat := 118140960795 + 5165285 * 2 ^ 59
def prefixEnd_5165285 : Nat := 4983230072969 + 3 ^ 40 * 5165285 * 2
def baseEnd_5165285 : Nat := 2652273922458928532382793

theorem tailTrace_5165285 : CollatzResearch.WordTrace tailWord_5165285 prefixEnd_5165285 2652273922458928532382793 := by
  unfold tailWord_5165285
  simp only [CollatzResearch.WordTrace]
  refine ⟨188393421092062080290729309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125595614061374720193819539 188393421092062080290729309)
  ·
    refine ⟨70647532909523280109023491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188393421092062080290729309 70647532909523280109023491)
    ·
      refine ⟨105971299364284920163535237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70647532909523280109023491 105971299364284920163535237)
      ·
        refine ⟨19869618630803422530662857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105971299364284920163535237 19869618630803422530662857)
        ·
          refine ⟨14902213973102566897997143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19869618630803422530662857 14902213973102566897997143)
          ·
            refine ⟨22353320959653850346995715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14902213973102566897997143 22353320959653850346995715)
            ·
              refine ⟨33529981439480775520493573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22353320959653850346995715 33529981439480775520493573)
              ·
                refine ⟨6286871519902645410092545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33529981439480775520493573 6286871519902645410092545)
                ·
                  refine ⟨4715153639926984057569409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6286871519902645410092545 4715153639926984057569409)
                  ·
                    refine ⟨3536365229945238043177057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715153639926984057569409 3536365229945238043177057)
                    ·
                      refine ⟨2652273922458928532382793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536365229945238043177057 2652273922458928532382793)
                      ·
                        rfl

theorem cell23_5165285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_5165285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165285 prefixEnd_5165285 := by exact prefixLift 5165285
  have htrace : WordTrace (prefixWord ++ tailWord_5165285) baseStart_5165285 baseEnd_5165285 := by
    simpa [prefixWord, tailWord_5165285, baseEnd_5165285] using wordTrace_append hprefix tailTrace_5165285
  have hstable : (prefixWord ++ tailWord_5165285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165285).length < 2 ^ (prefixWord ++ tailWord_5165285).sum := by decide
  have hdescent : baseEnd_5165285 < baseStart_5165285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165291 : List Nat := [1, 1, 1, 1, 2, 5, 3, 4, 5]
def baseStart_5165291 : Nat := 118140960795 + 5165291 * 2 ^ 59
def prefixEnd_5165291 : Nat := 4983230072969 + 3 ^ 40 * 5165291 * 2
def baseEnd_5165291 : Nat := 294697444815872834323085

theorem tailTrace_5165291 : CollatzResearch.WordTrace tailWord_5165291 prefixEnd_5165291 294697444815872834323085 := by
  unfold tailWord_5165291
  simp only [CollatzResearch.WordTrace]
  refine ⟨188393639930040343315447727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125595759953360228876965151 188393639930040343315447727)
  ·
    refine ⟨282590459895060514973171591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188393639930040343315447727 282590459895060514973171591)
    ·
      refine ⟨423885689842590772459757387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282590459895060514973171591 423885689842590772459757387)
      ·
        refine ⟨635828534763886158689636081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423885689842590772459757387 635828534763886158689636081)
        ·
          refine ⟨476871401072914619017227061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 635828534763886158689636081 476871401072914619017227061)
          ·
            refine ⟨44706693850585745532865037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 476871401072914619017227061 44706693850585745532865037)
            ·
              refine ⟨16765010193969654574824389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44706693850585745532865037 16765010193969654574824389)
              ·
                refine ⟨3143439411369310232779573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16765010193969654574824389 3143439411369310232779573)
                ·
                  refine ⟨294697444815872834323085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3143439411369310232779573 294697444815872834323085)
                  ·
                    rfl

theorem cell23_5165291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 5].length) (baseStart_5165291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165291 prefixEnd_5165291 := by exact prefixLift 5165291
  have htrace : WordTrace (prefixWord ++ tailWord_5165291) baseStart_5165291 baseEnd_5165291 := by
    simpa [prefixWord, tailWord_5165291, baseEnd_5165291] using wordTrace_append hprefix tailTrace_5165291
  have hstable : (prefixWord ++ tailWord_5165291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165291).length < 2 ^ (prefixWord ++ tailWord_5165291).sum := by decide
  have hdescent : baseEnd_5165291 < baseStart_5165291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165294 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_5165294 : Nat := 118140960795 + 5165294 * 2 ^ 59
def prefixEnd_5165294 : Nat := 4983230072969 + 3 ^ 40 * 5165294 * 2
def baseEnd_5165294 : Nat := 2652278543784818997170251

theorem tailTrace_5165294 : CollatzResearch.WordTrace tailWord_5165294 prefixEnd_5165294 2652278543784818997170251 := by
  unfold tailWord_5165294
  simp only [CollatzResearch.WordTrace]
  refine ⟨23549218668628684353475867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125595832899352983218537957 23549218668628684353475867)
  ·
    refine ⟨35323828002943026530213801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23549218668628684353475867 35323828002943026530213801)
    ·
      refine ⟨26492871002207269897660351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35323828002943026530213801 26492871002207269897660351)
      ·
        refine ⟨39739306503310904846490527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26492871002207269897660351 39739306503310904846490527)
        ·
          refine ⟨59608959754966357269735791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39739306503310904846490527 59608959754966357269735791)
          ·
            refine ⟨89413439632449535904603687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59608959754966357269735791 89413439632449535904603687)
            ·
              refine ⟨134120159448674303856905531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89413439632449535904603687 134120159448674303856905531)
              ·
                refine ⟨201180239173011455785358297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134120159448674303856905531 201180239173011455785358297)
                ·
                  refine ⟨150885179379758591839018723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201180239173011455785358297 150885179379758591839018723)
                  ·
                    refine ⟨226327769069637887758528085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150885179379758591839018723 226327769069637887758528085)
                    ·
                      refine ⟨2652278543784818997170251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226327769069637887758528085 2652278543784818997170251)
                      ·
                        rfl

theorem cell23_5165294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_5165294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165294 prefixEnd_5165294 := by exact prefixLift 5165294
  have htrace : WordTrace (prefixWord ++ tailWord_5165294) baseStart_5165294 baseEnd_5165294 := by
    simpa [prefixWord, tailWord_5165294, baseEnd_5165294] using wordTrace_append hprefix tailTrace_5165294
  have hstable : (prefixWord ++ tailWord_5165294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165294).length < 2 ^ (prefixWord ++ tailWord_5165294).sum := by decide
  have hdescent : baseEnd_5165294 < baseStart_5165294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165304 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 4, 5]
def baseStart_5165304 : Nat := 118140960795 + 5165304 * 2 ^ 59
def prefixEnd_5165304 : Nat := 4983230072969 + 3 ^ 40 * 5165304 * 2
def baseEnd_5165304 : Nat := 884094559530454652681735

theorem tailTrace_5165304 : CollatzResearch.WordTrace tailWord_5165304 prefixEnd_5165304 884094559530454652681735 := by
  unfold tailWord_5165304
  simp only [CollatzResearch.WordTrace]
  refine ⟨94197057039496623267835483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125596076052662164357113977 94197057039496623267835483)
  ·
    refine ⟨141295585559244934901753225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94197057039496623267835483 141295585559244934901753225)
    ·
      refine ⟨105971689169433701176314919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141295585559244934901753225 105971689169433701176314919)
      ·
        refine ⟨158957533754150551764472379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105971689169433701176314919 158957533754150551764472379)
        ·
          refine ⟨238436300631225827646708569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158957533754150551764472379 238436300631225827646708569)
          ·
            refine ⟨178827225473419370735031427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238436300631225827646708569 178827225473419370735031427)
            ·
              refine ⟨268240838210129056102547141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178827225473419370735031427 268240838210129056102547141)
              ·
                refine ⟨50295157164399198019227589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268240838210129056102547141 50295157164399198019227589)
                ·
                  refine ⟨9430341968324849628605173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50295157164399198019227589 9430341968324849628605173)
                  ·
                    refine ⟨884094559530454652681735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9430341968324849628605173 884094559530454652681735)
                    ·
                      rfl

theorem cell23_5165304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_5165304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165304 prefixEnd_5165304 := by exact prefixLift 5165304
  have htrace : WordTrace (prefixWord ++ tailWord_5165304) baseStart_5165304 baseEnd_5165304 := by
    simpa [prefixWord, tailWord_5165304, baseEnd_5165304] using wordTrace_append hprefix tailTrace_5165304
  have hstable : (prefixWord ++ tailWord_5165304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165304).length < 2 ^ (prefixWord ++ tailWord_5165304).sum := by decide
  have hdescent : baseEnd_5165304 < baseStart_5165304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165311 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 2, 5, 2]
def baseStart_5165311 : Nat := 118140960795 + 5165311 * 2 ^ 59
def prefixEnd_5165311 : Nat := 4983230072969 + 3 ^ 40 * 5165311 * 2
def baseEnd_5165311 : Nat := 2652287272955945430657673

theorem tailTrace_5165311 : CollatzResearch.WordTrace tailWord_5165311 prefixEnd_5165311 2652287272955945430657673 := by
  unfold tailWord_5165311
  simp only [CollatzResearch.WordTrace]
  refine ⟨188394369389967886731175787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125596246259978591154117191 188394369389967886731175787)
  ·
    refine ⟨282591554084951830096763681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188394369389967886731175787 282591554084951830096763681)
    ·
      refine ⟨211943665563713872572572761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282591554084951830096763681 211943665563713872572572761)
      ·
        refine ⟨158957749172785404429429571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211943665563713872572572761 158957749172785404429429571)
        ·
          refine ⟨238436623759178106644144357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158957749172785404429429571 238436623759178106644144357)
          ·
            refine ⟨44706866954845894995777067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238436623759178106644144357 44706866954845894995777067)
            ·
              refine ⟨67060300432268842493665601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44706866954845894995777067 67060300432268842493665601)
              ·
                refine ⟨50295225324201631870249201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67060300432268842493665601 50295225324201631870249201)
                ·
                  refine ⟨37721418993151223902686901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50295225324201631870249201 37721418993151223902686901)
                  ·
                    refine ⟨3536383030607927240876897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37721418993151223902686901 3536383030607927240876897)
                    ·
                      refine ⟨2652287272955945430657673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536383030607927240876897 2652287272955945430657673)
                      ·
                        rfl

theorem cell23_5165311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_5165311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165311 prefixEnd_5165311 := by exact prefixLift 5165311
  have htrace : WordTrace (prefixWord ++ tailWord_5165311) baseStart_5165311 baseEnd_5165311 := by
    simpa [prefixWord, tailWord_5165311, baseEnd_5165311] using wordTrace_append hprefix tailTrace_5165311
  have hstable : (prefixWord ++ tailWord_5165311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165311).length < 2 ^ (prefixWord ++ tailWord_5165311).sum := by decide
  have hdescent : baseEnd_5165311 < baseStart_5165311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165321 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 2, 5]
def baseStart_5165321 : Nat := 118140960795 + 5165321 * 2 ^ 59
def prefixEnd_5165321 : Nat := 4983230072969 + 3 ^ 40 * 5165321 * 2
def baseEnd_5165321 : Nat := 884097469254163463844209

theorem tailTrace_5165321 : CollatzResearch.WordTrace tailWord_5165321 prefixEnd_5165321 884097469254163463844209 := by
  unfold tailWord_5165321
  simp only [CollatzResearch.WordTrace]
  refine ⟨188394734119931658439039817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125596489413287772292693211 188394734119931658439039817)
  ·
    refine ⟨141296050589948743829279863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188394734119931658439039817 141296050589948743829279863)
    ·
      refine ⟨211944075884923115743919795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141296050589948743829279863 211944075884923115743919795)
      ·
        refine ⟨317916113827384673615879693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211944075884923115743919795 317916113827384673615879693)
        ·
          refine ⟨119218542685269252605954885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317916113827384673615879693 119218542685269252605954885)
          ·
            refine ⟨22353476753487984863616541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119218542685269252605954885 22353476753487984863616541)
            ·
              refine ⟨8382553782557994323856203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22353476753487984863616541 8382553782557994323856203)
              ·
                refine ⟨12573830673836991485784305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8382553782557994323856203 12573830673836991485784305)
                ·
                  refine ⟨9430373005377743614338229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12573830673836991485784305 9430373005377743614338229)
                  ·
                    refine ⟨884097469254163463844209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9430373005377743614338229 884097469254163463844209)
                    ·
                      rfl

theorem cell23_5165321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_5165321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165321 prefixEnd_5165321 := by exact prefixLift 5165321
  have htrace : WordTrace (prefixWord ++ tailWord_5165321) baseStart_5165321 baseEnd_5165321 := by
    simpa [prefixWord, tailWord_5165321, baseEnd_5165321] using wordTrace_append hprefix tailTrace_5165321
  have hstable : (prefixWord ++ tailWord_5165321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165321).length < 2 ^ (prefixWord ++ tailWord_5165321).sum := by decide
  have hdescent : baseEnd_5165321 < baseStart_5165321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165411 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 3, 5]
def baseStart_5165411 : Nat := 118140960795 + 5165411 * 2 ^ 59
def prefixEnd_5165411 : Nat := 4983230072969 + 3 ^ 40 * 5165411 * 2
def baseEnd_5165411 : Nat := 884112873673798346469071

theorem tailTrace_5165411 : CollatzResearch.WordTrace tailWord_5165411 prefixEnd_5165411 884112873673798346469071 := by
  unfold tailWord_5165411
  simp only [CollatzResearch.WordTrace]
  refine ⟨188398016689605603809816087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125598677793070402539877391 188398016689605603809816087)
  ·
    refine ⟨282597025034408405714724131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188398016689605603809816087 282597025034408405714724131)
    ·
      refine ⟨423895537551612608572086197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282597025034408405714724131 423895537551612608572086197)
      ·
        refine ⟨39740206645463682053633081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 423895537551612608572086197 39740206645463682053633081)
        ·
          refine ⟨29805154984097761540224811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39740206645463682053633081 29805154984097761540224811)
          ·
            refine ⟨44707732476146642310337217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29805154984097761540224811 44707732476146642310337217)
            ·
              refine ⟨33530799357109981732752913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44707732476146642310337217 33530799357109981732752913)
              ·
                refine ⟨25148099517832486299564685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33530799357109981732752913 25148099517832486299564685)
                ·
                  refine ⟨9430537319187182362336757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25148099517832486299564685 9430537319187182362336757)
                  ·
                    refine ⟨884112873673798346469071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9430537319187182362336757 884112873673798346469071)
                    ·
                      rfl

theorem cell23_5165411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 5].length) (baseStart_5165411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165411 prefixEnd_5165411 := by exact prefixLift 5165411
  have htrace : WordTrace (prefixWord ++ tailWord_5165411) baseStart_5165411 baseEnd_5165411 := by
    simpa [prefixWord, tailWord_5165411, baseEnd_5165411] using wordTrace_append hprefix tailTrace_5165411
  have hstable : (prefixWord ++ tailWord_5165411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165411).length < 2 ^ (prefixWord ++ tailWord_5165411).sum := by decide
  have hdescent : baseEnd_5165411 < baseStart_5165411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165415 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 6]
def baseStart_5165415 : Nat := 118140960795 + 5165415 * 2 ^ 59
def prefixEnd_5165415 : Nat := 4983230072969 + 3 ^ 40 * 5165415 * 2
def baseEnd_5165415 : Nat := 294704519438223669306355

theorem tailTrace_5165415 : CollatzResearch.WordTrace tailWord_5165415 prefixEnd_5165415 294704519438223669306355 := by
  unfold tailWord_5165415
  simp only [CollatzResearch.WordTrace]
  refine ⟨188398162581591112492961699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125598775054394074995307799 188398162581591112492961699)
  ·
    refine ⟨282597243872386668739442549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188398162581591112492961699 282597243872386668739442549)
    ·
      refine ⟨26493491613036250194322739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 282597243872386668739442549 26493491613036250194322739)
      ·
        refine ⟨39740237419554375291484109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26493491613036250194322739 39740237419554375291484109)
        ·
          refine ⟨14902589032332890734306541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39740237419554375291484109 14902589032332890734306541)
          ·
            refine ⟨5588470887124834025364953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14902589032332890734306541 5588470887124834025364953)
            ·
              refine ⟨4191353165343625519023715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588470887124834025364953 4191353165343625519023715)
              ·
                refine ⟨6287029748015438278535573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191353165343625519023715 6287029748015438278535573)
                ·
                  refine ⟨294704519438223669306355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6287029748015438278535573 294704519438223669306355)
                  ·
                    rfl

theorem cell23_5165415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 6].length) (baseStart_5165415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165415 prefixEnd_5165415 := by exact prefixLift 5165415
  have htrace : WordTrace (prefixWord ++ tailWord_5165415) baseStart_5165415 baseEnd_5165415 := by
    simpa [prefixWord, tailWord_5165415, baseEnd_5165415] using wordTrace_append hprefix tailTrace_5165415
  have hstable : (prefixWord ++ tailWord_5165415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165415).length < 2 ^ (prefixWord ++ tailWord_5165415).sum := by decide
  have hdescent : baseEnd_5165415 < baseStart_5165415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165435 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 2, 3, 2]
def baseStart_5165435 : Nat := 118140960795 + 5165435 * 2 ^ 59
def prefixEnd_5165435 : Nat := 4983230072969 + 3 ^ 40 * 5165435 * 2
def baseEnd_5165435 : Nat := 2652350944557102945507103

theorem tailTrace_5165435 : CollatzResearch.WordTrace tailWord_5165435 prefixEnd_5165435 2652350944557102945507103 := by
  unfold tailWord_5165435
  simp only [CollatzResearch.WordTrace]
  refine ⟨188398892041518655908689759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125599261361012437272459839 188398892041518655908689759)
  ·
    refine ⟨282598338062277983863034639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188398892041518655908689759 282598338062277983863034639)
    ·
      refine ⟨423897507093416975794551959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282598338062277983863034639 423897507093416975794551959)
      ·
        refine ⟨635846260640125463691827939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423897507093416975794551959 635846260640125463691827939)
        ·
          refine ⟨953769390960188195537741909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635846260640125463691827939 953769390960188195537741909)
          ·
            refine ⟨11176985050314705416457913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 953769390960188195537741909 11176985050314705416457913)
            ·
              refine ⟨8382738787736029062343435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11176985050314705416457913 8382738787736029062343435)
              ·
                refine ⟨12574108181604043593515153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8382738787736029062343435 12574108181604043593515153)
                ·
                  refine ⟨9430581136203032695136365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12574108181604043593515153 9430581136203032695136365)
                  ·
                    refine ⟨3536467926076137260676137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9430581136203032695136365 3536467926076137260676137)
                    ·
                      refine ⟨2652350944557102945507103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536467926076137260676137 2652350944557102945507103)
                      ·
                        rfl

theorem cell23_5165435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3, 2].length) (baseStart_5165435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165435 prefixEnd_5165435 := by exact prefixLift 5165435
  have htrace : WordTrace (prefixWord ++ tailWord_5165435) baseStart_5165435 baseEnd_5165435 := by
    simpa [prefixWord, tailWord_5165435, baseEnd_5165435] using wordTrace_append hprefix tailTrace_5165435
  have hstable : (prefixWord ++ tailWord_5165435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165435).length < 2 ^ (prefixWord ++ tailWord_5165435).sum := by decide
  have hdescent : baseEnd_5165435 < baseStart_5165435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165461 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_5165461 : Nat := 118140960795 + 5165461 * 2 ^ 59
def prefixEnd_5165461 : Nat := 4983230072969 + 3 ^ 40 * 5165461 * 2
def baseEnd_5165461 : Nat := 2652364295054119843781983

theorem tailTrace_5165461 : CollatzResearch.WordTrace tailWord_5165461 prefixEnd_5165461 2652364295054119843781983 := by
  unfold tailWord_5165461
  simp only [CollatzResearch.WordTrace]
  refine ⟨188399840339424462349136237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125599893559616308232757491 188399840339424462349136237)
  ·
    refine ⟨70649940127284173380926089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188399840339424462349136237 70649940127284173380926089)
    ·
      refine ⟨52987455095463130035694567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70649940127284173380926089 52987455095463130035694567)
      ·
        refine ⟨79481182643194695053541851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52987455095463130035694567 79481182643194695053541851)
        ·
          refine ⟨119221773964792042580312777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79481182643194695053541851 119221773964792042580312777)
          ·
            refine ⟨89416330473594031935234583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119221773964792042580312777 89416330473594031935234583)
            ·
              refine ⟨134124495710391047902851875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89416330473594031935234583 134124495710391047902851875)
              ·
                refine ⟨201186743565586571854277813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134124495710391047902851875 201186743565586571854277813)
                ·
                  refine ⟨18861257209273741111338545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201186743565586571854277813 18861257209273741111338545)
                  ·
                    refine ⟨14145942906955305833503909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18861257209273741111338545 14145942906955305833503909)
                    ·
                      refine ⟨2652364295054119843781983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14145942906955305833503909 2652364295054119843781983)
                      ·
                        rfl

theorem cell23_5165461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_5165461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165461 prefixEnd_5165461 := by exact prefixLift 5165461
  have htrace : WordTrace (prefixWord ++ tailWord_5165461) baseStart_5165461 baseEnd_5165461 := by
    simpa [prefixWord, tailWord_5165461, baseEnd_5165461] using wordTrace_append hprefix tailTrace_5165461
  have hstable : (prefixWord ++ tailWord_5165461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165461).length < 2 ^ (prefixWord ++ tailWord_5165461).sum := by decide
  have hdescent : baseEnd_5165461 < baseStart_5165461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165465 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 3, 2, 2]
def baseStart_5165465 : Nat := 118140960795 + 5165465 * 2 ^ 59
def prefixEnd_5165465 : Nat := 4983230072969 + 3 ^ 40 * 5165465 * 2
def baseEnd_5165465 : Nat := 2652366348976737828131965

theorem tailTrace_5165465 : CollatzResearch.WordTrace tailWord_5165465 prefixEnd_5165465 2652366348976737828131965 := by
  unfold tailWord_5165465
  simp only [CollatzResearch.WordTrace]
  refine ⟨188399986231409971032281849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125599990820939980688187899 188399986231409971032281849)
  ·
    refine ⟨141299989673557478274211387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188399986231409971032281849 141299989673557478274211387)
    ·
      refine ⟨211949984510336217411317081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141299989673557478274211387 211949984510336217411317081)
      ·
        refine ⟨158962488382752163058487811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211949984510336217411317081 158962488382752163058487811)
        ·
          refine ⟨238443732574128244587731717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158962488382752163058487811 238443732574128244587731717)
          ·
            refine ⟨44708199857649045860199697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238443732574128244587731717 44708199857649045860199697)
            ·
              refine ⟨33531149893236784395149773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44708199857649045860199697 33531149893236784395149773)
              ·
                refine ⟨12574181209963794148181165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33531149893236784395149773 12574181209963794148181165)
                ·
                  refine ⟨4715317953736422805567937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12574181209963794148181165 4715317953736422805567937)
                  ·
                    refine ⟨3536488465302317104175953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715317953736422805567937 3536488465302317104175953)
                    ·
                      refine ⟨2652366348976737828131965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536488465302317104175953 2652366348976737828131965)
                      ·
                        rfl

theorem cell23_5165465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_5165465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165465 prefixEnd_5165465 := by exact prefixLift 5165465
  have htrace : WordTrace (prefixWord ++ tailWord_5165465) baseStart_5165465 baseEnd_5165465 := by
    simpa [prefixWord, tailWord_5165465, baseEnd_5165465] using wordTrace_append hprefix tailTrace_5165465
  have hstable : (prefixWord ++ tailWord_5165465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165465).length < 2 ^ (prefixWord ++ tailWord_5165465).sum := by decide
  have hdescent : baseEnd_5165465 < baseStart_5165465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165502 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_5165502 : Nat := 118140960795 + 5165502 * 2 ^ 59
def prefixEnd_5165502 : Nat := 4983230072969 + 3 ^ 40 * 5165502 * 2
def baseEnd_5165502 : Nat := 2652385347760954183369295

theorem tailTrace_5165502 : CollatzResearch.WordTrace tailWord_5165502 prefixEnd_5165502 2652385347760954183369295 := by
  unfold tailWord_5165502
  simp only [CollatzResearch.WordTrace]
  refine ⟨23550166966534490793922345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125600890488183950900919173 23550166966534490793922345)
  ·
    refine ⟨17662625224900868095441759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23550166966534490793922345 17662625224900868095441759)
    ·
      refine ⟨26493937837351302143162639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17662625224900868095441759 26493937837351302143162639)
      ·
        refine ⟨39740906756026953214743959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26493937837351302143162639 39740906756026953214743959)
        ·
          refine ⟨59611360134040429822115939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39740906756026953214743959 59611360134040429822115939)
          ·
            refine ⟨89417040201060644733173909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59611360134040429822115939 89417040201060644733173909)
            ·
              refine ⟨4191423759424717721867527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89417040201060644733173909 4191423759424717721867527)
              ·
                refine ⟨6287135639137076582801291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191423759424717721867527 6287135639137076582801291)
                ·
                  refine ⟨9430703458705614874201937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6287135639137076582801291 9430703458705614874201937)
                  ·
                    refine ⟨7073027594029211155651453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9430703458705614874201937 7073027594029211155651453)
                    ·
                      refine ⟨2652385347760954183369295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7073027594029211155651453 2652385347760954183369295)
                      ·
                        rfl

theorem cell23_5165502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_5165502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165502 prefixEnd_5165502 := by exact prefixLift 5165502
  have htrace : WordTrace (prefixWord ++ tailWord_5165502) baseStart_5165502 baseEnd_5165502 := by
    simpa [prefixWord, tailWord_5165502, baseEnd_5165502] using wordTrace_append hprefix tailTrace_5165502
  have hstable : (prefixWord ++ tailWord_5165502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165502).length < 2 ^ (prefixWord ++ tailWord_5165502).sum := by decide
  have hdescent : baseEnd_5165502 < baseStart_5165502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165521 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_5165521 : Nat := 118140960795 + 5165521 * 2 ^ 59
def prefixEnd_5165521 : Nat := 4983230072969 + 3 ^ 40 * 5165521 * 2
def baseEnd_5165521 : Nat := 2652395103893389609031707

theorem tailTrace_5165521 : CollatzResearch.WordTrace tailWord_5165521 prefixEnd_5165521 2652395103893389609031707 := by
  unfold tailWord_5165521
  simp only [CollatzResearch.WordTrace]
  refine ⟨188402028719207092596320417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125601352479471395064213611 188402028719207092596320417)
  ·
    refine ⟨141301521539405319447240313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188402028719207092596320417 141301521539405319447240313)
    ·
      refine ⟨105976141154553989585430235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141301521539405319447240313 105976141154553989585430235)
      ·
        refine ⟨158964211731830984378145353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105976141154553989585430235 158964211731830984378145353)
        ·
          refine ⟨119223158798873238283609015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158964211731830984378145353 119223158798873238283609015)
          ·
            refine ⟨178834738198309857425413523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119223158798873238283609015 178834738198309857425413523)
            ·
              refine ⟨268252107297464786138120285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178834738198309857425413523 268252107297464786138120285)
              ·
                refine ⟨100594540236549294801795107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268252107297464786138120285 100594540236549294801795107)
                ·
                  refine ⟨150891810354823942202692661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100594540236549294801795107 150891810354823942202692661)
                  ·
                    refine ⟨14146107220764744581502437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 150891810354823942202692661 14146107220764744581502437)
                    ·
                      refine ⟨2652395103893389609031707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14146107220764744581502437 2652395103893389609031707)
                      ·
                        rfl

theorem cell23_5165521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_5165521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165521 prefixEnd_5165521 := by exact prefixLift 5165521
  have htrace : WordTrace (prefixWord ++ tailWord_5165521) baseStart_5165521 baseEnd_5165521 := by
    simpa [prefixWord, tailWord_5165521, baseEnd_5165521] using wordTrace_append hprefix tailTrace_5165521
  have hstable : (prefixWord ++ tailWord_5165521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165521).length < 2 ^ (prefixWord ++ tailWord_5165521).sum := by decide
  have hdescent : baseEnd_5165521 < baseStart_5165521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165555 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 6, 2, 2]
def baseStart_5165555 : Nat := 118140960795 + 5165555 * 2 ^ 59
def prefixEnd_5165555 : Nat := 4983230072969 + 3 ^ 40 * 5165555 * 2
def baseEnd_5165555 : Nat := 2652412562235642476006551

theorem tailTrace_5165555 : CollatzResearch.WordTrace tailWord_5165555 prefixEnd_5165555 2652412562235642476006551 := by
  unfold tailWord_5165555
  simp only [CollatzResearch.WordTrace]
  refine ⟨188403268801083916403058119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125602179200722610935372079 188403268801083916403058119)
  ·
    refine ⟨282604903201625874604587179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188403268801083916403058119 282604903201625874604587179)
    ·
      refine ⟨423907354802438811906880769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282604903201625874604587179 423907354802438811906880769)
      ·
        refine ⟨317930516101829108930160577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423907354802438811906880769 317930516101829108930160577)
        ·
          refine ⟨238447887076371831697620433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317930516101829108930160577 238447887076371831697620433)
          ·
            refine ⟨178835915307278873773215325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238447887076371831697620433 178835915307278873773215325)
            ·
              refine ⟨67063468240229577664955747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178835915307278873773215325 67063468240229577664955747)
              ·
                refine ⟨100595202360344366497433621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67063468240229577664955747 100595202360344366497433621)
                ·
                  refine ⟨4715400110641142179567201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100595202360344366497433621 4715400110641142179567201)
                  ·
                    refine ⟨3536550082980856634675401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715400110641142179567201 3536550082980856634675401)
                    ·
                      refine ⟨2652412562235642476006551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536550082980856634675401 2652412562235642476006551)
                      ·
                        rfl

theorem cell23_5165555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 2, 2].length) (baseStart_5165555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165555 prefixEnd_5165555 := by exact prefixLift 5165555
  have htrace : WordTrace (prefixWord ++ tailWord_5165555) baseStart_5165555 baseEnd_5165555 := by
    simpa [prefixWord, tailWord_5165555, baseEnd_5165555] using wordTrace_append hprefix tailTrace_5165555
  have hstable : (prefixWord ++ tailWord_5165555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165555).length < 2 ^ (prefixWord ++ tailWord_5165555).sum := by decide
  have hdescent : baseEnd_5165555 < baseStart_5165555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165561 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 9]
def baseStart_5165561 : Nat := 118140960795 + 5165561 * 2 ^ 59
def prefixEnd_5165561 : Nat := 4983230072969 + 3 ^ 40 * 5165561 * 2
def baseEnd_5165561 : Nat := 294712849235507716947947

theorem tailTrace_5165561 : CollatzResearch.WordTrace tailWord_5165561 prefixEnd_5165561 294712849235507716947947 := by
  unfold tailWord_5165561
  simp only [CollatzResearch.WordTrace]
  refine ⟨188403487639062179427776537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125602325092708119618517691 188403487639062179427776537)
  ·
    refine ⟨141302615729296634570832403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188403487639062179427776537 141302615729296634570832403)
    ·
      refine ⟨211953923593944951856248605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141302615729296634570832403 211953923593944951856248605)
      ·
        refine ⟨79482721347729356946093227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211953923593944951856248605 79482721347729356946093227)
        ·
          refine ⟨119224082021594035419139841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79482721347729356946093227 119224082021594035419139841)
          ·
            refine ⟨89418061516195526564354881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119224082021594035419139841 89418061516195526564354881)
            ·
              refine ⟨67063546137146644923266161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89418061516195526564354881 67063546137146644923266161)
              ·
                refine ⟨50297659602859983692449621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67063546137146644923266161 50297659602859983692449621)
                ·
                  refine ⟨294712849235507716947947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50297659602859983692449621 294712849235507716947947)
                  ·
                    rfl

theorem cell23_5165561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_5165561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165561 prefixEnd_5165561 := by exact prefixLift 5165561
  have htrace : WordTrace (prefixWord ++ tailWord_5165561) baseStart_5165561 baseEnd_5165561 := by
    simpa [prefixWord, tailWord_5165561, baseEnd_5165561] using wordTrace_append hprefix tailTrace_5165561
  have hstable : (prefixWord ++ tailWord_5165561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165561).length < 2 ^ (prefixWord ++ tailWord_5165561).sum := by decide
  have hdescent : baseEnd_5165561 < baseStart_5165561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165571 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7]
def baseStart_5165571 : Nat := 118140960795 + 5165571 * 2 ^ 59
def prefixEnd_5165571 : Nat := 4983230072969 + 3 ^ 40 * 5165571 * 2
def baseEnd_5165571 : Nat := 2652420777926114413406477

theorem tailTrace_5165571 : CollatzResearch.WordTrace tailWord_5165571 prefixEnd_5165571 2652420777926114413406477 := by
  unfold tailWord_5165571
  simp only [CollatzResearch.WordTrace]
  refine ⟨188403852369025951135640567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125602568246017300757093711 188403852369025951135640567)
  ·
    refine ⟨282605778553538926703460851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188403852369025951135640567 282605778553538926703460851)
    ·
      refine ⟨423908667830308390055191277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282605778553538926703460851 423908667830308390055191277)
      ·
        refine ⟨158965750436365646270696729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 423908667830308390055191277 158965750436365646270696729)
        ·
          refine ⟨119224312827274234703022547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158965750436365646270696729 119224312827274234703022547)
          ·
            refine ⟨178836469240911352054533821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119224312827274234703022547 178836469240911352054533821)
            ·
              refine ⟨67063675965341757020450183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178836469240911352054533821 67063675965341757020450183)
              ·
                refine ⟨100595513948012635530675275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67063675965341757020450183 100595513948012635530675275)
                ·
                  refine ⟨150893270922018953296012913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100595513948012635530675275 150893270922018953296012913)
                  ·
                    refine ⟨113169953191514214972009685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150893270922018953296012913 113169953191514214972009685)
                    ·
                      refine ⟨2652420777926114413406477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113169953191514214972009685 2652420777926114413406477)
                      ·
                        rfl

theorem cell23_5165571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_5165571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165571 prefixEnd_5165571 := by exact prefixLift 5165571
  have htrace : WordTrace (prefixWord ++ tailWord_5165571) baseStart_5165571 baseEnd_5165571 := by
    simpa [prefixWord, tailWord_5165571, baseEnd_5165571] using wordTrace_append hprefix tailTrace_5165571
  have hstable : (prefixWord ++ tailWord_5165571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165571).length < 2 ^ (prefixWord ++ tailWord_5165571).sum := by decide
  have hdescent : baseEnd_5165571 < baseStart_5165571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165618 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_5165618 : Nat := 118140960795 + 5165618 * 2 ^ 59
def prefixEnd_5165618 : Nat := 4983230072969 + 3 ^ 40 * 5165618 * 2
def baseEnd_5165618 : Nat := 2652444911516875729518761

theorem tailTrace_5165618 : CollatzResearch.WordTrace tailWord_5165618 prefixEnd_5165618 2652444911516875729518761 := by
  unfold tailWord_5165618
  simp only [CollatzResearch.WordTrace]
  refine ⟨47101391649963919540650377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125603711066570452108401005 47101391649963919540650377)
  ·
    refine ⟨35326043737472939655487783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47101391649963919540650377 35326043737472939655487783)
    ·
      refine ⟨52989065606209409483231675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35326043737472939655487783 52989065606209409483231675)
      ·
        refine ⟨79483598409314114224847513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52989065606209409483231675 79483598409314114224847513)
        ·
          refine ⟨59612698806985585668635635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79483598409314114224847513 59612698806985585668635635)
          ·
            refine ⟨89419048210478378502953453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59612698806985585668635635 89419048210478378502953453)
            ·
              refine ⟨33532143078929391938607545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89419048210478378502953453 33532143078929391938607545)
              ·
                refine ⟨25149107309197043953955659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33532143078929391938607545 25149107309197043953955659)
                ·
                  refine ⟨37723660963795565930933489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25149107309197043953955659 37723660963795565930933489)
                  ·
                    refine ⟨28292745722846674448200117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37723660963795565930933489 28292745722846674448200117)
                    ·
                      refine ⟨2652444911516875729518761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28292745722846674448200117 2652444911516875729518761)
                      ·
                        rfl

theorem cell23_5165618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_5165618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165618 prefixEnd_5165618 := by exact prefixLift 5165618
  have htrace : WordTrace (prefixWord ++ tailWord_5165618) baseStart_5165618 baseEnd_5165618 := by
    simpa [prefixWord, tailWord_5165618, baseEnd_5165618] using wordTrace_append hprefix tailTrace_5165618
  have hstable : (prefixWord ++ tailWord_5165618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165618).length < 2 ^ (prefixWord ++ tailWord_5165618).sum := by decide
  have hdescent : baseEnd_5165618 < baseStart_5165618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165629 : List Nat := [1, 4, 1, 3, 2, 3, 2, 2, 5]
def baseStart_5165629 : Nat := 118140960795 + 5165629 * 2 ^ 59
def prefixEnd_5165629 : Nat := 4983230072969 + 3 ^ 40 * 5165629 * 2
def baseEnd_5165629 : Nat := 294716728867119465164579

theorem tailTrace_5165629 : CollatzResearch.WordTrace tailWord_5165629 prefixEnd_5165629 294716728867119465164579 := by
  unfold tailWord_5165629
  simp only [CollatzResearch.WordTrace]
  refine ⟨188405967802815827041251941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125603978535210551360834627 188405967802815827041251941)
  ·
    refine ⟨35326118963027967570234739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188405967802815827041251941 35326118963027967570234739)
    ·
      refine ⟨52989178444541951355352109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35326118963027967570234739 52989178444541951355352109)
      ·
        refine ⟨19870941916703231758257041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52989178444541951355352109 19870941916703231758257041)
        ·
          refine ⟨14903206437527423818692781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19870941916703231758257041 14903206437527423818692781)
          ·
            refine ⟨5588702414072783932009793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14903206437527423818692781 5588702414072783932009793)
            ·
              refine ⟨4191526810554587949007345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588702414072783932009793 4191526810554587949007345)
              ·
                refine ⟨3143645107915940961755509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4191526810554587949007345 3143645107915940961755509)
                ·
                  refine ⟨294716728867119465164579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3143645107915940961755509 294716728867119465164579)
                  ·
                    rfl

theorem cell23_5165629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_5165629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165629 prefixEnd_5165629 := by exact prefixLift 5165629
  have htrace : WordTrace (prefixWord ++ tailWord_5165629) baseStart_5165629 baseEnd_5165629 := by
    simpa [prefixWord, tailWord_5165629, baseEnd_5165629] using wordTrace_append hprefix tailTrace_5165629
  have hstable : (prefixWord ++ tailWord_5165629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165629).length < 2 ^ (prefixWord ++ tailWord_5165629).sum := by decide
  have hdescent : baseEnd_5165629 < baseStart_5165629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165655 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 3, 4]
def baseStart_5165655 : Nat := 118140960795 + 5165655 * 2 ^ 59
def prefixEnd_5165655 : Nat := 4983230072969 + 3 ^ 40 * 5165655 * 2
def baseEnd_5165655 : Nat := 884154636767030694918697

theorem tailTrace_5165655 : CollatzResearch.WordTrace tailWord_5165655 prefixEnd_5165655 884154636767030694918697 := by
  unfold tailWord_5165655
  simp only [CollatzResearch.WordTrace]
  refine ⟨188406916100721633481698419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125604610733814422321132279 188406916100721633481698419)
  ·
    refine ⟨282610374151082450222547629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188406916100721633481698419 282610374151082450222547629)
    ·
      refine ⟨105978890306655918833455361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282610374151082450222547629 105978890306655918833455361)
      ·
        refine ⟨79484167729991939125091521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105978890306655918833455361 79484167729991939125091521)
        ·
          refine ⟨59613125797493954343818641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79484167729991939125091521 59613125797493954343818641)
          ·
            refine ⟨44709844348120465757863981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59613125797493954343818641 44709844348120465757863981)
            ·
              refine ⟨16766191630545174659198993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44709844348120465757863981 16766191630545174659198993)
              ·
                refine ⟨12574643722908880994399245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16766191630545174659198993 12574643722908880994399245)
                ·
                  refine ⟨4715491396090830372899717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12574643722908880994399245 4715491396090830372899717)
                  ·
                    refine ⟨884154636767030694918697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4715491396090830372899717 884154636767030694918697)
                    ·
                      rfl

theorem cell23_5165655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_5165655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165655 prefixEnd_5165655 := by exact prefixLift 5165655
  have htrace : WordTrace (prefixWord ++ tailWord_5165655) baseStart_5165655 baseEnd_5165655 := by
    simpa [prefixWord, tailWord_5165655, baseEnd_5165655] using wordTrace_append hprefix tailTrace_5165655
  have hstable : (prefixWord ++ tailWord_5165655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165655).length < 2 ^ (prefixWord ++ tailWord_5165655).sum := by decide
  have hdescent : baseEnd_5165655 < baseStart_5165655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165665 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_5165665 : Nat := 118140960795 + 5165665 * 2 ^ 59
def prefixEnd_5165665 : Nat := 4983230072969 + 3 ^ 40 * 5165665 * 2
def baseEnd_5165665 : Nat := 2652469045107637045631045

theorem tailTrace_5165665 : CollatzResearch.WordTrace tailWord_5165665 prefixEnd_5165665 2652469045107637045631045 := by
  unfold tailWord_5165665
  simp only [CollatzResearch.WordTrace]
  refine ⟨188407280830685405189562449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125604853887123603459708299 188407280830685405189562449)
  ·
    refine ⟨141305460623014053892171837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188407280830685405189562449 141305460623014053892171837)
    ·
      refine ⟨52989547733630270209564439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141305460623014053892171837 52989547733630270209564439)
      ·
        refine ⟨79484321600445405314346659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52989547733630270209564439 79484321600445405314346659)
        ·
          refine ⟨119226482400668107971519989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79484321600445405314346659 119226482400668107971519989)
          ·
            refine ⟨11177482725062635122329999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119226482400668107971519989 11177482725062635122329999)
            ·
              refine ⟨16766224087593952683494999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11177482725062635122329999 16766224087593952683494999)
              ·
                refine ⟨25149336131390929025242499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16766224087593952683494999 25149336131390929025242499)
                ·
                  refine ⟨37724004197086393537863749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25149336131390929025242499 37724004197086393537863749)
                  ·
                    refine ⟨7073250786953698788349453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37724004197086393537863749 7073250786953698788349453)
                    ·
                      refine ⟨2652469045107637045631045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7073250786953698788349453 2652469045107637045631045)
                      ·
                        rfl

theorem cell23_5165665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_5165665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165665 prefixEnd_5165665 := by exact prefixLift 5165665
  have htrace : WordTrace (prefixWord ++ tailWord_5165665) baseStart_5165665 baseEnd_5165665 := by
    simpa [prefixWord, tailWord_5165665, baseEnd_5165665] using wordTrace_append hprefix tailTrace_5165665
  have hstable : (prefixWord ++ tailWord_5165665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165665).length < 2 ^ (prefixWord ++ tailWord_5165665).sum := by decide
  have hdescent : baseEnd_5165665 < baseStart_5165665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165668 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 8]
def baseStart_5165668 : Nat := 118140960795 + 5165668 * 2 ^ 59
def prefixEnd_5165668 : Nat := 4983230072969 + 3 ^ 40 * 5165668 * 2
def baseEnd_5165668 : Nat := 294718953949955614877059

theorem tailTrace_5165668 : CollatzResearch.WordTrace tailWord_5165668 prefixEnd_5165668 294718953949955614877059 := by
  unfold tailWord_5165668
  simp only [CollatzResearch.WordTrace]
  refine ⟨94203695124837268350960829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125604926833116357801281105 94203695124837268350960829)
  ·
    refine ⟨35326385671813975631610311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94203695124837268350960829 35326385671813975631610311)
    ·
      refine ⟨52989578507720963447415467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35326385671813975631610311 52989578507720963447415467)
      ·
        refine ⟨79484367761581445171123201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52989578507720963447415467 79484367761581445171123201)
        ·
          refine ⟨59613275821186083878342401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79484367761581445171123201 59613275821186083878342401)
          ·
            refine ⟨44709956865889562908756801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59613275821186083878342401 44709956865889562908756801)
            ·
              refine ⟨33532467649417172181567601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44709956865889562908756801 33532467649417172181567601)
              ·
                refine ⟨25149350737062879136175701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33532467649417172181567601 25149350737062879136175701)
                ·
                  refine ⟨294718953949955614877059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25149350737062879136175701 294718953949955614877059)
                  ·
                    rfl

theorem cell23_5165668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_5165668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165668 prefixEnd_5165668 := by exact prefixLift 5165668
  have htrace : WordTrace (prefixWord ++ tailWord_5165668) baseStart_5165668 baseEnd_5165668 := by
    simpa [prefixWord, tailWord_5165668, baseEnd_5165668] using wordTrace_append hprefix tailTrace_5165668
  have hstable : (prefixWord ++ tailWord_5165668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165668).length < 2 ^ (prefixWord ++ tailWord_5165668).sum := by decide
  have hdescent : baseEnd_5165668 < baseStart_5165668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165766 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_5165766 : Nat := 118140960795 + 5165766 * 2 ^ 59
def prefixEnd_5165766 : Nat := 4983230072969 + 3 ^ 40 * 5165766 * 2
def baseEnd_5165766 : Nat := 884173635551247050156027

theorem tailTrace_5165766 : CollatzResearch.WordTrace tailWord_5165766 prefixEnd_5165766 884173635551247050156027 := by
  unfold tailWord_5165766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5887842643853734357468411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125607309735546332959326101 5887842643853734357468411)
  ·
    refine ⟨8831763965780601536202617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5887842643853734357468411 8831763965780601536202617)
    ·
      refine ⟨6623822974335451152151963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8831763965780601536202617 6623822974335451152151963)
      ·
        refine ⟨9935734461503176728227945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6623822974335451152151963 9935734461503176728227945)
        ·
          refine ⟨7451800846127382546170959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9935734461503176728227945 7451800846127382546170959)
          ·
            refine ⟨11177701269191073819256439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7451800846127382546170959 11177701269191073819256439)
            ·
              refine ⟨16766551903786610728884659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11177701269191073819256439 16766551903786610728884659)
              ·
                refine ⟨25149827855679916093326989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16766551903786610728884659 25149827855679916093326989)
                ·
                  refine ⟨9431185445879968534997621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25149827855679916093326989 9431185445879968534997621)
                  ·
                    refine ⟨884173635551247050156027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9431185445879968534997621 884173635551247050156027)
                    ·
                      rfl

theorem cell23_5165766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_5165766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165766 prefixEnd_5165766 := by exact prefixLift 5165766
  have htrace : WordTrace (prefixWord ++ tailWord_5165766) baseStart_5165766 baseEnd_5165766 := by
    simpa [prefixWord, tailWord_5165766, baseEnd_5165766] using wordTrace_append hprefix tailTrace_5165766
  have hstable : (prefixWord ++ tailWord_5165766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165766).length < 2 ^ (prefixWord ++ tailWord_5165766).sum := by decide
  have hdescent : baseEnd_5165766 < baseStart_5165766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165773 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5165773 : Nat := 118140960795 + 5165773 * 2 ^ 59
def prefixEnd_5165773 : Nat := 4983230072969 + 3 ^ 40 * 5165773 * 2
def baseEnd_5165773 : Nat := 2652524501018322623080549

theorem tailTrace_5165773 : CollatzResearch.WordTrace tailWord_5165773 prefixEnd_5165773 2652524501018322623080549 := by
  unfold tailWord_5165773
  simp only [CollatzResearch.WordTrace]
  refine ⟨188411219914294139634493973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125607479942862759756329315 188411219914294139634493973)
  ·
    refine ⟨8831775933482537795366905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 188411219914294139634493973 8831775933482537795366905)
    ·
      refine ⟨6623831950111903346525179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8831775933482537795366905 6623831950111903346525179)
      ·
        refine ⟨9935747925167855019787769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6623831950111903346525179 9935747925167855019787769)
        ·
          refine ⟨7451810943875891264840827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9935747925167855019787769 7451810943875891264840827)
          ·
            refine ⟨11177716415813836897261241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7451810943875891264840827 11177716415813836897261241)
            ·
              refine ⟨8383287311860377672945931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11177716415813836897261241 8383287311860377672945931)
              ·
                refine ⟨12574930967790566509418897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8383287311860377672945931 12574930967790566509418897)
                ·
                  refine ⟨9431198225842924882064173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12574930967790566509418897 9431198225842924882064173)
                  ·
                    refine ⟨3536699334691096830774065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9431198225842924882064173 3536699334691096830774065)
                    ·
                      refine ⟨2652524501018322623080549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536699334691096830774065 2652524501018322623080549)
                      ·
                        rfl

theorem cell23_5165773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5165773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165773 prefixEnd_5165773 := by exact prefixLift 5165773
  have htrace : WordTrace (prefixWord ++ tailWord_5165773) baseStart_5165773 baseEnd_5165773 := by
    simpa [prefixWord, tailWord_5165773, baseEnd_5165773] using wordTrace_append hprefix tailTrace_5165773
  have hstable : (prefixWord ++ tailWord_5165773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165773).length < 2 ^ (prefixWord ++ tailWord_5165773).sum := by decide
  have hdescent : baseEnd_5165773 < baseStart_5165773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165786 : List Nat := [3, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2]
def baseStart_5165786 : Nat := 118140960795 + 5165786 * 2 ^ 59
def prefixEnd_5165786 : Nat := 4983230072969 + 3 ^ 40 * 5165786 * 2
def baseEnd_5165786 : Nat := 2652531176266831072217989

theorem tailTrace_5165786 : CollatzResearch.WordTrace tailWord_5165786 prefixEnd_5165786 2652531176266831072217989 := by
  unfold tailWord_5165786
  simp only [CollatzResearch.WordTrace]
  refine ⟨47102923515811760713679303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125607796042164695236478141 47102923515811760713679303)
  ·
    refine ⟨70654385273717641070518955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47102923515811760713679303 70654385273717641070518955)
    ·
      refine ⟨105981577910576461605778433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70654385273717641070518955 105981577910576461605778433)
      ·
        refine ⟨79486183432932346204333825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105981577910576461605778433 79486183432932346204333825)
        ·
          refine ⟨59614637574699259653250369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79486183432932346204333825 59614637574699259653250369)
          ·
            refine ⟨44710978181024444739937777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59614637574699259653250369 44710978181024444739937777)
            ·
              refine ⟨33533233635768333554953333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44710978181024444739937777 33533233635768333554953333)
              ·
                refine ⟨3143740653353281270776875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33533233635768333554953333 3143740653353281270776875)
                ·
                  refine ⟨4715610980029921906165313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143740653353281270776875 4715610980029921906165313)
                  ·
                    refine ⟨3536708235022441429623985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715610980029921906165313 3536708235022441429623985)
                    ·
                      refine ⟨2652531176266831072217989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536708235022441429623985 2652531176266831072217989)
                      ·
                        rfl

theorem cell23_5165786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_5165786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165786 prefixEnd_5165786 := by exact prefixLift 5165786
  have htrace : WordTrace (prefixWord ++ tailWord_5165786) baseStart_5165786 baseEnd_5165786 := by
    simpa [prefixWord, tailWord_5165786, baseEnd_5165786] using wordTrace_append hprefix tailTrace_5165786
  have hstable : (prefixWord ++ tailWord_5165786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165786).length < 2 ^ (prefixWord ++ tailWord_5165786).sum := by decide
  have hdescent : baseEnd_5165786 < baseStart_5165786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165805 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_5165805 : Nat := 118140960795 + 5165805 * 2 ^ 59
def prefixEnd_5165805 : Nat := 4983230072969 + 3 ^ 40 * 5165805 * 2
def baseEnd_5165805 : Nat := 884180310799755499293467

theorem tailTrace_5165805 : CollatzResearch.WordTrace tailWord_5165805 prefixEnd_5165805 884180310799755499293467 := by
  unfold tailWord_5165805
  simp only [CollatzResearch.WordTrace]
  refine ⟨188412387050178209099658869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125608258033452139399772579 188412387050178209099658869)
  ·
    refine ⟨17663661285954207103093019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188412387050178209099658869 17663661285954207103093019)
    ·
      refine ⟨26495491928931310654639529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17663661285954207103093019 26495491928931310654639529)
      ·
        refine ⟨19871618946698482990979647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26495491928931310654639529 19871618946698482990979647)
        ·
          refine ⟨29807428420047724486469471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19871618946698482990979647 29807428420047724486469471)
          ·
            refine ⟨44711142630071586729704207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29807428420047724486469471 44711142630071586729704207)
            ·
              refine ⟨67066713945107380094556311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44711142630071586729704207 67066713945107380094556311)
              ·
                refine ⟨100600070917661070141834467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67066713945107380094556311 100600070917661070141834467)
                ·
                  refine ⟨150900106376491605212751701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100600070917661070141834467 150900106376491605212751701)
                  ·
                    refine ⟨884180310799755499293467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 150900106376491605212751701 884180310799755499293467)
                    ·
                      rfl

theorem cell23_5165805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_5165805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165805 prefixEnd_5165805 := by exact prefixLift 5165805
  have htrace : WordTrace (prefixWord ++ tailWord_5165805) baseStart_5165805 baseEnd_5165805 := by
    simpa [prefixWord, tailWord_5165805, baseEnd_5165805] using wordTrace_append hprefix tailTrace_5165805
  have hstable : (prefixWord ++ tailWord_5165805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165805).length < 2 ^ (prefixWord ++ tailWord_5165805).sum := by decide
  have hdescent : baseEnd_5165805 < baseStart_5165805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165825 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_5165825 : Nat := 118140960795 + 5165825 * 2 ^ 59
def prefixEnd_5165825 : Nat := 4983230072969 + 3 ^ 40 * 5165825 * 2
def baseEnd_5165825 : Nat := 2652551202012356419630309

theorem tailTrace_5165825 : CollatzResearch.WordTrace tailWord_5165825 prefixEnd_5165825 2652551202012356419630309 := by
  unfold tailWord_5165825
  simp only [CollatzResearch.WordTrace]
  refine ⟨188413116510105752515386929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125608744340070501676924619 188413116510105752515386929)
  ·
    refine ⟨141309837382579314386540197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188413116510105752515386929 141309837382579314386540197)
    ·
      refine ⟨26495594509233621447476287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141309837382579314386540197 26495594509233621447476287)
      ·
        refine ⟨39743391763850432171214431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26495594509233621447476287 39743391763850432171214431)
        ·
          refine ⟨59615087645775648256821647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39743391763850432171214431 59615087645775648256821647)
          ·
            refine ⟨89422631468663472385232471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59615087645775648256821647 89422631468663472385232471)
            ·
              refine ⟨134133947202995208577848707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89422631468663472385232471 134133947202995208577848707)
              ·
                refine ⟨201200920804492812866773061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134133947202995208577848707 201200920804492812866773061)
                ·
                  refine ⟨37725172650842402412519949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201200920804492812866773061 37725172650842402412519949)
                  ·
                    refine ⟨14146939744065900904694981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37725172650842402412519949 14146939744065900904694981)
                    ·
                      refine ⟨2652551202012356419630309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14146939744065900904694981 2652551202012356419630309)
                      ·
                        rfl

theorem cell23_5165825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_5165825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165825 prefixEnd_5165825 := by exact prefixLift 5165825
  have htrace : WordTrace (prefixWord ++ tailWord_5165825) baseStart_5165825 baseEnd_5165825 := by
    simpa [prefixWord, tailWord_5165825, baseEnd_5165825] using wordTrace_append hprefix tailTrace_5165825
  have hstable : (prefixWord ++ tailWord_5165825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165825).length < 2 ^ (prefixWord ++ tailWord_5165825).sum := by decide
  have hdescent : baseEnd_5165825 < baseStart_5165825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165845 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_5165845 : Nat := 118140960795 + 5165845 * 2 ^ 59
def prefixEnd_5165845 : Nat := 4983230072969 + 3 ^ 40 * 5165845 * 2
def baseEnd_5165845 : Nat := 2652561471625446341380217

theorem tailTrace_5165845 : CollatzResearch.WordTrace tailWord_5165845 prefixEnd_5165845 2652561471625446341380217 := by
  unfold tailWord_5165845
  simp only [CollatzResearch.WordTrace]
  refine ⟨188413845970033295931114989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125609230646688863954076659 188413845970033295931114989)
  ·
    refine ⟨70655192238762485974168121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188413845970033295931114989 70655192238762485974168121)
    ·
      refine ⟨52991394179071864480626091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70655192238762485974168121 52991394179071864480626091)
      ·
        refine ⟨79487091268607796720939137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52991394179071864480626091 79487091268607796720939137)
        ·
          refine ⟨59615318451455847540704353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79487091268607796720939137 59615318451455847540704353)
          ·
            refine ⟨44711488838591885655528265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59615318451455847540704353 44711488838591885655528265)
            ·
              refine ⟨33533616628943914241646199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44711488838591885655528265 33533616628943914241646199)
              ·
                refine ⟨50300424943415871362469299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33533616628943914241646199 50300424943415871362469299)
                ·
                  refine ⟨75450637415123807043703949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50300424943415871362469299 75450637415123807043703949)
                  ·
                    refine ⟨28293989030671427641388981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75450637415123807043703949 28293989030671427641388981)
                    ·
                      refine ⟨2652561471625446341380217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28293989030671427641388981 2652561471625446341380217)
                      ·
                        rfl

theorem cell23_5165845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_5165845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165845 prefixEnd_5165845 := by exact prefixLift 5165845
  have htrace : WordTrace (prefixWord ++ tailWord_5165845) baseStart_5165845 baseEnd_5165845 := by
    simpa [prefixWord, tailWord_5165845, baseEnd_5165845] using wordTrace_append hprefix tailTrace_5165845
  have hstable : (prefixWord ++ tailWord_5165845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165845).length < 2 ^ (prefixWord ++ tailWord_5165845).sum := by decide
  have hdescent : baseEnd_5165845 < baseStart_5165845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165932 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_5165932 : Nat := 118140960795 + 5165932 * 2 ^ 59
def prefixEnd_5165932 : Nat := 4983230072969 + 3 ^ 40 * 5165932 * 2
def baseEnd_5165932 : Nat := 2652606144442387500992317

theorem tailTrace_5165932 : CollatzResearch.WordTrace tailWord_5165932 prefixEnd_5165932 2652606144442387500992317 := by
  unfold tailWord_5165932
  simp only [CollatzResearch.WordTrace]
  refine ⟨94208509560359054894766025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125611346080478739859688033 94208509560359054894766025)
  ·
    refine ⟨70656382170269291171074519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94208509560359054894766025 70656382170269291171074519)
    ·
      refine ⟨105984573255403936756611779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70656382170269291171074519 105984573255403936756611779)
      ·
        refine ⟨158976859883105905134917669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105984573255403936756611779 158976859883105905134917669)
        ·
          refine ⟨29808161228082357212797063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158976859883105905134917669 29808161228082357212797063)
          ·
            refine ⟨44712241842123535819195595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29808161228082357212797063 44712241842123535819195595)
            ·
              refine ⟨67068362763185303728793393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44712241842123535819195595 67068362763185303728793393)
              ·
                refine ⟨50301272072388977796595045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67068362763185303728793393 50301272072388977796595045)
                ·
                  refine ⟨9431488513572933336861571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50301272072388977796595045 9431488513572933336861571)
                  ·
                    refine ⟨14147232770359400005292357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9431488513572933336861571 14147232770359400005292357)
                    ·
                      refine ⟨2652606144442387500992317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14147232770359400005292357 2652606144442387500992317)
                      ·
                        rfl

theorem cell23_5165932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_5165932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165932 prefixEnd_5165932 := by exact prefixLift 5165932
  have htrace : WordTrace (prefixWord ++ tailWord_5165932) baseStart_5165932 baseEnd_5165932 := by
    simpa [prefixWord, tailWord_5165932, baseEnd_5165932] using wordTrace_append hprefix tailTrace_5165932
  have hstable : (prefixWord ++ tailWord_5165932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165932).length < 2 ^ (prefixWord ++ tailWord_5165932).sum := by decide
  have hdescent : baseEnd_5165932 < baseStart_5165932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5165935 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_5165935 : Nat := 118140960795 + 5165935 * 2 ^ 59
def prefixEnd_5165935 : Nat := 4983230072969 + 3 ^ 40 * 5165935 * 2
def baseEnd_5165935 : Nat := 2652607684884350989254803

theorem tailTrace_5165935 : CollatzResearch.WordTrace tailWord_5165935 prefixEnd_5165935 2652607684884350989254803 := by
  unfold tailWord_5165935
  simp only [CollatzResearch.WordTrace]
  refine ⟨188417128539707241301891259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125611419026471494201260839 188417128539707241301891259)
  ·
    refine ⟨282625692809560861952836889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188417128539707241301891259 282625692809560861952836889)
    ·
      refine ⟨211969269607170646464627667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282625692809560861952836889 211969269607170646464627667)
      ·
        refine ⟨317953904410755969696941501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211969269607170646464627667 317953904410755969696941501)
        ·
          refine ⟨119232714154033488636353063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317953904410755969696941501 119232714154033488636353063)
          ·
            refine ⟨178849071231050232954529595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119232714154033488636353063 178849071231050232954529595)
            ·
              refine ⟨268273606846575349431794393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178849071231050232954529595 268273606846575349431794393)
              ·
                refine ⟨201205205134931512073845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268273606846575349431794393 201205205134931512073845795)
                ·
                  refine ⟨301807807702397268110768693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201205205134931512073845795 301807807702397268110768693)
                  ·
                    refine ⟨28294481972099743885384565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 301807807702397268110768693 28294481972099743885384565)
                    ·
                      refine ⟨2652607684884350989254803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28294481972099743885384565 2652607684884350989254803)
                      ·
                        rfl

theorem cell23_5165935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_5165935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5165935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5165935 prefixEnd_5165935 := by exact prefixLift 5165935
  have htrace : WordTrace (prefixWord ++ tailWord_5165935) baseStart_5165935 baseEnd_5165935 := by
    simpa [prefixWord, tailWord_5165935, baseEnd_5165935] using wordTrace_append hprefix tailTrace_5165935
  have hstable : (prefixWord ++ tailWord_5165935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5165935).length < 2 ^ (prefixWord ++ tailWord_5165935).sum := by decide
  have hdescent : baseEnd_5165935 < baseStart_5165935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5165935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166053 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_5166053 : Nat := 118140960795 + 5166053 * 2 ^ 59
def prefixEnd_5166053 : Nat := 4983230072969 + 3 ^ 40 * 5166053 * 2
def baseEnd_5166053 : Nat := 884222758533860509193087

theorem tailTrace_5166053 : CollatzResearch.WordTrace tailWord_5166053 prefixEnd_5166053 884222758533860509193087 := by
  unfold tailWord_5166053
  simp only [CollatzResearch.WordTrace]
  refine ⟨188421432353279747454686813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125614288235519831636457875 188421432353279747454686813)
  ·
    refine ⟨70658037132479905295507555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188421432353279747454686813 70658037132479905295507555)
    ·
      refine ⟨105987055698719857943261333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70658037132479905295507555 105987055698719857943261333)
      ·
        refine ⟨4968143235877493341090375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105987055698719857943261333 4968143235877493341090375)
        ·
          refine ⟨7452214853816240011635563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968143235877493341090375 7452214853816240011635563)
          ·
            refine ⟨11178322280724360017453345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452214853816240011635563 11178322280724360017453345)
            ·
              refine ⟨8383741710543270013090009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11178322280724360017453345 8383741710543270013090009)
              ·
                refine ⟨6287806282907452509817507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8383741710543270013090009 6287806282907452509817507)
                ·
                  refine ⟨9431709424361178764726261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6287806282907452509817507 9431709424361178764726261)
                  ·
                    refine ⟨884222758533860509193087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9431709424361178764726261 884222758533860509193087)
                    ·
                      rfl

theorem cell23_5166053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_5166053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166053 prefixEnd_5166053 := by exact prefixLift 5166053
  have htrace : WordTrace (prefixWord ++ tailWord_5166053) baseStart_5166053 baseEnd_5166053 := by
    simpa [prefixWord, tailWord_5166053, baseEnd_5166053] using wordTrace_append hprefix tailTrace_5166053
  have hstable : (prefixWord ++ tailWord_5166053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166053).length < 2 ^ (prefixWord ++ tailWord_5166053).sum := by decide
  have hdescent : baseEnd_5166053 < baseStart_5166053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166076 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_5166076 : Nat := 118140960795 + 5166076 * 2 ^ 59
def prefixEnd_5166076 : Nat := 4983230072969 + 3 ^ 40 * 5166076 * 2
def baseEnd_5166076 : Nat := 2652680085656634937591655

theorem tailTrace_5166076 : CollatzResearch.WordTrace tailWord_5166076 prefixEnd_5166076 2652680085656634937591655 := by
  unfold tailWord_5166076
  simp only [CollatzResearch.WordTrace]
  refine ⟨94211135616098211191387041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125614847488130948255182721 94211135616098211191387041)
  ·
    refine ⟨70658351712073658393540281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94211135616098211191387041 70658351712073658393540281)
    ·
      refine ⟨52993763784055243795155211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70658351712073658393540281 52993763784055243795155211)
      ·
        refine ⟨79490645676082865692732817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52993763784055243795155211 79490645676082865692732817)
        ·
          refine ⟨59617984257062149269549613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79490645676082865692732817 59617984257062149269549613)
          ·
            refine ⟨22356744096398305976081105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59617984257062149269549613 22356744096398305976081105)
            ·
              refine ⟨16767558072298729482060829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22356744096398305976081105 16767558072298729482060829)
              ·
                refine ⟨6287834277112023555772811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16767558072298729482060829 6287834277112023555772811)
                ·
                  refine ⟨9431751415668035333659217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6287834277112023555772811 9431751415668035333659217)
                  ·
                    refine ⟨7073813561751026500244413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9431751415668035333659217 7073813561751026500244413)
                    ·
                      refine ⟨2652680085656634937591655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7073813561751026500244413 2652680085656634937591655)
                      ·
                        rfl

theorem cell23_5166076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_5166076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166076 prefixEnd_5166076 := by exact prefixLift 5166076
  have htrace : WordTrace (prefixWord ++ tailWord_5166076) baseStart_5166076 baseEnd_5166076 := by
    simpa [prefixWord, tailWord_5166076, baseEnd_5166076] using wordTrace_append hprefix tailTrace_5166076
  have hstable : (prefixWord ++ tailWord_5166076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166076).length < 2 ^ (prefixWord ++ tailWord_5166076).sum := by decide
  have hdescent : baseEnd_5166076 < baseStart_5166076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166090 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_5166090 : Nat := 118140960795 + 5166090 * 2 ^ 59
def prefixEnd_5166090 : Nat := 4983230072969 + 3 ^ 40 * 5166090 * 2
def baseEnd_5166090 : Nat := 2652687274385797882816591

theorem tailTrace_5166090 : CollatzResearch.WordTrace tailWord_5166090 prefixEnd_5166090 2652687274385797882816591 := by
  unfold tailWord_5166090
  simp only [CollatzResearch.WordTrace]
  refine ⟨47105695463536425693445931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125615187902763801849189149 47105695463536425693445931)
  ·
    refine ⟨70658543195304638540168897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47105695463536425693445931 70658543195304638540168897)
    ·
      refine ⟨52993907396478478905126673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70658543195304638540168897 52993907396478478905126673)
      ·
        refine ⟨39745430547358859178845005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52993907396478478905126673 39745430547358859178845005)
        ·
          refine ⟨14904536455259572192066877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39745430547358859178845005 14904536455259572192066877)
          ·
            refine ⟨5589201170722339572025079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14904536455259572192066877 5589201170722339572025079)
            ·
              refine ⟨8383801756083509358037619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589201170722339572025079 8383801756083509358037619)
              ·
                refine ⟨12575702634125264037056429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8383801756083509358037619 12575702634125264037056429)
                ·
                  refine ⟨4715888487796974013896161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12575702634125264037056429 4715888487796974013896161)
                  ·
                    refine ⟨3536916365847730510422121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715888487796974013896161 3536916365847730510422121)
                    ·
                      refine ⟨2652687274385797882816591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536916365847730510422121 2652687274385797882816591)
                      ·
                        rfl

theorem cell23_5166090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_5166090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166090 prefixEnd_5166090 := by exact prefixLift 5166090
  have htrace : WordTrace (prefixWord ++ tailWord_5166090) baseStart_5166090 baseEnd_5166090 := by
    simpa [prefixWord, tailWord_5166090, baseEnd_5166090] using wordTrace_append hprefix tailTrace_5166090
  have hstable : (prefixWord ++ tailWord_5166090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166090).length < 2 ^ (prefixWord ++ tailWord_5166090).sum := by decide
  have hdescent : baseEnd_5166090 < baseStart_5166090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166099 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 7, 2]
def baseStart_5166099 : Nat := 118140960795 + 5166099 * 2 ^ 59
def prefixEnd_5166099 : Nat := 4983230072969 + 3 ^ 40 * 5166099 * 2
def baseEnd_5166099 : Nat := 2652691895711688347604049

theorem tailTrace_5166099 : CollatzResearch.WordTrace tailWord_5166099 prefixEnd_5166099 2652691895711688347604049 := by
  unfold tailWord_5166099
  simp only [CollatzResearch.WordTrace]
  refine ⟨188423110111113097310861351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125615406740742064873907567 188423110111113097310861351)
  ·
    refine ⟨282634665166669645966292027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188423110111113097310861351 282634665166669645966292027)
    ·
      refine ⟨423951997750004468949438041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282634665166669645966292027 423951997750004468949438041)
      ·
        refine ⟨317963998312503351712078531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423951997750004468949438041 317963998312503351712078531)
        ·
          refine ⟨476945997468755027568117797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317963998312503351712078531 476945997468755027568117797)
          ·
            refine ⟨89427374525391567669022087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 476945997468755027568117797 89427374525391567669022087)
            ·
              refine ⟨134141061788087351503533131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89427374525391567669022087 134141061788087351503533131)
              ·
                refine ⟨201211592682131027255299697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134141061788087351503533131 201211592682131027255299697)
                ·
                  refine ⟨150908694511598270441474773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201211592682131027255299697 150908694511598270441474773)
                  ·
                    refine ⟨3536922527615584463472065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 150908694511598270441474773 3536922527615584463472065)
                    ·
                      refine ⟨2652691895711688347604049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536922527615584463472065 2652691895711688347604049)
                      ·
                        rfl

theorem cell23_5166099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7, 2].length) (baseStart_5166099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166099 prefixEnd_5166099 := by exact prefixLift 5166099
  have htrace : WordTrace (prefixWord ++ tailWord_5166099) baseStart_5166099 baseEnd_5166099 := by
    simpa [prefixWord, tailWord_5166099, baseEnd_5166099] using wordTrace_append hprefix tailTrace_5166099
  have hstable : (prefixWord ++ tailWord_5166099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166099).length < 2 ^ (prefixWord ++ tailWord_5166099).sum := by decide
  have hdescent : baseEnd_5166099 < baseStart_5166099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166149 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_5166149 : Nat := 118140960795 + 5166149 * 2 ^ 59
def prefixEnd_5166149 : Nat := 4983230072969 + 3 ^ 40 * 5166149 * 2
def baseEnd_5166149 : Nat := 2652717569744413151978819

theorem tailTrace_5166149 : CollatzResearch.WordTrace tailWord_5166149 prefixEnd_5166149 2652717569744413151978819 := by
  unfold tailWord_5166149
  simp only [CollatzResearch.WordTrace]
  refine ⟨188424933760931955850181501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125616622507287970566787667 188424933760931955850181501)
  ·
    refine ⟨70659350160349483443818063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188424933760931955850181501 70659350160349483443818063)
    ·
      refine ⟨105989025240524225165727095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70659350160349483443818063 105989025240524225165727095)
      ·
        refine ⟨158983537860786337748590643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105989025240524225165727095 158983537860786337748590643)
        ·
          refine ⟨238475306791179506622885965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158983537860786337748590643 238475306791179506622885965)
          ·
            refine ⟨89428240046692314983582237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238475306791179506622885965 89428240046692314983582237)
            ·
              refine ⟨33535590017509618118843339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89428240046692314983582237 33535590017509618118843339)
              ·
                refine ⟨50303385026264427178265009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33535590017509618118843339 50303385026264427178265009)
                ·
                  refine ⟨37727538769698320383698757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50303385026264427178265009 37727538769698320383698757)
                  ·
                    refine ⟨7073913519318435071943517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37727538769698320383698757 7073913519318435071943517)
                    ·
                      refine ⟨2652717569744413151978819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7073913519318435071943517 2652717569744413151978819)
                      ·
                        rfl

theorem cell23_5166149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_5166149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166149 prefixEnd_5166149 := by exact prefixLift 5166149
  have htrace : WordTrace (prefixWord ++ tailWord_5166149) baseStart_5166149 baseEnd_5166149 := by
    simpa [prefixWord, tailWord_5166149, baseEnd_5166149] using wordTrace_append hprefix tailTrace_5166149
  have hstable : (prefixWord ++ tailWord_5166149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166149).length < 2 ^ (prefixWord ++ tailWord_5166149).sum := by decide
  have hdescent : baseEnd_5166149 < baseStart_5166149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166150 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5166150 : Nat := 118140960795 + 5166150 * 2 ^ 59
def prefixEnd_5166150 : Nat := 4983230072969 + 3 ^ 40 * 5166150 * 2
def baseEnd_5166150 : Nat := 2652718083225067648066315

theorem tailTrace_5166150 : CollatzResearch.WordTrace tailWord_5166150 prefixEnd_5166150 2652718083225067648066315 := by
  unfold tailWord_5166150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5888280319810260406905247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125616646822618888680645269 5888280319810260406905247)
  ·
    refine ⟨8832420479715390610357871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5888280319810260406905247 8832420479715390610357871)
    ·
      refine ⟨13248630719573085915536807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8832420479715390610357871 13248630719573085915536807)
      ·
        refine ⟨19872946079359628873305211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13248630719573085915536807 19872946079359628873305211)
        ·
          refine ⟨29809419119039443309957817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19872946079359628873305211 29809419119039443309957817)
          ·
            refine ⟨22357064339279582482468363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29809419119039443309957817 22357064339279582482468363)
            ·
              refine ⟨33535596508919373723702545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22357064339279582482468363 33535596508919373723702545)
              ·
                refine ⟨25151697381689530292776909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33535596508919373723702545 25151697381689530292776909)
                ·
                  refine ⟨9431886518133573859791341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25151697381689530292776909 9431886518133573859791341)
                  ·
                    refine ⟨3536957444300090197421753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9431886518133573859791341 3536957444300090197421753)
                    ·
                      refine ⟨2652718083225067648066315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536957444300090197421753 2652718083225067648066315)
                      ·
                        rfl

theorem cell23_5166150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5166150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166150 prefixEnd_5166150 := by exact prefixLift 5166150
  have htrace : WordTrace (prefixWord ++ tailWord_5166150) baseStart_5166150 baseEnd_5166150 := by
    simpa [prefixWord, tailWord_5166150, baseEnd_5166150] using wordTrace_append hprefix tailTrace_5166150
  have hstable : (prefixWord ++ tailWord_5166150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166150).length < 2 ^ (prefixWord ++ tailWord_5166150).sum := by decide
  have hdescent : baseEnd_5166150 < baseStart_5166150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166179 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 3]
def baseStart_5166179 : Nat := 118140960795 + 5166179 * 2 ^ 59
def prefixEnd_5166179 : Nat := 4983230072969 + 3 ^ 40 * 5166179 * 2
def baseEnd_5166179 : Nat := 2652732974164048034603681

theorem tailTrace_5166179 : CollatzResearch.WordTrace tailWord_5166179 prefixEnd_5166179 2652732974164048034603681 := by
  unfold tailWord_5166179
  simp only [CollatzResearch.WordTrace]
  refine ⟨188426027950823270973773591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125617351967215513982515727 188426027950823270973773591)
  ·
    refine ⟨282639041926234906460660387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188426027950823270973773591 282639041926234906460660387)
    ·
      refine ⟨423958562889352359690990581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282639041926234906460660387 423958562889352359690990581)
      ·
        refine ⟨39746115270876783721030367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 423958562889352359690990581 39746115270876783721030367)
        ·
          refine ⟨59619172906315175581545551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39746115270876783721030367 59619172906315175581545551)
          ·
            refine ⟨89428759359472763372318327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59619172906315175581545551 89428759359472763372318327)
            ·
              refine ⟨134143139039209145058477491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89428759359472763372318327 134143139039209145058477491)
              ·
                refine ⟨201214708558813717587716237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134143139039209145058477491 201214708558813717587716237)
                ·
                  refine ⟨75455515709555144095393589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201214708558813717587716237 75455515709555144095393589)
                  ·
                    refine ⟨7073954597770794758943149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75455515709555144095393589 7073954597770794758943149)
                    ·
                      refine ⟨2652732974164048034603681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7073954597770794758943149 2652732974164048034603681)
                      ·
                        rfl

theorem cell23_5166179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_5166179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166179 prefixEnd_5166179 := by exact prefixLift 5166179
  have htrace : WordTrace (prefixWord ++ tailWord_5166179) baseStart_5166179 baseEnd_5166179 := by
    simpa [prefixWord, tailWord_5166179, baseEnd_5166179] using wordTrace_append hprefix tailTrace_5166179
  have hstable : (prefixWord ++ tailWord_5166179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166179).length < 2 ^ (prefixWord ++ tailWord_5166179).sum := by decide
  have hdescent : baseEnd_5166179 < baseStart_5166179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166184 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5166184 : Nat := 118140960795 + 5166184 * 2 ^ 59
def prefixEnd_5166184 : Nat := 4983230072969 + 3 ^ 40 * 5166184 * 2
def baseEnd_5166184 : Nat := 2652735541567320515041159

theorem tailTrace_5166184 : CollatzResearch.WordTrace tailWord_5166184 prefixEnd_5166184 2652735541567320515041159 := by
  unfold tailWord_5166184
  simp only [CollatzResearch.WordTrace]
  refine ⟨94213105157902578413852803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125617473543870104551803737 94213105157902578413852803)
  ·
    refine ⟨141319657736853867620779205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94213105157902578413852803 141319657736853867620779205)
    ·
      refine ⟨26497435825660100178896101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141319657736853867620779205 26497435825660100178896101)
      ·
        refine ⟨4968269217311268783543019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26497435825660100178896101 4968269217311268783543019)
        ·
          refine ⟨7452403825966903175314529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968269217311268783543019 7452403825966903175314529)
          ·
            refine ⟨5589302869475177381485897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7452403825966903175314529 5589302869475177381485897)
            ·
              refine ⟨4191977152106383036114423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5589302869475177381485897 4191977152106383036114423)
              ·
                refine ⟨6287965728159574554171635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4191977152106383036114423 6287965728159574554171635)
                ·
                  refine ⟨9431948592239361831257453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6287965728159574554171635 9431948592239361831257453)
                  ·
                    refine ⟨3536980722089760686721545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9431948592239361831257453 3536980722089760686721545)
                    ·
                      refine ⟨2652735541567320515041159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536980722089760686721545 2652735541567320515041159)
                      ·
                        rfl

theorem cell23_5166184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5166184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166184 prefixEnd_5166184 := by exact prefixLift 5166184
  have htrace : WordTrace (prefixWord ++ tailWord_5166184) baseStart_5166184 baseEnd_5166184 := by
    simpa [prefixWord, tailWord_5166184, baseEnd_5166184] using wordTrace_append hprefix tailTrace_5166184
  have hstable : (prefixWord ++ tailWord_5166184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166184).length < 2 ^ (prefixWord ++ tailWord_5166184).sum := by decide
  have hdescent : baseEnd_5166184 < baseStart_5166184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166197 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5166197 : Nat := 118140960795 + 5166197 * 2 ^ 59
def prefixEnd_5166197 : Nat := 4983230072969 + 3 ^ 40 * 5166197 * 2
def baseEnd_5166197 : Nat := 2652742216815828964178599

theorem tailTrace_5166197 : CollatzResearch.WordTrace tailWord_5166197 prefixEnd_5166197 2652742216815828964178599 := by
  unfold tailWord_5166197
  simp only [CollatzResearch.WordTrace]
  refine ⟨188426684464758060047928845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125617789643172040031952563 188426684464758060047928845)
  ·
    refine ⟨70660006674284272517973317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188426684464758060047928845 70660006674284272517973317)
    ·
      refine ⟨13248751251428301097119997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70660006674284272517973317 13248751251428301097119997)
      ·
        refine ⟨4968281719285612911419999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13248751251428301097119997 4968281719285612911419999)
        ·
          refine ⟨7452422578928419367129999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968281719285612911419999 7452422578928419367129999)
          ·
            refine ⟨11178633868392629050694999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452422578928419367129999 11178633868392629050694999)
            ·
              refine ⟨16767950802588943576042499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11178633868392629050694999 16767950802588943576042499)
              ·
                refine ⟨25151926203883415364063749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16767950802588943576042499 25151926203883415364063749)
                ·
                  refine ⟨4715986163228140380761953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25151926203883415364063749 4715986163228140380761953)
                  ·
                    refine ⟨3536989622421105285571465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4715986163228140380761953 3536989622421105285571465)
                    ·
                      refine ⟨2652742216815828964178599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3536989622421105285571465 2652742216815828964178599)
                      ·
                        rfl

theorem cell23_5166197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5166197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166197 prefixEnd_5166197 := by exact prefixLift 5166197
  have htrace : WordTrace (prefixWord ++ tailWord_5166197) baseStart_5166197 baseEnd_5166197 := by
    simpa [prefixWord, tailWord_5166197, baseEnd_5166197] using wordTrace_append hprefix tailTrace_5166197
  have hstable : (prefixWord ++ tailWord_5166197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166197).length < 2 ^ (prefixWord ++ tailWord_5166197).sum := by decide
  have hdescent : baseEnd_5166197 < baseStart_5166197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166199 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 4, 5]
def baseStart_5166199 : Nat := 118140960795 + 5166199 * 2 ^ 59
def prefixEnd_5166199 : Nat := 4983230072969 + 3 ^ 40 * 5166199 * 2
def baseEnd_5166199 : Nat := 884247747925712652117863

theorem tailTrace_5166199 : CollatzResearch.WordTrace tailWord_5166199 prefixEnd_5166199 884247747925712652117863 := by
  unfold tailWord_5166199
  simp only [CollatzResearch.WordTrace]
  refine ⟨188426757410750814389501651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125617838273833876259667767 188426757410750814389501651)
  ·
    refine ⟨282640136116126221584252477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188426757410750814389501651 282640136116126221584252477)
    ·
      refine ⟨105990051043547333094094679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 282640136116126221584252477 105990051043547333094094679)
      ·
        refine ⟨158985076565320999641142019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105990051043547333094094679 158985076565320999641142019)
        ·
          refine ⟨238477614847981499461713029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158985076565320999641142019 238477614847981499461713029)
          ·
            refine ⟨44714552783996531149071193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238477614847981499461713029 44714552783996531149071193)
            ·
              refine ⟨33535914587997398361803395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44714552783996531149071193 33535914587997398361803395)
              ·
                refine ⟨50303871881996097542705093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33535914587997398361803395 50303871881996097542705093)
                ·
                  refine ⟨9431975977874268289257205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50303871881996097542705093 9431975977874268289257205)
                  ·
                    refine ⟨884247747925712652117863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9431975977874268289257205 884247747925712652117863)
                    ·
                      rfl

theorem cell23_5166199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_5166199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166199 prefixEnd_5166199 := by exact prefixLift 5166199
  have htrace : WordTrace (prefixWord ++ tailWord_5166199) baseStart_5166199 baseEnd_5166199 := by
    simpa [prefixWord, tailWord_5166199, baseEnd_5166199] using wordTrace_append hprefix tailTrace_5166199
  have hstable : (prefixWord ++ tailWord_5166199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166199).length < 2 ^ (prefixWord ++ tailWord_5166199).sum := by decide
  have hdescent : baseEnd_5166199 < baseStart_5166199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166236 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5166236 : Nat := 118140960795 + 5166236 * 2 ^ 59
def prefixEnd_5166236 : Nat := 4983230072969 + 3 ^ 40 * 5166236 * 2
def baseEnd_5166236 : Nat := 2652762242561354311590919

theorem tailTrace_5166236 : CollatzResearch.WordTrace tailWord_5166236 prefixEnd_5166236 2652762242561354311590919 := by
  unfold tailWord_5166236
  simp only [CollatzResearch.WordTrace]
  refine ⟨94214053455808384854299281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125618737941077846472399041 94214053455808384854299281)
  ·
    refine ⟨70660540091856288640724461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94214053455808384854299281 70660540091856288640724461)
    ·
      refine ⟨26497702534446108240271673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70660540091856288640724461 26497702534446108240271673)
      ·
        refine ⟨19873276900834581180203755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26497702534446108240271673 19873276900834581180203755)
        ·
          refine ⟨29809915351251871770305633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19873276900834581180203755 29809915351251871770305633)
          ·
            refine ⟨22357436513438903827729225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29809915351251871770305633 22357436513438903827729225)
            ·
              refine ⟨16768077385079177870796919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22357436513438903827729225 16768077385079177870796919)
              ·
                refine ⟨25152116077618766806195379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16768077385079177870796919 25152116077618766806195379)
                ·
                  refine ⟨37728174116428150209293069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25152116077618766806195379 37728174116428150209293069)
                  ·
                    refine ⟨14148065293660556328484901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37728174116428150209293069 14148065293660556328484901)
                    ·
                      refine ⟨2652762242561354311590919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14148065293660556328484901 2652762242561354311590919)
                      ·
                        rfl

theorem cell23_5166236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5166236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166236 prefixEnd_5166236 := by exact prefixLift 5166236
  have htrace : WordTrace (prefixWord ++ tailWord_5166236) baseStart_5166236 baseEnd_5166236 := by
    simpa [prefixWord, tailWord_5166236, baseEnd_5166236] using wordTrace_append hprefix tailTrace_5166236
  have hstable : (prefixWord ++ tailWord_5166236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166236).length < 2 ^ (prefixWord ++ tailWord_5166236).sum := by decide
  have hdescent : baseEnd_5166236 < baseStart_5166236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166256 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3]
def baseStart_5166256 : Nat := 118140960795 + 5166256 * 2 ^ 59
def prefixEnd_5166256 : Nat := 4983230072969 + 3 ^ 40 * 5166256 * 2
def baseEnd_5166256 : Nat := 2652772512174444233340827

theorem tailTrace_5166256 : CollatzResearch.WordTrace tailWord_5166256 prefixEnd_5166256 2652772512174444233340827 := by
  unfold tailWord_5166256
  simp only [CollatzResearch.WordTrace]
  refine ⟨94214418185772156562163311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125619224247696208749551081 94214418185772156562163311)
  ·
    refine ⟨141321627278658234843244967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94214418185772156562163311 141321627278658234843244967)
    ·
      refine ⟨211982440917987352264867451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141321627278658234843244967 211982440917987352264867451)
      ·
        refine ⟨317973661376981028397301177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211982440917987352264867451 317973661376981028397301177)
        ·
          refine ⟨238480246032735771297975883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317973661376981028397301177 238480246032735771297975883)
          ·
            refine ⟨357720369049103656946963825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238480246032735771297975883 357720369049103656946963825)
            ·
              refine ⟨268290276786827742710222869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357720369049103656946963825 268290276786827742710222869)
              ·
                refine ⟨12576106724382550439541697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 268290276786827742710222869 12576106724382550439541697)
                ·
                  refine ⟨9432080043286912829656273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12576106724382550439541697 9432080043286912829656273)
                  ·
                    refine ⟨7074060032465184622242205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9432080043286912829656273 7074060032465184622242205)
                    ·
                      refine ⟨2652772512174444233340827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7074060032465184622242205 2652772512174444233340827)
                      ·
                        rfl

theorem cell23_5166256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_5166256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166256 prefixEnd_5166256 := by exact prefixLift 5166256
  have htrace : WordTrace (prefixWord ++ tailWord_5166256) baseStart_5166256 baseEnd_5166256 := by
    simpa [prefixWord, tailWord_5166256, baseEnd_5166256] using wordTrace_append hprefix tailTrace_5166256
  have hstable : (prefixWord ++ tailWord_5166256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166256).length < 2 ^ (prefixWord ++ tailWord_5166256).sum := by decide
  have hdescent : baseEnd_5166256 < baseStart_5166256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166259 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 8]
def baseStart_5166259 : Nat := 118140960795 + 5166259 * 2 ^ 59
def prefixEnd_5166259 : Nat := 4983230072969 + 3 ^ 40 * 5166259 * 2
def baseEnd_5166259 : Nat := 294752672512934191289257

theorem tailTrace_5166259 : CollatzResearch.WordTrace tailWord_5166259 prefixEnd_5166259 294752672512934191289257 := by
  unfold tailWord_5166259
  simp only [CollatzResearch.WordTrace]
  refine ⟨188428945790533444636685831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125619297193688963091123887 188428945790533444636685831)
  ·
    refine ⟨282643418685800166955028747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188428945790533444636685831 282643418685800166955028747)
    ·
      refine ⟨423965128028700250432543121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282643418685800166955028747 423965128028700250432543121)
      ·
        refine ⟨317973846021525187824407341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423965128028700250432543121 317973846021525187824407341)
        ·
          refine ⟨119240192258071945434152753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317973846021525187824407341 119240192258071945434152753)
          ·
            refine ⟨89430144193553959075614565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119240192258071945434152753 89430144193553959075614565)
            ·
              refine ⟨16768152036291367326677731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89430144193553959075614565 16768152036291367326677731)
              ·
                refine ⟨25152228054437050990016597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16768152036291367326677731 25152228054437050990016597)
                ·
                  refine ⟨294752672512934191289257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25152228054437050990016597 294752672512934191289257)
                  ·
                    rfl

theorem cell23_5166259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 8].length) (baseStart_5166259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166259 prefixEnd_5166259 := by exact prefixLift 5166259
  have htrace : WordTrace (prefixWord ++ tailWord_5166259) baseStart_5166259 baseEnd_5166259 := by
    simpa [prefixWord, tailWord_5166259, baseEnd_5166259] using wordTrace_append hprefix tailTrace_5166259
  have hstable : (prefixWord ++ tailWord_5166259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166259).length < 2 ^ (prefixWord ++ tailWord_5166259).sum := by decide
  have hdescent : baseEnd_5166259 < baseStart_5166259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166279 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_5166279 : Nat := 118140960795 + 5166279 * 2 ^ 59
def prefixEnd_5166279 : Nat := 4983230072969 + 3 ^ 40 * 5166279 * 2
def baseEnd_5166279 : Nat := 2652784322229497643353221

theorem tailTrace_5166279 : CollatzResearch.WordTrace tailWord_5166279 prefixEnd_5166279 2652784322229497643353221 := by
  unfold tailWord_5166279
  simp only [CollatzResearch.WordTrace]
  refine ⟨188429675250460988052413891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125619783500307325368275927 188429675250460988052413891)
  ·
    refine ⟨282644512875691482078620837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188429675250460988052413891 282644512875691482078620837)
    ·
      refine ⟨52995846164192152889741407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 282644512875691482078620837 52995846164192152889741407)
      ·
        refine ⟨79493769246288229334612111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52995846164192152889741407 79493769246288229334612111)
        ·
          refine ⟨119240653869432344001918167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79493769246288229334612111 119240653869432344001918167)
          ·
            refine ⟨178860980804148516002877251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119240653869432344001918167 178860980804148516002877251)
            ·
              refine ⟨268291471206222774004315877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178860980804148516002877251 268291471206222774004315877)
              ·
                refine ⟨50304650851166770125809227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268291471206222774004315877 50304650851166770125809227)
                ·
                  refine ⟨75456976276750155188713841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50304650851166770125809227 75456976276750155188713841)
                  ·
                    refine ⟨56592732207562616391535381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75456976276750155188713841 56592732207562616391535381)
                    ·
                      refine ⟨2652784322229497643353221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56592732207562616391535381 2652784322229497643353221)
                      ·
                        rfl

theorem cell23_5166279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_5166279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166279 prefixEnd_5166279 := by exact prefixLift 5166279
  have htrace : WordTrace (prefixWord ++ tailWord_5166279) baseStart_5166279 baseEnd_5166279 := by
    simpa [prefixWord, tailWord_5166279, baseEnd_5166279] using wordTrace_append hprefix tailTrace_5166279
  have hstable : (prefixWord ++ tailWord_5166279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166279).length < 2 ^ (prefixWord ++ tailWord_5166279).sum := by decide
  have hdescent : baseEnd_5166279 < baseStart_5166279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166336 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 6, 4]
def baseStart_5166336 : Nat := 118140960795 + 5166336 * 2 ^ 59
def prefixEnd_5166336 : Nat := 4983230072969 + 3 ^ 40 * 5166336 * 2
def baseEnd_5166336 : Nat := 884271196875601306780153

theorem tailTrace_5166336 : CollatzResearch.WordTrace tailWord_5166336 prefixEnd_5166336 884271196875601306780153 := by
  unfold tailWord_5166336
  simp only [CollatzResearch.WordTrace]
  refine ⟨94215877105627243393619431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125621169474169657858159241 94215877105627243393619431)
  ·
    refine ⟨141323815658440865090429147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94215877105627243393619431 141323815658440865090429147)
    ·
      refine ⟨211985723487661297635643721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141323815658440865090429147 211985723487661297635643721)
      ·
        refine ⟨158989292615745973226732791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211985723487661297635643721 158989292615745973226732791)
        ·
          refine ⟨238483938923618959840099187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158989292615745973226732791 238483938923618959840099187)
          ·
            refine ⟨357725908385428439760148781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238483938923618959840099187 357725908385428439760148781)
            ·
              refine ⟨134147215644535664910055793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357725908385428439760148781 134147215644535664910055793)
              ·
                refine ⟨100610411733401748682541845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134147215644535664910055793 100610411733401748682541845)
                ·
                  refine ⟨4716113050003206969494149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100610411733401748682541845 4716113050003206969494149)
                  ·
                    refine ⟨884271196875601306780153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4716113050003206969494149 884271196875601306780153)
                    ·
                      rfl

theorem cell23_5166336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_5166336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166336 prefixEnd_5166336 := by exact prefixLift 5166336
  have htrace : WordTrace (prefixWord ++ tailWord_5166336) baseStart_5166336 baseEnd_5166336 := by
    simpa [prefixWord, tailWord_5166336, baseEnd_5166336] using wordTrace_append hprefix tailTrace_5166336
  have hstable : (prefixWord ++ tailWord_5166336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166336).length < 2 ^ (prefixWord ++ tailWord_5166336).sum := by decide
  have hdescent : baseEnd_5166336 < baseStart_5166336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166360 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 1, 1, 4]
def baseStart_5166360 : Nat := 118140960795 + 5166360 * 2 ^ 59
def prefixEnd_5166360 : Nat := 4983230072969 + 3 ^ 40 * 5166360 * 2
def baseEnd_5166360 : Nat := 2652825914162511826440349

theorem tailTrace_5166360 : CollatzResearch.WordTrace tailWord_5166360 prefixEnd_5166360 2652825914162511826440349 := by
  unfold tailWord_5166360
  simp only [CollatzResearch.WordTrace]
  refine ⟨94216314781583769443056267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125621753042111692590741689 94216314781583769443056267)
  ·
    refine ⟨141324472172375654164584401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94216314781583769443056267 141324472172375654164584401)
    ·
      refine ⟨105993354129281740623438301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141324472172375654164584401 105993354129281740623438301)
      ·
        refine ⟨39747507798480652733789363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105993354129281740623438301 39747507798480652733789363)
        ·
          refine ⟨59621261697720979100684045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39747507798480652733789363 59621261697720979100684045)
          ·
            refine ⟨22357973136645367162756517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59621261697720979100684045 22357973136645367162756517)
            ·
              refine ⟨4192119963121006343016847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22357973136645367162756517 4192119963121006343016847)
              ·
                refine ⟨6288179944681509514525271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192119963121006343016847 6288179944681509514525271)
                ·
                  refine ⟨9432269917022264271787907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6288179944681509514525271 9432269917022264271787907)
                  ·
                    refine ⟨14148404875533396407681861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9432269917022264271787907 14148404875533396407681861)
                    ·
                      refine ⟨2652825914162511826440349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14148404875533396407681861 2652825914162511826440349)
                      ·
                        rfl

theorem cell23_5166360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_5166360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166360 prefixEnd_5166360 := by exact prefixLift 5166360
  have htrace : WordTrace (prefixWord ++ tailWord_5166360) baseStart_5166360 baseEnd_5166360 := by
    simpa [prefixWord, tailWord_5166360, baseEnd_5166360] using wordTrace_append hprefix tailTrace_5166360
  have hstable : (prefixWord ++ tailWord_5166360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166360).length < 2 ^ (prefixWord ++ tailWord_5166360).sum := by decide
  have hdescent : baseEnd_5166360 < baseStart_5166360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166370 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_5166370 : Nat := 118140960795 + 5166370 * 2 ^ 59
def prefixEnd_5166370 : Nat := 4983230072969 + 3 ^ 40 * 5166370 * 2
def baseEnd_5166370 : Nat := 884277016323018929105101

theorem tailTrace_5166370 : CollatzResearch.WordTrace tailWord_5166370 prefixEnd_5166370 884277016323018929105101 := by
  unfold tailWord_5166370
  simp only [CollatzResearch.WordTrace]
  refine ⟨47108248573282827648494141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125621996195420873729317709 47108248573282827648494141)
  ·
    refine ⟨17665593214981060368185303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47108248573282827648494141 17665593214981060368185303)
    ·
      refine ⟨26498389822471590552277955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17665593214981060368185303 26498389822471590552277955)
      ·
        refine ⟨39747584733707385828416933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26498389822471590552277955 39747584733707385828416933)
        ·
          refine ⟨7452672137570134842828175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39747584733707385828416933 7452672137570134842828175)
          ·
            refine ⟨11179008206355202264242263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452672137570134842828175 11179008206355202264242263)
            ·
              refine ⟨16768512309532803396363395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11179008206355202264242263 16768512309532803396363395)
              ·
                refine ⟨25152768464299205094545093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16768512309532803396363395 25152768464299205094545093)
                ·
                  refine ⟨4716144087056100955227205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25152768464299205094545093 4716144087056100955227205)
                  ·
                    refine ⟨884277016323018929105101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4716144087056100955227205 884277016323018929105101)
                    ·
                      rfl

theorem cell23_5166370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_5166370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166370 prefixEnd_5166370 := by exact prefixLift 5166370
  have htrace : WordTrace (prefixWord ++ tailWord_5166370) baseStart_5166370 baseEnd_5166370 := by
    simpa [prefixWord, tailWord_5166370, baseEnd_5166370] using wordTrace_append hprefix tailTrace_5166370
  have hstable : (prefixWord ++ tailWord_5166370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166370).length < 2 ^ (prefixWord ++ tailWord_5166370).sum := by decide
  have hdescent : baseEnd_5166370 < baseStart_5166370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166426 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_5166426 : Nat := 118140960795 + 5166426 * 2 ^ 59
def prefixEnd_5166426 : Nat := 4983230072969 + 3 ^ 40 * 5166426 * 2
def baseEnd_5166426 : Nat := 884286601295236189405015

theorem tailTrace_5166426 : CollatzResearch.WordTrace tailWord_5166426 prefixEnd_5166426 884286601295236189405015 := by
  unfold tailWord_5166426
  simp only [CollatzResearch.WordTrace]
  refine ⟨47108759195232108039503783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125623357853952288105343421 47108759195232108039503783)
  ·
    refine ⟨70663138792848162059255675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47108759195232108039503783 70663138792848162059255675)
    ·
      refine ⟨105994708189272243088883513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70663138792848162059255675 105994708189272243088883513)
      ·
        refine ⟨79496031141954182316662635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105994708189272243088883513 79496031141954182316662635)
        ·
          refine ⟨119244046712931273474993953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79496031141954182316662635 119244046712931273474993953)
          ·
            refine ⟨89433035034698455106245465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119244046712931273474993953 89433035034698455106245465)
            ·
              refine ⟨67074776276023841329684099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89433035034698455106245465 67074776276023841329684099)
              ·
                refine ⟨100612164414035761994526149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67074776276023841329684099 100612164414035761994526149)
                ·
                  refine ⟨18864780827631705373973653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100612164414035761994526149 18864780827631705373973653)
                  ·
                    refine ⟨884286601295236189405015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18864780827631705373973653 884286601295236189405015)
                    ·
                      rfl

theorem cell23_5166426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_5166426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166426 prefixEnd_5166426 := by exact prefixLift 5166426
  have htrace : WordTrace (prefixWord ++ tailWord_5166426) baseStart_5166426 baseEnd_5166426 := by
    simpa [prefixWord, tailWord_5166426, baseEnd_5166426] using wordTrace_append hprefix tailTrace_5166426
  have hstable : (prefixWord ++ tailWord_5166426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166426).length < 2 ^ (prefixWord ++ tailWord_5166426).sum := by decide
  have hdescent : baseEnd_5166426 < baseStart_5166426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166444 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 3]
def baseStart_5166444 : Nat := 118140960795 + 5166444 * 2 ^ 59
def prefixEnd_5166444 : Nat := 4983230072969 + 3 ^ 40 * 5166444 * 2
def baseEnd_5166444 : Nat := 2652869046537489497789963

theorem tailTrace_5166444 : CollatzResearch.WordTrace tailWord_5166444 prefixEnd_5166444 2652869046537489497789963 := by
  unfold tailWord_5166444
  simp only [CollatzResearch.WordTrace]
  refine ⟨94217846647431610616085193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125623795529908814154780257 94217846647431610616085193)
  ·
    refine ⟨70663384985573707962063895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94217846647431610616085193 70663384985573707962063895)
    ·
      refine ⟨105995077478360561943095843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70663384985573707962063895 105995077478360561943095843)
      ·
        refine ⟨158992616217540842914643765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105995077478360561943095843 158992616217540842914643765)
        ·
          refine ⟨14905557770394454023247853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158992616217540842914643765 14905557770394454023247853)
          ·
            refine ⟨5589584163897920258717945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14905557770394454023247853 5589584163897920258717945)
            ·
              refine ⟨4192188122923440194038459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5589584163897920258717945 4192188122923440194038459)
              ·
                refine ⟨6288282184385160291057689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4192188122923440194038459 6288282184385160291057689)
                ·
                  refine ⟨4716211638288870218293267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6288282184385160291057689 4716211638288870218293267)
                  ·
                    refine ⟨7074317457433305327439901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4716211638288870218293267 7074317457433305327439901)
                    ·
                      refine ⟨2652869046537489497789963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7074317457433305327439901 2652869046537489497789963)
                      ·
                        rfl

theorem cell23_5166444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_5166444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166444 prefixEnd_5166444 := by exact prefixLift 5166444
  have htrace : WordTrace (prefixWord ++ tailWord_5166444) baseStart_5166444 baseEnd_5166444 := by
    simpa [prefixWord, tailWord_5166444, baseEnd_5166444] using wordTrace_append hprefix tailTrace_5166444
  have hstable : (prefixWord ++ tailWord_5166444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166444).length < 2 ^ (prefixWord ++ tailWord_5166444).sum := by decide
  have hdescent : baseEnd_5166444 < baseStart_5166444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166450 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_5166450 : Nat := 118140960795 + 5166450 * 2 ^ 59
def prefixEnd_5166450 : Nat := 4983230072969 + 3 ^ 40 * 5166450 * 2
def baseEnd_5166450 : Nat := 2652872127421416474314935

theorem tailTrace_5166450 : CollatzResearch.WordTrace tailWord_5166450 prefixEnd_5166450 2652872127421416474314935 := by
  unfold tailWord_5166450
  simp only [CollatzResearch.WordTrace]
  refine ⟨47108978033210371064222201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125623941421894322837925869 47108978033210371064222201)
  ·
    refine ⟨35331733524907778298166651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47108978033210371064222201 35331733524907778298166651)
    ·
      refine ⟨52997600287361667447249977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35331733524907778298166651 52997600287361667447249977)
      ·
        refine ⟨39748200215521250585437483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52997600287361667447249977 39748200215521250585437483)
        ·
          refine ⟨59622300323281875878156225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39748200215521250585437483 59622300323281875878156225)
          ·
            refine ⟨44716725242461406908617169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59622300323281875878156225 44716725242461406908617169)
            ·
              refine ⟨33537543931846055181462877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44716725242461406908617169 33537543931846055181462877)
              ·
                refine ⟨12576578974442270693048579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33537543931846055181462877 12576578974442270693048579)
                ·
                  refine ⟨18864868461663406039572869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12576578974442270693048579 18864868461663406039572869)
                  ·
                    refine ⟨3537162836561888632419913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18864868461663406039572869 3537162836561888632419913)
                    ·
                      refine ⟨2652872127421416474314935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537162836561888632419913 2652872127421416474314935)
                      ·
                        rfl

theorem cell23_5166450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_5166450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166450 prefixEnd_5166450 := by exact prefixLift 5166450
  have htrace : WordTrace (prefixWord ++ tailWord_5166450) baseStart_5166450 baseEnd_5166450 := by
    simpa [prefixWord, tailWord_5166450, baseEnd_5166450] using wordTrace_append hprefix tailTrace_5166450
  have hstable : (prefixWord ++ tailWord_5166450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166450).length < 2 ^ (prefixWord ++ tailWord_5166450).sum := by decide
  have hdescent : baseEnd_5166450 < baseStart_5166450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166484 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_5166484 : Nat := 118140960795 + 5166484 * 2 ^ 59
def prefixEnd_5166484 : Nat := 4983230072969 + 3 ^ 40 * 5166484 * 2
def baseEnd_5166484 : Nat := 2652889585763669341289779

theorem tailTrace_5166484 : CollatzResearch.WordTrace tailWord_5166484 prefixEnd_5166484 2652889585763669341289779 := by
  unfold tailWord_5166484
  simp only [CollatzResearch.WordTrace]
  refine ⟨94218576107359154031813253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125624768143145538709084337 94218576107359154031813253)
  ·
    refine ⟨17665983020129841380964985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94218576107359154031813253 17665983020129841380964985)
    ·
      refine ⟨13249487265097381035723739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17665983020129841380964985 13249487265097381035723739)
      ·
        refine ⟨19874230897646071553585609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13249487265097381035723739 19874230897646071553585609)
        ·
          refine ⟨14905673173234553665189207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19874230897646071553585609 14905673173234553665189207)
          ·
            refine ⟨22358509759851830497783811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14905673173234553665189207 22358509759851830497783811)
            ·
              refine ⟨33537764639777745746675717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22358509759851830497783811 33537764639777745746675717)
              ·
                refine ⟨6288330869958327327501697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33537764639777745746675717 6288330869958327327501697)
                ·
                  refine ⟨4716248152468745495626273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6288330869958327327501697 4716248152468745495626273)
                  ·
                    refine ⟨3537186114351559121719705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4716248152468745495626273 3537186114351559121719705)
                    ·
                      refine ⟨2652889585763669341289779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537186114351559121719705 2652889585763669341289779)
                      ·
                        rfl

theorem cell23_5166484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_5166484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166484 prefixEnd_5166484 := by exact prefixLift 5166484
  have htrace : WordTrace (prefixWord ++ tailWord_5166484) baseStart_5166484 baseEnd_5166484 := by
    simpa [prefixWord, tailWord_5166484, baseEnd_5166484] using wordTrace_append hprefix tailTrace_5166484
  have hstable : (prefixWord ++ tailWord_5166484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166484).length < 2 ^ (prefixWord ++ tailWord_5166484).sum := by decide
  have hdescent : baseEnd_5166484 < baseStart_5166484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166490 : List Nat := [3, 1, 1, 4, 1, 1, 3, 4, 5]
def baseStart_5166490 : Nat := 118140960795 + 5166490 * 2 ^ 59
def prefixEnd_5166490 : Nat := 4983230072969 + 3 ^ 40 * 5166490 * 2
def baseEnd_5166490 : Nat := 294765851849732924201639

theorem tailTrace_5166490 : CollatzResearch.WordTrace tailWord_5166490 prefixEnd_5166490 294765851849732924201639 := by
  unfold tailWord_5166490
  simp only [CollatzResearch.WordTrace]
  refine ⟨47109342763174142772086231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125624914035131047392229949 47109342763174142772086231)
  ·
    refine ⟨70664014144761214158129347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47109342763174142772086231 70664014144761214158129347)
    ·
      refine ⟨105996021217141821237194021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70664014144761214158129347 105996021217141821237194021)
      ·
        refine ⟨19874253978214091481973879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105996021217141821237194021 19874253978214091481973879)
        ·
          refine ⟨29811380967321137222960819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19874253978214091481973879 29811380967321137222960819)
          ·
            refine ⟨44717071450981705834441229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29811380967321137222960819 44717071450981705834441229)
            ·
              refine ⟨16768901794118139687915461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44717071450981705834441229 16768901794118139687915461)
              ·
                refine ⟨3144169086397151191484149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16768901794118139687915461 3144169086397151191484149)
                ·
                  refine ⟨294765851849732924201639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3144169086397151191484149 294765851849732924201639)
                  ·
                    rfl

theorem cell23_5166490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_5166490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166490 prefixEnd_5166490 := by exact prefixLift 5166490
  have htrace : WordTrace (prefixWord ++ tailWord_5166490) baseStart_5166490 baseEnd_5166490 := by
    simpa [prefixWord, tailWord_5166490, baseEnd_5166490] using wordTrace_append hprefix tailTrace_5166490
  have hstable : (prefixWord ++ tailWord_5166490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166490).length < 2 ^ (prefixWord ++ tailWord_5166490).sum := by decide
  have hdescent : baseEnd_5166490 < baseStart_5166490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166503 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5166503 : Nat := 118140960795 + 5166503 * 2 ^ 59
def prefixEnd_5166503 : Nat := 4983230072969 + 3 ^ 40 * 5166503 * 2
def baseEnd_5166503 : Nat := 884299780632034922317397

theorem tailTrace_5166503 : CollatzResearch.WordTrace tailWord_5166503 prefixEnd_5166503 884299780632034922317397 := by
  unfold tailWord_5166503
  simp only [CollatzResearch.WordTrace]
  refine ⟨188437845201649474308568163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125625230134432982872378775 188437845201649474308568163)
  ·
    refine ⟨282656767802474211462852245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188437845201649474308568163 282656767802474211462852245)
    ·
      refine ⟨13249535990740978662321199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 282656767802474211462852245 13249535990740978662321199)
      ·
        refine ⟨19874303986111467993481799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13249535990740978662321199 19874303986111467993481799)
        ·
          refine ⟨29811455979167201990222699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19874303986111467993481799 29811455979167201990222699)
          ·
            refine ⟨44717183968750802985334049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29811455979167201990222699 44717183968750802985334049)
            ·
              refine ⟨33537887976563102239000537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44717183968750802985334049 33537887976563102239000537)
              ·
                refine ⟨25153415982422326679250403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33537887976563102239000537 25153415982422326679250403)
                ·
                  refine ⟨37730123973633490018875605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25153415982422326679250403 37730123973633490018875605)
                  ·
                    refine ⟨884299780632034922317397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37730123973633490018875605 884299780632034922317397)
                    ·
                      rfl

theorem cell23_5166503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5166503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166503 prefixEnd_5166503 := by exact prefixLift 5166503
  have htrace : WordTrace (prefixWord ++ tailWord_5166503) baseStart_5166503 baseEnd_5166503 := by
    simpa [prefixWord, tailWord_5166503, baseEnd_5166503] using wordTrace_append hprefix tailTrace_5166503
  have hstable : (prefixWord ++ tailWord_5166503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166503).length < 2 ^ (prefixWord ++ tailWord_5166503).sum := by decide
  have hdescent : baseEnd_5166503 < baseStart_5166503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166557 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_5166557 : Nat := 118140960795 + 5166557 * 2 ^ 59
def prefixEnd_5166557 : Nat := 4983230072969 + 3 ^ 40 * 5166557 * 2
def baseEnd_5166557 : Nat := 2652927069851447555676943

theorem tailTrace_5166557 : CollatzResearch.WordTrace tailWord_5166557 prefixEnd_5166557 2652927069851447555676943 := by
  unfold tailWord_5166557
  simp only [CollatzResearch.WordTrace]
  refine ⟨188439814743453841531033925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125626543162302561020689283 188439814743453841531033925)
  ·
    refine ⟨35332465264397595287068861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188439814743453841531033925 35332465264397595287068861)
    ·
      refine ⟨13249674474149098232650823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35332465264397595287068861 13249674474149098232650823)
      ·
        refine ⟨19874511711223647348976235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13249674474149098232650823 19874511711223647348976235)
        ·
          refine ⟨29811767566835471023464353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19874511711223647348976235 29811767566835471023464353)
          ·
            refine ⟨22358825675126603267598265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29811767566835471023464353 22358825675126603267598265)
            ·
              refine ⟨16769119256344952450698699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22358825675126603267598265 16769119256344952450698699)
              ·
                refine ⟨25153678884517428676048049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16769119256344952450698699 25153678884517428676048049)
                ·
                  refine ⟨18865259163388071507036037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25153678884517428676048049 18865259163388071507036037)
                  ·
                    refine ⟨3537236093135263407569257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18865259163388071507036037 3537236093135263407569257)
                    ·
                      refine ⟨2652927069851447555676943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537236093135263407569257 2652927069851447555676943)
                      ·
                        rfl

theorem cell23_5166557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_5166557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166557 prefixEnd_5166557 := by exact prefixLift 5166557
  have htrace : WordTrace (prefixWord ++ tailWord_5166557) baseStart_5166557 baseEnd_5166557 := by
    simpa [prefixWord, tailWord_5166557, baseEnd_5166557] using wordTrace_append hprefix tailTrace_5166557
  have hstable : (prefixWord ++ tailWord_5166557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166557).length < 2 ^ (prefixWord ++ tailWord_5166557).sum := by decide
  have hdescent : baseEnd_5166557 < baseStart_5166557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166584 : List Nat := [2, 1, 2, 1, 1, 7, 1, 3, 1, 4]
def baseStart_5166584 : Nat := 118140960795 + 5166584 * 2 ^ 59
def prefixEnd_5166584 : Nat := 4983230072969 + 3 ^ 40 * 5166584 * 2
def baseEnd_5166584 : Nat := 884313644609706316679773

theorem tailTrace_5166584 : CollatzResearch.WordTrace tailWord_5166584 prefixEnd_5166584 884313644609706316679773 := by
  unfold tailWord_5166584
  simp only [CollatzResearch.WordTrace]
  refine ⟨94220399757178012571133403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125627199676237350094844537 94220399757178012571133403)
  ·
    refine ⟨141330599635767018856700105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94220399757178012571133403 141330599635767018856700105)
    ·
      refine ⟨105997949726825264142525079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141330599635767018856700105 105997949726825264142525079)
      ·
        refine ⟨158996924590237896213787619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105997949726825264142525079 158996924590237896213787619)
        ·
          refine ⟨238495386885356844320681429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158996924590237896213787619 238495386885356844320681429)
          ·
            refine ⟨5589735630125551038765971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 238495386885356844320681429 5589735630125551038765971)
            ·
              refine ⟨8384603445188326558148957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589735630125551038765971 8384603445188326558148957)
              ·
                refine ⟨3144226291945622459305859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8384603445188326558148957 3144226291945622459305859)
                ·
                  refine ⟨4716339437918433688958789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144226291945622459305859 4716339437918433688958789)
                  ·
                    refine ⟨884313644609706316679773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4716339437918433688958789 884313644609706316679773)
                    ·
                      rfl

theorem cell23_5166584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_5166584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166584 prefixEnd_5166584 := by exact prefixLift 5166584
  have htrace : WordTrace (prefixWord ++ tailWord_5166584) baseStart_5166584 baseEnd_5166584 := by
    simpa [prefixWord, tailWord_5166584, baseEnd_5166584] using wordTrace_append hprefix tailTrace_5166584
  have hstable : (prefixWord ++ tailWord_5166584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166584).length < 2 ^ (prefixWord ++ tailWord_5166584).sum := by decide
  have hdescent : baseEnd_5166584 < baseStart_5166584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166594 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5166594 : Nat := 118140960795 + 5166594 * 2 ^ 59
def prefixEnd_5166594 : Nat := 4983230072969 + 3 ^ 40 * 5166594 * 2
def baseEnd_5166594 : Nat := 2652946068635663910914273

theorem tailTrace_5166594 : CollatzResearch.WordTrace tailWord_5166594 prefixEnd_5166594 2652946068635663910914273 := by
  unfold tailWord_5166594
  simp only [CollatzResearch.WordTrace]
  refine ⟨47110291061079949212532709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125627442829546531233420557 47110291061079949212532709)
  ·
    refine ⟨8833179573952490477349883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47110291061079949212532709 8833179573952490477349883)
    ·
      refine ⟨13249769360928735716024825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8833179573952490477349883 13249769360928735716024825)
      ·
        refine ⟨9937327020696551787018619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13249769360928735716024825 9937327020696551787018619)
        ·
          refine ⟨14905990531044827680527929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9937327020696551787018619 14905990531044827680527929)
          ·
            refine ⟨11179492898283620760395947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14905990531044827680527929 11179492898283620760395947)
            ·
              refine ⟨16769239347425431140593921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11179492898283620760395947 16769239347425431140593921)
              ·
                refine ⟨12576929510569073355445441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16769239347425431140593921 12576929510569073355445441)
                ·
                  refine ⟨9432697132926805016584081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12576929510569073355445441 9432697132926805016584081)
                  ·
                    refine ⟨7074522849695103762438061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9432697132926805016584081 7074522849695103762438061)
                    ·
                      refine ⟨2652946068635663910914273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7074522849695103762438061 2652946068635663910914273)
                      ·
                        rfl

theorem cell23_5166594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5166594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166594 prefixEnd_5166594 := by exact prefixLift 5166594
  have htrace : WordTrace (prefixWord ++ tailWord_5166594) baseStart_5166594 baseEnd_5166594 := by
    simpa [prefixWord, tailWord_5166594, baseEnd_5166594] using wordTrace_append hprefix tailTrace_5166594
  have hstable : (prefixWord ++ tailWord_5166594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166594).length < 2 ^ (prefixWord ++ tailWord_5166594).sum := by decide
  have hdescent : baseEnd_5166594 < baseStart_5166594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166634 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_5166634 : Nat := 118140960795 + 5166634 * 2 ^ 59
def prefixEnd_5166634 : Nat := 4983230072969 + 3 ^ 40 * 5166634 * 2
def baseEnd_5166634 : Nat := 2652966607861843754414089

theorem tailTrace_5166634 : CollatzResearch.WordTrace tailWord_5166634 prefixEnd_5166634 2652966607861843754414089 := by
  unfold tailWord_5166634
  simp only [CollatzResearch.WordTrace]
  refine ⟨47110655791043720920396739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125628415442783255787724637 47110655791043720920396739)
  ·
    refine ⟨70665983686565581380595109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47110655791043720920396739 70665983686565581380595109)
    ·
      refine ⟨13249871941231046508861583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70665983686565581380595109 13249871941231046508861583)
      ·
        refine ⟨19874807911846569763292375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13249871941231046508861583 19874807911846569763292375)
        ·
          refine ⟨29812211867769854644938563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19874807911846569763292375 29812211867769854644938563)
          ·
            refine ⟨44718317801654781967407845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29812211867769854644938563 44718317801654781967407845)
            ·
              refine ⟨8384684587810271618888971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44718317801654781967407845 8384684587810271618888971)
              ·
                refine ⟨12577026881715407428333457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8384684587810271618888971 12577026881715407428333457)
                ·
                  refine ⟨9432770161286555571250093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12577026881715407428333457 9432770161286555571250093)
                  ·
                    refine ⟨3537288810482458339218785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9432770161286555571250093 3537288810482458339218785)
                    ·
                      refine ⟨2652966607861843754414089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3537288810482458339218785 2652966607861843754414089)
                      ·
                        rfl

theorem cell23_5166634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_5166634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166634 prefixEnd_5166634 := by exact prefixLift 5166634
  have htrace : WordTrace (prefixWord ++ tailWord_5166634) baseStart_5166634 baseEnd_5166634 := by
    simpa [prefixWord, tailWord_5166634, baseEnd_5166634] using wordTrace_append hprefix tailTrace_5166634
  have hstable : (prefixWord ++ tailWord_5166634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166634).length < 2 ^ (prefixWord ++ tailWord_5166634).sum := by decide
  have hdescent : baseEnd_5166634 < baseStart_5166634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5166653 : List Nat := [1, 4, 1, 3, 14]
def baseStart_5166653 : Nat := 118140960795 + 5166653 * 2 ^ 59
def prefixEnd_5166653 : Nat := 4983230072969 + 3 ^ 40 * 5166653 * 2
def baseEnd_5166653 : Nat := 3639199401912591467869

theorem tailTrace_5166653 : CollatzResearch.WordTrace tailWord_5166653 prefixEnd_5166653 3639199401912591467869 := by
  unfold tailWord_5166653
  simp only [CollatzResearch.WordTrace]
  refine ⟨188443316151106049926528613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125628877434070699951019075 188443316151106049926528613)
  ·
    refine ⟨35333121778332384361224115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188443316151106049926528613 35333121778332384361224115)
    ·
      refine ⟨52999682667498576541836173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35333121778332384361224115 52999682667498576541836173)
      ·
        refine ⟨19874881000311966203188565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52999682667498576541836173 19874881000311966203188565)
        ·
          refine ⟨3639199401912591467869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 19874881000311966203188565 3639199401912591467869)
          ·
            rfl

theorem cell23_5166653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 14].length) (baseStart_5166653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5166653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5166653 prefixEnd_5166653 := by exact prefixLift 5166653
  have htrace : WordTrace (prefixWord ++ tailWord_5166653) baseStart_5166653 baseEnd_5166653 := by
    simpa [prefixWord, tailWord_5166653, baseEnd_5166653] using wordTrace_append hprefix tailTrace_5166653
  have hstable : (prefixWord ++ tailWord_5166653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5166653).length < 2 ^ (prefixWord ++ tailWord_5166653).sum := by decide
  have hdescent : baseEnd_5166653 < baseStart_5166653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5166653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
