import V185TrunkScan23Chunk1137

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6741448 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_6741448 : Nat := 118140960795 + 6741448 * 2 ^ 59
def prefixEnd_6741448 : Nat := 4983230072969 + 3 ^ 40 * 6741448 * 2
def baseEnd_6741448 : Nat := 3461603131291445287396651

theorem tailTrace_6741448 : CollatzResearch.WordTrace tailWord_6741448 prefixEnd_6741448 3461603131291445287396651 := by
  unfold tailWord_6741448
  simp only [CollatzResearch.WordTrace]
  refine ⟨122940404240446359250020499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163920538987261812333360665 122940404240446359250020499)
  ·
    refine ⟨184410606360669538875030749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122940404240446359250020499 184410606360669538875030749)
    ·
      refine ⟨69153977385251077078136531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184410606360669538875030749 69153977385251077078136531)
      ·
        refine ⟨103730966077876615617204797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69153977385251077078136531 103730966077876615617204797)
        ·
          refine ⟨38899112279203730856451799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103730966077876615617204797 38899112279203730856451799)
          ·
            refine ⟨58348668418805596284677699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38899112279203730856451799 58348668418805596284677699)
            ·
              refine ⟨87523002628208394427016549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58348668418805596284677699 87523002628208394427016549)
              ·
                refine ⟨16410562992789073955065603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87523002628208394427016549 16410562992789073955065603)
                ·
                  refine ⟨24615844489183610932598405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16410562992789073955065603 24615844489183610932598405)
                  ·
                    refine ⟨4615470841721927049862201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24615844489183610932598405 4615470841721927049862201)
                    ·
                      refine ⟨3461603131291445287396651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615470841721927049862201 3461603131291445287396651)
                      ·
                        rfl

theorem cell23_6741448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_6741448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741448 prefixEnd_6741448 := by exact prefixLift 6741448
  have htrace : WordTrace (prefixWord ++ tailWord_6741448) baseStart_6741448 baseEnd_6741448 := by
    simpa [prefixWord, tailWord_6741448, baseEnd_6741448] using wordTrace_append hprefix tailTrace_6741448
  have hstable : (prefixWord ++ tailWord_6741448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741448).length < 2 ^ (prefixWord ++ tailWord_6741448).sum := by decide
  have hdescent : baseEnd_6741448 < baseStart_6741448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741452 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 1, 3, 2]
def baseStart_6741452 : Nat := 118140960795 + 6741452 * 2 ^ 59
def prefixEnd_6741452 : Nat := 4983230072969 + 3 ^ 40 * 6741452 * 2
def baseEnd_6741452 : Nat := 3461605185214063271746633

theorem tailTrace_6741452 : CollatzResearch.WordTrace tailWord_6741452 prefixEnd_6741452 3461605185214063271746633 := by
  unfold tailWord_6741452
  simp only [CollatzResearch.WordTrace]
  refine ⟨122940477186439113591593305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163920636248585484788791073 122940477186439113591593305)
  ·
    refine ⟨92205357889829335193694979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122940477186439113591593305 92205357889829335193694979)
    ·
      refine ⟨138308036834744002790542469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92205357889829335193694979 138308036834744002790542469)
      ·
        refine ⟨25932756906514500523226713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138308036834744002790542469 25932756906514500523226713)
        ·
          refine ⟨19449567679885875392420035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25932756906514500523226713 19449567679885875392420035)
          ·
            refine ⟨29174351519828813088630053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19449567679885875392420035 29174351519828813088630053)
            ·
              refine ⟨5470190909967902454118135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29174351519828813088630053 5470190909967902454118135)
              ·
                refine ⟨8205286364951853681177203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470190909967902454118135 8205286364951853681177203)
                ·
                  refine ⟨12307929547427780521765805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8205286364951853681177203 12307929547427780521765805)
                  ·
                    refine ⟨4615473580285417695662177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12307929547427780521765805 4615473580285417695662177)
                    ·
                      refine ⟨3461605185214063271746633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615473580285417695662177 3461605185214063271746633)
                      ·
                        rfl

theorem cell23_6741452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_6741452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741452 prefixEnd_6741452 := by exact prefixLift 6741452
  have htrace : WordTrace (prefixWord ++ tailWord_6741452) baseStart_6741452 baseEnd_6741452 := by
    simpa [prefixWord, tailWord_6741452, baseEnd_6741452] using wordTrace_append hprefix tailTrace_6741452
  have hstable : (prefixWord ++ tailWord_6741452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741452).length < 2 ^ (prefixWord ++ tailWord_6741452).sum := by decide
  have hdescent : baseEnd_6741452 < baseStart_6741452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741461 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6741461 : Nat := 118140960795 + 6741461 * 2 ^ 59
def prefixEnd_6741461 : Nat := 4983230072969 + 3 ^ 40 * 6741461 * 2
def baseEnd_6741461 : Nat := 3461609806539953736534091

theorem tailTrace_6741461 : CollatzResearch.WordTrace tailWord_6741461 prefixEnd_6741461 3461609806539953736534091 := by
  unfold tailWord_6741461
  simp only [CollatzResearch.WordTrace]
  refine ⟨245881282629845621720264237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163920855086563747813509491 245881282629845621720264237)
  ·
    refine ⟨92205480986192108145099089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245881282629845621720264237 92205480986192108145099089)
    ·
      refine ⟨69154110739644081108824317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92205480986192108145099089 69154110739644081108824317)
      ·
        refine ⟨25932791527366530415809119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69154110739644081108824317 25932791527366530415809119)
        ·
          refine ⟨38899187291049795623713679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25932791527366530415809119 38899187291049795623713679)
          ·
            refine ⟨58348780936574693435570519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38899187291049795623713679 58348780936574693435570519)
            ·
              refine ⟨87523171404862040153355779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58348780936574693435570519 87523171404862040153355779)
              ·
                refine ⟨131284757107293060230033669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87523171404862040153355779 131284757107293060230033669)
                ·
                  refine ⟨24615891957617448793131313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131284757107293060230033669 24615891957617448793131313)
                  ·
                    refine ⟨18461918968213086594848485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24615891957617448793131313 18461918968213086594848485)
                    ·
                      refine ⟨3461609806539953736534091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18461918968213086594848485 3461609806539953736534091)
                      ·
                        rfl

theorem cell23_6741461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6741461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741461 prefixEnd_6741461 := by exact prefixLift 6741461
  have htrace : WordTrace (prefixWord ++ tailWord_6741461) baseStart_6741461 baseEnd_6741461 := by
    simpa [prefixWord, tailWord_6741461, baseEnd_6741461] using wordTrace_append hprefix tailTrace_6741461
  have hstable : (prefixWord ++ tailWord_6741461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741461).length < 2 ^ (prefixWord ++ tailWord_6741461).sum := by decide
  have hdescent : baseEnd_6741461 < baseStart_6741461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741465 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 4, 2, 2]
def baseStart_6741465 : Nat := 118140960795 + 6741465 * 2 ^ 59
def prefixEnd_6741465 : Nat := 4983230072969 + 3 ^ 40 * 6741465 * 2
def baseEnd_6741465 : Nat := 3461611860462571720884073

theorem tailTrace_6741465 : CollatzResearch.WordTrace tailWord_6741465 prefixEnd_6741465 3461611860462571720884073 := by
  unfold tailWord_6741465
  simp only [CollatzResearch.WordTrace]
  refine ⟨245881428521831130403409849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163920952347887420268939899 245881428521831130403409849)
  ·
    refine ⟨184411071391373347802557387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245881428521831130403409849 184411071391373347802557387)
    ·
      refine ⟨276616607087060021703836081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184411071391373347802557387 276616607087060021703836081)
      ·
        refine ⟨207462455315295016277877061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276616607087060021703836081 207462455315295016277877061)
        ·
          refine ⟨38899210371617815552101949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207462455315295016277877061 38899210371617815552101949)
          ·
            refine ⟨14587203889356680832038231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38899210371617815552101949 14587203889356680832038231)
            ·
              refine ⟨21880805834035021248057347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14587203889356680832038231 21880805834035021248057347)
              ·
                refine ⟨32821208751052531872086021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21880805834035021248057347 32821208751052531872086021)
                ·
                  refine ⟨6153976640822349726016129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32821208751052531872086021 6153976640822349726016129)
                  ·
                    refine ⟨4615482480616762294512097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6153976640822349726016129 4615482480616762294512097)
                    ·
                      refine ⟨3461611860462571720884073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615482480616762294512097 3461611860462571720884073)
                      ·
                        rfl

theorem cell23_6741465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_6741465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741465 prefixEnd_6741465 := by exact prefixLift 6741465
  have htrace : WordTrace (prefixWord ++ tailWord_6741465) baseStart_6741465 baseEnd_6741465 := by
    simpa [prefixWord, tailWord_6741465, baseEnd_6741465] using wordTrace_append hprefix tailTrace_6741465
  have hstable : (prefixWord ++ tailWord_6741465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741465).length < 2 ^ (prefixWord ++ tailWord_6741465).sum := by decide
  have hdescent : baseEnd_6741465 < baseStart_6741465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741471 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 7]
def baseStart_6741471 : Nat := 118140960795 + 6741471 * 2 ^ 59
def prefixEnd_6741471 : Nat := 4983230072969 + 3 ^ 40 * 6741471 * 2
def baseEnd_6741471 : Nat := 384623882371833188601005

theorem tailTrace_6741471 : CollatzResearch.WordTrace tailWord_6741471 prefixEnd_6741471 384623882371833188601005 := by
  unfold tailWord_6741471
  simp only [CollatzResearch.WordTrace]
  refine ⟨245881647359809393428128267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163921098239872928952085511 245881647359809393428128267)
  ·
    refine ⟨368822471039714090142192401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245881647359809393428128267 368822471039714090142192401)
    ·
      refine ⟨276616853279785567606644301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368822471039714090142192401 276616853279785567606644301)
      ·
        refine ⟨103731319979919587852491613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276616853279785567606644301 103731319979919587852491613)
        ·
          refine ⟨38899244992469845444684355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103731319979919587852491613 38899244992469845444684355)
          ·
            refine ⟨58348867488704768167026533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38899244992469845444684355 58348867488704768167026533)
            ·
              refine ⟨10940412654132144031317475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58348867488704768167026533 10940412654132144031317475)
              ·
                refine ⟨16410618981198216046976213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10940412654132144031317475 16410618981198216046976213)
                ·
                  refine ⟨384623882371833188601005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16410618981198216046976213 384623882371833188601005)
                  ·
                    rfl

theorem cell23_6741471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 7].length) (baseStart_6741471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741471 prefixEnd_6741471 := by exact prefixLift 6741471
  have htrace : WordTrace (prefixWord ++ tailWord_6741471) baseStart_6741471 baseEnd_6741471 := by
    simpa [prefixWord, tailWord_6741471, baseEnd_6741471] using wordTrace_append hprefix tailTrace_6741471
  have hstable : (prefixWord ++ tailWord_6741471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741471).length < 2 ^ (prefixWord ++ tailWord_6741471).sum := by decide
  have hdescent : baseEnd_6741471 < baseStart_6741471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741482 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_6741482 : Nat := 118140960795 + 6741482 * 2 ^ 59
def prefixEnd_6741482 : Nat := 4983230072969 + 3 ^ 40 * 6741482 * 2
def baseEnd_6741482 : Nat := 3461620589633698154371495

theorem tailTrace_6741482 : CollatzResearch.WordTrace tailWord_6741482 prefixEnd_6741482 3461620589633698154371495 := by
  unfold tailWord_6741482
  simp only [CollatzResearch.WordTrace]
  refine ⟨61470512140692385576694675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163921365708513028204519133 61470512140692385576694675)
  ·
    refine ⟨92205768211038578365042013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61470512140692385576694675 92205768211038578365042013)
    ·
      refine ⟨34577163079139466886890755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92205768211038578365042013 34577163079139466886890755)
      ·
        refine ⟨51865744618709200330336133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34577163079139466886890755 51865744618709200330336133)
        ·
          refine ⟨9724827116007975061938025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51865744618709200330336133 9724827116007975061938025)
          ·
            refine ⟨7293620337005981296453519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9724827116007975061938025 7293620337005981296453519)
            ·
              refine ⟨10940430505508971944680279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7293620337005981296453519 10940430505508971944680279)
              ·
                refine ⟨16410645758263457917020419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10940430505508971944680279 16410645758263457917020419)
                ·
                  refine ⟨24615968637395186875530629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16410645758263457917020419 24615968637395186875530629)
                  ·
                    refine ⟨4615494119511597539161993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24615968637395186875530629 4615494119511597539161993)
                    ·
                      refine ⟨3461620589633698154371495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615494119511597539161993 3461620589633698154371495)
                      ·
                        rfl

theorem cell23_6741482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_6741482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741482 prefixEnd_6741482 := by exact prefixLift 6741482
  have htrace : WordTrace (prefixWord ++ tailWord_6741482) baseStart_6741482 baseEnd_6741482 := by
    simpa [prefixWord, tailWord_6741482, baseEnd_6741482] using wordTrace_append hprefix tailTrace_6741482
  have hstable : (prefixWord ++ tailWord_6741482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741482).length < 2 ^ (prefixWord ++ tailWord_6741482).sum := by decide
  have hdescent : baseEnd_6741482 < baseStart_6741482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741501 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_6741501 : Nat := 118140960795 + 6741501 * 2 ^ 59
def prefixEnd_6741501 : Nat := 4983230072969 + 3 ^ 40 * 6741501 * 2
def baseEnd_6741501 : Nat := 1153876781922044526677969

theorem tailTrace_6741501 : CollatzResearch.WordTrace tailWord_6741501 prefixEnd_6741501 1153876781922044526677969 := by
  unfold tailWord_6741501
  simp only [CollatzResearch.WordTrace]
  refine ⟨245882741549700708551720357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163921827699800472367813571 245882741549700708551720357)
  ·
    refine ⟨46103014040568882853447567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245882741549700708551720357 46103014040568882853447567)
    ·
      refine ⟨69154521060853324280171351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46103014040568882853447567 69154521060853324280171351)
      ·
        refine ⟨103731781591279986420257027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69154521060853324280171351 103731781591279986420257027)
        ·
          refine ⟨155597672386919979630385541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103731781591279986420257027 155597672386919979630385541)
          ·
            refine ⟨29174563572547496180697289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155597672386919979630385541 29174563572547496180697289)
            ·
              refine ⟨21880922679410622135522967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29174563572547496180697289 21880922679410622135522967)
              ·
                refine ⟨32821384019115933203284451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21880922679410622135522967 32821384019115933203284451)
                ·
                  refine ⟨49232076028673899804926677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32821384019115933203284451 49232076028673899804926677)
                  ·
                    refine ⟨1153876781922044526677969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49232076028673899804926677 1153876781922044526677969)
                    ·
                      rfl

theorem cell23_6741501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_6741501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741501 prefixEnd_6741501 := by exact prefixLift 6741501
  have htrace : WordTrace (prefixWord ++ tailWord_6741501) baseStart_6741501 baseEnd_6741501 := by
    simpa [prefixWord, tailWord_6741501, baseEnd_6741501] using wordTrace_append hprefix tailTrace_6741501
  have hstable : (prefixWord ++ tailWord_6741501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741501).length < 2 ^ (prefixWord ++ tailWord_6741501).sum := by decide
  have hdescent : baseEnd_6741501 < baseStart_6741501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741528 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_6741528 : Nat := 118140960795 + 6741528 * 2 ^ 59
def prefixEnd_6741528 : Nat := 4983230072969 + 3 ^ 40 * 6741528 * 2
def baseEnd_6741528 : Nat := 3461644209743804974396283

theorem tailTrace_6741528 : CollatzResearch.WordTrace tailWord_6741528 prefixEnd_6741528 3461644209743804974396283 := by
  unfold tailWord_6741528
  simp only [CollatzResearch.WordTrace]
  refine ⟨122941863160301446081476619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163922484213735261441968825 122941863160301446081476619)
  ·
    refine ⟨184412794740452169122214929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122941863160301446081476619 184412794740452169122214929)
    ·
      refine ⟨138309596055339126841661197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184412794740452169122214929 138309596055339126841661197)
      ·
        refine ⟨51866098520752172565622949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138309596055339126841661197 51866098520752172565622949)
        ·
          refine ⟨9724893472641032356054303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51866098520752172565622949 9724893472641032356054303)
          ·
            refine ⟨14587340208961548534081455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9724893472641032356054303 14587340208961548534081455)
            ·
              refine ⟨21881010313442322801122183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14587340208961548534081455 21881010313442322801122183)
              ·
                refine ⟨32821515470163484201683275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21881010313442322801122183 32821515470163484201683275)
                ·
                  refine ⟨49232273205245226302524913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32821515470163484201683275 49232273205245226302524913)
                  ·
                    refine ⟨36924204903933919726893685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49232273205245226302524913 36924204903933919726893685)
                    ·
                      refine ⟨3461644209743804974396283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36924204903933919726893685 3461644209743804974396283)
                      ·
                        rfl

theorem cell23_6741528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_6741528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741528 prefixEnd_6741528 := by exact prefixLift 6741528
  have htrace : WordTrace (prefixWord ++ tailWord_6741528) baseStart_6741528 baseEnd_6741528 := by
    simpa [prefixWord, tailWord_6741528, baseEnd_6741528] using wordTrace_append hprefix tailTrace_6741528
  have hstable : (prefixWord ++ tailWord_6741528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741528).length < 2 ^ (prefixWord ++ tailWord_6741528).sum := by decide
  have hdescent : baseEnd_6741528 < baseStart_6741528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741578 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 6]
def baseStart_6741578 : Nat := 118140960795 + 6741578 * 2 ^ 59
def prefixEnd_6741578 : Nat := 4983230072969 + 3 ^ 40 * 6741578 * 2
def baseEnd_6741578 : Nat := 384629987086281086530117

theorem tailTrace_6741578 : CollatzResearch.WordTrace tailWord_6741578 prefixEnd_6741578 384629987086281086530117 := by
  unfold tailWord_6741578
  simp only [CollatzResearch.WordTrace]
  refine ⟨61471387492605437675568347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163923699980281167134848925 61471387492605437675568347)
  ·
    refine ⟨92207081238908156513352521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61471387492605437675568347 92207081238908156513352521)
    ·
      refine ⟨69155310929181117385014391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92207081238908156513352521 69155310929181117385014391)
      ·
        refine ⟨103732966393771676077521587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69155310929181117385014391 103732966393771676077521587)
        ·
          refine ⟨155599449590657514116282381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103732966393771676077521587 155599449590657514116282381)
          ·
            refine ⟨58349793596496567793605893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155599449590657514116282381 58349793596496567793605893)
            ·
              refine ⟨10940586299343106461301105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58349793596496567793605893 10940586299343106461301105)
              ·
                refine ⟨8205439724507329845975829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10940586299343106461301105 8205439724507329845975829)
                ·
                  refine ⟨384629987086281086530117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8205439724507329845975829 384629987086281086530117)
                  ·
                    rfl

theorem cell23_6741578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_6741578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741578 prefixEnd_6741578 := by exact prefixLift 6741578
  have htrace : WordTrace (prefixWord ++ tailWord_6741578) baseStart_6741578 baseEnd_6741578 := by
    simpa [prefixWord, tailWord_6741578, baseEnd_6741578] using wordTrace_append hprefix tailTrace_6741578
  have hstable : (prefixWord ++ tailWord_6741578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741578).length < 2 ^ (prefixWord ++ tailWord_6741578).sum := by decide
  have hdescent : baseEnd_6741578 < baseStart_6741578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741601 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6741601 : Nat := 118140960795 + 6741601 * 2 ^ 59
def prefixEnd_6741601 : Nat := 4983230072969 + 3 ^ 40 * 6741601 * 2
def baseEnd_6741601 : Nat := 3461681693831583188783447

theorem tailTrace_6741601 : CollatzResearch.WordTrace tailWord_6741601 prefixEnd_6741601 3461681693831583188783447 := by
  unfold tailWord_6741601
  simp only [CollatzResearch.WordTrace]
  refine ⟨245886388849338425630360657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163924259232892283753573771 245886388849338425630360657)
  ·
    refine ⟨184414791637003819222770493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245886388849338425630360657 184414791637003819222770493)
    ·
      refine ⟨69155546863876432208538935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184414791637003819222770493 69155546863876432208538935)
      ·
        refine ⟨103733320295814648312808403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69155546863876432208538935 103733320295814648312808403)
        ·
          refine ⟨155599980443721972469212605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103733320295814648312808403 155599980443721972469212605)
          ·
            refine ⟨58349992666395739675954727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155599980443721972469212605 58349992666395739675954727)
            ·
              refine ⟨87524988999593609513932091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58349992666395739675954727 87524988999593609513932091)
              ·
                refine ⟨131287483499390414270898137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87524988999593609513932091 131287483499390414270898137)
                ·
                  refine ⟨98465612624542810703173603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131287483499390414270898137 98465612624542810703173603)
                  ·
                    refine ⟨147698418936814216054760405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98465612624542810703173603 147698418936814216054760405)
                    ·
                      refine ⟨3461681693831583188783447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147698418936814216054760405 3461681693831583188783447)
                      ·
                        rfl

theorem cell23_6741601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6741601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741601 prefixEnd_6741601 := by exact prefixLift 6741601
  have htrace : WordTrace (prefixWord ++ tailWord_6741601) baseStart_6741601 baseEnd_6741601 := by
    simpa [prefixWord, tailWord_6741601, baseEnd_6741601] using wordTrace_append hprefix tailTrace_6741601
  have hstable : (prefixWord ++ tailWord_6741601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741601).length < 2 ^ (prefixWord ++ tailWord_6741601).sum := by decide
  have hdescent : baseEnd_6741601 < baseStart_6741601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741605 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_6741605 : Nat := 118140960795 + 6741605 * 2 ^ 59
def prefixEnd_6741605 : Nat := 4983230072969 + 3 ^ 40 * 6741605 * 2
def baseEnd_6741605 : Nat := 3461683747754201173133429

theorem tailTrace_6741605 : CollatzResearch.WordTrace tailWord_6741605 prefixEnd_6741605 3461683747754201173133429 := by
  unfold tailWord_6741605
  simp only [CollatzResearch.WordTrace]
  refine ⟨245886534741323934313506269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163924356494215956209004179 245886534741323934313506269)
  ·
    refine ⟨92207450527996475367564851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245886534741323934313506269 92207450527996475367564851)
    ·
      refine ⟨138311175791994713051347277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92207450527996475367564851 138311175791994713051347277)
      ·
        refine ⟨51866690921998017394255229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138311175791994713051347277 51866690921998017394255229)
        ·
          refine ⟨19450009095749256522845711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51866690921998017394255229 19450009095749256522845711)
          ·
            refine ⟨29175013643623884784268567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19450009095749256522845711 29175013643623884784268567)
            ·
              refine ⟨43762520465435827176402851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29175013643623884784268567 43762520465435827176402851)
              ·
                refine ⟨65643780698153740764604277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43762520465435827176402851 65643780698153740764604277)
                ·
                  refine ⟨6154104440451913196681651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65643780698153740764604277 6154104440451913196681651)
                  ·
                    refine ⟨9231156660677869795022477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6154104440451913196681651 9231156660677869795022477)
                    ·
                      refine ⟨3461683747754201173133429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9231156660677869795022477 3461683747754201173133429)
                      ·
                        rfl

theorem cell23_6741605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_6741605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741605 prefixEnd_6741605 := by exact prefixLift 6741605
  have htrace : WordTrace (prefixWord ++ tailWord_6741605) baseStart_6741605 baseEnd_6741605 := by
    simpa [prefixWord, tailWord_6741605, baseEnd_6741605] using wordTrace_append hprefix tailTrace_6741605
  have hstable : (prefixWord ++ tailWord_6741605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741605).length < 2 ^ (prefixWord ++ tailWord_6741605).sum := by decide
  have hdescent : baseEnd_6741605 < baseStart_6741605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741648 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3]
def baseStart_6741648 : Nat := 118140960795 + 6741648 * 2 ^ 59
def prefixEnd_6741648 : Nat := 4983230072969 + 3 ^ 40 * 6741648 * 2
def baseEnd_6741648 : Nat := 3461705827422344504895731

theorem tailTrace_6741648 : CollatzResearch.WordTrace tailWord_6741648 prefixEnd_6741648 3461705827422344504895731 := by
  unfold tailWord_6741648
  simp only [CollatzResearch.WordTrace]
  refine ⟨122944051540084076328660799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163925402053445435104881065 122944051540084076328660799)
  ·
    refine ⟨184416077310126114492991199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122944051540084076328660799 184416077310126114492991199)
    ·
      refine ⟨276624115965189171739486799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184416077310126114492991199 276624115965189171739486799)
      ·
        refine ⟨414936173947783757609230199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276624115965189171739486799 414936173947783757609230199)
        ·
          refine ⟨622404260921675636413845299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414936173947783757609230199 622404260921675636413845299)
          ·
            refine ⟨933606391382513454620767949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622404260921675636413845299 933606391382513454620767949)
            ·
              refine ⟨350102396768442545482787981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 933606391382513454620767949 350102396768442545482787981)
              ·
                refine ⟨131288398788165954556045493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350102396768442545482787981 131288398788165954556045493)
                ·
                  refine ⟨12308287386390558239629265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131288398788165954556045493 12308287386390558239629265)
                  ·
                    refine ⟨9231215539792918679721949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12308287386390558239629265 9231215539792918679721949)
                    ·
                      refine ⟨3461705827422344504895731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9231215539792918679721949 3461705827422344504895731)
                      ·
                        rfl

theorem cell23_6741648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_6741648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741648 prefixEnd_6741648 := by exact prefixLift 6741648
  have htrace : WordTrace (prefixWord ++ tailWord_6741648) baseStart_6741648 baseEnd_6741648 := by
    simpa [prefixWord, tailWord_6741648, baseEnd_6741648] using wordTrace_append hprefix tailTrace_6741648
  have hstable : (prefixWord ++ tailWord_6741648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741648).length < 2 ^ (prefixWord ++ tailWord_6741648).sum := by decide
  have hdescent : baseEnd_6741648 < baseStart_6741648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741655 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 1, 6]
def baseStart_6741655 : Nat := 118140960795 + 6741655 * 2 ^ 59
def prefixEnd_6741655 : Nat := 4983230072969 + 3 ^ 40 * 6741655 * 2
def baseEnd_6741655 : Nat := 1153903140595641992502733

theorem tailTrace_6741655 : CollatzResearch.WordTrace tailWord_6741655 prefixEnd_6741655 1153903140595641992502733 := by
  unfold tailWord_6741655
  simp only [CollatzResearch.WordTrace]
  refine ⟨245888358391142792852826419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163925572260761861901884279 245888358391142792852826419)
  ·
    refine ⟨368832537586714189279239629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245888358391142792852826419 368832537586714189279239629)
    ·
      refine ⟨138312201595017820979714861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368832537586714189279239629 138312201595017820979714861)
      ·
        refine ⟨51867075598131682867393073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138312201595017820979714861 51867075598131682867393073)
        ·
          refine ⟨38900306698598762150544805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51867075598131682867393073 38900306698598762150544805)
          ·
            refine ⟨7293807505987267903227151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38900306698598762150544805 7293807505987267903227151)
            ·
              refine ⟨10940711258980901854840727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7293807505987267903227151 10940711258980901854840727)
              ·
                refine ⟨16411066888471352782261091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10940711258980901854840727 16411066888471352782261091)
                ·
                  refine ⟨24616600332707029173391637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16411066888471352782261091 24616600332707029173391637)
                  ·
                    refine ⟨1153903140595641992502733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24616600332707029173391637 1153903140595641992502733)
                    ·
                      rfl

theorem cell23_6741655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_6741655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741655 prefixEnd_6741655 := by exact prefixLift 6741655
  have htrace : WordTrace (prefixWord ++ tailWord_6741655) baseStart_6741655 baseEnd_6741655 := by
    simpa [prefixWord, tailWord_6741655, baseEnd_6741655] using wordTrace_append hprefix tailTrace_6741655
  have hstable : (prefixWord ++ tailWord_6741655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741655).length < 2 ^ (prefixWord ++ tailWord_6741655).sum := by decide
  have hdescent : baseEnd_6741655 < baseStart_6741655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741662 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_6741662 : Nat := 118140960795 + 6741662 * 2 ^ 59
def prefixEnd_6741662 : Nat := 4983230072969 + 3 ^ 40 * 6741662 * 2
def baseEnd_6741662 : Nat := 3461713016151507450120667

theorem tailTrace_6741662 : CollatzResearch.WordTrace tailWord_6741662 prefixEnd_6741662 3461713016151507450120667 := by
  unfold tailWord_6741662
  simp only [CollatzResearch.WordTrace]
  refine ⟨30736076712764679131041405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163925742468078288698887493 30736076712764679131041405)
  ·
    refine ⟨11526028767286754674140527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30736076712764679131041405 11526028767286754674140527)
    ·
      refine ⟨17289043150930132011210791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11526028767286754674140527 17289043150930132011210791)
      ·
        refine ⟨25933564726395198016816187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17289043150930132011210791 25933564726395198016816187)
        ·
          refine ⟨38900347089592797025224281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25933564726395198016816187 38900347089592797025224281)
          ·
            refine ⟨29175260317194597768918211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38900347089592797025224281 29175260317194597768918211)
            ·
              refine ⟨43762890475791896653377317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29175260317194597768918211 43762890475791896653377317)
              ·
                refine ⟨8205541964210980622508247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43762890475791896653377317 8205541964210980622508247)
                ·
                  refine ⟨12308312946316470933762371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8205541964210980622508247 12308312946316470933762371)
                  ·
                    refine ⟨18462469419474706400643557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12308312946316470933762371 18462469419474706400643557)
                    ·
                      refine ⟨3461713016151507450120667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18462469419474706400643557 3461713016151507450120667)
                      ·
                        rfl

theorem cell23_6741662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_6741662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741662 prefixEnd_6741662 := by exact prefixLift 6741662
  have htrace : WordTrace (prefixWord ++ tailWord_6741662) baseStart_6741662 baseEnd_6741662 := by
    simpa [prefixWord, tailWord_6741662, baseEnd_6741662] using wordTrace_append hprefix tailTrace_6741662
  have hstable : (prefixWord ++ tailWord_6741662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741662).length < 2 ^ (prefixWord ++ tailWord_6741662).sum := by decide
  have hdescent : baseEnd_6741662 < baseStart_6741662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741668 : List Nat := [2, 3, 1, 2, 2, 3, 1, 9]
def baseStart_6741668 : Nat := 118140960795 + 6741668 * 2 ^ 59
def prefixEnd_6741668 : Nat := 4983230072969 + 3 ^ 40 * 6741668 * 2
def baseEnd_6741668 : Nat := 128211707297608682468357

theorem tailTrace_6741668 : CollatzResearch.WordTrace tailWord_6741668 prefixEnd_6741668 128211707297608682468357 := by
  unfold tailWord_6741668
  simp only [CollatzResearch.WordTrace]
  refine ⟨122944416270047848036524829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163925888360063797382033105 122944416270047848036524829)
  ·
    refine ⟨46104156101267943013696811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122944416270047848036524829 46104156101267943013696811)
    ·
      refine ⟨69156234151901914520545217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46104156101267943013696811 69156234151901914520545217)
      ·
        refine ⟨51867175613926435890408913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69156234151901914520545217 51867175613926435890408913)
        ·
          refine ⟨38900381710444826917806685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51867175613926435890408913 38900381710444826917806685)
          ·
            refine ⟨14587643141416810094177507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38900381710444826917806685 14587643141416810094177507)
            ·
              refine ⟨21881464712125215141266261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14587643141416810094177507 21881464712125215141266261)
              ·
                refine ⟨128211707297608682468357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21881464712125215141266261 128211707297608682468357)
                ·
                  rfl

theorem cell23_6741668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 9].length) (baseStart_6741668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741668 prefixEnd_6741668 := by exact prefixLift 6741668
  have htrace : WordTrace (prefixWord ++ tailWord_6741668) baseStart_6741668 baseEnd_6741668 := by
    simpa [prefixWord, tailWord_6741668, baseEnd_6741668] using wordTrace_append hprefix tailTrace_6741668
  have hstable : (prefixWord ++ tailWord_6741668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741668).length < 2 ^ (prefixWord ++ tailWord_6741668).sum := by decide
  have hdescent : baseEnd_6741668 < baseStart_6741668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741685 : List Nat := [1, 3, 3, 3, 2, 2, 9]
def baseStart_6741685 : Nat := 118140960795 + 6741685 * 2 ^ 59
def prefixEnd_6741685 : Nat := 4983230072969 + 3 ^ 40 * 6741685 * 2
def baseEnd_6741685 : Nat := 42737343533414331606581

theorem tailTrace_6741685 : CollatzResearch.WordTrace tailWord_6741685 prefixEnd_6741685 42737343533414331606581 := by
  unfold tailWord_6741685
  simp only [CollatzResearch.WordTrace]
  refine ⟨245889452581034107976418509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163926301720689405317612339 245889452581034107976418509)
  ·
    refine ⟨92208544717887790491156941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245889452581034107976418509 92208544717887790491156941)
    ·
      refine ⟨34578204269207921434183853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92208544717887790491156941 34578204269207921434183853)
      ·
        refine ⟨12966826600952970537818945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34578204269207921434183853 12966826600952970537818945)
        ·
          refine ⟨9725119950714727903364209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12966826600952970537818945 9725119950714727903364209)
          ·
            refine ⟨7293839963036045927523157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9725119950714727903364209 7293839963036045927523157)
            ·
              refine ⟨42737343533414331606581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7293839963036045927523157 42737343533414331606581)
              ·
                rfl

theorem cell23_6741685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 9].length) (baseStart_6741685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741685 prefixEnd_6741685 := by exact prefixLift 6741685
  have htrace : WordTrace (prefixWord ++ tailWord_6741685) baseStart_6741685 baseEnd_6741685 := by
    simpa [prefixWord, tailWord_6741685, baseEnd_6741685] using wordTrace_append hprefix tailTrace_6741685
  have hstable : (prefixWord ++ tailWord_6741685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741685).length < 2 ^ (prefixWord ++ tailWord_6741685).sum := by decide
  have hdescent : baseEnd_6741685 < baseStart_6741685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741695 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 3]
def baseStart_6741695 : Nat := 118140960795 + 6741695 * 2 ^ 59
def prefixEnd_6741695 : Nat := 4983230072969 + 3 ^ 40 * 6741695 * 2
def baseEnd_6741695 : Nat := 3461729961013105821008015

theorem tailTrace_6741695 : CollatzResearch.WordTrace tailWord_6741695 prefixEnd_6741695 3461729961013105821008015 := by
  unfold tailWord_6741695
  simp only [CollatzResearch.WordTrace]
  refine ⟨245889817310997879684282539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163926544873998586456188359 245889817310997879684282539)
  ·
    refine ⟨368834725966496819526423809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245889817310997879684282539 368834725966496819526423809)
    ·
      refine ⟨276626044474872614644817857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368834725966496819526423809 276626044474872614644817857)
      ·
        refine ⟨207469533356154460983613393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276626044474872614644817857 207469533356154460983613393)
        ·
          refine ⟨155602150017115845737710045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207469533356154460983613393 155602150017115845737710045)
          ·
            refine ⟨58350806256418442151641267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155602150017115845737710045 58350806256418442151641267)
            ·
              refine ⟨87526209384627663227461901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58350806256418442151641267 87526209384627663227461901)
              ·
                refine ⟨32822328519235373710298213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87526209384627663227461901 32822328519235373710298213)
                ·
                  refine ⟨6154186597356632570680915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32822328519235373710298213 6154186597356632570680915)
                  ·
                    refine ⟨9231279896034948856021373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6154186597356632570680915 9231279896034948856021373)
                    ·
                      refine ⟨3461729961013105821008015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9231279896034948856021373 3461729961013105821008015)
                      ·
                        rfl

theorem cell23_6741695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_6741695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741695 prefixEnd_6741695 := by exact prefixLift 6741695
  have htrace : WordTrace (prefixWord ++ tailWord_6741695) baseStart_6741695 baseEnd_6741695 := by
    simpa [prefixWord, tailWord_6741695, baseEnd_6741695] using wordTrace_append hprefix tailTrace_6741695
  have hstable : (prefixWord ++ tailWord_6741695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741695).length < 2 ^ (prefixWord ++ tailWord_6741695).sum := by decide
  have hdescent : baseEnd_6741695 < baseStart_6741695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741696 : List Nat := [2, 1, 1, 2, 4, 1, 5, 2, 1, 2, 2]
def baseStart_6741696 : Nat := 118140960795 + 6741696 * 2 ^ 59
def prefixEnd_6741696 : Nat := 4983230072969 + 3 ^ 40 * 6741696 * 2
def baseEnd_6741696 : Nat := 3461730474493760317095511

theorem tailTrace_6741696 : CollatzResearch.WordTrace tailWord_6741696 prefixEnd_6741696 3461730474493760317095511 := by
  unfold tailWord_6741696
  simp only [CollatzResearch.WordTrace]
  refine ⟨122944926891997128427534471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163926569189329504570045961 122944926891997128427534471)
  ·
    refine ⟨184417390337995692641301707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122944926891997128427534471 184417390337995692641301707)
    ·
      refine ⟨276626085506993538961952561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184417390337995692641301707 276626085506993538961952561)
      ·
        refine ⟨207469564130245154221464421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276626085506993538961952561 207469564130245154221464421)
        ·
          refine ⟨38900543274420966416524579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207469564130245154221464421 38900543274420966416524579)
          ·
            refine ⟨58350814911631449624786869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38900543274420966416524579 58350814911631449624786869)
            ·
              refine ⟨5470388897965448402323769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58350814911631449624786869 5470388897965448402323769)
              ·
                refine ⟨4102791673474086301742827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5470388897965448402323769 4102791673474086301742827)
                ·
                  refine ⟨6154187510211129452614241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102791673474086301742827 6154187510211129452614241)
                  ·
                    refine ⟨4615640632658347089460681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6154187510211129452614241 4615640632658347089460681)
                    ·
                      refine ⟨3461730474493760317095511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615640632658347089460681 3461730474493760317095511)
                      ·
                        rfl

theorem cell23_6741696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_6741696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741696 prefixEnd_6741696 := by exact prefixLift 6741696
  have htrace : WordTrace (prefixWord ++ tailWord_6741696) baseStart_6741696 baseEnd_6741696 := by
    simpa [prefixWord, tailWord_6741696, baseEnd_6741696] using wordTrace_append hprefix tailTrace_6741696
  have hstable : (prefixWord ++ tailWord_6741696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741696).length < 2 ^ (prefixWord ++ tailWord_6741696).sum := by decide
  have hdescent : baseEnd_6741696 < baseStart_6741696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741702 : List Nat := [6, 1, 2, 1, 1, 1, 1, 10]
def baseStart_6741702 : Nat := 118140960795 + 6741702 * 2 ^ 59
def prefixEnd_6741702 : Nat := 4983230072969 + 3 ^ 40 * 6741702 * 2
def baseEnd_6741702 : Nat := 128212353902877307171129

theorem tailTrace_6741702 : CollatzResearch.WordTrace tailWord_6741702 prefixEnd_6741702 128212353902877307171129 := by
  unfold tailWord_6741702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684064769436641246243355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163926715081315013253191573 7684064769436641246243355)
  ·
    refine ⟨11526097154154961869365033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7684064769436641246243355 11526097154154961869365033)
    ·
      refine ⟨8644572865616221402023775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11526097154154961869365033 8644572865616221402023775)
      ·
        refine ⟨12966859298424332103035663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8644572865616221402023775 12966859298424332103035663)
        ·
          refine ⟨19450288947636498154553495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12966859298424332103035663 19450288947636498154553495)
          ·
            refine ⟨29175433421454747231830243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19450288947636498154553495 29175433421454747231830243)
            ·
              refine ⟨43763150132182120847745365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29175433421454747231830243 43763150132182120847745365)
              ·
                refine ⟨128212353902877307171129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43763150132182120847745365 128212353902877307171129)
                ·
                  rfl

theorem cell23_6741702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_6741702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741702 prefixEnd_6741702 := by exact prefixLift 6741702
  have htrace : WordTrace (prefixWord ++ tailWord_6741702) baseStart_6741702 baseEnd_6741702 := by
    simpa [prefixWord, tailWord_6741702, baseEnd_6741702] using wordTrace_append hprefix tailTrace_6741702
  have hstable : (prefixWord ++ tailWord_6741702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741702).length < 2 ^ (prefixWord ++ tailWord_6741702).sum := by decide
  have hdescent : baseEnd_6741702 < baseStart_6741702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741706 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_6741706 : Nat := 118140960795 + 6741706 * 2 ^ 59
def prefixEnd_6741706 : Nat := 4983230072969 + 3 ^ 40 * 6741706 * 2
def baseEnd_6741706 : Nat := 1153911869766768425990155

theorem tailTrace_6741706 : CollatzResearch.WordTrace tailWord_6741706 prefixEnd_6741706 1153911869766768425990155 := by
  unfold tailWord_6741706
  simp only [CollatzResearch.WordTrace]
  refine ⟨61472554628489507140733243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163926812342638685708621981 61472554628489507140733243)
  ·
    refine ⟨92208831942734260711099865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61472554628489507140733243 92208831942734260711099865)
    ·
      refine ⟨69156623957050695533324899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92208831942734260711099865 69156623957050695533324899)
      ·
        refine ⟨103734935935576043299987349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69156623957050695533324899 103734935935576043299987349)
        ·
          refine ⟨4862575121980127029686907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103734935935576043299987349 4862575121980127029686907)
          ·
            refine ⟨7293862682970190544530361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4862575121980127029686907 7293862682970190544530361)
            ·
              refine ⟨5470397012227642908397771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7293862682970190544530361 5470397012227642908397771)
              ·
                refine ⟨8205595518341464362596657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470397012227642908397771 8205595518341464362596657)
                ·
                  refine ⟨6154196638756098271947493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8205595518341464362596657 6154196638756098271947493)
                  ·
                    refine ⟨1153911869766768425990155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6154196638756098271947493 1153911869766768425990155)
                    ·
                      rfl

theorem cell23_6741706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_6741706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741706 prefixEnd_6741706 := by exact prefixLift 6741706
  have htrace : WordTrace (prefixWord ++ tailWord_6741706) baseStart_6741706 baseEnd_6741706 := by
    simpa [prefixWord, tailWord_6741706, baseEnd_6741706] using wordTrace_append hprefix tailTrace_6741706
  have hstable : (prefixWord ++ tailWord_6741706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741706).length < 2 ^ (prefixWord ++ tailWord_6741706).sum := by decide
  have hdescent : baseEnd_6741706 < baseStart_6741706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741722 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2]
def baseStart_6741722 : Nat := 118140960795 + 6741722 * 2 ^ 59
def prefixEnd_6741722 : Nat := 4983230072969 + 3 ^ 40 * 6741722 * 2
def baseEnd_6741722 : Nat := 3461743824990777215370391

theorem tailTrace_6741722 : CollatzResearch.WordTrace tailWord_6741722 prefixEnd_6741722 3461743824990777215370391 := by
  unfold tailWord_6741722
  simp only [CollatzResearch.WordTrace]
  refine ⟨61472700520475015823878855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163927201387933375530343613 61472700520475015823878855)
  ·
    refine ⟨92209050780712523735818283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61472700520475015823878855 92209050780712523735818283)
    ·
      refine ⟨138313576171068785603727425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92209050780712523735818283 138313576171068785603727425)
      ·
        refine ⟨103735182128301589202795569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138313576171068785603727425 103735182128301589202795569)
        ·
          refine ⟨77801386596226191902096677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103735182128301589202795569 77801386596226191902096677)
          ·
            refine ⟨14587759986792410981643127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77801386596226191902096677 14587759986792410981643127)
            ·
              refine ⟨21881639980188616472464691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14587759986792410981643127 21881639980188616472464691)
              ·
                refine ⟨32822459970282924708697037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21881639980188616472464691 32822459970282924708697037)
                ·
                  refine ⟨12308422488856096765761389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32822459970282924708697037 12308422488856096765761389)
                  ·
                    refine ⟨4615658433321036287160521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12308422488856096765761389 4615658433321036287160521)
                    ·
                      refine ⟨3461743824990777215370391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615658433321036287160521 3461743824990777215370391)
                      ·
                        rfl

theorem cell23_6741722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_6741722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741722 prefixEnd_6741722 := by exact prefixLift 6741722
  have htrace : WordTrace (prefixWord ++ tailWord_6741722) baseStart_6741722 baseEnd_6741722 := by
    simpa [prefixWord, tailWord_6741722, baseEnd_6741722] using wordTrace_append hprefix tailTrace_6741722
  have hstable : (prefixWord ++ tailWord_6741722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741722).length < 2 ^ (prefixWord ++ tailWord_6741722).sum := by decide
  have hdescent : baseEnd_6741722 < baseStart_6741722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741792 : List Nat := [2, 1, 1, 5, 1, 1, 4, 3, 5]
def baseStart_6741792 : Nat := 118140960795 + 6741792 * 2 ^ 59
def prefixEnd_6741792 : Nat := 4983230072969 + 3 ^ 40 * 6741792 * 2
def baseEnd_6741792 : Nat := 384642196515176882388341

theorem tailTrace_6741792 : CollatzResearch.WordTrace tailWord_6741792 prefixEnd_6741792 384642196515176882388341 := by
  unfold tailWord_6741792
  simp only [CollatzResearch.WordTrace]
  refine ⟨122946677595823232625281815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163928903461097643500375753 122946677595823232625281815)
  ·
    refine ⟨184420016393734848937922723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122946677595823232625281815 184420016393734848937922723)
    ·
      refine ⟨276630024590602273406884085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184420016393734848937922723 276630024590602273406884085)
      ·
        refine ⟨25934064805368963131895383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276630024590602273406884085 25934064805368963131895383)
        ·
          refine ⟨38901097208053444697843075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25934064805368963131895383 38901097208053444697843075)
          ·
            refine ⟨58351645812080167046764613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38901097208053444697843075 58351645812080167046764613)
            ·
              refine ⟨10940933589765031321268365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58351645812080167046764613 10940933589765031321268365)
              ·
                refine ⟨4102850096161886745475637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10940933589765031321268365 4102850096161886745475637)
                ·
                  refine ⟨384642196515176882388341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4102850096161886745475637 384642196515176882388341)
                  ·
                    rfl

theorem cell23_6741792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 5].length) (baseStart_6741792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741792 prefixEnd_6741792 := by exact prefixLift 6741792
  have htrace : WordTrace (prefixWord ++ tailWord_6741792) baseStart_6741792 baseEnd_6741792 := by
    simpa [prefixWord, tailWord_6741792, baseEnd_6741792] using wordTrace_append hprefix tailTrace_6741792
  have hstable : (prefixWord ++ tailWord_6741792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741792).length < 2 ^ (prefixWord ++ tailWord_6741792).sum := by decide
  have hdescent : baseEnd_6741792 < baseStart_6741792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741869 : List Nat := [1, 5, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_6741869 : Nat := 118140960795 + 6741869 * 2 ^ 59
def prefixEnd_6741869 : Nat := 4983230072969 + 3 ^ 40 * 6741869 * 2
def baseEnd_6741869 : Nat := 1153939768882329380077405

theorem tailTrace_6741869 : CollatzResearch.WordTrace tailWord_6741869 prefixEnd_6741869 1153939768882329380077405 := by
  unfold tailWord_6741869
  simp only [CollatzResearch.WordTrace]
  refine ⟨245896163612367507401116661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163930775741578338267411107 245896163612367507401116661)
  ·
    refine ⟨23052765338659453818854687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245896163612367507401116661 23052765338659453818854687)
    ·
      refine ⟨34579148007989180728282031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23052765338659453818854687 34579148007989180728282031)
      ·
        refine ⟨51868722011983771092423047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34579148007989180728282031 51868722011983771092423047)
        ·
          refine ⟨77803083017975656638634571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51868722011983771092423047 77803083017975656638634571)
          ·
            refine ⟨116704624526963484957951857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77803083017975656638634571 116704624526963484957951857)
            ·
              refine ⟨87528468395222613718463893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116704624526963484957951857 87528468395222613718463893)
              ·
                refine ⟨4102896956026060018052995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87528468395222613718463893 4102896956026060018052995)
                ·
                  refine ⟨6154345434039090027079493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102896956026060018052995 6154345434039090027079493)
                  ·
                    refine ⟨1153939768882329380077405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6154345434039090027079493 1153939768882329380077405)
                    ·
                      rfl

theorem cell23_6741869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_6741869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741869 prefixEnd_6741869 := by exact prefixLift 6741869
  have htrace : WordTrace (prefixWord ++ tailWord_6741869) baseStart_6741869 baseEnd_6741869 := by
    simpa [prefixWord, tailWord_6741869, baseEnd_6741869] using wordTrace_append hprefix tailTrace_6741869
  have hstable : (prefixWord ++ tailWord_6741869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741869).length < 2 ^ (prefixWord ++ tailWord_6741869).sum := by decide
  have hdescent : baseEnd_6741869 < baseStart_6741869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741882 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 6]
def baseStart_6741882 : Nat := 118140960795 + 6741882 * 2 ^ 59
def prefixEnd_6741882 : Nat := 4983230072969 + 3 ^ 40 * 6741882 * 2
def baseEnd_6741882 : Nat := 384647331321721843263295

theorem tailTrace_6741882 : CollatzResearch.WordTrace tailWord_6741882 prefixEnd_6741882 384647331321721843263295 := by
  unfold tailWord_6741882
  simp only [CollatzResearch.WordTrace]
  refine ⟨61474159440330102655334975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163931091840880273747559933 61474159440330102655334975)
  ·
    refine ⟨92211239160495153983002463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61474159440330102655334975 92211239160495153983002463)
    ·
      refine ⟨138316858740742730974503695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92211239160495153983002463 138316858740742730974503695)
      ·
        refine ⟨207475288111114096461755543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138316858740742730974503695 207475288111114096461755543)
        ·
          refine ⟨311212932166671144692633315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207475288111114096461755543 311212932166671144692633315)
          ·
            refine ⟨466819398250006717038949973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311212932166671144692633315 466819398250006717038949973)
            ·
              refine ⟨5470539823242266215300195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 466819398250006717038949973 5470539823242266215300195)
              ·
                refine ⟨8205809734863399322950293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470539823242266215300195 8205809734863399322950293)
                ·
                  refine ⟨384647331321721843263295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8205809734863399322950293 384647331321721843263295)
                  ·
                    rfl

theorem cell23_6741882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_6741882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741882 prefixEnd_6741882 := by exact prefixLift 6741882
  have htrace : WordTrace (prefixWord ++ tailWord_6741882) baseStart_6741882 baseEnd_6741882 := by
    simpa [prefixWord, tailWord_6741882, baseEnd_6741882] using wordTrace_append hprefix tailTrace_6741882
  have hstable : (prefixWord ++ tailWord_6741882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741882).length < 2 ^ (prefixWord ++ tailWord_6741882).sum := by decide
  have hdescent : baseEnd_6741882 < baseStart_6741882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741935 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_6741935 : Nat := 118140960795 + 6741935 * 2 ^ 59
def prefixEnd_6741935 : Nat := 4983230072969 + 3 ^ 40 * 6741935 * 2
def baseEnd_6741935 : Nat := 3461853196370184882006911

theorem tailTrace_6741935 : CollatzResearch.WordTrace tailWord_6741935 prefixEnd_6741935 3461853196370184882006911 := by
  unfold tailWord_6741935
  simp only [CollatzResearch.WordTrace]
  refine ⟨245898570830128400673019259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163932380553418933782012839 245898570830128400673019259)
  ·
    refine ⟨368847856245192601009528889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245898570830128400673019259 368847856245192601009528889)
    ·
      refine ⟨276635892183894450757146667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368847856245192601009528889 276635892183894450757146667)
      ·
        refine ⟨414953838275841676135720001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276635892183894450757146667 414953838275841676135720001)
        ·
          refine ⟨311215378706881257101790001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414953838275841676135720001 311215378706881257101790001)
          ·
            refine ⟨233411534030160942826342501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311215378706881257101790001 233411534030160942826342501)
            ·
              refine ⟨43764662630655176779939219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233411534030160942826342501 43764662630655176779939219)
              ·
                refine ⟨65646993945982765169908829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43764662630655176779939219 65646993945982765169908829)
                ·
                  refine ⟨24617622729743536938715811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65646993945982765169908829 24617622729743536938715811)
                  ·
                    refine ⟨36926434094615305408073717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24617622729743536938715811 36926434094615305408073717)
                    ·
                      refine ⟨3461853196370184882006911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36926434094615305408073717 3461853196370184882006911)
                      ·
                        rfl

theorem cell23_6741935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_6741935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741935 prefixEnd_6741935 := by exact prefixLift 6741935
  have htrace : WordTrace (prefixWord ++ tailWord_6741935) baseStart_6741935 baseEnd_6741935 := by
    simpa [prefixWord, tailWord_6741935, baseEnd_6741935] using wordTrace_append hprefix tailTrace_6741935
  have hstable : (prefixWord ++ tailWord_6741935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741935).length < 2 ^ (prefixWord ++ tailWord_6741935).sum := by decide
  have hdescent : baseEnd_6741935 < baseStart_6741935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741952 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3]
def baseStart_6741952 : Nat := 118140960795 + 6741952 * 2 ^ 59
def prefixEnd_6741952 : Nat := 4983230072969 + 3 ^ 40 * 6741952 * 2
def baseEnd_6741952 : Nat := 3461861925541311315494333

theorem tailTrace_6741952 : CollatzResearch.WordTrace tailWord_6741952 prefixEnd_6741952 3461861925541311315494333 := by
  unfold tailWord_6741952
  simp only [CollatzResearch.WordTrace]
  refine ⟨122949595435533406288194055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163932793914044541717592073 122949595435533406288194055)
  ·
    refine ⟨184424393153300109432291083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122949595435533406288194055 184424393153300109432291083)
    ·
      refine ⟨276636589729950164148436625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184424393153300109432291083 276636589729950164148436625)
      ·
        refine ⟨207477442297462623111327469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276636589729950164148436625 207477442297462623111327469)
        ·
          refine ⟨77804040861548483666747801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207477442297462623111327469 77804040861548483666747801)
          ·
            refine ⟨58353030646161362750060851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77804040861548483666747801 58353030646161362750060851)
            ·
              refine ⟨87529545969242044125091277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58353030646161362750060851 87529545969242044125091277)
              ·
                refine ⟨32823579738465766546909229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87529545969242044125091277 32823579738465766546909229)
                ·
                  refine ⟨12308842401924662455090961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32823579738465766546909229 12308842401924662455090961)
                  ·
                    refine ⟨9231631801443496841318221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12308842401924662455090961 9231631801443496841318221)
                    ·
                      refine ⟨3461861925541311315494333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9231631801443496841318221 3461861925541311315494333)
                      ·
                        rfl

theorem cell23_6741952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_6741952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741952 prefixEnd_6741952 := by exact prefixLift 6741952
  have htrace : WordTrace (prefixWord ++ tailWord_6741952) baseStart_6741952 baseEnd_6741952 := by
    simpa [prefixWord, tailWord_6741952, baseEnd_6741952] using wordTrace_append hprefix tailTrace_6741952
  have hstable : (prefixWord ++ tailWord_6741952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741952).length < 2 ^ (prefixWord ++ tailWord_6741952).sum := by decide
  have hdescent : baseEnd_6741952 < baseStart_6741952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741962 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_6741962 : Nat := 118140960795 + 6741962 * 2 ^ 59
def prefixEnd_6741962 : Nat := 4983230072969 + 3 ^ 40 * 6741962 * 2
def baseEnd_6741962 : Nat := 3461867060347856276369287

theorem tailTrace_6741962 : CollatzResearch.WordTrace tailWord_6741962 prefixEnd_6741962 3461867060347856276369287 := by
  unfold tailWord_6741962
  simp only [CollatzResearch.WordTrace]
  refine ⟨61474888900257646071063035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163933037067353722856168093 61474888900257646071063035)
  ·
    refine ⟨92212333350386469106594553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61474888900257646071063035 92212333350386469106594553)
    ·
      refine ⟨69159250012789851829945915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92212333350386469106594553 69159250012789851829945915)
      ·
        refine ⟨103738875019184777744918873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69159250012789851829945915 103738875019184777744918873)
        ·
          refine ⟨77804156264388583308689155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103738875019184777744918873 77804156264388583308689155)
          ·
            refine ⟨116706234396582874963033733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77804156264388583308689155 116706234396582874963033733)
            ·
              refine ⟨21882418949359289055568825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116706234396582874963033733 21882418949359289055568825)
              ·
                refine ⟨16411814212019466791676619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21882418949359289055568825 16411814212019466791676619)
                ·
                  refine ⟨24617721318029200187514929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16411814212019466791676619 24617721318029200187514929)
                  ·
                    refine ⟨18463290988521900140636197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24617721318029200187514929 18463290988521900140636197)
                    ·
                      refine ⟨3461867060347856276369287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18463290988521900140636197 3461867060347856276369287)
                      ·
                        rfl

theorem cell23_6741962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_6741962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741962 prefixEnd_6741962 := by exact prefixLift 6741962
  have htrace : WordTrace (prefixWord ++ tailWord_6741962) baseStart_6741962 baseEnd_6741962 := by
    simpa [prefixWord, tailWord_6741962, baseEnd_6741962] using wordTrace_append hprefix tailTrace_6741962
  have hstable : (prefixWord ++ tailWord_6741962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741962).length < 2 ^ (prefixWord ++ tailWord_6741962).sum := by decide
  have hdescent : baseEnd_6741962 < baseStart_6741962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741983 : List Nat := [1, 1, 2, 3, 4, 1, 2, 4, 1, 2, 2]
def baseStart_6741983 : Nat := 118140960795 + 6741983 * 2 ^ 59
def prefixEnd_6741983 : Nat := 4983230072969 + 3 ^ 40 * 6741983 * 2
def baseEnd_6741983 : Nat := 3461877843441600694206691

theorem tailTrace_6741983 : CollatzResearch.WordTrace tailWord_6741983 prefixEnd_6741983 3461877843441600694206691 := by
  unfold tailWord_6741983
  simp only [CollatzResearch.WordTrace]
  refine ⟨245900321533954504870766603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163933547689303003247177735 245900321533954504870766603)
  ·
    refine ⟨368850482300931757306149905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245900321533954504870766603 368850482300931757306149905)
    ·
      refine ⟨276637861725698817979612429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368850482300931757306149905 276637861725698817979612429)
      ·
        refine ⟨103739198147137056742354661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276637861725698817979612429 103739198147137056742354661)
        ·
          refine ⟨19451099652588198139191499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103739198147137056742354661 19451099652588198139191499)
          ·
            refine ⟨29176649478882297208787249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19451099652588198139191499 29176649478882297208787249)
            ·
              refine ⟨21882487109161722906590437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29176649478882297208787249 21882487109161722906590437)
              ·
                refine ⟨4102966332967823044985707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21882487109161722906590437 4102966332967823044985707)
                ·
                  refine ⟨6154449499451734567478561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102966332967823044985707 6154449499451734567478561)
                  ·
                    refine ⟨4615837124588800925608921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6154449499451734567478561 4615837124588800925608921)
                    ·
                      refine ⟨3461877843441600694206691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615837124588800925608921 3461877843441600694206691)
                      ·
                        rfl

theorem cell23_6741983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_6741983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741983 prefixEnd_6741983 := by exact prefixLift 6741983
  have htrace : WordTrace (prefixWord ++ tailWord_6741983) baseStart_6741983 baseEnd_6741983 := by
    simpa [prefixWord, tailWord_6741983, baseEnd_6741983] using wordTrace_append hprefix tailTrace_6741983
  have hstable : (prefixWord ++ tailWord_6741983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741983).length < 2 ^ (prefixWord ++ tailWord_6741983).sum := by decide
  have hdescent : baseEnd_6741983 < baseStart_6741983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741985 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 9]
def baseStart_6741985 : Nat := 118140960795 + 6741985 * 2 ^ 59
def prefixEnd_6741985 : Nat := 4983230072969 + 3 ^ 40 * 6741985 * 2
def baseEnd_6741985 : Nat := 1153959623467636562127227

theorem tailTrace_6741985 : CollatzResearch.WordTrace tailWord_6741985 prefixEnd_6741985 1153959623467636562127227 := by
  unfold tailWord_6741985
  simp only [CollatzResearch.WordTrace]
  refine ⟨245900394479947259212339409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163933596319964839474892939 245900394479947259212339409)
  ·
    refine ⟨184425295859960444409254557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245900394479947259212339409 184425295859960444409254557)
    ·
      refine ⟨69159485947485166653470459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184425295859960444409254557 69159485947485166653470459)
      ·
        refine ⟨103739228921227749980205689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69159485947485166653470459 103739228921227749980205689)
        ·
          refine ⟨77804421690920812485154267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103739228921227749980205689 77804421690920812485154267)
          ·
            refine ⟨116706632536381218727731401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77804421690920812485154267 116706632536381218727731401)
            ·
              refine ⟨87529974402285914045798551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116706632536381218727731401 87529974402285914045798551)
              ·
                refine ⟨131294961603428871068697827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87529974402285914045798551 131294961603428871068697827)
                ·
                  refine ⟨196942442405143306603046741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131294961603428871068697827 196942442405143306603046741)
                  ·
                    refine ⟨1153959623467636562127227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 196942442405143306603046741 1153959623467636562127227)
                    ·
                      rfl

theorem cell23_6741985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_6741985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741985 prefixEnd_6741985 := by exact prefixLift 6741985
  have htrace : WordTrace (prefixWord ++ tailWord_6741985) baseStart_6741985 baseEnd_6741985 := by
    simpa [prefixWord, tailWord_6741985, baseEnd_6741985] using wordTrace_append hprefix tailTrace_6741985
  have hstable : (prefixWord ++ tailWord_6741985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741985).length < 2 ^ (prefixWord ++ tailWord_6741985).sum := by decide
  have hdescent : baseEnd_6741985 < baseStart_6741985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741986 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_6741986 : Nat := 118140960795 + 6741986 * 2 ^ 59
def prefixEnd_6741986 : Nat := 4983230072969 + 3 ^ 40 * 6741986 * 2
def baseEnd_6741986 : Nat := 3461879383883564182469177

theorem tailTrace_6741986 : CollatzResearch.WordTrace tailWord_6741986 prefixEnd_6741986 3461879383883564182469177 := by
  unfold tailWord_6741986
  simp only [CollatzResearch.WordTrace]
  refine ⟨61475107738235909095781453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163933620635295757588750541 61475107738235909095781453)
  ·
    refine ⟨23053165401838465910918045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61475107738235909095781453 23053165401838465910918045)
    ·
      refine ⟨8644937025689424716594267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23053165401838465910918045 8644937025689424716594267)
      ·
        refine ⟨12967405538534137074891401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8644937025689424716594267 12967405538534137074891401)
        ·
          refine ⟨9725554153900602806168551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12967405538534137074891401 9725554153900602806168551)
          ·
            refine ⟨14588331230850904209252827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9725554153900602806168551 14588331230850904209252827)
            ·
              refine ⟨21882496846276356313879241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14588331230850904209252827 21882496846276356313879241)
              ·
                refine ⟨16411872634707267235409431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21882496846276356313879241 16411872634707267235409431)
                ·
                  refine ⟨24617808952060900853114147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16411872634707267235409431 24617808952060900853114147)
                  ·
                    refine ⟨36926713428091351279671221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24617808952060900853114147 36926713428091351279671221)
                    ·
                      refine ⟨3461879383883564182469177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36926713428091351279671221 3461879383883564182469177)
                      ·
                        rfl

theorem cell23_6741986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_6741986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741986 prefixEnd_6741986 := by exact prefixLift 6741986
  have htrace : WordTrace (prefixWord ++ tailWord_6741986) baseStart_6741986 baseEnd_6741986 := by
    simpa [prefixWord, tailWord_6741986, baseEnd_6741986] using wordTrace_append hprefix tailTrace_6741986
  have hstable : (prefixWord ++ tailWord_6741986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741986).length < 2 ^ (prefixWord ++ tailWord_6741986).sum := by decide
  have hdescent : baseEnd_6741986 < baseStart_6741986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741995 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5]
def baseStart_6741995 : Nat := 118140960795 + 6741995 * 2 ^ 59
def prefixEnd_6741995 : Nat := 4983230072969 + 3 ^ 40 * 6741995 * 2
def baseEnd_6741995 : Nat := 3461884005209454647256635

theorem tailTrace_6741995 : CollatzResearch.WordTrace tailWord_6741995 prefixEnd_6741995 3461884005209454647256635 := by
  unfold tailWord_6741995
  simp only [CollatzResearch.WordTrace]
  refine ⟨245900759209911030920203439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163933839473274020613468959 245900759209911030920203439)
  ·
    refine ⟨368851138814866546380305159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245900759209911030920203439 368851138814866546380305159)
    ·
      refine ⟨553276708222299819570457739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368851138814866546380305159 553276708222299819570457739)
      ·
        refine ⟨829915062333449729355686609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553276708222299819570457739 829915062333449729355686609)
        ·
          refine ⟨622436296750087297016764957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 829915062333449729355686609 622436296750087297016764957)
          ·
            refine ⟨233413611281282736381286859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 622436296750087297016764957 233413611281282736381286859)
            ·
              refine ⟨350120416921924104571930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233413611281282736381286859 350120416921924104571930289)
              ·
                refine ⟨262590312691443078428947717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350120416921924104571930289 262590312691443078428947717)
                ·
                  refine ⟨49235683629645577205427697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262590312691443078428947717 49235683629645577205427697)
                  ·
                    refine ⟨36926762722234182904070773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49235683629645577205427697 36926762722234182904070773)
                    ·
                      refine ⟨3461884005209454647256635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36926762722234182904070773 3461884005209454647256635)
                      ·
                        rfl

theorem cell23_6741995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_6741995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741995 prefixEnd_6741995 := by exact prefixLift 6741995
  have htrace : WordTrace (prefixWord ++ tailWord_6741995) baseStart_6741995 baseEnd_6741995 := by
    simpa [prefixWord, tailWord_6741995, baseEnd_6741995] using wordTrace_append hprefix tailTrace_6741995
  have hstable : (prefixWord ++ tailWord_6741995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741995).length < 2 ^ (prefixWord ++ tailWord_6741995).sum := by decide
  have hdescent : baseEnd_6741995 < baseStart_6741995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742006 : List Nat := [5, 1, 1, 1, 4, 2, 2, 7]
def baseStart_6742006 : Nat := 118140960795 + 6742006 * 2 ^ 59
def prefixEnd_6742006 : Nat := 4983230072969 + 3 ^ 40 * 6742006 * 2
def baseEnd_6742006 : Nat := 128218135314690892748855

theorem tailTrace_6742006 : CollatzResearch.WordTrace tailWord_6742006 prefixEnd_6742006 128218135314690892748855 := by
  unfold tailWord_6742006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15368822525804448737428367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163934106941914119865902581 15368822525804448737428367)
  ·
    refine ⟨23053233788706673106142551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15368822525804448737428367 23053233788706673106142551)
    ·
      refine ⟨34579850683060009659213827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23053233788706673106142551 34579850683060009659213827)
      ·
        refine ⟨51869776024590014488820741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34579850683060009659213827 51869776024590014488820741)
        ·
          refine ⟨9725583004610627716653889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51869776024590014488820741 9725583004610627716653889)
          ·
            refine ⟨7294187253457970787490417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9725583004610627716653889 7294187253457970787490417)
            ·
              refine ⟨5470640440093478090617813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7294187253457970787490417 5470640440093478090617813)
              ·
                refine ⟨128218135314690892748855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5470640440093478090617813 128218135314690892748855)
                ·
                  rfl

theorem cell23_6742006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_6742006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742006 prefixEnd_6742006 := by exact prefixLift 6742006
  have htrace : WordTrace (prefixWord ++ tailWord_6742006) baseStart_6742006 baseEnd_6742006 := by
    simpa [prefixWord, tailWord_6742006, baseEnd_6742006] using wordTrace_append hprefix tailTrace_6742006
  have hstable : (prefixWord ++ tailWord_6742006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742006).length < 2 ^ (prefixWord ++ tailWord_6742006).sum := by decide
  have hdescent : baseEnd_6742006 < baseStart_6742006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742015 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 1, 8]
def baseStart_6742015 : Nat := 118140960795 + 6742015 * 2 ^ 59
def prefixEnd_6742015 : Nat := 4983230072969 + 3 ^ 40 * 6742015 * 2
def baseEnd_6742015 : Nat := 1153964758274181523002181

theorem tailTrace_6742015 : CollatzResearch.WordTrace tailWord_6742015 prefixEnd_6742015 1153964758274181523002181 := by
  unfold tailWord_6742015
  simp only [CollatzResearch.WordTrace]
  refine ⟨245901488669838574335931499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163934325779892382890620999 245901488669838574335931499)
  ·
    refine ⟨368852233004757861503897249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245901488669838574335931499 368852233004757861503897249)
    ·
      refine ⟨276639174753568396127922937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368852233004757861503897249 276639174753568396127922937)
      ·
        refine ⟨207479381065176297095942203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276639174753568396127922937 207479381065176297095942203)
        ·
          refine ⟨311219071597764445643913305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207479381065176297095942203 311219071597764445643913305)
          ·
            refine ⟨233414303698323334232934979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311219071597764445643913305 233414303698323334232934979)
            ·
              refine ⟨350121455547485001349402469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233414303698323334232934979 350121455547485001349402469)
              ·
                refine ⟨65647772915153437753012963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350121455547485001349402469 65647772915153437753012963)
                ·
                  refine ⟨98471659372730156629519445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65647772915153437753012963 98471659372730156629519445)
                  ·
                    refine ⟨1153964758274181523002181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98471659372730156629519445 1153964758274181523002181)
                    ·
                      rfl

theorem cell23_6742015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_6742015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742015 prefixEnd_6742015 := by exact prefixLift 6742015
  have htrace : WordTrace (prefixWord ++ tailWord_6742015) baseStart_6742015 baseEnd_6742015 := by
    simpa [prefixWord, tailWord_6742015, baseEnd_6742015] using wordTrace_append hprefix tailTrace_6742015
  have hstable : (prefixWord ++ tailWord_6742015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742015).length < 2 ^ (prefixWord ++ tailWord_6742015).sum := by decide
  have hdescent : baseEnd_6742015 < baseStart_6742015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742086 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6742086 : Nat := 118140960795 + 6742086 * 2 ^ 59
def prefixEnd_6742086 : Nat := 4983230072969 + 3 ^ 40 * 6742086 * 2
def baseEnd_6742086 : Nat := 3461930731949013791218717

theorem tailTrace_6742086 : CollatzResearch.WordTrace tailWord_6742086 prefixEnd_6742086 3461930731949013791218717 := by
  unfold tailWord_6742086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684502445393167295680191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163936052168387568974510741 7684502445393167295680191)
  ·
    refine ⟨11526753668089750943520287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7684502445393167295680191 11526753668089750943520287)
    ·
      refine ⟨17290130502134626415280431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11526753668089750943520287 17290130502134626415280431)
      ·
        refine ⟨25935195753201939622920647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17290130502134626415280431 25935195753201939622920647)
        ·
          refine ⟨38902793629802909434380971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25935195753201939622920647 38902793629802909434380971)
          ·
            refine ⟨58354190444704364151571457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38902793629802909434380971 58354190444704364151571457)
            ·
              refine ⟨43765642833528273113678593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58354190444704364151571457 43765642833528273113678593)
              ·
                refine ⟨32824232125146204835258945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43765642833528273113678593 32824232125146204835258945)
                ·
                  refine ⟨24618174093859653626444209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32824232125146204835258945 24618174093859653626444209)
                  ·
                    refine ⟨18463630570394740219833157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24618174093859653626444209 18463630570394740219833157)
                    ·
                      refine ⟨3461930731949013791218717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18463630570394740219833157 3461930731949013791218717)
                      ·
                        rfl

theorem cell23_6742086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6742086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742086 prefixEnd_6742086 := by exact prefixLift 6742086
  have htrace : WordTrace (prefixWord ++ tailWord_6742086) baseStart_6742086 baseEnd_6742086 := by
    simpa [prefixWord, tailWord_6742086, baseEnd_6742086] using wordTrace_append hprefix tailTrace_6742086
  have hstable : (prefixWord ++ tailWord_6742086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742086).length < 2 ^ (prefixWord ++ tailWord_6742086).sum := by decide
  have hdescent : baseEnd_6742086 < baseStart_6742086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742129 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 1, 6, 2]
def baseStart_6742129 : Nat := 118140960795 + 6742129 * 2 ^ 59
def prefixEnd_6742129 : Nat := 4983230072969 + 3 ^ 40 * 6742129 * 2
def baseEnd_6742129 : Nat := 3461952811617157122981019

theorem tailTrace_6742129 : CollatzResearch.WordTrace tailWord_6742129 prefixEnd_6742129 3461952811617157122981019 := by
  unfold tailWord_6742129
  simp only [CollatzResearch.WordTrace]
  refine ⟨245905646591425571805581441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163937097727617047870387627 245905646591425571805581441)
  ·
    refine ⟨184429234943569178854186081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245905646591425571805581441 184429234943569178854186081)
    ·
      refine ⟨138321926207676884140639561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184429234943569178854186081 138321926207676884140639561)
      ·
        refine ⟨103741444655757663105479671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138321926207676884140639561 103741444655757663105479671)
        ·
          refine ⟨155612166983636494658219507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103741444655757663105479671 155612166983636494658219507)
          ·
            refine ⟨233418250475454741987329261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155612166983636494658219507 233418250475454741987329261)
            ·
              refine ⟨87531843928295528245248473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233418250475454741987329261 87531843928295528245248473)
              ·
                refine ⟨65648882946221646183936355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87531843928295528245248473 65648882946221646183936355)
                ·
                  refine ⟨98473324419332469275904533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65648882946221646183936355 98473324419332469275904533)
                  ·
                    refine ⟨4615937082156209497308025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98473324419332469275904533 4615937082156209497308025)
                    ·
                      refine ⟨3461952811617157122981019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615937082156209497308025 3461952811617157122981019)
                      ·
                        rfl

theorem cell23_6742129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_6742129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742129 prefixEnd_6742129 := by exact prefixLift 6742129
  have htrace : WordTrace (prefixWord ++ tailWord_6742129) baseStart_6742129 baseEnd_6742129 := by
    simpa [prefixWord, tailWord_6742129, baseEnd_6742129] using wordTrace_append hprefix tailTrace_6742129
  have hstable : (prefixWord ++ tailWord_6742129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742129).length < 2 ^ (prefixWord ++ tailWord_6742129).sum := by decide
  have hdescent : baseEnd_6742129 < baseStart_6742129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742192 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_6742192 : Nat := 118140960795 + 6742192 * 2 ^ 59
def prefixEnd_6742192 : Nat := 4983230072969 + 3 ^ 40 * 6742192 * 2
def baseEnd_6742192 : Nat := 3461985160898390376493229

theorem tailTrace_6742192 : CollatzResearch.WordTrace tailWord_6742192 prefixEnd_6742192 3461985160898390376493229 := by
  unfold tailWord_6742192
  simp only [CollatzResearch.WordTrace]
  refine ⟨122953972195098666782562415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163938629593464889043416553 122953972195098666782562415)
  ·
    refine ⟨184430958292648000173843623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122953972195098666782562415 184430958292648000173843623)
    ·
      refine ⟨276646437438972000260765435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184430958292648000173843623 276646437438972000260765435)
      ·
        refine ⟨414969656158458000391148153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276646437438972000260765435 414969656158458000391148153)
        ·
          refine ⟨311227242118843500293361115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414969656158458000391148153 311227242118843500293361115)
          ·
            refine ⟨466840863178265250440041673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311227242118843500293361115 466840863178265250440041673)
            ·
              refine ⟨350130647383698937830031255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466840863178265250440041673 350130647383698937830031255)
              ·
                refine ⟨525195971075548406745046883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350130647383698937830031255 525195971075548406745046883)
                ·
                  refine ⟨787793956613322610117570325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525195971075548406745046883 787793956613322610117570325)
                  ·
                    refine ⟨36927841716249497349261109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 787793956613322610117570325 36927841716249497349261109)
                    ·
                      refine ⟨3461985160898390376493229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36927841716249497349261109 3461985160898390376493229)
                      ·
                        rfl

theorem cell23_6742192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_6742192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742192 prefixEnd_6742192 := by exact prefixLift 6742192
  have htrace : WordTrace (prefixWord ++ tailWord_6742192) baseStart_6742192 baseEnd_6742192 := by
    simpa [prefixWord, tailWord_6742192, baseEnd_6742192] using wordTrace_append hprefix tailTrace_6742192
  have hstable : (prefixWord ++ tailWord_6742192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742192).length < 2 ^ (prefixWord ++ tailWord_6742192).sum := by decide
  have hdescent : baseEnd_6742192 < baseStart_6742192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742213 : List Nat := [1, 3, 1, 1, 1, 1, 4, 6, 1, 1, 3]
def baseStart_6742213 : Nat := 118140960795 + 6742213 * 2 ^ 59
def prefixEnd_6742213 : Nat := 4983230072969 + 3 ^ 40 * 6742213 * 2
def baseEnd_6742213 : Nat := 3461995943992134794330633

theorem tailTrace_6742213 : CollatzResearch.WordTrace tailWord_6742213 prefixEnd_6742213 3461995943992134794330633 := by
  unfold tailWord_6742213
  simp only [CollatzResearch.WordTrace]
  refine ⟨245908710323121254151639293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163939140215414169434426195 245908710323121254151639293)
  ·
    refine ⟨92215766371170470306864735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245908710323121254151639293 92215766371170470306864735)
    ·
      refine ⟨138323649556755705460297103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92215766371170470306864735 138323649556755705460297103)
      ·
        refine ⟨207485474335133558190445655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138323649556755705460297103 207485474335133558190445655)
        ·
          refine ⟨311228211502700337285668483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207485474335133558190445655 311228211502700337285668483)
          ·
            refine ⟨466842317254050505928502725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311228211502700337285668483 466842317254050505928502725)
            ·
              refine ⟨87532934485134469861594261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466842317254050505928502725 87532934485134469861594261)
              ·
                refine ⟨4103106303990678274762231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87532934485134469861594261 4103106303990678274762231)
                ·
                  refine ⟨6154659455986017412143347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103106303990678274762231 6154659455986017412143347)
                  ·
                    refine ⟨9231989183979026118215021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6154659455986017412143347 9231989183979026118215021)
                    ·
                      refine ⟨3461995943992134794330633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9231989183979026118215021 3461995943992134794330633)
                      ·
                        rfl

theorem cell23_6742213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_6742213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742213 prefixEnd_6742213 := by exact prefixLift 6742213
  have htrace : WordTrace (prefixWord ++ tailWord_6742213) baseStart_6742213 baseEnd_6742213 := by
    simpa [prefixWord, tailWord_6742213, baseEnd_6742213] using wordTrace_append hprefix tailTrace_6742213
  have hstable : (prefixWord ++ tailWord_6742213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742213).length < 2 ^ (prefixWord ++ tailWord_6742213).sum := by decide
  have hdescent : baseEnd_6742213 < baseStart_6742213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742219 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 4]
def baseStart_6742219 : Nat := 118140960795 + 6742219 * 2 ^ 59
def prefixEnd_6742219 : Nat := 4983230072969 + 3 ^ 40 * 6742219 * 2
def baseEnd_6742219 : Nat := 3461999024876061770855605

theorem tailTrace_6742219 : CollatzResearch.WordTrace tailWord_6742219 prefixEnd_6742219 3461999024876061770855605 := by
  unfold tailWord_6742219
  simp only [CollatzResearch.WordTrace]
  refine ⟨245908929161099517176357711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163939286107399678117571807 245908929161099517176357711)
  ·
    refine ⟨368863393741649275764536567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245908929161099517176357711 368863393741649275764536567)
    ·
      refine ⟨553295090612473913646804851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368863393741649275764536567 553295090612473913646804851)
      ·
        refine ⟨829942635918710870470207277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553295090612473913646804851 829942635918710870470207277)
        ·
          refine ⟨311228488469516576426327729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 829942635918710870470207277 311228488469516576426327729)
          ·
            refine ⟨233421366352137432319745797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311228488469516576426327729 233421366352137432319745797)
            ·
              refine ⟨43766506191025768559952337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233421366352137432319745797 43766506191025768559952337)
              ·
                refine ⟨32824879643269326419964253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43766506191025768559952337 32824879643269326419964253)
                ·
                  refine ⟨12309329866225997407486595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32824879643269326419964253 12309329866225997407486595)
                  ·
                    refine ⟨18463994799338996111229893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12309329866225997407486595 18463994799338996111229893)
                    ·
                      refine ⟨3461999024876061770855605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18463994799338996111229893 3461999024876061770855605)
                      ·
                        rfl

theorem cell23_6742219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 4].length) (baseStart_6742219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742219 prefixEnd_6742219 := by exact prefixLift 6742219
  have htrace : WordTrace (prefixWord ++ tailWord_6742219) baseStart_6742219 baseEnd_6742219 := by
    simpa [prefixWord, tailWord_6742219, baseEnd_6742219] using wordTrace_append hprefix tailTrace_6742219
  have hstable : (prefixWord ++ tailWord_6742219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742219).length < 2 ^ (prefixWord ++ tailWord_6742219).sum := by decide
  have hdescent : baseEnd_6742219 < baseStart_6742219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742220 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 6]
def baseStart_6742220 : Nat := 118140960795 + 6742220 * 2 ^ 59
def prefixEnd_6742220 : Nat := 4983230072969 + 3 ^ 40 * 6742220 * 2
def baseEnd_6742220 : Nat := 384666615372968474104789

theorem tailTrace_6742220 : CollatzResearch.WordTrace tailWord_6742220 prefixEnd_6742220 384666615372968474104789 := by
  unfold tailWord_6742220
  simp only [CollatzResearch.WordTrace]
  refine ⟨122954482817047947173572057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163939310422730596231429409 122954482817047947173572057)
  ·
    refine ⟨92215862112785960380179043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122954482817047947173572057 92215862112785960380179043)
    ·
      refine ⟨138323793169178940570268565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92215862112785960380179043 138323793169178940570268565)
      ·
        refine ⟨6483927804805262839231339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138323793169178940570268565 6483927804805262839231339)
        ·
          refine ⟨9725891707207894258847009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6483927804805262839231339 9725891707207894258847009)
          ·
            refine ⟨7294418780405920694135257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9725891707207894258847009 7294418780405920694135257)
            ·
              refine ⟨5470814085304440520601443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7294418780405920694135257 5470814085304440520601443)
              ·
                refine ⟨8206221127956660780902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470814085304440520601443 8206221127956660780902165)
                ·
                  refine ⟨384666615372968474104789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8206221127956660780902165 384666615372968474104789)
                  ·
                    rfl

theorem cell23_6742220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_6742220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742220 prefixEnd_6742220 := by exact prefixLift 6742220
  have htrace : WordTrace (prefixWord ++ tailWord_6742220) baseStart_6742220 baseEnd_6742220 := by
    simpa [prefixWord, tailWord_6742220, baseEnd_6742220] using wordTrace_append hprefix tailTrace_6742220
  have hstable : (prefixWord ++ tailWord_6742220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742220).length < 2 ^ (prefixWord ++ tailWord_6742220).sum := by decide
  have hdescent : baseEnd_6742220 < baseStart_6742220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742249 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_6742249 : Nat := 118140960795 + 6742249 * 2 ^ 59
def prefixEnd_6742249 : Nat := 4983230072969 + 3 ^ 40 * 6742249 * 2
def baseEnd_6742249 : Nat := 3462014429295696653480467

theorem tailTrace_6742249 : CollatzResearch.WordTrace tailWord_6742249 prefixEnd_6742249 3462014429295696653480467 := by
  unfold tailWord_6742249
  simp only [CollatzResearch.WordTrace]
  refine ⟨245910023350990832299949801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163940015567327221533299867 245910023350990832299949801)
  ·
    refine ⟨184432517513243124224962351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245910023350990832299949801 184432517513243124224962351)
    ·
      refine ⟨276648776269864686337443527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184432517513243124224962351 276648776269864686337443527)
      ·
        refine ⟨414973164404797029506165291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276648776269864686337443527 414973164404797029506165291)
        ·
          refine ⟨622459746607195544259247937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414973164404797029506165291 622459746607195544259247937)
          ·
            refine ⟨466844809955396658194435953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622459746607195544259247937 466844809955396658194435953)
            ·
              refine ⟨350133607466547493645826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466844809955396658194435953 350133607466547493645826965)
              ·
                refine ⟨16412512849994413764648139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 350133607466547493645826965 16412512849994413764648139)
                ·
                  refine ⟨24618769274991620646972209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16412512849994413764648139 24618769274991620646972209)
                  ·
                    refine ⟨18464076956243715485229157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24618769274991620646972209 18464076956243715485229157)
                    ·
                      refine ⟨3462014429295696653480467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18464076956243715485229157 3462014429295696653480467)
                      ·
                        rfl

theorem cell23_6742249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_6742249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742249 prefixEnd_6742249 := by exact prefixLift 6742249
  have htrace : WordTrace (prefixWord ++ tailWord_6742249) baseStart_6742249 baseEnd_6742249 := by
    simpa [prefixWord, tailWord_6742249, baseEnd_6742249] using wordTrace_append hprefix tailTrace_6742249
  have hstable : (prefixWord ++ tailWord_6742249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742249).length < 2 ^ (prefixWord ++ tailWord_6742249).sum := by decide
  have hdescent : baseEnd_6742249 < baseStart_6742249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742256 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3]
def baseStart_6742256 : Nat := 118140960795 + 6742256 * 2 ^ 59
def prefixEnd_6742256 : Nat := 4983230072969 + 3 ^ 40 * 6742256 * 2
def baseEnd_6742256 : Nat := 3462018023660278126092935

theorem tailTrace_6742256 : CollatzResearch.WordTrace tailWord_6742256 prefixEnd_6742256 3462018023660278126092935 := by
  unfold tailWord_6742256
  simp only [CollatzResearch.WordTrace]
  refine ⟨122955139330982736247727311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163940185774643648330303081 122955139330982736247727311)
  ·
    refine ⟨184432708996474104371590967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122955139330982736247727311 184432708996474104371590967)
    ·
      refine ⟨276649063494711156557386451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184432708996474104371590967 276649063494711156557386451)
      ·
        refine ⟨414973595242066734836079677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276649063494711156557386451 414973595242066734836079677)
        ·
          refine ⟨155615098215775025563529879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414973595242066734836079677 155615098215775025563529879)
          ·
            refine ⟨233422647323662538345294819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155615098215775025563529879 233422647323662538345294819)
            ·
              refine ⟨350133970985493807517942229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233422647323662538345294819 350133970985493807517942229)
              ·
                refine ⟨8206264944972511113701771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 350133970985493807517942229 8206264944972511113701771)
                ·
                  refine ⟨12309397417458766670552657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8206264944972511113701771 12309397417458766670552657)
                  ·
                    refine ⟨9232048063094075002914493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12309397417458766670552657 9232048063094075002914493)
                    ·
                      refine ⟨3462018023660278126092935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232048063094075002914493 3462018023660278126092935)
                      ·
                        rfl

theorem cell23_6742256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_6742256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742256 prefixEnd_6742256 := by exact prefixLift 6742256
  have htrace : WordTrace (prefixWord ++ tailWord_6742256) baseStart_6742256 baseEnd_6742256 := by
    simpa [prefixWord, tailWord_6742256, baseEnd_6742256] using wordTrace_append hprefix tailTrace_6742256
  have hstable : (prefixWord ++ tailWord_6742256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742256).length < 2 ^ (prefixWord ++ tailWord_6742256).sum := by decide
  have hdescent : baseEnd_6742256 < baseStart_6742256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742270 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6742270 : Nat := 118140960795 + 6742270 * 2 ^ 59
def prefixEnd_6742270 : Nat := 4983230072969 + 3 ^ 40 * 6742270 * 2
def baseEnd_6742270 : Nat := 3462025212389441071317871

theorem tailTrace_6742270 : CollatzResearch.WordTrace tailWord_6742270 prefixEnd_6742270 3462025212389441071317871 := by
  unfold tailWord_6742270
  simp only [CollatzResearch.WordTrace]
  refine ⟨30738848660489344110808033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163940526189276501924309509 30738848660489344110808033)
  ·
    refine ⟨23054136495367008083106025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30738848660489344110808033 23054136495367008083106025)
    ·
      refine ⟨17290602371525256062329519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23054136495367008083106025 17290602371525256062329519)
      ·
        refine ⟨25935903557287884093494279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17290602371525256062329519 25935903557287884093494279)
        ·
          refine ⟨38903855335931826140241419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25935903557287884093494279 38903855335931826140241419)
          ·
            refine ⟨58355783003897739210362129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38903855335931826140241419 58355783003897739210362129)
            ·
              refine ⟨43766837252923304407771597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58355783003897739210362129 43766837252923304407771597)
              ·
                refine ⟨16412563969846239152914349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43766837252923304407771597 16412563969846239152914349)
                ·
                  refine ⟨6154711488692339682342881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16412563969846239152914349 6154711488692339682342881)
                  ·
                    refine ⟨4616033616519254761757161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6154711488692339682342881 4616033616519254761757161)
                    ·
                      refine ⟨3462025212389441071317871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616033616519254761757161 3462025212389441071317871)
                      ·
                        rfl

theorem cell23_6742270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6742270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742270 prefixEnd_6742270 := by exact prefixLift 6742270
  have htrace : WordTrace (prefixWord ++ tailWord_6742270) baseStart_6742270 baseEnd_6742270 := by
    simpa [prefixWord, tailWord_6742270, baseEnd_6742270] using wordTrace_append hprefix tailTrace_6742270
  have hstable : (prefixWord ++ tailWord_6742270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742270).length < 2 ^ (prefixWord ++ tailWord_6742270).sum := by decide
  have hdescent : baseEnd_6742270 < baseStart_6742270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742319 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 2, 6]
def baseStart_6742319 : Nat := 118140960795 + 6742319 * 2 ^ 59
def prefixEnd_6742319 : Nat := 4983230072969 + 3 ^ 40 * 6742319 * 2
def baseEnd_6742319 : Nat := 1154016790980503793201715

theorem tailTrace_6742319 : CollatzResearch.WordTrace tailWord_6742319 prefixEnd_6742319 1154016790980503793201715 := by
  unfold tailWord_6742319
  simp only [CollatzResearch.WordTrace]
  refine ⟨245912576460737234254998011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163941717640491489503332007 245912576460737234254998011)
  ·
    refine ⟨368868864691105851382497017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245912576460737234254998011 368868864691105851382497017)
    ·
      refine ⟨276651648518329388536872763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368868864691105851382497017 276651648518329388536872763)
      ·
        refine ⟨414977472777494082805309145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276651648518329388536872763 414977472777494082805309145)
        ·
          refine ⟨311233104583120562103981859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414977472777494082805309145 311233104583120562103981859)
          ·
            refine ⟨466849656874680843155972789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311233104583120562103981859 466849656874680843155972789)
            ·
              refine ⟨43767155332001329045872449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 466849656874680843155972789 43767155332001329045872449)
              ·
                refine ⟨32825366499000996784404337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43767155332001329045872449 32825366499000996784404337)
                ·
                  refine ⟨24619024874250747588303253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32825366499000996784404337 24619024874250747588303253)
                  ·
                    refine ⟨1154016790980503793201715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24619024874250747588303253 1154016790980503793201715)
                    ·
                      rfl

theorem cell23_6742319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_6742319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742319 prefixEnd_6742319 := by exact prefixLift 6742319
  have htrace : WordTrace (prefixWord ++ tailWord_6742319) baseStart_6742319 baseEnd_6742319 := by
    simpa [prefixWord, tailWord_6742319, baseEnd_6742319] using wordTrace_append hprefix tailTrace_6742319
  have hstable : (prefixWord ++ tailWord_6742319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742319).length < 2 ^ (prefixWord ++ tailWord_6742319).sum := by decide
  have hdescent : baseEnd_6742319 < baseStart_6742319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742337 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6742337 : Nat := 118140960795 + 6742337 * 2 ^ 59
def prefixEnd_6742337 : Nat := 4983230072969 + 3 ^ 40 * 6742337 * 2
def baseEnd_6742337 : Nat := 3462059615593292309180063

theorem tailTrace_6742337 : CollatzResearch.WordTrace tailWord_6742337 prefixEnd_6742337 3462059615593292309180063 := by
  unfold tailWord_6742337
  simp only [CollatzResearch.WordTrace]
  refine ⟨245913232974672023329153265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163942155316448015552768843 245913232974672023329153265)
  ·
    refine ⟨184434924731004017496864949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245913232974672023329153265 184434924731004017496864949)
    ·
      refine ⟨17290774193531626640331089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184434924731004017496864949 17290774193531626640331089)
      ·
        refine ⟨12968080645148719980248317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17290774193531626640331089 12968080645148719980248317)
        ·
          refine ⟨4863030241930769992593119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12968080645148719980248317 4863030241930769992593119)
          ·
            refine ⟨7294545362896154988889679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863030241930769992593119 7294545362896154988889679)
            ·
              refine ⟨10941818044344232483334519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7294545362896154988889679 10941818044344232483334519)
              ·
                refine ⟨16412727066516348725001779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10941818044344232483334519 16412727066516348725001779)
                ·
                  refine ⟨24619090599774523087502669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16412727066516348725001779 24619090599774523087502669)
                  ·
                    refine ⟨9232158974915446157813501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24619090599774523087502669 9232158974915446157813501)
                    ·
                      refine ⟨3462059615593292309180063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232158974915446157813501 3462059615593292309180063)
                      ·
                        rfl

theorem cell23_6742337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6742337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742337 prefixEnd_6742337 := by exact prefixLift 6742337
  have htrace : WordTrace (prefixWord ++ tailWord_6742337) baseStart_6742337 baseEnd_6742337 := by
    simpa [prefixWord, tailWord_6742337, baseEnd_6742337] using wordTrace_append hprefix tailTrace_6742337
  have hstable : (prefixWord ++ tailWord_6742337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742337).length < 2 ^ (prefixWord ++ tailWord_6742337).sum := by decide
  have hdescent : baseEnd_6742337 < baseStart_6742337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742369 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6742369 : Nat := 118140960795 + 6742369 * 2 ^ 59
def prefixEnd_6742369 : Nat := 4983230072969 + 3 ^ 40 * 6742369 * 2
def baseEnd_6742369 : Nat := 3462076046974236183979915

theorem tailTrace_6742369 : CollatzResearch.WordTrace tailWord_6742369 prefixEnd_6742369 3462076046974236183979915 := by
  unfold tailWord_6742369
  simp only [CollatzResearch.WordTrace]
  refine ⟨245914400110556092794318161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163942933407037395196212107 245914400110556092794318161)
  ·
    refine ⟨184435800082917069595738621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245914400110556092794318161 184435800082917069595738621)
    ·
      refine ⟨69163425031093901098401983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184435800082917069595738621 69163425031093901098401983)
      ·
        refine ⟨103745137546640851647602975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69163425031093901098401983 103745137546640851647602975)
        ·
          refine ⟨155617706319961277471404463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103745137546640851647602975 155617706319961277471404463)
          ·
            refine ⟨233426559479941916207106695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155617706319961277471404463 233426559479941916207106695)
            ·
              refine ⟨350139839219912874310660043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233426559479941916207106695 350139839219912874310660043)
              ·
                refine ⟨525209758829869311465990065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350139839219912874310660043 525209758829869311465990065)
                ·
                  refine ⟨393907319122401983599492549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525209758829869311465990065 393907319122401983599492549)
                  ·
                    refine ⟨73857622335450371924904853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393907319122401983599492549 73857622335450371924904853)
                    ·
                      refine ⟨3462076046974236183979915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73857622335450371924904853 3462076046974236183979915)
                      ·
                        rfl

theorem cell23_6742369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6742369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742369 prefixEnd_6742369 := by exact prefixLift 6742369
  have htrace : WordTrace (prefixWord ++ tailWord_6742369) baseStart_6742369 baseEnd_6742369 := by
    simpa [prefixWord, tailWord_6742369, baseEnd_6742369] using wordTrace_append hprefix tailTrace_6742369
  have hstable : (prefixWord ++ tailWord_6742369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742369).length < 2 ^ (prefixWord ++ tailWord_6742369).sum := by decide
  have hdescent : baseEnd_6742369 < baseStart_6742369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742419 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11]
def baseStart_6742419 : Nat := 118140960795 + 6742419 * 2 ^ 59
def prefixEnd_6742419 : Nat := 4983230072969 + 3 ^ 40 * 6742419 * 2
def baseEnd_6742419 : Nat := 3462101721006960988354685

theorem tailTrace_6742419 : CollatzResearch.WordTrace tailWord_6742419 prefixEnd_6742419 3462101721006960988354685 := by
  unfold tailWord_6742419
  simp only [CollatzResearch.WordTrace]
  refine ⟨245916223760374951333638311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163944149173583300889092207 245916223760374951333638311)
  ·
    refine ⟨368874335640562427000457467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245916223760374951333638311 368874335640562427000457467)
    ·
      refine ⟨553311503460843640500686201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368874335640562427000457467 553311503460843640500686201)
      ·
        refine ⟨414983627595632730375514651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553311503460843640500686201 414983627595632730375514651)
        ·
          refine ⟨622475441393449095563271977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414983627595632730375514651 622475441393449095563271977)
          ·
            refine ⟨466856581045086821672453983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622475441393449095563271977 466856581045086821672453983)
            ·
              refine ⟨700284871567630232508680975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466856581045086821672453983 700284871567630232508680975)
              ·
                refine ⟨1050427307351445348763021463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700284871567630232508680975 1050427307351445348763021463)
                ·
                  refine ⟨1575640961027168023144532195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050427307351445348763021463 1575640961027168023144532195)
                  ·
                    refine ⟨2363461441540752034716798293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1575640961027168023144532195 2363461441540752034716798293)
                    ·
                      refine ⟨3462101721006960988354685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2363461441540752034716798293 3462101721006960988354685)
                      ·
                        rfl

theorem cell23_6742419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_6742419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742419 prefixEnd_6742419 := by exact prefixLift 6742419
  have htrace : WordTrace (prefixWord ++ tailWord_6742419) baseStart_6742419 baseEnd_6742419 := by
    simpa [prefixWord, tailWord_6742419, baseEnd_6742419] using wordTrace_append hprefix tailTrace_6742419
  have hstable : (prefixWord ++ tailWord_6742419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742419).length < 2 ^ (prefixWord ++ tailWord_6742419).sum := by decide
  have hdescent : baseEnd_6742419 < baseStart_6742419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742430 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6742430 : Nat := 118140960795 + 6742430 * 2 ^ 59
def prefixEnd_6742430 : Nat := 4983230072969 + 3 ^ 40 * 6742430 * 2
def baseEnd_6742430 : Nat := 1154035789764720148439045

theorem tailTrace_6742430 : CollatzResearch.WordTrace tailWord_6742430 prefixEnd_6742430 1154035789764720148439045 := by
  unfold tailWord_6742430
  simp only [CollatzResearch.WordTrace]
  refine ⟨30739578120416887526536093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163944416642223400141525829 30739578120416887526536093)
  ·
    refine ⟨11527341795156332822451035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30739578120416887526536093 11527341795156332822451035)
    ·
      refine ⟨17291012692734499233676553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11527341795156332822451035 17291012692734499233676553)
      ·
        refine ⟨12968259519550874425257415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17291012692734499233676553 12968259519550874425257415)
        ·
          refine ⟨19452389279326311637886123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12968259519550874425257415 19452389279326311637886123)
          ·
            refine ⟨29178583918989467456829185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19452389279326311637886123 29178583918989467456829185)
            ·
              refine ⟨21883937939242100592621889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29178583918989467456829185 21883937939242100592621889)
              ·
                refine ⟨16412953454431575444466417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21883937939242100592621889 16412953454431575444466417)
                ·
                  refine ⟨12309715090823681583349813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16412953454431575444466417 12309715090823681583349813)
                  ·
                    refine ⟨1154035789764720148439045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12309715090823681583349813 1154035789764720148439045)
                    ·
                      rfl

theorem cell23_6742430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6742430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742430 prefixEnd_6742430 := by exact prefixLift 6742430
  have htrace : WordTrace (prefixWord ++ tailWord_6742430) baseStart_6742430 baseEnd_6742430 := by
    simpa [prefixWord, tailWord_6742430, baseEnd_6742430] using wordTrace_append hprefix tailTrace_6742430
  have hstable : (prefixWord ++ tailWord_6742430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742430).length < 2 ^ (prefixWord ++ tailWord_6742430).sum := by decide
  have hdescent : baseEnd_6742430 < baseStart_6742430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742460 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_6742460 : Nat := 118140960795 + 6742460 * 2 ^ 59
def prefixEnd_6742460 : Nat := 4983230072969 + 3 ^ 40 * 6742460 * 2
def baseEnd_6742460 : Nat := 1154040924571265109313999

theorem tailTrace_6742460 : CollatzResearch.WordTrace tailWord_6742460 prefixEnd_6742460 1154040924571265109313999 := by
  unfold tailWord_6742460
  simp only [CollatzResearch.WordTrace]
  refine ⟨122958859576613207667940417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163945146102150943557253889 122958859576613207667940417)
  ·
    refine ⟨92219144682459905750955313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122958859576613207667940417 92219144682459905750955313)
    ·
      refine ⟨69164358511844929313216485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92219144682459905750955313 69164358511844929313216485)
      ·
        refine ⟨12968317220970924246228091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69164358511844929313216485 12968317220970924246228091)
        ·
          refine ⟨19452475831456386369342137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12968317220970924246228091 19452475831456386369342137)
          ·
            refine ⟨14589356873592289777006603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19452475831456386369342137 14589356873592289777006603)
            ·
              refine ⟨21884035310388434665509905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14589356873592289777006603 21884035310388434665509905)
              ·
                refine ⟨16413026482791325999132429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21884035310388434665509905 16413026482791325999132429)
                ·
                  refine ⟨6154884931046747249674661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16413026482791325999132429 6154884931046747249674661)
                  ·
                    refine ⟨1154040924571265109313999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6154884931046747249674661 1154040924571265109313999)
                    ·
                      rfl

theorem cell23_6742460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_6742460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742460 prefixEnd_6742460 := by exact prefixLift 6742460
  have htrace : WordTrace (prefixWord ++ tailWord_6742460) baseStart_6742460 baseEnd_6742460 := by
    simpa [prefixWord, tailWord_6742460, baseEnd_6742460] using wordTrace_append hprefix tailTrace_6742460
  have hstable : (prefixWord ++ tailWord_6742460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742460).length < 2 ^ (prefixWord ++ tailWord_6742460).sum := by decide
  have hdescent : baseEnd_6742460 < baseStart_6742460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742510 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_6742510 : Nat := 118140960795 + 6742510 * 2 ^ 59
def prefixEnd_6742510 : Nat := 4983230072969 + 3 ^ 40 * 6742510 * 2
def baseEnd_6742510 : Nat := 3462148447746520132316767

theorem tailTrace_6742510 : CollatzResearch.WordTrace tailWord_6742510 prefixEnd_6742510 3462148447746520132316767 := by
  unfold tailWord_6742510
  simp only [CollatzResearch.WordTrace]
  refine ⟨30739942850380659234400123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163946361868696849250133989 30739942850380659234400123)
  ·
    refine ⟨46109914275570988851600185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30739942850380659234400123 46109914275570988851600185)
    ·
      refine ⟨34582435706678241638700139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46109914275570988851600185 34582435706678241638700139)
      ·
        refine ⟨51873653560017362458050209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34582435706678241638700139 51873653560017362458050209)
        ·
          refine ⟨38905240170013021843537657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51873653560017362458050209 38905240170013021843537657)
          ·
            refine ⟨29178930127509766382653243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38905240170013021843537657 29178930127509766382653243)
            ·
              refine ⟨43768395191264649573979865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29178930127509766382653243 43768395191264649573979865)
              ·
                refine ⟨32826296393448487180484899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43768395191264649573979865 32826296393448487180484899)
                ·
                  refine ⟨49239444590172730770727349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32826296393448487180484899 49239444590172730770727349)
                  ·
                    refine ⟨4616197930328693509755689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49239444590172730770727349 4616197930328693509755689)
                    ·
                      refine ⟨3462148447746520132316767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616197930328693509755689 3462148447746520132316767)
                      ·
                        rfl

theorem cell23_6742510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_6742510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742510 prefixEnd_6742510 := by exact prefixLift 6742510
  have htrace : WordTrace (prefixWord ++ tailWord_6742510) baseStart_6742510 baseEnd_6742510 := by
    simpa [prefixWord, tailWord_6742510, baseEnd_6742510] using wordTrace_append hprefix tailTrace_6742510
  have hstable : (prefixWord ++ tailWord_6742510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742510).length < 2 ^ (prefixWord ++ tailWord_6742510).sum := by decide
  have hdescent : baseEnd_6742510 < baseStart_6742510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742533 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_6742533 : Nat := 118140960795 + 6742533 * 2 ^ 59
def prefixEnd_6742533 : Nat := 4983230072969 + 3 ^ 40 * 6742533 * 2
def baseEnd_6742533 : Nat := 1154053419267191180776387

theorem tailTrace_6742533 : CollatzResearch.WordTrace tailWord_6742533 prefixEnd_6742533 1154053419267191180776387 := by
  unfold tailWord_6742533
  simp only [CollatzResearch.WordTrace]
  refine ⟨245920381681961948803288253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163946921121307965868858835 245920381681961948803288253)
  ·
    refine ⟨92220143130735730801233095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245920381681961948803288253 92220143130735730801233095)
    ·
      refine ⟨138330214696103596201849643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92220143130735730801233095 138330214696103596201849643)
      ·
        refine ⟨207495322044155394302774465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138330214696103596201849643 207495322044155394302774465)
        ·
          refine ⟨155621491533116545727080849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207495322044155394302774465 155621491533116545727080849)
          ·
            refine ⟨116716118649837409295310637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155621491533116545727080849 116716118649837409295310637)
            ·
              refine ⟨43768544493689028485741489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116716118649837409295310637 43768544493689028485741489)
              ·
                refine ⟨32826408370266771364306117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43768544493689028485741489 32826408370266771364306117)
                ·
                  refine ⟨6154951569425019630807397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32826408370266771364306117 6154951569425019630807397)
                  ·
                    refine ⟨1154053419267191180776387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6154951569425019630807397 1154053419267191180776387)
                    ·
                      rfl

theorem cell23_6742533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_6742533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742533 prefixEnd_6742533 := by exact prefixLift 6742533
  have htrace : WordTrace (prefixWord ++ tailWord_6742533) baseStart_6742533 baseEnd_6742533 := by
    simpa [prefixWord, tailWord_6742533, baseEnd_6742533] using wordTrace_append hprefix tailTrace_6742533
  have hstable : (prefixWord ++ tailWord_6742533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742533).length < 2 ^ (prefixWord ++ tailWord_6742533).sum := by decide
  have hdescent : baseEnd_6742533 < baseStart_6742533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742540 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_6742540 : Nat := 118140960795 + 6742540 * 2 ^ 59
def prefixEnd_6742540 : Nat := 4983230072969 + 3 ^ 40 * 6742540 * 2
def baseEnd_6742540 : Nat := 3462163852166155014941629

theorem tailTrace_6742540 : CollatzResearch.WordTrace tailWord_6742540 prefixEnd_6742540 3462163852166155014941629 := by
  unfold tailWord_6742540
  simp only [CollatzResearch.WordTrace]
  refine ⟨122960318496468294499396537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163947091328624392665862049 122960318496468294499396537)
  ·
    refine ⟨92220238872351220874547403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122960318496468294499396537 92220238872351220874547403)
    ·
      refine ⟨138330358308526831311821105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92220238872351220874547403 138330358308526831311821105)
      ·
        refine ⟨103747768731395123483865829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138330358308526831311821105 103747768731395123483865829)
        ·
          refine ⟨19452706637136585653224843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103747768731395123483865829 19452706637136585653224843)
          ·
            refine ⟨29179059955704878479837265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19452706637136585653224843 29179059955704878479837265)
            ·
              refine ⟨21884294966778658859877949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29179059955704878479837265 21884294966778658859877949)
              ·
                refine ⟨8206610612541997072454231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21884294966778658859877949 8206610612541997072454231)
                ·
                  refine ⟨12309915918812995608681347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8206610612541997072454231 12309915918812995608681347)
                  ·
                    refine ⟨18464873878219493413022021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12309915918812995608681347 18464873878219493413022021)
                    ·
                      refine ⟨3462163852166155014941629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18464873878219493413022021 3462163852166155014941629)
                      ·
                        rfl

theorem cell23_6742540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_6742540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742540 prefixEnd_6742540 := by exact prefixLift 6742540
  have htrace : WordTrace (prefixWord ++ tailWord_6742540) baseStart_6742540 baseEnd_6742540 := by
    simpa [prefixWord, tailWord_6742540, baseEnd_6742540] using wordTrace_append hprefix tailTrace_6742540
  have hstable : (prefixWord ++ tailWord_6742540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742540).length < 2 ^ (prefixWord ++ tailWord_6742540).sum := by decide
  have hdescent : baseEnd_6742540 < baseStart_6742540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742551 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6742551 : Nat := 118140960795 + 6742551 * 2 ^ 59
def prefixEnd_6742551 : Nat := 4983230072969 + 3 ^ 40 * 6742551 * 2
def baseEnd_6742551 : Nat := 3462169500453354471904079

theorem tailTrace_6742551 : CollatzResearch.WordTrace tailWord_6742551 prefixEnd_6742551 3462169500453354471904079 := by
  unfold tailWord_6742551
  simp only [CollatzResearch.WordTrace]
  refine ⟨245921038195896737877443507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163947358797264491918295671 245921038195896737877443507)
  ·
    refine ⟨368881557293845106816165261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245921038195896737877443507 368881557293845106816165261)
    ·
      refine ⟨138330583985191915056061973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368881557293845106816165261 138330583985191915056061973)
      ·
        refine ⟨6484246124305871018252905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138330583985191915056061973 6484246124305871018252905)
        ·
          refine ⟨4863184593229403263689679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6484246124305871018252905 4863184593229403263689679)
          ·
            refine ⟨7294776889844104895534519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863184593229403263689679 7294776889844104895534519)
            ·
              refine ⟨10942165334766157343301779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7294776889844104895534519 10942165334766157343301779)
              ·
                refine ⟨16413248002149236014952669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10942165334766157343301779 16413248002149236014952669)
                ·
                  refine ⟨6154968000805963505607251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16413248002149236014952669 6154968000805963505607251)
                  ·
                    refine ⟨9232452001208945258410877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6154968000805963505607251 9232452001208945258410877)
                    ·
                      refine ⟨3462169500453354471904079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232452001208945258410877 3462169500453354471904079)
                      ·
                        rfl

theorem cell23_6742551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6742551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742551 prefixEnd_6742551 := by exact prefixLift 6742551
  have htrace : WordTrace (prefixWord ++ tailWord_6742551) baseStart_6742551 baseEnd_6742551 := by
    simpa [prefixWord, tailWord_6742551, baseEnd_6742551] using wordTrace_append hprefix tailTrace_6742551
  have hstable : (prefixWord ++ tailWord_6742551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742551).length < 2 ^ (prefixWord ++ tailWord_6742551).sum := by decide
  have hdescent : baseEnd_6742551 < baseStart_6742551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742563 : List Nat := [1, 1, 1, 4, 4, 2, 2, 8]
def baseStart_6742563 : Nat := 118140960795 + 6742563 * 2 ^ 59
def prefixEnd_6742563 : Nat := 4983230072969 + 3 ^ 40 * 6742563 * 2
def baseEnd_6742563 : Nat := 128228728230415126850149

theorem tailTrace_6742563 : CollatzResearch.WordTrace tailWord_6742563 prefixEnd_6742563 128228728230415126850149 := by
  unfold tailWord_6742563
  simp only [CollatzResearch.WordTrace]
  refine ⟨245921475871853263926880343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163947650581235509284586895 245921475871853263926880343)
  ·
    refine ⟨368882213807779895890320515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245921475871853263926880343 368882213807779895890320515)
    ·
      refine ⟨553323320711669843835480773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368882213807779895890320515 553323320711669843835480773)
      ·
        refine ⟨103748122633438095719152645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 553323320711669843835480773 103748122633438095719152645)
        ·
          refine ⟨19452772993769642947341121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103748122633438095719152645 19452772993769642947341121)
          ·
            refine ⟨14589579745327232210505841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19452772993769642947341121 14589579745327232210505841)
            ·
              refine ⟨10942184808995424157879381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14589579745327232210505841 10942184808995424157879381)
              ·
                refine ⟨128228728230415126850149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10942184808995424157879381 128228728230415126850149)
                ·
                  rfl

theorem cell23_6742563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 8].length) (baseStart_6742563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742563 prefixEnd_6742563 := by exact prefixLift 6742563
  have htrace : WordTrace (prefixWord ++ tailWord_6742563) baseStart_6742563 baseEnd_6742563 := by
    simpa [prefixWord, tailWord_6742563, baseEnd_6742563] using wordTrace_append hprefix tailTrace_6742563
  have hstable : (prefixWord ++ tailWord_6742563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742563).length < 2 ^ (prefixWord ++ tailWord_6742563).sum := by decide
  have hdescent : baseEnd_6742563 < baseStart_6742563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742574 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_6742574 : Nat := 118140960795 + 6742574 * 2 ^ 59
def prefixEnd_6742574 : Nat := 4983230072969 + 3 ^ 40 * 6742574 * 2
def baseEnd_6742574 : Nat := 3462181310508407881916473

theorem tailTrace_6742574 : CollatzResearch.WordTrace tailWord_6742574 prefixEnd_6742574 3462181310508407881916473 := by
  unfold tailWord_6742574
  simp only [CollatzResearch.WordTrace]
  refine ⟨30740234634351676600691347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163947918049875608537020517 30740234634351676600691347)
  ·
    refine ⟨46110351951527514901037021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30740234634351676600691347 46110351951527514901037021)
    ·
      refine ⟨17291381981822818087888883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46110351951527514901037021 17291381981822818087888883)
      ·
        refine ⟨25937072972734227131833325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17291381981822818087888883 25937072972734227131833325)
        ·
          refine ⟨9726402364775335174437497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25937072972734227131833325 9726402364775335174437497)
          ·
            refine ⟨7294801773581501380828123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9726402364775335174437497 7294801773581501380828123)
            ·
              refine ⟨10942202660372252071242185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7294801773581501380828123 10942202660372252071242185)
              ·
                refine ⟨8206651995279189053431639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10942202660372252071242185 8206651995279189053431639)
                ·
                  refine ⟨12309977992918783580147459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8206651995279189053431639 12309977992918783580147459)
                  ·
                    refine ⟨18464966989378175370221189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12309977992918783580147459 18464966989378175370221189)
                    ·
                      refine ⟨3462181310508407881916473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18464966989378175370221189 3462181310508407881916473)
                      ·
                        rfl

theorem cell23_6742574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_6742574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742574 prefixEnd_6742574 := by exact prefixLift 6742574
  have htrace : WordTrace (prefixWord ++ tailWord_6742574) baseStart_6742574 baseEnd_6742574 := by
    simpa [prefixWord, tailWord_6742574, baseEnd_6742574] using wordTrace_append hprefix tailTrace_6742574
  have hstable : (prefixWord ++ tailWord_6742574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742574).length < 2 ^ (prefixWord ++ tailWord_6742574).sum := by decide
  have hdescent : baseEnd_6742574 < baseStart_6742574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742613 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6742613 : Nat := 118140960795 + 6742613 * 2 ^ 59
def prefixEnd_6742613 : Nat := 4983230072969 + 3 ^ 40 * 6742613 * 2
def baseEnd_6742613 : Nat := 3462201336253933229328793

theorem tailTrace_6742613 : CollatzResearch.WordTrace tailWord_6742613 prefixEnd_6742613 3462201336253933229328793 := by
  unfold tailWord_6742613
  simp only [CollatzResearch.WordTrace]
  refine ⟨245923299521672122466200493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163948866347781414977466995 245923299521672122466200493)
  ·
    refine ⟨92221237320627045924825185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245923299521672122466200493 92221237320627045924825185)
    ·
      refine ⟨69165927990470284443618889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92221237320627045924825185 69165927990470284443618889)
      ·
        refine ⟨51874445992852713332714167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69165927990470284443618889 51874445992852713332714167)
        ·
          refine ⟨77811668989279069999071251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51874445992852713332714167 77811668989279069999071251)
          ·
            refine ⟨116717503483918604998606877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77811668989279069999071251 116717503483918604998606877)
            ·
              refine ⟨43769063806469476874477579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116717503483918604998606877 43769063806469476874477579)
              ·
                refine ⟨65653595709704215311716369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43769063806469476874477579 65653595709704215311716369)
                ·
                  refine ⟨49240196782278161483787277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65653595709704215311716369 49240196782278161483787277)
                  ·
                    refine ⟨18465073793354310556420229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49240196782278161483787277 18465073793354310556420229)
                    ·
                      refine ⟨3462201336253933229328793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18465073793354310556420229 3462201336253933229328793)
                      ·
                        rfl

theorem cell23_6742613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6742613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742613 prefixEnd_6742613 := by exact prefixLift 6742613
  have htrace : WordTrace (prefixWord ++ tailWord_6742613) baseStart_6742613 baseEnd_6742613 := by
    simpa [prefixWord, tailWord_6742613, baseEnd_6742613] using wordTrace_append hprefix tailTrace_6742613
  have hstable : (prefixWord ++ tailWord_6742613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742613).length < 2 ^ (prefixWord ++ tailWord_6742613).sum := by decide
  have hdescent : baseEnd_6742613 < baseStart_6742613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742633 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 3]
def baseStart_6742633 : Nat := 118140960795 + 6742633 * 2 ^ 59
def prefixEnd_6742633 : Nat := 4983230072969 + 3 ^ 40 * 6742633 * 2
def baseEnd_6742633 : Nat := 3462211605867023151078701

theorem tailTrace_6742633 : CollatzResearch.WordTrace tailWord_6742633 prefixEnd_6742633 3462211605867023151078701 := by
  unfold tailWord_6742633
  simp only [CollatzResearch.WordTrace]
  refine ⟨245924028981599665881928553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163949352654399777254619035 245924028981599665881928553)
  ·
    refine ⟨184443021736199749411446415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245924028981599665881928553 184443021736199749411446415)
    ·
      refine ⟨276664532604299624117169623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184443021736199749411446415 276664532604299624117169623)
      ·
        refine ⟨414996798906449436175754435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276664532604299624117169623 414996798906449436175754435)
        ·
          refine ⟨622495198359674154263631653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414996798906449436175754435 622495198359674154263631653)
          ·
            refine ⟨116717849692438903924430935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 622495198359674154263631653 116717849692438903924430935)
            ·
              refine ⟨175076774538658355886646403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116717849692438903924430935 175076774538658355886646403)
              ·
                refine ⟨262615161807987533829969605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175076774538658355886646403 262615161807987533829969605)
                ·
                  refine ⟨49240342838997662593119301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262615161807987533829969605 49240342838997662593119301)
                  ·
                    refine ⟨9232564282312061736209869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49240342838997662593119301 9232564282312061736209869)
                    ·
                      refine ⟨3462211605867023151078701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232564282312061736209869 3462211605867023151078701)
                      ·
                        rfl

theorem cell23_6742633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_6742633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742633 prefixEnd_6742633 := by exact prefixLift 6742633
  have htrace : WordTrace (prefixWord ++ tailWord_6742633) baseStart_6742633 baseEnd_6742633 := by
    simpa [prefixWord, tailWord_6742633, baseEnd_6742633] using wordTrace_append hprefix tailTrace_6742633
  have hstable : (prefixWord ++ tailWord_6742633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742633).length < 2 ^ (prefixWord ++ tailWord_6742633).sum := by decide
  have hdescent : baseEnd_6742633 < baseStart_6742633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742658 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6742658 : Nat := 118140960795 + 6742658 * 2 ^ 59
def prefixEnd_6742658 : Nat := 4983230072969 + 3 ^ 40 * 6742658 * 2
def baseEnd_6742658 : Nat := 3462224442883385553266087

theorem tailTrace_6742658 : CollatzResearch.WordTrace tailWord_6742658 prefixEnd_6742658 3462224442883385553266087 := by
  unfold tailWord_6742658
  simp only [CollatzResearch.WordTrace]
  refine ⟨61481235201627273787897157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163949960537672730101059085 61481235201627273787897157)
  ·
    refine ⟨11527731600305113835230717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61481235201627273787897157 11527731600305113835230717)
    ·
      refine ⟨4322899350114417688211519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11527731600305113835230717 4322899350114417688211519)
      ·
        refine ⟨6484349025171626532317279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4322899350114417688211519 6484349025171626532317279)
        ·
          refine ⟨9726523537757439798475919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6484349025171626532317279 9726523537757439798475919)
          ·
            refine ⟨14589785306636159697713879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9726523537757439798475919 14589785306636159697713879)
            ·
              refine ⟨21884677959954239546570819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14589785306636159697713879 21884677959954239546570819)
              ·
                refine ⟨32827016939931359319856229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21884677959954239546570819 32827016939931359319856229)
                ·
                  refine ⟨6155065676237129872473043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32827016939931359319856229 6155065676237129872473043)
                  ·
                    refine ⟨9232598514355694808709565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155065676237129872473043 9232598514355694808709565)
                    ·
                      refine ⟨3462224442883385553266087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232598514355694808709565 3462224442883385553266087)
                      ·
                        rfl

theorem cell23_6742658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6742658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742658 prefixEnd_6742658 := by exact prefixLift 6742658
  have htrace : WordTrace (prefixWord ++ tailWord_6742658) baseStart_6742658 baseEnd_6742658 := by
    simpa [prefixWord, tailWord_6742658, baseEnd_6742658] using wordTrace_append hprefix tailTrace_6742658
  have hstable : (prefixWord ++ tailWord_6742658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742658).length < 2 ^ (prefixWord ++ tailWord_6742658).sum := by decide
  have hdescent : baseEnd_6742658 < baseStart_6742658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742660 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6742660 : Nat := 118140960795 + 6742660 * 2 ^ 59
def prefixEnd_6742660 : Nat := 4983230072969 + 3 ^ 40 * 6742660 * 2
def baseEnd_6742660 : Nat := 3462225469844694545441077

theorem tailTrace_6742660 : CollatzResearch.WordTrace tailWord_6742660 prefixEnd_6742660 3462225469844694545441077 := by
  unfold tailWord_6742660
  simp only [CollatzResearch.WordTrace]
  refine ⟨122962506876250924746580717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163950009168334566328774289 122962506876250924746580717)
  ·
    refine ⟨46110940078594096779967769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122962506876250924746580717 46110940078594096779967769)
    ·
      refine ⟨34583205058945572584975827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46110940078594096779967769 34583205058945572584975827)
      ·
        refine ⟨51874807588418358877463741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34583205058945572584975827 51874807588418358877463741)
        ·
          refine ⟨19453052845656884579048903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51874807588418358877463741 19453052845656884579048903)
          ·
            refine ⟨29179579268485326868573355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19453052845656884579048903 29179579268485326868573355)
            ·
              refine ⟨43769368902727990302860033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29179579268485326868573355 43769368902727990302860033)
              ·
                refine ⟨32827026677045992727145025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43769368902727990302860033 32827026677045992727145025)
                ·
                  refine ⟨24620270007784494545358769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32827026677045992727145025 24620270007784494545358769)
                  ·
                    refine ⟨18465202505838370909019077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24620270007784494545358769 18465202505838370909019077)
                    ·
                      refine ⟨3462225469844694545441077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18465202505838370909019077 3462225469844694545441077)
                      ·
                        rfl

theorem cell23_6742660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6742660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742660 prefixEnd_6742660 := by exact prefixLift 6742660
  have htrace : WordTrace (prefixWord ++ tailWord_6742660) baseStart_6742660 baseEnd_6742660 := by
    simpa [prefixWord, tailWord_6742660, baseEnd_6742660] using wordTrace_append hprefix tailTrace_6742660
  have hstable : (prefixWord ++ tailWord_6742660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742660).length < 2 ^ (prefixWord ++ tailWord_6742660).sum := by decide
  have hdescent : baseEnd_6742660 < baseStart_6742660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742670 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_6742670 : Nat := 118140960795 + 6742670 * 2 ^ 59
def prefixEnd_6742670 : Nat := 4983230072969 + 3 ^ 40 * 6742670 * 2
def baseEnd_6742670 : Nat := 384692289405693278479559

theorem tailTrace_6742670 : CollatzResearch.WordTrace tailWord_6742670 prefixEnd_6742670 384692289405693278479559 := by
  unfold tailWord_6742670
  simp only [CollatzResearch.WordTrace]
  refine ⟨30740672310308202650128183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163950252321643747467350309 30740672310308202650128183)
  ·
    refine ⟨46111008465462303975192275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30740672310308202650128183 46111008465462303975192275)
    ·
      refine ⟨69166512698193455962788413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46111008465462303975192275 69166512698193455962788413)
      ·
        refine ⟨25937442261822545986045655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69166512698193455962788413 25937442261822545986045655)
        ·
          refine ⟨38906163392733818979068483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25937442261822545986045655 38906163392733818979068483)
          ·
            refine ⟨58359245089100728468602725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38906163392733818979068483 58359245089100728468602725)
            ·
              refine ⟨10942358454206386587863011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58359245089100728468602725 10942358454206386587863011)
              ·
                refine ⟨16413537681309579881794517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10942358454206386587863011 16413537681309579881794517)
                ·
                  refine ⟨384692289405693278479559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16413537681309579881794517 384692289405693278479559)
                  ·
                    rfl

theorem cell23_6742670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_6742670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742670 prefixEnd_6742670 := by exact prefixLift 6742670
  have htrace : WordTrace (prefixWord ++ tailWord_6742670) baseStart_6742670 baseEnd_6742670 := by
    simpa [prefixWord, tailWord_6742670, baseEnd_6742670] using wordTrace_append hprefix tailTrace_6742670
  have hstable : (prefixWord ++ tailWord_6742670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742670).length < 2 ^ (prefixWord ++ tailWord_6742670).sum := by decide
  have hdescent : baseEnd_6742670 < baseStart_6742670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742680 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_6742680 : Nat := 118140960795 + 6742680 * 2 ^ 59
def prefixEnd_6742680 : Nat := 4983230072969 + 3 ^ 40 * 6742680 * 2
def baseEnd_6742680 : Nat := 3462235739457784467190985

theorem tailTrace_6742680 : CollatzResearch.WordTrace tailWord_6742680 prefixEnd_6742680 3462235739457784467190985 := by
  unfold tailWord_6742680
  simp only [CollatzResearch.WordTrace]
  refine ⟨122962871606214696454444747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163950495474952928605926329 122962871606214696454444747)
  ·
    refine ⟨184444307409322044681667121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122962871606214696454444747 184444307409322044681667121)
    ·
      refine ⟨138333230556991533511250341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184444307409322044681667121 138333230556991533511250341)
      ·
        refine ⟨25937480729435912533359439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138333230556991533511250341 25937480729435912533359439)
        ·
          refine ⟨38906221094153868800039159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25937480729435912533359439 38906221094153868800039159)
          ·
            refine ⟨58359331641230803200058739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38906221094153868800039159 58359331641230803200058739)
            ·
              refine ⟨87538997461846204800088109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58359331641230803200058739 87538997461846204800088109)
              ·
                refine ⟨32827124048192326800033041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87538997461846204800088109 32827124048192326800033041)
                ·
                  refine ⟨24620343036144245100024781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32827124048192326800033041 24620343036144245100024781)
                  ·
                    refine ⟨9232628638554091912509293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24620343036144245100024781 9232628638554091912509293)
                    ·
                      refine ⟨3462235739457784467190985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232628638554091912509293 3462235739457784467190985)
                      ·
                        rfl

theorem cell23_6742680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_6742680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742680 prefixEnd_6742680 := by exact prefixLift 6742680
  have htrace : WordTrace (prefixWord ++ tailWord_6742680) baseStart_6742680 baseEnd_6742680 := by
    simpa [prefixWord, tailWord_6742680, baseEnd_6742680] using wordTrace_append hprefix tailTrace_6742680
  have hstable : (prefixWord ++ tailWord_6742680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742680).length < 2 ^ (prefixWord ++ tailWord_6742680).sum := by decide
  have hdescent : baseEnd_6742680 < baseStart_6742680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742693 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_6742693 : Nat := 118140960795 + 6742693 * 2 ^ 59
def prefixEnd_6742693 : Nat := 4983230072969 + 3 ^ 40 * 6742693 * 2
def baseEnd_6742693 : Nat := 3462242414706292916328425

theorem tailTrace_6742693 : CollatzResearch.WordTrace tailWord_6742693 prefixEnd_6742693 3462242414706292916328425 := by
  unfold tailWord_6742693
  simp only [CollatzResearch.WordTrace]
  refine ⟨245926217361382296129112733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163950811574254864086075155 245926217361382296129112733)
  ·
    refine ⟨92222331510518361048417275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245926217361382296129112733 92222331510518361048417275)
    ·
      refine ⟨138333497265777541572625913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92222331510518361048417275 138333497265777541572625913)
      ·
        refine ⟨103750122949333156179469435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138333497265777541572625913 103750122949333156179469435)
        ·
          refine ⟨155625184423999734269204153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103750122949333156179469435 155625184423999734269204153)
          ·
            refine ⟨116718888317999800701903115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155625184423999734269204153 116718888317999800701903115)
            ·
              refine ⟨175078332476999701052854673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116718888317999800701903115 175078332476999701052854673)
              ·
                refine ⟨131308749357749775789641005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175078332476999701052854673 131308749357749775789641005)
                ·
                  refine ⟨49240781009156165921115377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131308749357749775789641005 49240781009156165921115377)
                  ·
                    refine ⟨36930585756867124440836533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49240781009156165921115377 36930585756867124440836533)
                    ·
                      refine ⟨3462242414706292916328425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36930585756867124440836533 3462242414706292916328425)
                      ·
                        rfl

theorem cell23_6742693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_6742693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742693 prefixEnd_6742693 := by exact prefixLift 6742693
  have htrace : WordTrace (prefixWord ++ tailWord_6742693) baseStart_6742693 baseEnd_6742693 := by
    simpa [prefixWord, tailWord_6742693, baseEnd_6742693] using wordTrace_append hprefix tailTrace_6742693
  have hstable : (prefixWord ++ tailWord_6742693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742693).length < 2 ^ (prefixWord ++ tailWord_6742693).sum := by decide
  have hdescent : baseEnd_6742693 < baseStart_6742693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742720 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_6742720 : Nat := 118140960795 + 6742720 * 2 ^ 59
def prefixEnd_6742720 : Nat := 4983230072969 + 3 ^ 40 * 6742720 * 2
def baseEnd_6742720 : Nat := 3462256278683964310690801

theorem tailTrace_6742720 : CollatzResearch.WordTrace tailWord_6742720 prefixEnd_6742720 3462256278683964310690801 := by
  unfold tailWord_6742720
  simp only [CollatzResearch.WordTrace]
  refine ⟨122963601066142239870172807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163951468088189653160230409 122963601066142239870172807)
  ·
    refine ⟨184445401599213359805259211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122963601066142239870172807 184445401599213359805259211)
    ·
      refine ⟨276668102398820039707888817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184445401599213359805259211 276668102398820039707888817)
      ·
        refine ⟨207501076799115029780916613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276668102398820039707888817 207501076799115029780916613)
        ·
          refine ⟨38906451899834068083921865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207501076799115029780916613 38906451899834068083921865)
          ·
            refine ⟨29179838924875551062941399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38906451899834068083921865 29179838924875551062941399)
            ·
              refine ⟨43769758387313326594412099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29179838924875551062941399 43769758387313326594412099)
              ·
                refine ⟨65654637580969989891618149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43769758387313326594412099 65654637580969989891618149)
                ·
                  refine ⟨12310244546431873104678403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65654637580969989891618149 12310244546431873104678403)
                  ·
                    refine ⟨18465366819647809657017605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12310244546431873104678403 18465366819647809657017605)
                    ·
                      refine ⟨3462256278683964310690801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18465366819647809657017605 3462256278683964310690801)
                      ·
                        rfl

theorem cell23_6742720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_6742720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742720 prefixEnd_6742720 := by exact prefixLift 6742720
  have htrace : WordTrace (prefixWord ++ tailWord_6742720) baseStart_6742720 baseEnd_6742720 := by
    simpa [prefixWord, tailWord_6742720, baseEnd_6742720] using wordTrace_append hprefix tailTrace_6742720
  have hstable : (prefixWord ++ tailWord_6742720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742720).length < 2 ^ (prefixWord ++ tailWord_6742720).sum := by decide
  have hdescent : baseEnd_6742720 < baseStart_6742720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742721 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 7]
def baseStart_6742721 : Nat := 118140960795 + 6742721 * 2 ^ 59
def prefixEnd_6742721 : Nat := 4983230072969 + 3 ^ 40 * 6742721 * 2
def baseEnd_6742721 : Nat := 384695199129402089642033

theorem tailTrace_6742721 : CollatzResearch.WordTrace tailWord_6742721 prefixEnd_6742721 384695199129402089642033 := by
  unfold tailWord_6742721
  simp only [CollatzResearch.WordTrace]
  refine ⟨245927238605280856911132017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163951492403520571274088011 245927238605280856911132017)
  ·
    refine ⟨184445428953960642683349013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245927238605280856911132017 184445428953960642683349013)
    ·
      refine ⟨8645879482216905125781985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184445428953960642683349013 8645879482216905125781985)
      ·
        refine ⟨6484409611662678844336489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8645879482216905125781985 6484409611662678844336489)
        ·
          refine ⟨4863307208747009133252367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6484409611662678844336489 4863307208747009133252367)
          ·
            refine ⟨7294960813120513699878551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863307208747009133252367 7294960813120513699878551)
            ·
              refine ⟨10942441219680770549817827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7294960813120513699878551 10942441219680770549817827)
              ·
                refine ⟨16413661829521155824726741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10942441219680770549817827 16413661829521155824726741)
                ·
                  refine ⟨384695199129402089642033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16413661829521155824726741 384695199129402089642033)
                  ·
                    rfl

theorem cell23_6742721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 7].length) (baseStart_6742721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742721 prefixEnd_6742721 := by exact prefixLift 6742721
  have htrace : WordTrace (prefixWord ++ tailWord_6742721) baseStart_6742721 baseEnd_6742721 := by
    simpa [prefixWord, tailWord_6742721, baseEnd_6742721] using wordTrace_append hprefix tailTrace_6742721
  have hstable : (prefixWord ++ tailWord_6742721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742721).length < 2 ^ (prefixWord ++ tailWord_6742721).sum := by decide
  have hdescent : baseEnd_6742721 < baseStart_6742721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742757 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_6742757 : Nat := 118140960795 + 6742757 * 2 ^ 59
def prefixEnd_6742757 : Nat := 4983230072969 + 3 ^ 40 * 6742757 * 2
def baseEnd_6742757 : Nat := 3462275277468180665928131

theorem tailTrace_6742757 : CollatzResearch.WordTrace tailWord_6742757 prefixEnd_6742757 3462275277468180665928131 := by
  unfold tailWord_6742757
  simp only [CollatzResearch.WordTrace]
  refine ⟨245928551633150435059442525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163952367755433623372961683 245928551633150435059442525)
  ·
    refine ⟨92223206862431413147290947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245928551633150435059442525 92223206862431413147290947)
    ·
      refine ⟨138334810293647119720936421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92223206862431413147290947 138334810293647119720936421)
      ·
        refine ⟨25937776930058834947675579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138334810293647119720936421 25937776930058834947675579)
        ·
          refine ⟨38906665395088252421513369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25937776930058834947675579 38906665395088252421513369)
          ·
            refine ⟨29179999046316189316135027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38906665395088252421513369 29179999046316189316135027)
            ·
              refine ⟨43769998569474283974202541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29179999046316189316135027 43769998569474283974202541)
              ·
                refine ⟨16413749463552856490325953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43769998569474283974202541 16413749463552856490325953)
                ·
                  refine ⟨12310312097664642367744465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16413749463552856490325953 12310312097664642367744465)
                  ·
                    refine ⟨9232734073248481775808349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12310312097664642367744465 9232734073248481775808349)
                    ·
                      refine ⟨3462275277468180665928131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232734073248481775808349 3462275277468180665928131)
                      ·
                        rfl

theorem cell23_6742757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_6742757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742757 prefixEnd_6742757 := by exact prefixLift 6742757
  have htrace : WordTrace (prefixWord ++ tailWord_6742757) baseStart_6742757 baseEnd_6742757 := by
    simpa [prefixWord, tailWord_6742757, baseEnd_6742757] using wordTrace_append hprefix tailTrace_6742757
  have hstable : (prefixWord ++ tailWord_6742757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742757).length < 2 ^ (prefixWord ++ tailWord_6742757).sum := by decide
  have hdescent : baseEnd_6742757 < baseStart_6742757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742763 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8]
def baseStart_6742763 : Nat := 118140960795 + 6742763 * 2 ^ 59
def prefixEnd_6742763 : Nat := 4983230072969 + 3 ^ 40 * 6742763 * 2
def baseEnd_6742763 : Nat := 3462278358352107642453103

theorem tailTrace_6742763 : CollatzResearch.WordTrace tailWord_6742763 prefixEnd_6742763 3462278358352107642453103 := by
  unfold tailWord_6742763
  simp only [CollatzResearch.WordTrace]
  refine ⟨245928770471128698084160943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163952513647419132056107295 245928770471128698084160943)
  ·
    refine ⟨368893155706693047126241415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245928770471128698084160943 368893155706693047126241415)
    ·
      refine ⟨553339733560039570689362123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368893155706693047126241415 553339733560039570689362123)
      ·
        refine ⟨830009600340059356034043185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553339733560039570689362123 830009600340059356034043185)
        ·
          refine ⟨622507200255044517025532389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830009600340059356034043185 622507200255044517025532389)
          ·
            refine ⟨116720100047820846942287323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 622507200255044517025532389 116720100047820846942287323)
            ·
              refine ⟨175080150071731270413430985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116720100047820846942287323 175080150071731270413430985)
              ·
                refine ⟨131310112553798452810073239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175080150071731270413430985 131310112553798452810073239)
                ·
                  refine ⟨196965168830697679215109859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131310112553798452810073239 196965168830697679215109859)
                  ·
                    refine ⟨295447753246046518822664789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196965168830697679215109859 295447753246046518822664789)
                    ·
                      refine ⟨3462278358352107642453103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 295447753246046518822664789 3462278358352107642453103)
                      ·
                        rfl

theorem cell23_6742763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_6742763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742763 prefixEnd_6742763 := by exact prefixLift 6742763
  have htrace : WordTrace (prefixWord ++ tailWord_6742763) baseStart_6742763 baseEnd_6742763 := by
    simpa [prefixWord, tailWord_6742763, baseEnd_6742763] using wordTrace_append hprefix tailTrace_6742763
  have hstable : (prefixWord ++ tailWord_6742763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742763).length < 2 ^ (prefixWord ++ tailWord_6742763).sum := by decide
  have hdescent : baseEnd_6742763 < baseStart_6742763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742787 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 3]
def baseStart_6742787 : Nat := 118140960795 + 6742787 * 2 ^ 59
def prefixEnd_6742787 : Nat := 4983230072969 + 3 ^ 40 * 6742787 * 2
def baseEnd_6742787 : Nat := 3462290681887815548552993

theorem tailTrace_6742787 : CollatzResearch.WordTrace tailWord_6742787 prefixEnd_6742787 3462290681887815548552993 := by
  unfold tailWord_6742787
  simp only [CollatzResearch.WordTrace]
  refine ⟨245929645823041750183034615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163953097215361166788689743 245929645823041750183034615)
  ·
    refine ⟨368894468734562625274551923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245929645823041750183034615 368894468734562625274551923)
    ·
      refine ⟨553341703101843937911827885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368894468734562625274551923 553341703101843937911827885)
      ·
        refine ⟨207503138663191476716935457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553341703101843937911827885 207503138663191476716935457)
        ·
          refine ⟨155627353997393607537701593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207503138663191476716935457 155627353997393607537701593)
          ·
            refine ⟨116720515498045205653276195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155627353997393607537701593 116720515498045205653276195)
            ·
              refine ⟨175080773247067808479914293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116720515498045205653276195 175080773247067808479914293)
              ·
                refine ⟨16413822491912607044991965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175080773247067808479914293 16413822491912607044991965)
                ·
                  refine ⟨6155183434467227641871987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16413822491912607044991965 6155183434467227641871987)
                  ·
                    refine ⟨9232775151700841462807981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155183434467227641871987 9232775151700841462807981)
                    ·
                      refine ⟨3462290681887815548552993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232775151700841462807981 3462290681887815548552993)
                      ·
                        rfl

theorem cell23_6742787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_6742787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742787 prefixEnd_6742787 := by exact prefixLift 6742787
  have htrace : WordTrace (prefixWord ++ tailWord_6742787) baseStart_6742787 baseEnd_6742787 := by
    simpa [prefixWord, tailWord_6742787, baseEnd_6742787] using wordTrace_append hprefix tailTrace_6742787
  have hstable : (prefixWord ++ tailWord_6742787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742787).length < 2 ^ (prefixWord ++ tailWord_6742787).sum := by decide
  have hdescent : baseEnd_6742787 < baseStart_6742787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742821 : List Nat := [1, 3, 1, 2, 3, 1, 4, 3, 1, 1, 3]
def baseStart_6742821 : Nat := 118140960795 + 6742821 * 2 ^ 59
def prefixEnd_6742821 : Nat := 4983230072969 + 3 ^ 40 * 6742821 * 2
def baseEnd_6742821 : Nat := 3462308140230068415527837

theorem tailTrace_6742821 : CollatzResearch.WordTrace tailWord_6742821 prefixEnd_6742821 3462308140230068415527837 := by
  unfold tailWord_6742821
  simp only [CollatzResearch.WordTrace]
  refine ⟨245930885904918573989772317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163953923936612382659848211 245930885904918573989772317)
  ·
    refine ⟨92224082214344465246164619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245930885904918573989772317 92224082214344465246164619)
    ·
      refine ⟨138336123321516697869246929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92224082214344465246164619 138336123321516697869246929)
      ·
        refine ⟨103752092491137523401935197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138336123321516697869246929 103752092491137523401935197)
        ·
          refine ⟨38907034684176571275725699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103752092491137523401935197 38907034684176571275725699)
          ·
            refine ⟨58360552026264856913588549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38907034684176571275725699 58360552026264856913588549)
            ·
              refine ⟨10942603504924660671297853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58360552026264856913588549 10942603504924660671297853)
              ·
                refine ⟨4103476314346747751736695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10942603504924660671297853 4103476314346747751736695)
                ·
                  refine ⟨6155214471520121627605043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103476314346747751736695 6155214471520121627605043)
                  ·
                    refine ⟨9232821707280182441407565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155214471520121627605043 9232821707280182441407565)
                    ·
                      refine ⟨3462308140230068415527837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232821707280182441407565 3462308140230068415527837)
                      ·
                        rfl

theorem cell23_6742821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_6742821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742821 prefixEnd_6742821 := by exact prefixLift 6742821
  have htrace : WordTrace (prefixWord ++ tailWord_6742821) baseStart_6742821 baseEnd_6742821 := by
    simpa [prefixWord, tailWord_6742821, baseEnd_6742821] using wordTrace_append hprefix tailTrace_6742821
  have hstable : (prefixWord ++ tailWord_6742821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742821).length < 2 ^ (prefixWord ++ tailWord_6742821).sum := by decide
  have hdescent : baseEnd_6742821 < baseStart_6742821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742838 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6742838 : Nat := 118140960795 + 6742838 * 2 ^ 59
def prefixEnd_6742838 : Nat := 4983230072969 + 3 ^ 40 * 6742838 * 2
def baseEnd_6742838 : Nat := 3462316869401194849015259

theorem tailTrace_6742838 : CollatzResearch.WordTrace tailWord_6742838 prefixEnd_6742838 3462316869401194849015259 := by
  unfold tailWord_6742838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15370719121616061618321323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163954337297237990595427445 15370719121616061618321323)
  ·
    refine ⟨23056078682424092427481985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15370719121616061618321323 23056078682424092427481985)
    ·
      refine ⟨17292059011818069320611489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23056078682424092427481985 17292059011818069320611489)
      ·
        refine ⟨12969044258863551990458617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17292059011818069320611489 12969044258863551990458617)
        ·
          refine ⟨9726783194147663992843963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12969044258863551990458617 9726783194147663992843963)
          ·
            refine ⟨14590174791221495989265945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9726783194147663992843963 14590174791221495989265945)
            ·
              refine ⟨10942631093416121991949459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14590174791221495989265945 10942631093416121991949459)
              ·
                refine ⟨16413946640124182987924189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10942631093416121991949459 16413946640124182987924189)
                ·
                  refine ⟨6155229990046568620471571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16413946640124182987924189 6155229990046568620471571)
                  ·
                    refine ⟨9232844985069852930707357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155229990046568620471571 9232844985069852930707357)
                    ·
                      refine ⟨3462316869401194849015259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232844985069852930707357 3462316869401194849015259)
                      ·
                        rfl

theorem cell23_6742838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6742838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742838 prefixEnd_6742838 := by exact prefixLift 6742838
  have htrace : WordTrace (prefixWord ++ tailWord_6742838) baseStart_6742838 baseEnd_6742838 := by
    simpa [prefixWord, tailWord_6742838, baseEnd_6742838] using wordTrace_append hprefix tailTrace_6742838
  have hstable : (prefixWord ++ tailWord_6742838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742838).length < 2 ^ (prefixWord ++ tailWord_6742838).sum := by decide
  have hdescent : baseEnd_6742838 < baseStart_6742838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742840 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_6742840 : Nat := 118140960795 + 6742840 * 2 ^ 59
def prefixEnd_6742840 : Nat := 4983230072969 + 3 ^ 40 * 6742840 * 2
def baseEnd_6742840 : Nat := 3462317896362503841190249

theorem tailTrace_6742840 : CollatzResearch.WordTrace tailWord_6742840 prefixEnd_6742840 3462317896362503841190249 := by
  unfold tailWord_6742840
  simp only [CollatzResearch.WordTrace]
  refine ⟨122965789445924870117356987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163954385927899826823142649 122965789445924870117356987)
  ·
    refine ⟨184448684168887305176035481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122965789445924870117356987 184448684168887305176035481)
    ·
      refine ⟨138336513126665478882026611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184448684168887305176035481 138336513126665478882026611)
      ·
        refine ⟨207504769689998218323039917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138336513126665478882026611 207504769689998218323039917)
        ·
          refine ⟨77814288633749331871139969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207504769689998218323039917 77814288633749331871139969)
          ·
            refine ⟨58360716475311998903354977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77814288633749331871139969 58360716475311998903354977)
            ·
              refine ⟨43770537356483999177516233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58360716475311998903354977 43770537356483999177516233)
              ·
                refine ⟨32827903017362999383137175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43770537356483999177516233 32827903017362999383137175)
                ·
                  refine ⟨49241854526044499074705763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32827903017362999383137175 49241854526044499074705763)
                  ·
                    refine ⟨73862781789066748612058645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49241854526044499074705763 73862781789066748612058645)
                    ·
                      refine ⟨3462317896362503841190249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73862781789066748612058645 3462317896362503841190249)
                      ·
                        rfl

theorem cell23_6742840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_6742840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742840 prefixEnd_6742840 := by exact prefixLift 6742840
  have htrace : WordTrace (prefixWord ++ tailWord_6742840) baseStart_6742840 baseEnd_6742840 := by
    simpa [prefixWord, tailWord_6742840, baseEnd_6742840] using wordTrace_append hprefix tailTrace_6742840
  have hstable : (prefixWord ++ tailWord_6742840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742840).length < 2 ^ (prefixWord ++ tailWord_6742840).sum := by decide
  have hdescent : baseEnd_6742840 < baseStart_6742840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742847 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_6742847 : Nat := 118140960795 + 6742847 * 2 ^ 59
def prefixEnd_6742847 : Nat := 4983230072969 + 3 ^ 40 * 6742847 * 2
def baseEnd_6742847 : Nat := 3462321490727085313802717

theorem tailTrace_6742847 : CollatzResearch.WordTrace tailWord_6742847 prefixEnd_6742847 3462321490727085313802717 := by
  unfold tailWord_6742847
  simp only [CollatzResearch.WordTrace]
  refine ⟨245931834202824380430218795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163954556135216253620145863 245931834202824380430218795)
  ·
    refine ⟨368897751304236570645328193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245931834202824380430218795 368897751304236570645328193)
    ·
      refine ⟨276673313478177427983996145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368897751304236570645328193 276673313478177427983996145)
      ·
        refine ⟨207504985108633070987997109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276673313478177427983996145 207504985108633070987997109)
        ·
          refine ⟨19453592353934350405124729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207504985108633070987997109 19453592353934350405124729)
          ·
            refine ⟨14590194265450762803843547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19453592353934350405124729 14590194265450762803843547)
            ·
              refine ⟨21885291398176144205765321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14590194265450762803843547 21885291398176144205765321)
              ·
                refine ⟨16413968548632108154323991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21885291398176144205765321 16413968548632108154323991)
                ·
                  refine ⟨24620952822948162231485987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16413968548632108154323991 24620952822948162231485987)
                  ·
                    refine ⟨36931429234422243347228981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24620952822948162231485987 36931429234422243347228981)
                    ·
                      refine ⟨3462321490727085313802717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36931429234422243347228981 3462321490727085313802717)
                      ·
                        rfl

theorem cell23_6742847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_6742847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742847 prefixEnd_6742847 := by exact prefixLift 6742847
  have htrace : WordTrace (prefixWord ++ tailWord_6742847) baseStart_6742847 baseEnd_6742847 := by
    simpa [prefixWord, tailWord_6742847, baseEnd_6742847] using wordTrace_append hprefix tailTrace_6742847
  have hstable : (prefixWord ++ tailWord_6742847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742847).length < 2 ^ (prefixWord ++ tailWord_6742847).sum := by decide
  have hdescent : baseEnd_6742847 < baseStart_6742847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742857 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 4]
def baseStart_6742857 : Nat := 118140960795 + 6742857 * 2 ^ 59
def prefixEnd_6742857 : Nat := 4983230072969 + 3 ^ 40 * 6742857 * 2
def baseEnd_6742857 : Nat := 3462326625533630274677671

theorem tailTrace_6742857 : CollatzResearch.WordTrace tailWord_6742857 prefixEnd_6742857 3462326625533630274677671 := by
  unfold tailWord_6742857
  simp only [CollatzResearch.WordTrace]
  refine ⟨245932198932788152138082825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163954799288525434758721883 245932198932788152138082825)
  ·
    refine ⟨184449149199591114103562119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245932198932788152138082825 184449149199591114103562119)
    ·
      refine ⟨276673723799386671155343179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184449149199591114103562119 276673723799386671155343179)
      ·
        refine ⟨415010585699080006733014769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276673723799386671155343179 415010585699080006733014769)
        ·
          refine ⟨311257939274310005049761077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415010585699080006733014769 311257939274310005049761077)
          ·
            refine ⟨29180431806966562973415101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311257939274310005049761077 29180431806966562973415101)
            ·
              refine ⟨10942661927612461115030663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29180431806966562973415101 10942661927612461115030663)
              ·
                refine ⟨16413992891418691672545995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10942661927612461115030663 16413992891418691672545995)
                ·
                  refine ⟨24620989337128037508818993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16413992891418691672545995 24620989337128037508818993)
                  ·
                    refine ⟨18465742002846028131614245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24620989337128037508818993 18465742002846028131614245)
                    ·
                      refine ⟨3462326625533630274677671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18465742002846028131614245 3462326625533630274677671)
                      ·
                        rfl

theorem cell23_6742857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_6742857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742857 prefixEnd_6742857 := by exact prefixLift 6742857
  have htrace : WordTrace (prefixWord ++ tailWord_6742857) baseStart_6742857 baseEnd_6742857 := by
    simpa [prefixWord, tailWord_6742857, baseEnd_6742857] using wordTrace_append hprefix tailTrace_6742857
  have hstable : (prefixWord ++ tailWord_6742857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742857).length < 2 ^ (prefixWord ++ tailWord_6742857).sum := by decide
  have hdescent : baseEnd_6742857 < baseStart_6742857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742911 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 2, 1, 3]
def baseStart_6742911 : Nat := 118140960795 + 6742911 * 2 ^ 59
def prefixEnd_6742911 : Nat := 4983230072969 + 3 ^ 40 * 6742911 * 2
def baseEnd_6742911 : Nat := 3462354353488973063402423

theorem tailTrace_6742911 : CollatzResearch.WordTrace tailWord_6742911 prefixEnd_6742911 3462354353488973063402423 := by
  unfold tailWord_6742911
  simp only [CollatzResearch.WordTrace]
  refine ⟨245934168474592519360548587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163956112316395012907032391 245934168474592519360548587)
  ·
    refine ⟨368901252711888779040822881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245934168474592519360548587 368901252711888779040822881)
    ·
      refine ⟨276675939533916584280617161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368901252711888779040822881 276675939533916584280617161)
      ·
        refine ⟨207506954650437438210462871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276675939533916584280617161 207506954650437438210462871)
        ·
          refine ⟨311260431975656157315694307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207506954650437438210462871 311260431975656157315694307)
          ·
            refine ⟨466890647963484235973541461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311260431975656157315694307 466890647963484235973541461)
            ·
              refine ⟨5471374780822080890314939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 466890647963484235973541461 5471374780822080890314939)
              ·
                refine ⟨8207062171233121335472409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471374780822080890314939 8207062171233121335472409)
                ·
                  refine ⟨6155296628424841001604307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8207062171233121335472409 6155296628424841001604307)
                  ·
                    refine ⟨9232944942637261502406461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155296628424841001604307 9232944942637261502406461)
                    ·
                      refine ⟨3462354353488973063402423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9232944942637261502406461 3462354353488973063402423)
                      ·
                        rfl

theorem cell23_6742911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_6742911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742911 prefixEnd_6742911 := by exact prefixLift 6742911
  have htrace : WordTrace (prefixWord ++ tailWord_6742911) baseStart_6742911 baseEnd_6742911 := by
    simpa [prefixWord, tailWord_6742911, baseEnd_6742911] using wordTrace_append hprefix tailTrace_6742911
  have hstable : (prefixWord ++ tailWord_6742911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742911).length < 2 ^ (prefixWord ++ tailWord_6742911).sum := by decide
  have hdescent : baseEnd_6742911 < baseStart_6742911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742921 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 1, 3, 2]
def baseStart_6742921 : Nat := 118140960795 + 6742921 * 2 ^ 59
def prefixEnd_6742921 : Nat := 4983230072969 + 3 ^ 40 * 6742921 * 2
def baseEnd_6742921 : Nat := 3462359488295518024277377

theorem tailTrace_6742921 : CollatzResearch.WordTrace tailWord_6742921 prefixEnd_6742921 3462359488295518024277377 := by
  unfold tailWord_6742921
  simp only [CollatzResearch.WordTrace]
  refine ⟨245934533204556291068412617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163956355469704194045608411 245934533204556291068412617)
  ·
    refine ⟨184450899903417218301309463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245934533204556291068412617 184450899903417218301309463)
    ·
      refine ⟨276676349855125827451964195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184450899903417218301309463 276676349855125827451964195)
      ·
        refine ⟨415014524782688741177946293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276676349855125827451964195 415014524782688741177946293)
        ·
          refine ⟨38907611698377069485432465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 415014524782688741177946293 38907611698377069485432465)
          ·
            refine ⟨29180708773782802114074349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38907611698377069485432465 29180708773782802114074349)
            ·
              refine ⟨10942765790168550792777881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29180708773782802114074349 10942765790168550792777881)
              ·
                refine ⟨8207074342626413094583411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10942765790168550792777881 8207074342626413094583411)
                ·
                  refine ⟨12310611513939619641875117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8207074342626413094583411 12310611513939619641875117)
                  ·
                    refine ⟨4616479317727357365703169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12310611513939619641875117 4616479317727357365703169)
                    ·
                      refine ⟨3462359488295518024277377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616479317727357365703169 3462359488295518024277377)
                      ·
                        rfl

theorem cell23_6742921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 3, 2].length) (baseStart_6742921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742921 prefixEnd_6742921 := by exact prefixLift 6742921
  have htrace : WordTrace (prefixWord ++ tailWord_6742921) baseStart_6742921 baseEnd_6742921 := by
    simpa [prefixWord, tailWord_6742921, baseEnd_6742921] using wordTrace_append hprefix tailTrace_6742921
  have hstable : (prefixWord ++ tailWord_6742921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742921).length < 2 ^ (prefixWord ++ tailWord_6742921).sum := by decide
  have hdescent : baseEnd_6742921 < baseStart_6742921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742967 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_6742967 : Nat := 118140960795 + 6742967 * 2 ^ 59
def prefixEnd_6742967 : Nat := 4983230072969 + 3 ^ 40 * 6742967 * 2
def baseEnd_6742967 : Nat := 3462383108405624844302165

theorem tailTrace_6742967 : CollatzResearch.WordTrace tailWord_6742967 prefixEnd_6742967 3462383108405624844302165 := by
  unfold tailWord_6742967
  simp only [CollatzResearch.WordTrace]
  refine ⟨245936210962389640924587155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163957473974926427283058103 245936210962389640924587155)
  ·
    refine ⟨368904316443584461386880733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245936210962389640924587155 368904316443584461386880733)
    ·
      refine ⟨138339118666344173020080275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368904316443584461386880733 138339118666344173020080275)
      ·
        refine ⟨207508677999516259530120413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138339118666344173020080275 207508677999516259530120413)
        ·
          refine ⟨77815754249818597323795155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207508677999516259530120413 77815754249818597323795155)
          ·
            refine ⟨116723631374727895985692733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77815754249818597323795155 116723631374727895985692733)
            ·
              refine ⟨43771361765522960994634775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116723631374727895985692733 43771361765522960994634775)
              ·
                refine ⟨65657042648284441491952163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43771361765522960994634775 65657042648284441491952163)
                ·
                  refine ⟨98485563972426662237928245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65657042648284441491952163 98485563972426662237928245)
                  ·
                    refine ⟨9233021622414999584805773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98485563972426662237928245 9233021622414999584805773)
                    ·
                      refine ⟨3462383108405624844302165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9233021622414999584805773 3462383108405624844302165)
                      ·
                        rfl

theorem cell23_6742967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_6742967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742967 prefixEnd_6742967 := by exact prefixLift 6742967
  have htrace : WordTrace (prefixWord ++ tailWord_6742967) baseStart_6742967 baseEnd_6742967 := by
    simpa [prefixWord, tailWord_6742967, baseEnd_6742967] using wordTrace_append hprefix tailTrace_6742967
  have hstable : (prefixWord ++ tailWord_6742967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742967).length < 2 ^ (prefixWord ++ tailWord_6742967).sum := by decide
  have hdescent : baseEnd_6742967 < baseStart_6742967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6742987 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 1, 7]
def baseStart_6742987 : Nat := 118140960795 + 6742987 * 2 ^ 59
def prefixEnd_6742987 : Nat := 4983230072969 + 3 ^ 40 * 6742987 * 2
def baseEnd_6742987 : Nat := 1154131126006238255350691

theorem tailTrace_6742987 : CollatzResearch.WordTrace tailWord_6742987 prefixEnd_6742987 1154131126006238255350691 := by
  unfold tailWord_6742987
  simp only [CollatzResearch.WordTrace]
  refine ⟨245936940422317184340315215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163957960281544789560210143 245936940422317184340315215)
  ·
    refine ⟨368905410633475776510472823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245936940422317184340315215 368905410633475776510472823)
    ·
      refine ⟨553358115950213664765709235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368905410633475776510472823 553358115950213664765709235)
      ·
        refine ⟨830037173925320497148563853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553358115950213664765709235 830037173925320497148563853)
        ·
          refine ⟨311263940221995186430711445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830037173925320497148563853 311263940221995186430711445)
          ·
            refine ⟨14590497197906024363939599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 311263940221995186430711445 14590497197906024363939599)
            ·
              refine ⟨21885745796859036545909399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14590497197906024363939599 21885745796859036545909399)
              ·
                refine ⟨32828618695288554818864099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21885745796859036545909399 32828618695288554818864099)
                ·
                  refine ⟨49242928042932832228296149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32828618695288554818864099 49242928042932832228296149)
                  ·
                    refine ⟨1154131126006238255350691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49242928042932832228296149 1154131126006238255350691)
                    ·
                      rfl

theorem cell23_6742987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 7].length) (baseStart_6742987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6742987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6742987 prefixEnd_6742987 := by exact prefixLift 6742987
  have htrace : WordTrace (prefixWord ++ tailWord_6742987) baseStart_6742987 baseEnd_6742987 := by
    simpa [prefixWord, tailWord_6742987, baseEnd_6742987] using wordTrace_append hprefix tailTrace_6742987
  have hstable : (prefixWord ++ tailWord_6742987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6742987).length < 2 ^ (prefixWord ++ tailWord_6742987).sum := by decide
  have hdescent : baseEnd_6742987 < baseStart_6742987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6742987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743037 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_6743037 : Nat := 118140960795 + 6743037 * 2 ^ 59
def prefixEnd_6743037 : Nat := 4983230072969 + 3 ^ 40 * 6743037 * 2
def baseEnd_6743037 : Nat := 3462419052051439570426843

theorem tailTrace_6743037 : CollatzResearch.WordTrace tailWord_6743037 prefixEnd_6743037 3462419052051439570426843 := by
  unfold tailWord_6743037
  simp only [CollatzResearch.WordTrace]
  refine ⟨245938764072136042879635365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163959176048090695253090243 245938764072136042879635365)
  ·
    refine ⟨46113518263525508039931631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245938764072136042879635365 46113518263525508039931631)
    ·
      refine ⟨69170277395288262059897447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46113518263525508039931631 69170277395288262059897447)
      ·
        refine ⟨103755416092932393089846171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69170277395288262059897447 103755416092932393089846171)
        ·
          refine ⟨155633124139398589634769257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103755416092932393089846171 155633124139398589634769257)
          ·
            refine ⟨116724843104548942226076943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155633124139398589634769257 116724843104548942226076943)
            ·
              refine ⟨175087264656823413339115415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116724843104548942226076943 175087264656823413339115415)
              ·
                refine ⟨262630896985235120008673123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175087264656823413339115415 262630896985235120008673123)
                ·
                  refine ⟨393946345477852680013009685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262630896985235120008673123 393946345477852680013009685)
                  ·
                    refine ⟨18466234944274344375609829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 393946345477852680013009685 18466234944274344375609829)
                    ·
                      refine ⟨3462419052051439570426843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18466234944274344375609829 3462419052051439570426843)
                      ·
                        rfl

theorem cell23_6743037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_6743037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743037 prefixEnd_6743037 := by exact prefixLift 6743037
  have htrace : WordTrace (prefixWord ++ tailWord_6743037) baseStart_6743037 baseEnd_6743037 := by
    simpa [prefixWord, tailWord_6743037, baseEnd_6743037] using wordTrace_append hprefix tailTrace_6743037
  have hstable : (prefixWord ++ tailWord_6743037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743037).length < 2 ^ (prefixWord ++ tailWord_6743037).sum := by decide
  have hdescent : baseEnd_6743037 < baseStart_6743037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743042 : List Nat := [3, 4, 1, 3, 2, 1, 1, 3, 5]
def baseStart_6743042 : Nat := 118140960795 + 6743042 * 2 ^ 59
def prefixEnd_6743042 : Nat := 4983230072969 + 3 ^ 40 * 6743042 * 2
def baseEnd_6743042 : Nat := 384713513272745783429369

theorem tailTrace_6743042 : CollatzResearch.WordTrace tailWord_6743042 prefixEnd_6743042 384713513272745783429369 := by
  unfold tailWord_6743042
  simp only [CollatzResearch.WordTrace]
  refine ⟨61484736609279482183391845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163959297624745285822378253 61484736609279482183391845)
  ·
    refine ⟨11528388114239902909385971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61484736609279482183391845 11528388114239902909385971)
    ·
      refine ⟨17292582171359854364078957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11528388114239902909385971 17292582171359854364078957)
      ·
        refine ⟨6484718314259945386529609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17292582171359854364078957 6484718314259945386529609)
        ·
          refine ⟨4863538735694959039897207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6484718314259945386529609 4863538735694959039897207)
          ·
            refine ⟨7295308103542438559845811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863538735694959039897207 7295308103542438559845811)
            ·
              refine ⟨10942962155313657839768717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295308103542438559845811 10942962155313657839768717)
              ·
                refine ⟨4103610808242621689913269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10942962155313657839768717 4103610808242621689913269)
                ·
                  refine ⟨384713513272745783429369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4103610808242621689913269 384713513272745783429369)
                  ·
                    rfl

theorem cell23_6743042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_6743042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743042 prefixEnd_6743042 := by exact prefixLift 6743042
  have htrace : WordTrace (prefixWord ++ tailWord_6743042) baseStart_6743042 baseEnd_6743042 := by
    simpa [prefixWord, tailWord_6743042, baseEnd_6743042] using wordTrace_append hprefix tailTrace_6743042
  have hstable : (prefixWord ++ tailWord_6743042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743042).length < 2 ^ (prefixWord ++ tailWord_6743042).sum := by decide
  have hdescent : baseEnd_6743042 < baseStart_6743042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743047 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 10]
def baseStart_6743047 : Nat := 118140960795 + 6743047 * 2 ^ 59
def prefixEnd_6743047 : Nat := 4983230072969 + 3 ^ 40 * 6743047 * 2
def baseEnd_6743047 : Nat := 384713798539776059033533

theorem tailTrace_6743047 : CollatzResearch.WordTrace tailWord_6743047 prefixEnd_6743047 384713798539776059033533 := by
  unfold tailWord_6743047
  simp only [CollatzResearch.WordTrace]
  refine ⟨245939128802099814587499395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163959419201399876391666263 245939128802099814587499395)
  ·
    refine ⟨368908693203149721881249093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245939128802099814587499395 368908693203149721881249093)
    ·
      refine ⟨69170379975590572852734205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368908693203149721881249093 69170379975590572852734205)
      ·
        refine ⟨25938892490846464819775327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69170379975590572852734205 25938892490846464819775327)
        ·
          refine ⟨38908338736269697229662991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25938892490846464819775327 38908338736269697229662991)
          ·
            refine ⟨58362508104404545844494487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38908338736269697229662991 58362508104404545844494487)
            ·
              refine ⟨87543762156606818766741731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58362508104404545844494487 87543762156606818766741731)
              ·
                refine ⟨131315643234910228150112597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87543762156606818766741731 131315643234910228150112597)
                ·
                  refine ⟨384713798539776059033533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 131315643234910228150112597 384713798539776059033533)
                  ·
                    rfl

theorem cell23_6743047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 10].length) (baseStart_6743047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743047 prefixEnd_6743047 := by exact prefixLift 6743047
  have htrace : WordTrace (prefixWord ++ tailWord_6743047) baseStart_6743047 baseEnd_6743047 := by
    simpa [prefixWord, tailWord_6743047, baseEnd_6743047] using wordTrace_append hprefix tailTrace_6743047
  have hstable : (prefixWord ++ tailWord_6743047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743047).length < 2 ^ (prefixWord ++ tailWord_6743047).sum := by decide
  have hdescent : baseEnd_6743047 < baseStart_6743047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743061 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_6743061 : Nat := 118140960795 + 6743061 * 2 ^ 59
def prefixEnd_6743061 : Nat := 4983230072969 + 3 ^ 40 * 6743061 * 2
def baseEnd_6743061 : Nat := 3462431375587147476526733

theorem tailTrace_6743061 : CollatzResearch.WordTrace tailWord_6743061 prefixEnd_6743061 3462431375587147476526733 := by
  unfold tailWord_6743061
  simp only [CollatzResearch.WordTrace]
  refine ⟨245939639424049094978509037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163959759616032729985672691 245939639424049094978509037)
  ·
    refine ⟨92227364784018410616940889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245939639424049094978509037 92227364784018410616940889)
    ·
      refine ⟨69170523588013807962705667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92227364784018410616940889 69170523588013807962705667)
      ·
        refine ⟨103755785382020711944058501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69170523588013807962705667 103755785382020711944058501)
        ·
          refine ⟨19454209759128883489510969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103755785382020711944058501 19454209759128883489510969)
          ·
            refine ⟨14590657319346662617133227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19454209759128883489510969 14590657319346662617133227)
            ·
              refine ⟨21885985979019993925699841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14590657319346662617133227 21885985979019993925699841)
              ·
                refine ⟨16414489484264995444274881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21885985979019993925699841 16414489484264995444274881)
                ·
                  refine ⟨12310867113198746583206161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16414489484264995444274881 12310867113198746583206161)
                  ·
                    refine ⟨9233150334899059937404621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12310867113198746583206161 9233150334899059937404621)
                    ·
                      refine ⟨3462431375587147476526733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9233150334899059937404621 3462431375587147476526733)
                      ·
                        rfl

theorem cell23_6743061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_6743061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743061 prefixEnd_6743061 := by exact prefixLift 6743061
  have htrace : WordTrace (prefixWord ++ tailWord_6743061) baseStart_6743061 baseEnd_6743061 := by
    simpa [prefixWord, tailWord_6743061, baseEnd_6743061] using wordTrace_append hprefix tailTrace_6743061
  have hstable : (prefixWord ++ tailWord_6743061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743061).length < 2 ^ (prefixWord ++ tailWord_6743061).sum := by decide
  have hdescent : baseEnd_6743061 < baseStart_6743061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743068 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_6743068 : Nat := 118140960795 + 6743068 * 2 ^ 59
def prefixEnd_6743068 : Nat := 4983230072969 + 3 ^ 40 * 6743068 * 2
def baseEnd_6743068 : Nat := 1154144989983909649713067

theorem tailTrace_6743068 : CollatzResearch.WordTrace tailWord_6743068 prefixEnd_6743068 1154144989983909649713067 := by
  unfold tailWord_6743068
  simp only [CollatzResearch.WordTrace]
  refine ⟨122969947367511867587006929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163959929823349156782675905 122969947367511867587006929)
  ·
    refine ⟨92227460525633900690255197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122969947367511867587006929 92227460525633900690255197)
    ·
      refine ⟨34585297697112712758845699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92227460525633900690255197 34585297697112712758845699)
      ·
        refine ⟨51877946545669069138268549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34585297697112712758845699 51877946545669069138268549)
        ·
          refine ⟨9727114977312950463425353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51877946545669069138268549 9727114977312950463425353)
          ·
            refine ⟨7295336232984712847569015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9727114977312950463425353 7295336232984712847569015)
            ·
              refine ⟨10943004349477069271353523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295336232984712847569015 10943004349477069271353523)
              ·
                refine ⟨16414506524215603907030285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943004349477069271353523 16414506524215603907030285)
                ·
                  refine ⟨6155439946580851465136357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16414506524215603907030285 6155439946580851465136357)
                  ·
                    refine ⟨1154144989983909649713067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6155439946580851465136357 1154144989983909649713067)
                    ·
                      rfl

theorem cell23_6743068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_6743068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743068 prefixEnd_6743068 := by exact prefixLift 6743068
  have htrace : WordTrace (prefixWord ++ tailWord_6743068) baseStart_6743068 baseEnd_6743068 := by
    simpa [prefixWord, tailWord_6743068, baseEnd_6743068] using wordTrace_append hprefix tailTrace_6743068
  have hstable : (prefixWord ++ tailWord_6743068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743068).length < 2 ^ (prefixWord ++ tailWord_6743068).sum := by decide
  have hdescent : baseEnd_6743068 < baseStart_6743068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743141 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_6743141 : Nat := 118140960795 + 6743141 * 2 ^ 59
def prefixEnd_6743141 : Nat := 4983230072969 + 3 ^ 40 * 6743141 * 2
def baseEnd_6743141 : Nat := 1154157484679835721175455

theorem tailTrace_6743141 : CollatzResearch.WordTrace tailWord_6743141 prefixEnd_6743141 1154157484679835721175455 := by
  unfold tailWord_6743141
  simp only [CollatzResearch.WordTrace]
  refine ⟨245942557263759268641421277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163961704842506179094280851 245942557263759268641421277)
  ·
    refine ⟨92228458973909725740532979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245942557263759268641421277 92228458973909725740532979)
    ·
      refine ⟨138342688460864588610799469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92228458973909725740532979 138342688460864588610799469)
      ·
        refine ⟨51878508172824220729049801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138342688460864588610799469 51878508172824220729049801)
        ·
          refine ⟨38908881129618165546787351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51878508172824220729049801 38908881129618165546787351)
          ·
            refine ⟨58363321694427248320181027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38908881129618165546787351 58363321694427248320181027)
            ·
              refine ⟨87544982541640872480271541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58363321694427248320181027 87544982541640872480271541)
              ·
                refine ⟨8207342113278831795025457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87544982541640872480271541 8207342113278831795025457)
                ·
                  refine ⟨6155506584959123846269093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8207342113278831795025457 6155506584959123846269093)
                  ·
                    refine ⟨1154157484679835721175455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6155506584959123846269093 1154157484679835721175455)
                    ·
                      rfl

theorem cell23_6743141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_6743141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743141 prefixEnd_6743141 := by exact prefixLift 6743141
  have htrace : WordTrace (prefixWord ++ tailWord_6743141) baseStart_6743141 baseEnd_6743141 := by
    simpa [prefixWord, tailWord_6743141, baseEnd_6743141] using wordTrace_append hprefix tailTrace_6743141
  have hstable : (prefixWord ++ tailWord_6743141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743141).length < 2 ^ (prefixWord ++ tailWord_6743141).sum := by decide
  have hdescent : baseEnd_6743141 < baseStart_6743141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743147 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7]
def baseStart_6743147 : Nat := 118140960795 + 6743147 * 2 ^ 59
def prefixEnd_6743147 : Nat := 4983230072969 + 3 ^ 40 * 6743147 * 2
def baseEnd_6743147 : Nat := 3462475534923434140051337

theorem tailTrace_6743147 : CollatzResearch.WordTrace tailWord_6743147 prefixEnd_6743147 3462475534923434140051337 := by
  unfold tailWord_6743147
  simp only [CollatzResearch.WordTrace]
  refine ⟨245942776101737531666139695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163961850734491687777426463 245942776101737531666139695)
  ·
    refine ⟨368914164152606297499209543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245942776101737531666139695 368914164152606297499209543)
    ·
      refine ⟨553371246228909446248814315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368914164152606297499209543 553371246228909446248814315)
      ·
        refine ⟨830056869343364169373221473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553371246228909446248814315 830056869343364169373221473)
        ·
          refine ⟨622542652007523127029916105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830056869343364169373221473 622542652007523127029916105)
          ·
            refine ⟨466906989005642345272437079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622542652007523127029916105 466906989005642345272437079)
            ·
              refine ⟨700360483508463517908655619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466906989005642345272437079 700360483508463517908655619)
              ·
                refine ⟨1050540725262695276862983429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700360483508463517908655619 1050540725262695276862983429)
                ·
                  refine ⟨196976385986755364411809393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1050540725262695276862983429 196976385986755364411809393)
                  ·
                    refine ⟨147732289490066523308857045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196976385986755364411809393 147732289490066523308857045)
                    ·
                      refine ⟨3462475534923434140051337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147732289490066523308857045 3462475534923434140051337)
                      ·
                        rfl

theorem cell23_6743147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_6743147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743147 prefixEnd_6743147 := by exact prefixLift 6743147
  have htrace : WordTrace (prefixWord ++ tailWord_6743147) baseStart_6743147 baseEnd_6743147 := by
    simpa [prefixWord, tailWord_6743147, baseEnd_6743147] using wordTrace_append hprefix tailTrace_6743147
  have hstable : (prefixWord ++ tailWord_6743147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743147).length < 2 ^ (prefixWord ++ tailWord_6743147).sum := by decide
  have hdescent : baseEnd_6743147 < baseStart_6743147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743148 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 3, 2, 2]
def baseStart_6743148 : Nat := 118140960795 + 6743148 * 2 ^ 59
def prefixEnd_6743148 : Nat := 4983230072969 + 3 ^ 40 * 6743148 * 2
def baseEnd_6743148 : Nat := 3462476048404088636138833

theorem tailTrace_6743148 : CollatzResearch.WordTrace tailWord_6743148 prefixEnd_6743148 3462476048404088636138833 := by
  unfold tailWord_6743148
  simp only [CollatzResearch.WordTrace]
  refine ⟨122971406287366954418463049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163961875049822605891284065 122971406287366954418463049)
  ·
    refine ⟨92228554715525215813847287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122971406287366954418463049 92228554715525215813847287)
    ·
      refine ⟨138342832073287823720770931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92228554715525215813847287 138342832073287823720770931)
      ·
        refine ⟨207514248109931735581156397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138342832073287823720770931 207514248109931735581156397)
        ·
          refine ⟨77817843041224400842933649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207514248109931735581156397 77817843041224400842933649)
          ·
            refine ⟨58363382280918300632200237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77817843041224400842933649 58363382280918300632200237)
            ·
              refine ⟨21886268355344362737075089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58363382280918300632200237 21886268355344362737075089)
              ·
                refine ⟨16414701266508272052806317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21886268355344362737075089 16414701266508272052806317)
                ·
                  refine ⟨6155512974940602019802369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16414701266508272052806317 6155512974940602019802369)
                  ·
                    refine ⟨4616634731205451514851777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6155512974940602019802369 4616634731205451514851777)
                    ·
                      refine ⟨3462476048404088636138833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616634731205451514851777 3462476048404088636138833)
                      ·
                        rfl

theorem cell23_6743148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_6743148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743148 prefixEnd_6743148 := by exact prefixLift 6743148
  have htrace : WordTrace (prefixWord ++ tailWord_6743148) baseStart_6743148 baseEnd_6743148 := by
    simpa [prefixWord, tailWord_6743148, baseEnd_6743148] using wordTrace_append hprefix tailTrace_6743148
  have hstable : (prefixWord ++ tailWord_6743148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743148).length < 2 ^ (prefixWord ++ tailWord_6743148).sum := by decide
  have hdescent : baseEnd_6743148 < baseStart_6743148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743151 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 3]
def baseStart_6743151 : Nat := 118140960795 + 6743151 * 2 ^ 59
def prefixEnd_6743151 : Nat := 4983230072969 + 3 ^ 40 * 6743151 * 2
def baseEnd_6743151 : Nat := 3462477588846052124401319

theorem tailTrace_6743151 : CollatzResearch.WordTrace tailWord_6743151 prefixEnd_6743151 3462477588846052124401319 := by
  unfold tailWord_6743151
  simp only [CollatzResearch.WordTrace]
  refine ⟨245942921993723040349285307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163961947995815360232856871 245942921993723040349285307)
  ·
    refine ⟨368914382990584560523927961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245942921993723040349285307 368914382990584560523927961)
    ·
      refine ⟨276685787242938420392945971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368914382990584560523927961 276685787242938420392945971)
      ·
        refine ⟨415028680864407630589418957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276685787242938420392945971 415028680864407630589418957)
        ·
          refine ⟨155635755324152861471032109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415028680864407630589418957 155635755324152861471032109)
          ·
            refine ⟨58363408246557323051637041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155635755324152861471032109 58363408246557323051637041)
            ·
              refine ⟨43772556184917992288727781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58363408246557323051637041 43772556184917992288727781)
              ·
                refine ⟨8207354284672123554136459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43772556184917992288727781 8207354284672123554136459)
                ·
                  refine ⟨12311031427008185331204689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8207354284672123554136459 12311031427008185331204689)
                  ·
                    refine ⟨9233273570256138998403517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12311031427008185331204689 9233273570256138998403517)
                    ·
                      refine ⟨3462477588846052124401319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9233273570256138998403517 3462477588846052124401319)
                      ·
                        rfl

theorem cell23_6743151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_6743151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743151 prefixEnd_6743151 := by exact prefixLift 6743151
  have htrace : WordTrace (prefixWord ++ tailWord_6743151) baseStart_6743151 baseEnd_6743151 := by
    simpa [prefixWord, tailWord_6743151, baseEnd_6743151] using wordTrace_append hprefix tailTrace_6743151
  have hstable : (prefixWord ++ tailWord_6743151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743151).length < 2 ^ (prefixWord ++ tailWord_6743151).sum := by decide
  have hdescent : baseEnd_6743151 < baseStart_6743151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743168 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 1, 2, 3]
def baseStart_6743168 : Nat := 118140960795 + 6743168 * 2 ^ 59
def prefixEnd_6743168 : Nat := 4983230072969 + 3 ^ 40 * 6743168 * 2
def baseEnd_6743168 : Nat := 3462486318017178557888741

theorem tailTrace_6743168 : CollatzResearch.WordTrace tailWord_6743168 prefixEnd_6743168 3462486318017178557888741 := by
  unfold tailWord_6743168
  simp only [CollatzResearch.WordTrace]
  refine ⟨122971771017330726126327079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163962361356440968168436105 122971771017330726126327079)
  ·
    refine ⟨184457656525996089189490619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122971771017330726126327079 184457656525996089189490619)
    ·
      refine ⟨276686484788994133784235929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184457656525996089189490619 276686484788994133784235929)
      ·
        refine ⟨207514863591745600338176947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276686484788994133784235929 207514863591745600338176947)
        ·
          refine ⟨311272295387618400507265421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207514863591745600338176947 311272295387618400507265421)
          ·
            refine ⟨116727110770356900190224533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311272295387618400507265421 116727110770356900190224533)
            ·
              refine ⟨5471583317360479696416775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116727110770356900190224533 5471583317360479696416775)
              ·
                refine ⟨8207374976040719544625163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471583317360479696416775 8207374976040719544625163)
                ·
                  refine ⟨12311062464061079316937745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8207374976040719544625163 12311062464061079316937745)
                  ·
                    refine ⟨9233296848045809487703309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12311062464061079316937745 9233296848045809487703309)
                    ·
                      refine ⟨3462486318017178557888741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9233296848045809487703309 3462486318017178557888741)
                      ·
                        rfl

theorem cell23_6743168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_6743168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743168 prefixEnd_6743168 := by exact prefixLift 6743168
  have htrace : WordTrace (prefixWord ++ tailWord_6743168) baseStart_6743168 baseEnd_6743168 := by
    simpa [prefixWord, tailWord_6743168, baseEnd_6743168] using wordTrace_append hprefix tailTrace_6743168
  have hstable : (prefixWord ++ tailWord_6743168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743168).length < 2 ^ (prefixWord ++ tailWord_6743168).sum := by decide
  have hdescent : baseEnd_6743168 < baseStart_6743168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743182 : List Nat := [4, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_6743182 : Nat := 118140960795 + 6743182 * 2 ^ 59
def prefixEnd_6743182 : Nat := 4983230072969 + 3 ^ 40 * 6743182 * 2
def baseEnd_6743182 : Nat := 3462493506746341503113677

theorem tailTrace_6743182 : CollatzResearch.WordTrace tailWord_6743182 prefixEnd_6743182 3462493506746341503113677 := by
  unfold tailWord_6743182
  simp only [CollatzResearch.WordTrace]
  refine ⟨30743006582076341580457975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163962701771073821762442533 30743006582076341580457975)
  ·
    refine ⟨46114509873114512370686963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30743006582076341580457975 46114509873114512370686963)
    ·
      refine ⟨69171764809671768556030445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46114509873114512370686963 69171764809671768556030445)
      ·
        refine ⟨25939411803626913208511417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69171764809671768556030445 25939411803626913208511417)
        ·
          refine ⟨19454558852720184906383563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25939411803626913208511417 19454558852720184906383563)
          ·
            refine ⟨29181838279080277359575345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19454558852720184906383563 29181838279080277359575345)
            ·
              refine ⟨21886378709310208019681509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29181838279080277359575345 21886378709310208019681509)
              ·
                refine ⟨4103696007995664003690283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21886378709310208019681509 4103696007995664003690283)
                ·
                  refine ⟨6155544011993496005535425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103696007995664003690283 6155544011993496005535425)
                  ·
                    refine ⟨4616658008995122004151569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6155544011993496005535425 4616658008995122004151569)
                    ·
                      refine ⟨3462493506746341503113677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616658008995122004151569 3462493506746341503113677)
                      ·
                        rfl

theorem cell23_6743182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_6743182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743182 prefixEnd_6743182 := by exact prefixLift 6743182
  have htrace : WordTrace (prefixWord ++ tailWord_6743182) baseStart_6743182 baseEnd_6743182 := by
    simpa [prefixWord, tailWord_6743182, baseEnd_6743182] using wordTrace_append hprefix tailTrace_6743182
  have hstable : (prefixWord ++ tailWord_6743182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743182).length < 2 ^ (prefixWord ++ tailWord_6743182).sum := by decide
  have hdescent : baseEnd_6743182 < baseStart_6743182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743295 : List Nat := [1, 1, 2, 2, 1, 7, 2, 2, 5]
def baseStart_6743295 : Nat := 118140960795 + 6743295 * 2 ^ 59
def prefixEnd_6743295 : Nat := 4983230072969 + 3 ^ 40 * 6743295 * 2
def baseEnd_6743295 : Nat := 384727947784477729000073

theorem tailTrace_6743295 : CollatzResearch.WordTrace tailWord_6743295 prefixEnd_6743295 384727947784477729000073 := by
  unfold tailWord_6743295
  simp only [CollatzResearch.WordTrace]
  refine ⟨245948174105201352942527339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163965449403467568628351559 245948174105201352942527339)
  ·
    refine ⟨368922261157802029413791009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245948174105201352942527339 368922261157802029413791009)
    ·
      refine ⟨276691695868351522060343257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368922261157802029413791009 276691695868351522060343257)
      ·
        refine ⟨207518771901263641545257443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276691695868351522060343257 207518771901263641545257443)
        ·
          refine ⟨311278157851895462317886165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207518771901263641545257443 311278157851895462317886165)
          ·
            refine ⟨7295581824653799898075457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 311278157851895462317886165 7295581824653799898075457)
            ·
              refine ⟨5471686368490349923556593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7295581824653799898075457 5471686368490349923556593)
              ·
                refine ⟨4103764776367762442667445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471686368490349923556593 4103764776367762442667445)
                ·
                  refine ⟨384727947784477729000073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4103764776367762442667445 384727947784477729000073)
                  ·
                    rfl

theorem cell23_6743295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 5].length) (baseStart_6743295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743295 prefixEnd_6743295 := by exact prefixLift 6743295
  have htrace : WordTrace (prefixWord ++ tailWord_6743295) baseStart_6743295 baseEnd_6743295 := by
    simpa [prefixWord, tailWord_6743295, baseEnd_6743295] using wordTrace_append hprefix tailTrace_6743295
  have hstable : (prefixWord ++ tailWord_6743295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743295).length < 2 ^ (prefixWord ++ tailWord_6743295).sum := by decide
  have hdescent : baseEnd_6743295 < baseStart_6743295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743325 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6743325 : Nat := 118140960795 + 6743325 * 2 ^ 59
def prefixEnd_6743325 : Nat := 4983230072969 + 3 ^ 40 * 6743325 * 2
def baseEnd_6743325 : Nat := 1154188978159978147875173

theorem tailTrace_6743325 : CollatzResearch.WordTrace tailWord_6743325 prefixEnd_6743325 1154188978159978147875173 := by
  unfold tailWord_6743325
  simp only [CollatzResearch.WordTrace]
  refine ⟨245949268295092668066119429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163966178863395112044079619 245949268295092668066119429)
  ·
    refine ⟨46115487805329875262397393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245949268295092668066119429 46115487805329875262397393)
    ·
      refine ⟨34586615853997406446798045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46115487805329875262397393 34586615853997406446798045)
      ·
        refine ⟨12969980945249027417549267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34586615853997406446798045 12969980945249027417549267)
        ·
          refine ⟨19454971417873541126323901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12969980945249027417549267 19454971417873541126323901)
          ·
            refine ⟨7295614281702577922371463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19454971417873541126323901 7295614281702577922371463)
            ·
              refine ⟨10943421422553866883557195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295614281702577922371463 10943421422553866883557195)
              ·
                refine ⟨16415132133830800325335793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943421422553866883557195 16415132133830800325335793)
                ·
                  refine ⟨12311349100373100244001845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16415132133830800325335793 12311349100373100244001845)
                  ·
                    refine ⟨1154188978159978147875173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12311349100373100244001845 1154188978159978147875173)
                    ·
                      rfl

theorem cell23_6743325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6743325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743325 prefixEnd_6743325 := by exact prefixLift 6743325
  have htrace : WordTrace (prefixWord ++ tailWord_6743325) baseStart_6743325 baseEnd_6743325 := by
    simpa [prefixWord, tailWord_6743325, baseEnd_6743325] using wordTrace_append hprefix tailTrace_6743325
  have hstable : (prefixWord ++ tailWord_6743325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743325).length < 2 ^ (prefixWord ++ tailWord_6743325).sum := by decide
  have hdescent : baseEnd_6743325 < baseStart_6743325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743328 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4]
def baseStart_6743328 : Nat := 118140960795 + 6743328 * 2 ^ 59
def prefixEnd_6743328 : Nat := 4983230072969 + 3 ^ 40 * 6743328 * 2
def baseEnd_6743328 : Nat := 3462568474921897931888005

theorem tailTrace_6743328 : CollatzResearch.WordTrace tailWord_6743328 prefixEnd_6743328 3462568474921897931888005 := by
  unfold tailWord_6743328
  simp only [CollatzResearch.WordTrace]
  refine ⟨122974688857040899789239319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163966251809387866385652425 122974688857040899789239319)
  ·
    refine ⟨184462033285561349683858979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122974688857040899789239319 184462033285561349683858979)
    ·
      refine ⟨276693049928342024525788469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184462033285561349683858979 276693049928342024525788469)
      ·
        refine ⟨25939973430782064799292669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276693049928342024525788469 25939973430782064799292669)
        ·
          refine ⟨9727490036543274299734751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25939973430782064799292669 9727490036543274299734751)
          ·
            refine ⟨14591235054814911449602127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9727490036543274299734751 14591235054814911449602127)
            ·
              refine ⟨21886852582222367174403191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14591235054814911449602127 21886852582222367174403191)
              ·
                refine ⟨32830278873333550761604787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21886852582222367174403191 32830278873333550761604787)
                ·
                  refine ⟨49245418310000326142407181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32830278873333550761604787 49245418310000326142407181)
                  ·
                    refine ⟨18467031866250122303402693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49245418310000326142407181 18467031866250122303402693)
                    ·
                      refine ⟨3462568474921897931888005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18467031866250122303402693 3462568474921897931888005)
                      ·
                        rfl

theorem cell23_6743328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_6743328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743328 prefixEnd_6743328 := by exact prefixLift 6743328
  have htrace : WordTrace (prefixWord ++ tailWord_6743328) baseStart_6743328 baseEnd_6743328 := by
    simpa [prefixWord, tailWord_6743328, baseEnd_6743328] using wordTrace_append hprefix tailTrace_6743328
  have hstable : (prefixWord ++ tailWord_6743328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743328).length < 2 ^ (prefixWord ++ tailWord_6743328).sum := by decide
  have hdescent : baseEnd_6743328 < baseStart_6743328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743405 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_6743405 : Nat := 118140960795 + 6743405 * 2 ^ 59
def prefixEnd_6743405 : Nat := 4983230072969 + 3 ^ 40 * 6743405 * 2
def baseEnd_6743405 : Nat := 3462608012932294130625151

theorem tailTrace_6743405 : CollatzResearch.WordTrace tailWord_6743405 prefixEnd_6743405 3462608012932294130625151 := by
  unfold tailWord_6743405
  simp only [CollatzResearch.WordTrace]
  refine ⟨245952186134802841729031669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163968124089868561152687779 245952186134802841729031669)
  ·
    refine ⟨23058017450137766412096719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245952186134802841729031669 23058017450137766412096719)
    ·
      refine ⟨34587026175206649618145079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23058017450137766412096719 34587026175206649618145079)
      ·
        refine ⟨51880539262809974427217619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34587026175206649618145079 51880539262809974427217619)
        ·
          refine ⟨77820808894214961640826429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51880539262809974427217619 77820808894214961640826429)
          ·
            refine ⟨29182803335330610615309911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77820808894214961640826429 29182803335330610615309911)
            ·
              refine ⟨43774205002995915922964867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29182803335330610615309911 43774205002995915922964867)
              ·
                refine ⟨65661307504493873884447301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43774205002995915922964867 65661307504493873884447301)
                ·
                  refine ⟨12311495157092601353333869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65661307504493873884447301 12311495157092601353333869)
                  ·
                    refine ⟨4616810683909725507500201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12311495157092601353333869 4616810683909725507500201)
                    ·
                      refine ⟨3462608012932294130625151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616810683909725507500201 3462608012932294130625151)
                      ·
                        rfl

theorem cell23_6743405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_6743405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743405 prefixEnd_6743405 := by exact prefixLift 6743405
  have htrace : WordTrace (prefixWord ++ tailWord_6743405) baseStart_6743405 baseEnd_6743405 := by
    simpa [prefixWord, tailWord_6743405, baseEnd_6743405] using wordTrace_append hprefix tailTrace_6743405
  have hstable : (prefixWord ++ tailWord_6743405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743405).length < 2 ^ (prefixWord ++ tailWord_6743405).sum := by decide
  have hdescent : baseEnd_6743405 < baseStart_6743405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743406 : List Nat := [4, 1, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_6743406 : Nat := 118140960795 + 6743406 * 2 ^ 59
def prefixEnd_6743406 : Nat := 4983230072969 + 3 ^ 40 * 6743406 * 2
def baseEnd_6743406 : Nat := 1154202842137649542237549

theorem tailTrace_6743406 : CollatzResearch.WordTrace tailWord_6743406 prefixEnd_6743406 1154202842137649542237549 := by
  unfold tailWord_6743406
  simp only [CollatzResearch.WordTrace]
  refine ⟨30744027825974902362477259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163968148405199479266545381 30744027825974902362477259)
  ·
    refine ⟨46116041738962353543715889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30744027825974902362477259 46116041738962353543715889)
    ·
      refine ⟨34587031304221765157786917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46116041738962353543715889 34587031304221765157786917)
      ·
        refine ⟨6485068369541580967085047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34587031304221765157786917 6485068369541580967085047)
        ·
          refine ⟨9727602554312371450627571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485068369541580967085047 9727602554312371450627571)
          ·
            refine ⟨14591403831468557175941357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9727602554312371450627571 14591403831468557175941357)
            ·
              refine ⟨5471776436800708940978009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14591403831468557175941357 5471776436800708940978009)
              ·
                refine ⟨4103832327600531705733507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471776436800708940978009 4103832327600531705733507)
                ·
                  refine ⟨6155748491400797558600261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103832327600531705733507 6155748491400797558600261)
                  ·
                    refine ⟨1154202842137649542237549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6155748491400797558600261 1154202842137649542237549)
                    ·
                      rfl

theorem cell23_6743406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_6743406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743406 prefixEnd_6743406 := by exact prefixLift 6743406
  have htrace : WordTrace (prefixWord ++ tailWord_6743406) baseStart_6743406 baseEnd_6743406 := by
    simpa [prefixWord, tailWord_6743406, baseEnd_6743406] using wordTrace_append hprefix tailTrace_6743406
  have hstable : (prefixWord ++ tailWord_6743406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743406).length < 2 ^ (prefixWord ++ tailWord_6743406).sum := by decide
  have hdescent : baseEnd_6743406 < baseStart_6743406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743435 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 5, 2, 2]
def baseStart_6743435 : Nat := 118140960795 + 6743435 * 2 ^ 59
def prefixEnd_6743435 : Nat := 4983230072969 + 3 ^ 40 * 6743435 * 2
def baseEnd_6743435 : Nat := 3462623417351929013250013

theorem tailTrace_6743435 : CollatzResearch.WordTrace tailWord_6743435 prefixEnd_6743435 3462623417351929013250013 := by
  unfold tailWord_6743435
  simp only [CollatzResearch.WordTrace]
  refine ⟨245953280324694156852623759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163968853549796104568415839 245953280324694156852623759)
  ·
    refine ⟨368929920487041235278935639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245953280324694156852623759 368929920487041235278935639)
    ·
      refine ⟨553394880730561852918403459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368929920487041235278935639 553394880730561852918403459)
      ·
        refine ⟨830092321095842779377605189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553394880730561852918403459 830092321095842779377605189)
        ·
          refine ⟨155642310205470521133300973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 830092321095842779377605189 155642310205470521133300973)
          ·
            refine ⟨58365866327051445424987865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155642310205470521133300973 58365866327051445424987865)
            ·
              refine ⟨43774399745288584068740899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58365866327051445424987865 43774399745288584068740899)
              ·
                refine ⟨65661599617932876103111349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43774399745288584068740899 65661599617932876103111349)
                ·
                  refine ⟨6155774964181207134666689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65661599617932876103111349 6155774964181207134666689)
                  ·
                    refine ⟨4616831223135905351000017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6155774964181207134666689 4616831223135905351000017)
                    ·
                      refine ⟨3462623417351929013250013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616831223135905351000017 3462623417351929013250013)
                      ·
                        rfl

theorem cell23_6743435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 2, 2].length) (baseStart_6743435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743435 prefixEnd_6743435 := by exact prefixLift 6743435
  have htrace : WordTrace (prefixWord ++ tailWord_6743435) baseStart_6743435 baseEnd_6743435 := by
    simpa [prefixWord, tailWord_6743435, baseEnd_6743435] using wordTrace_append hprefix tailTrace_6743435
  have hstable : (prefixWord ++ tailWord_6743435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743435).length < 2 ^ (prefixWord ++ tailWord_6743435).sum := by decide
  have hdescent : baseEnd_6743435 < baseStart_6743435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743455 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 5]
def baseStart_6743455 : Nat := 118140960795 + 6743455 * 2 ^ 59
def prefixEnd_6743455 : Nat := 4983230072969 + 3 ^ 40 * 6743455 * 2
def baseEnd_6743455 : Nat := 3462633686965018934999921

theorem tailTrace_6743455 : CollatzResearch.WordTrace tailWord_6743455 prefixEnd_6743455 3462633686965018934999921 := by
  unfold tailWord_6743455
  simp only [CollatzResearch.WordTrace]
  refine ⟨245954009784621700268351819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163969339856414466845567879 245954009784621700268351819)
  ·
    refine ⟨368931014676932550402527729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245954009784621700268351819 368931014676932550402527729)
    ·
      refine ⟨276698261007699412801895797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368931014676932550402527729 276698261007699412801895797)
      ·
        refine ⟨25940461969471819950177731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276698261007699412801895797 25940461969471819950177731)
        ·
          refine ⟨38910692954207729925266597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25940461969471819950177731 38910692954207729925266597)
          ·
            refine ⟨7295754928913949360987487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38910692954207729925266597 7295754928913949360987487)
            ·
              refine ⟨10943632393370924041481231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295754928913949360987487 10943632393370924041481231)
              ·
                refine ⟨16415448590056386062221847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943632393370924041481231 16415448590056386062221847)
                ·
                  refine ⟨24623172885084579093332771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16415448590056386062221847 24623172885084579093332771)
                  ·
                    refine ⟨36934759327626868639999157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24623172885084579093332771 36934759327626868639999157)
                    ·
                      refine ⟨3462633686965018934999921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36934759327626868639999157 3462633686965018934999921)
                      ·
                        rfl

theorem cell23_6743455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_6743455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743455 prefixEnd_6743455 := by exact prefixLift 6743455
  have htrace : WordTrace (prefixWord ++ tailWord_6743455) baseStart_6743455 baseEnd_6743455 := by
    simpa [prefixWord, tailWord_6743455, baseEnd_6743455] using wordTrace_append hprefix tailTrace_6743455
  have hstable : (prefixWord ++ tailWord_6743455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743455).length < 2 ^ (prefixWord ++ tailWord_6743455).sum := by decide
  have hdescent : baseEnd_6743455 < baseStart_6743455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743461 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_6743461 : Nat := 118140960795 + 6743461 * 2 ^ 59
def prefixEnd_6743461 : Nat := 4983230072969 + 3 ^ 40 * 6743461 * 2
def baseEnd_6743461 : Nat := 3462636767848945911524893

theorem tailTrace_6743461 : CollatzResearch.WordTrace tailWord_6743461 prefixEnd_6743461 3462636767848945911524893 := by
  unfold tailWord_6743461
  simp only [CollatzResearch.WordTrace]
  refine ⟨245954228622599963293070237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163969485748399975528713491 245954228622599963293070237)
  ·
    refine ⟨92232835733474986234901339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245954228622599963293070237 92232835733474986234901339)
    ·
      refine ⟨138349253600212479352352009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92232835733474986234901339 138349253600212479352352009)
      ·
        refine ⟨103761940200159359514264007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138349253600212479352352009 103761940200159359514264007)
        ·
          refine ⟨155642910300239039271396011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103761940200159359514264007 155642910300239039271396011)
          ·
            refine ⟨233464365450358558907094017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155642910300239039271396011 233464365450358558907094017)
            ·
              refine ⟨175098274087768919180320513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233464365450358558907094017 175098274087768919180320513)
              ·
                refine ⟨131323705565826689385240385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175098274087768919180320513 131323705565826689385240385)
                ·
                  refine ⟨98492779174370017038930289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131323705565826689385240385 98492779174370017038930289)
                  ·
                    refine ⟨73869584380777512779197717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98492779174370017038930289 73869584380777512779197717)
                    ·
                      refine ⟨3462636767848945911524893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73869584380777512779197717 3462636767848945911524893)
                      ·
                        rfl

theorem cell23_6743461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_6743461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743461 prefixEnd_6743461 := by exact prefixLift 6743461
  have htrace : WordTrace (prefixWord ++ tailWord_6743461) baseStart_6743461 baseEnd_6743461 := by
    simpa [prefixWord, tailWord_6743461, baseEnd_6743461] using wordTrace_append hprefix tailTrace_6743461
  have hstable : (prefixWord ++ tailWord_6743461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743461).length < 2 ^ (prefixWord ++ tailWord_6743461).sum := by decide
  have hdescent : baseEnd_6743461 < baseStart_6743461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743485 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_6743485 : Nat := 118140960795 + 6743485 * 2 ^ 59
def prefixEnd_6743485 : Nat := 4983230072969 + 3 ^ 40 * 6743485 * 2
def baseEnd_6743485 : Nat := 3462649091384653817624783

theorem tailTrace_6743485 : CollatzResearch.WordTrace tailWord_6743485 prefixEnd_6743485 3462649091384653817624783 := by
  unfold tailWord_6743485
  simp only [CollatzResearch.WordTrace]
  refine ⟨245955103974513015391943909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163970069316342010261295939 245955103974513015391943909)
  ·
    refine ⟨46116581995221190385989483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245955103974513015391943909 46116581995221190385989483)
    ·
      refine ⟨69174872992831785578984225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46116581995221190385989483 69174872992831785578984225)
      ·
        refine ⟨51881154744623839184238169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69174872992831785578984225 51881154744623839184238169)
        ·
          refine ⟨38910866058467879388178627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51881154744623839184238169 38910866058467879388178627)
          ·
            refine ⟨58366299087701819082267941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38910866058467879388178627 58366299087701819082267941)
            ·
              refine ⟨10943681078944091077925239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58366299087701819082267941 10943681078944091077925239)
              ·
                refine ⟨16415521618416136616887859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943681078944091077925239 16415521618416136616887859)
                ·
                  refine ⟨24623282427624204925331789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16415521618416136616887859 24623282427624204925331789)
                  ·
                    refine ⟨9233730910359076846999421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24623282427624204925331789 9233730910359076846999421)
                    ·
                      refine ⟨3462649091384653817624783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9233730910359076846999421 3462649091384653817624783)
                      ·
                        rfl

theorem cell23_6743485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_6743485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743485 prefixEnd_6743485 := by exact prefixLift 6743485
  have htrace : WordTrace (prefixWord ++ tailWord_6743485) baseStart_6743485 baseEnd_6743485 := by
    simpa [prefixWord, tailWord_6743485, baseEnd_6743485] using wordTrace_append hprefix tailTrace_6743485
  have hstable : (prefixWord ++ tailWord_6743485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743485).length < 2 ^ (prefixWord ++ tailWord_6743485).sum := by decide
  have hdescent : baseEnd_6743485 < baseStart_6743485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743490 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6743490 : Nat := 118140960795 + 6743490 * 2 ^ 59
def prefixEnd_6743490 : Nat := 4983230072969 + 3 ^ 40 * 6743490 * 2
def baseEnd_6743490 : Nat := 3462651658787926298062261

theorem tailTrace_6743490 : CollatzResearch.WordTrace tailWord_6743490 prefixEnd_6743490 3462651658787926298062261 := by
  unfold tailWord_6743490
  simp only [CollatzResearch.WordTrace]
  refine ⟨61488821584873725311468981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163970190892996600830583949 61488821584873725311468981)
  ·
    refine ⟨5764577023581911747950217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61488821584873725311468981 5764577023581911747950217)
    ·
      refine ⟨4323432767686433810962663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5764577023581911747950217 4323432767686433810962663)
      ·
        refine ⟨6485149151529650716443995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323432767686433810962663 6485149151529650716443995)
        ·
          refine ⟨9727723727294476074665993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485149151529650716443995 9727723727294476074665993)
          ·
            refine ⟨7295792795470857055999495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9727723727294476074665993 7295792795470857055999495)
            ·
              refine ⟨10943689193206285583999243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295792795470857055999495 10943689193206285583999243)
              ·
                refine ⟨16415533789809428375998865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943689193206285583999243 16415533789809428375998865)
                ·
                  refine ⟨12311650342357071281999149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16415533789809428375998865 12311650342357071281999149)
                  ·
                    refine ⟨4616868878383901730749681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12311650342357071281999149 4616868878383901730749681)
                    ·
                      refine ⟨3462651658787926298062261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616868878383901730749681 3462651658787926298062261)
                      ·
                        rfl

theorem cell23_6743490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6743490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743490 prefixEnd_6743490 := by exact prefixLift 6743490
  have htrace : WordTrace (prefixWord ++ tailWord_6743490) baseStart_6743490 baseEnd_6743490 := by
    simpa [prefixWord, tailWord_6743490, baseEnd_6743490] using wordTrace_append hprefix tailTrace_6743490
  have hstable : (prefixWord ++ tailWord_6743490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743490).length < 2 ^ (prefixWord ++ tailWord_6743490).sum := by decide
  have hdescent : baseEnd_6743490 < baseStart_6743490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743495 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_6743495 : Nat := 118140960795 + 6743495 * 2 ^ 59
def prefixEnd_6743495 : Nat := 4983230072969 + 3 ^ 40 * 6743495 * 2
def baseEnd_6743495 : Nat := 3462654226191198778499737

theorem tailTrace_6743495 : CollatzResearch.WordTrace tailWord_6743495 prefixEnd_6743495 3462654226191198778499737 := by
  unfold tailWord_6743495
  simp only [CollatzResearch.WordTrace]
  refine ⟨245955468704476787099807939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163970312469651191399871959 245955468704476787099807939)
  ·
    refine ⟨368933203056715180649711909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245955468704476787099807939 368933203056715180649711909)
    ·
      refine ⟨69174975573134096371820983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368933203056715180649711909 69174975573134096371820983)
      ·
        refine ⟨103762463359701144557731475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69174975573134096371820983 103762463359701144557731475)
        ·
          refine ⟨155643695039551716836597213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103762463359701144557731475 155643695039551716836597213)
          ·
            refine ⟨58366385639831893813723955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155643695039551716836597213 58366385639831893813723955)
            ·
              refine ⟨87549578459747840720585933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58366385639831893813723955 87549578459747840720585933)
              ·
                refine ⟨32831091922405440270219725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87549578459747840720585933 32831091922405440270219725)
                ·
                  refine ⟨12311659470902040101332397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32831091922405440270219725 12311659470902040101332397)
                  ·
                    refine ⟨4616872301588265037999649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12311659470902040101332397 4616872301588265037999649)
                    ·
                      refine ⟨3462654226191198778499737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4616872301588265037999649 3462654226191198778499737)
                      ·
                        rfl

theorem cell23_6743495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_6743495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743495 prefixEnd_6743495 := by exact prefixLift 6743495
  have htrace : WordTrace (prefixWord ++ tailWord_6743495) baseStart_6743495 baseEnd_6743495 := by
    simpa [prefixWord, tailWord_6743495, baseEnd_6743495] using wordTrace_append hprefix tailTrace_6743495
  have hstable : (prefixWord ++ tailWord_6743495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743495).length < 2 ^ (prefixWord ++ tailWord_6743495).sum := by decide
  have hdescent : baseEnd_6743495 < baseStart_6743495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743548 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 7]
def baseStart_6743548 : Nat := 118140960795 + 6743548 * 2 ^ 59
def prefixEnd_6743548 : Nat := 4983230072969 + 3 ^ 40 * 6743548 * 2
def baseEnd_6743548 : Nat := 384742382296209674570777

theorem tailTrace_6743548 : CollatzResearch.WordTrace tailWord_6743548 prefixEnd_6743548 384742382296209674570777 := by
  unfold tailWord_6743548
  simp only [CollatzResearch.WordTrace]
  refine ⟨122978700886642388575743649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163971601182189851434324865 122978700886642388575743649)
  ·
    refine ⟨92234025664981791431807737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122978700886642388575743649 92234025664981791431807737)
    ·
      refine ⟨69175519248736343573855803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92234025664981791431807737 69175519248736343573855803)
      ·
        refine ⟨103763278873104515360783705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69175519248736343573855803 103763278873104515360783705)
        ·
          refine ⟨77822459154828386520587779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103763278873104515360783705 77822459154828386520587779)
          ·
            refine ⟨116733688732242579780881669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77822459154828386520587779 116733688732242579780881669)
            ·
              refine ⟨21887566637295483708915313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116733688732242579780881669 21887566637295483708915313)
              ·
                refine ⟨16415674977971612781686485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21887566637295483708915313 16415674977971612781686485)
                ·
                  refine ⟨384742382296209674570777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16415674977971612781686485 384742382296209674570777)
                  ·
                    rfl

theorem cell23_6743548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_6743548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743548 prefixEnd_6743548 := by exact prefixLift 6743548
  have htrace : WordTrace (prefixWord ++ tailWord_6743548) baseStart_6743548 baseEnd_6743548 := by
    simpa [prefixWord, tailWord_6743548, baseEnd_6743548] using wordTrace_append hprefix tailTrace_6743548
  have hstable : (prefixWord ++ tailWord_6743548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743548).length < 2 ^ (prefixWord ++ tailWord_6743548).sum := by decide
  have hdescent : baseEnd_6743548 < baseStart_6743548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743612 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_6743612 : Nat := 118140960795 + 6743612 * 2 ^ 59
def prefixEnd_6743612 : Nat := 4983230072969 + 3 ^ 40 * 6743612 * 2
def baseEnd_6743612 : Nat := 1154238101142591606912233

theorem tailTrace_6743612 : CollatzResearch.WordTrace tailWord_6743612 prefixEnd_6743612 1154238101142591606912233 := by
  unfold tailWord_6743612
  simp only [CollatzResearch.WordTrace]
  refine ⟨122979868022526458040908545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163973157363368610721211393 122979868022526458040908545)
  ·
    refine ⟨92234901016894843530681409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122979868022526458040908545 92234901016894843530681409)
    ·
      refine ⟨69176175762671132648011057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92234901016894843530681409 69176175762671132648011057)
      ·
        refine ⟨51882131822003349486008293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69176175762671132648011057 51882131822003349486008293)
        ·
          refine ⟨9727899716625628028626555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51882131822003349486008293 9727899716625628028626555)
          ·
            refine ⟨14591849574938442042939833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9727899716625628028626555 14591849574938442042939833)
            ·
              refine ⟨10943887181203831532204875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14591849574938442042939833 10943887181203831532204875)
              ·
                refine ⟨16415830771805747298307313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943887181203831532204875 16415830771805747298307313)
                ·
                  refine ⟨12311873078854310473730485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16415830771805747298307313 12311873078854310473730485)
                  ·
                    refine ⟨1154238101142591606912233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12311873078854310473730485 1154238101142591606912233)
                    ·
                      rfl

theorem cell23_6743612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_6743612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743612 prefixEnd_6743612 := by exact prefixLift 6743612
  have htrace : WordTrace (prefixWord ++ tailWord_6743612) baseStart_6743612 baseEnd_6743612 := by
    simpa [prefixWord, tailWord_6743612, baseEnd_6743612] using wordTrace_append hprefix tailTrace_6743612
  have hstable : (prefixWord ++ tailWord_6743612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743612).length < 2 ^ (prefixWord ++ tailWord_6743612).sum := by decide
  have hdescent : baseEnd_6743612 < baseStart_6743612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743615 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_6743615 : Nat := 118140960795 + 6743615 * 2 ^ 59
def prefixEnd_6743615 : Nat := 4983230072969 + 3 ^ 40 * 6743615 * 2
def baseEnd_6743615 : Nat := 3462715843869738308999185

theorem tailTrace_6743615 : CollatzResearch.WordTrace tailWord_6743615 prefixEnd_6743615 3462715843869738308999185 := by
  unfold tailWord_6743615
  simp only [CollatzResearch.WordTrace]
  refine ⟨245959845464042047594176299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163973230309361365062784199 245959845464042047594176299)
  ·
    refine ⟨368939768196063071391264449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245959845464042047594176299 368939768196063071391264449)
    ·
      refine ⟨276704826147047303543448337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368939768196063071391264449 276704826147047303543448337)
      ·
        refine ⟨207528619610285477657586253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276704826147047303543448337 207528619610285477657586253)
        ·
          refine ⟨77823232353857054121594845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207528619610285477657586253 77823232353857054121594845)
          ·
            refine ⟨29183712132696395295598067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77823232353857054121594845 29183712132696395295598067)
            ·
              refine ⟨43775568199044592943397101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29183712132696395295598067 43775568199044592943397101)
              ·
                refine ⟨16415838074641722353773913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43775568199044592943397101 16415838074641722353773913)
                ·
                  refine ⟨12311878555981291765330435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16415838074641722353773913 12311878555981291765330435)
                  ·
                    refine ⟨18467817833971937647995653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12311878555981291765330435 18467817833971937647995653)
                    ·
                      refine ⟨3462715843869738308999185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18467817833971937647995653 3462715843869738308999185)
                      ·
                        rfl

theorem cell23_6743615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_6743615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743615 prefixEnd_6743615 := by exact prefixLift 6743615
  have htrace : WordTrace (prefixWord ++ tailWord_6743615) baseStart_6743615 baseEnd_6743615 := by
    simpa [prefixWord, tailWord_6743615, baseEnd_6743615] using wordTrace_append hprefix tailTrace_6743615
  have hstable : (prefixWord ++ tailWord_6743615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743615).length < 2 ^ (prefixWord ++ tailWord_6743615).sum := by decide
  have hdescent : baseEnd_6743615 < baseStart_6743615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743655 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 6]
def baseStart_6743655 : Nat := 118140960795 + 6743655 * 2 ^ 59
def prefixEnd_6743655 : Nat := 4983230072969 + 3 ^ 40 * 6743655 * 2
def baseEnd_6743655 : Nat := 384748487010657572499889

theorem tailTrace_6743655 : CollatzResearch.WordTrace tailWord_6743655 prefixEnd_6743655 384748487010657572499889 := by
  unfold tailWord_6743655
  simp only [CollatzResearch.WordTrace]
  refine ⟨245961304383897134425632419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163974202922598089617088279 245961304383897134425632419)
  ·
    refine ⟨368941956575845701638448629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245961304383897134425632419 368941956575845701638448629)
    ·
      refine ⟨34588308428985534528604559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 368941956575845701638448629 34588308428985534528604559)
      ·
        refine ⟨51882462643478301792906839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34588308428985534528604559 51882462643478301792906839)
        ·
          refine ⟨77823693965217452689360259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51882462643478301792906839 77823693965217452689360259)
          ·
            refine ⟨116735540947826179034040389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77823693965217452689360259 116735540947826179034040389)
            ·
              refine ⟨21887913927717408568882573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116735540947826179034040389 21887913927717408568882573)
              ·
                refine ⟨8207967722894028213330965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21887913927717408568882573 8207967722894028213330965)
                ·
                  refine ⟨384748487010657572499889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8207967722894028213330965 384748487010657572499889)
                  ·
                    rfl

theorem cell23_6743655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 6].length) (baseStart_6743655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743655 prefixEnd_6743655 := by exact prefixLift 6743655
  have htrace : WordTrace (prefixWord ++ tailWord_6743655) baseStart_6743655 baseEnd_6743655 := by
    simpa [prefixWord, tailWord_6743655, baseEnd_6743655] using wordTrace_append hprefix tailTrace_6743655
  have hstable : (prefixWord ++ tailWord_6743655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743655).length < 2 ^ (prefixWord ++ tailWord_6743655).sum := by decide
  have hdescent : baseEnd_6743655 < baseStart_6743655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743669 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6743669 : Nat := 118140960795 + 6743669 * 2 ^ 59
def prefixEnd_6743669 : Nat := 4983230072969 + 3 ^ 40 * 6743669 * 2
def baseEnd_6743669 : Nat := 3462743571825081097723937

theorem tailTrace_6743669 : CollatzResearch.WordTrace tailWord_6743669 prefixEnd_6743669 3462743571825081097723937 := by
  unfold tailWord_6743669
  simp only [CollatzResearch.WordTrace]
  refine ⟨245961815005846414816642061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163974543337230943211094707 245961815005846414816642061)
  ·
    refine ⟨92235680627192405556240773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245961815005846414816642061 92235680627192405556240773)
    ·
      refine ⟨17294190117598576041795145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92235680627192405556240773 17294190117598576041795145)
      ·
        refine ⟨12970642588198932031346359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17294190117598576041795145 12970642588198932031346359)
        ·
          refine ⟨19455963882298398047019539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12970642588198932031346359 19455963882298398047019539)
          ·
            refine ⟨29183945823447597070529309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19455963882298398047019539 29183945823447597070529309)
            ·
              refine ⟨10943979683792848901448491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29183945823447597070529309 10943979683792848901448491)
              ·
                refine ⟨16415969525689273352172737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10943979683792848901448491 16415969525689273352172737)
                ·
                  refine ⟨12311977144266955014129553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16415969525689273352172737 12311977144266955014129553)
                  ·
                    refine ⟨9233982858200216260597165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12311977144266955014129553 9233982858200216260597165)
                    ·
                      refine ⟨3462743571825081097723937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9233982858200216260597165 3462743571825081097723937)
                      ·
                        rfl

theorem cell23_6743669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6743669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743669 prefixEnd_6743669 := by exact prefixLift 6743669
  have htrace : WordTrace (prefixWord ++ tailWord_6743669) baseStart_6743669 baseEnd_6743669 := by
    simpa [prefixWord, tailWord_6743669, baseEnd_6743669] using wordTrace_append hprefix tailTrace_6743669
  have hstable : (prefixWord ++ tailWord_6743669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743669).length < 2 ^ (prefixWord ++ tailWord_6743669).sum := by decide
  have hdescent : baseEnd_6743669 < baseStart_6743669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743692 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 4, 3, 2]
def baseStart_6743692 : Nat := 118140960795 + 6743692 * 2 ^ 59
def prefixEnd_6743692 : Nat := 4983230072969 + 3 ^ 40 * 6743692 * 2
def baseEnd_6743692 : Nat := 3462755381880134507736331

theorem tailTrace_6743692 : CollatzResearch.WordTrace tailWord_6743692 prefixEnd_6743692 3462755381880134507736331 := by
  unfold tailWord_6743692
  simp only [CollatzResearch.WordTrace]
  refine ⟨122981326942381544872364665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163975102589842059829819553 122981326942381544872364665)
  ·
    refine ⟨92235995206786158654273499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122981326942381544872364665 92235995206786158654273499)
    ·
      refine ⟨138353992810179237981410249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92235995206786158654273499 138353992810179237981410249)
      ·
        refine ⟨103765494607634428486057687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138353992810179237981410249 103765494607634428486057687)
        ·
          refine ⟨155648241911451642729086531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103765494607634428486057687 155648241911451642729086531)
          ·
            refine ⟨233472362867177464093629797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155648241911451642729086531 233472362867177464093629797)
            ·
              refine ⟨43776068037595774517555587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233472362867177464093629797 43776068037595774517555587)
              ·
                refine ⟨65664102056393661776333381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43776068037595774517555587 65664102056393661776333381)
                ·
                  refine ⟨12312019135573811583062509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65664102056393661776333381 12312019135573811583062509)
                  ·
                    refine ⟨4617007175840179343648441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12312019135573811583062509 4617007175840179343648441)
                    ·
                      refine ⟨3462755381880134507736331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617007175840179343648441 3462755381880134507736331)
                      ·
                        rfl

theorem cell23_6743692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_6743692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743692 prefixEnd_6743692 := by exact prefixLift 6743692
  have htrace : WordTrace (prefixWord ++ tailWord_6743692) baseStart_6743692 baseEnd_6743692 := by
    simpa [prefixWord, tailWord_6743692, baseEnd_6743692] using wordTrace_append hprefix tailTrace_6743692
  have hstable : (prefixWord ++ tailWord_6743692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743692).length < 2 ^ (prefixWord ++ tailWord_6743692).sum := by decide
  have hdescent : baseEnd_6743692 < baseStart_6743692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743705 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_6743705 : Nat := 118140960795 + 6743705 * 2 ^ 59
def prefixEnd_6743705 : Nat := 4983230072969 + 3 ^ 40 * 6743705 * 2
def baseEnd_6743705 : Nat := 3462762057128642956873771

theorem tailTrace_6743705 : CollatzResearch.WordTrace tailWord_6743705 prefixEnd_6743705 3462762057128642956873771 := by
  unfold tailWord_6743705
  simp only [CollatzResearch.WordTrace]
  refine ⟨245963128033715992964952569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163975418689143995309968379 245963128033715992964952569)
  ·
    refine ⟨184472346025286994723714427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245963128033715992964952569 184472346025286994723714427)
    ·
      refine ⟨276708519037930492085571641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184472346025286994723714427 276708519037930492085571641)
      ·
        refine ⟨207531389278447869064178731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276708519037930492085571641 207531389278447869064178731)
        ·
          refine ⟨311297083917671803596268097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207531389278447869064178731 311297083917671803596268097)
          ·
            refine ⟨233472812938253852697201073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311297083917671803596268097 233472812938253852697201073)
            ·
              refine ⟨175104609703690389522900805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233472812938253852697201073 175104609703690389522900805)
              ·
                refine ⟨32832114319441948035543901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175104609703690389522900805 32832114319441948035543901)
                ·
                  refine ⟨12312042869790730513328963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32832114319441948035543901 12312042869790730513328963)
                  ·
                    refine ⟨18468064304686095769993445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12312042869790730513328963 18468064304686095769993445)
                    ·
                      refine ⟨3462762057128642956873771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18468064304686095769993445 3462762057128642956873771)
                      ·
                        rfl

theorem cell23_6743705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_6743705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743705 prefixEnd_6743705 := by exact prefixLift 6743705
  have htrace : WordTrace (prefixWord ++ tailWord_6743705) baseStart_6743705 baseEnd_6743705 := by
    simpa [prefixWord, tailWord_6743705, baseEnd_6743705] using wordTrace_append hprefix tailTrace_6743705
  have hstable : (prefixWord ++ tailWord_6743705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743705).length < 2 ^ (prefixWord ++ tailWord_6743705).sum := by decide
  have hdescent : baseEnd_6743705 < baseStart_6743705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743742 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_6743742 : Nat := 118140960795 + 6743742 * 2 ^ 59
def prefixEnd_6743742 : Nat := 4983230072969 + 3 ^ 40 * 6743742 * 2
def baseEnd_6743742 : Nat := 3462781055912859312111101

theorem tailTrace_6743742 : CollatzResearch.WordTrace tailWord_6743742 prefixEnd_6743742 3462781055912859312111101 := by
  unfold tailWord_6743742
  simp only [CollatzResearch.WordTrace]
  refine ⟨30745559691822743535506185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163976318356387965522699653 30745559691822743535506185)
  ·
    refine ⟨23059169768867057651629639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30745559691822743535506185 23059169768867057651629639)
    ·
      refine ⟨34588754653300586477444459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23059169768867057651629639 34588754653300586477444459)
      ·
        refine ⟨51883131979950879716166689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34588754653300586477444459 51883131979950879716166689)
        ·
          refine ⟨38912348984963159787125017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51883131979950879716166689 38912348984963159787125017)
          ·
            refine ⟨29184261738722369840343763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38912348984963159787125017 29184261738722369840343763)
            ·
              refine ⟨43776392608083554760515645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29184261738722369840343763 43776392608083554760515645)
              ·
                refine ⟨16416147228031333035193367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43776392608083554760515645 16416147228031333035193367)
                ·
                  refine ⟨24624220842046999552790051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16416147228031333035193367 24624220842046999552790051)
                  ·
                    refine ⟨36936331263070499329185077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24624220842046999552790051 36936331263070499329185077)
                    ·
                      refine ⟨3462781055912859312111101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36936331263070499329185077 3462781055912859312111101)
                      ·
                        rfl

theorem cell23_6743742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_6743742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743742 prefixEnd_6743742 := by exact prefixLift 6743742
  have htrace : WordTrace (prefixWord ++ tailWord_6743742) baseStart_6743742 baseEnd_6743742 := by
    simpa [prefixWord, tailWord_6743742, baseEnd_6743742] using wordTrace_append hprefix tailTrace_6743742
  have hstable : (prefixWord ++ tailWord_6743742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743742).length < 2 ^ (prefixWord ++ tailWord_6743742).sum := by decide
  have hdescent : baseEnd_6743742 < baseStart_6743742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743750 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6743750 : Nat := 118140960795 + 6743750 * 2 ^ 59
def prefixEnd_6743750 : Nat := 4983230072969 + 3 ^ 40 * 6743750 * 2
def baseEnd_6743750 : Nat := 3462785163758095280811065

theorem tailTrace_6743750 : CollatzResearch.WordTrace tailWord_6743750 prefixEnd_6743750 3462785163758095280811065 := by
  unfold tailWord_6743750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7686399041204780176573147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163976512879035310433560469 7686399041204780176573147)
  ·
    refine ⟨11529598561807170264859721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7686399041204780176573147 11529598561807170264859721)
    ·
      refine ⟨8647198921355377698644791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11529598561807170264859721 8647198921355377698644791)
      ·
        refine ⟨12970798382033066547967187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8647198921355377698644791 12970798382033066547967187)
        ·
          refine ⟨19456197573049599821950781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12970798382033066547967187 19456197573049599821950781)
          ·
            refine ⟨7296074089893599933231543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19456197573049599821950781 7296074089893599933231543)
            ·
              refine ⟨10944111134840399899847315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296074089893599933231543 10944111134840399899847315)
              ·
                refine ⟨16416166702260599849770973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10944111134840399899847315 16416166702260599849770973)
                ·
                  refine ⟨6156062513347724943664115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16416166702260599849770973 6156062513347724943664115)
                  ·
                    refine ⟨9234093770021587415496173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156062513347724943664115 9234093770021587415496173)
                    ·
                      refine ⟨3462785163758095280811065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234093770021587415496173 3462785163758095280811065)
                      ·
                        rfl

theorem cell23_6743750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6743750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743750 prefixEnd_6743750 := by exact prefixLift 6743750
  have htrace : WordTrace (prefixWord ++ tailWord_6743750) baseStart_6743750 baseEnd_6743750 := by
    simpa [prefixWord, tailWord_6743750, baseEnd_6743750] using wordTrace_append hprefix tailTrace_6743750
  have hstable : (prefixWord ++ tailWord_6743750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743750).length < 2 ^ (prefixWord ++ tailWord_6743750).sum := by decide
  have hdescent : baseEnd_6743750 < baseStart_6743750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743762 : List Nat := [3, 2, 2, 2, 2, 2, 2, 8]
def baseStart_6743762 : Nat := 118140960795 + 6743762 * 2 ^ 59
def prefixEnd_6743762 : Nat := 4983230072969 + 3 ^ 40 * 6743762 * 2
def baseEnd_6743762 : Nat := 128251530575035156809667

theorem tailTrace_6743762 : CollatzResearch.WordTrace tailWord_6743762 prefixEnd_6743762 128251530575035156809667 := by
  unfold tailWord_6743762
  simp only [CollatzResearch.WordTrace]
  refine ⟨61491301748627372924944385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163976804663006327799851693 61491301748627372924944385)
  ·
    refine ⟨46118476311470529693708289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61491301748627372924944385 46118476311470529693708289)
    ·
      refine ⟨34588857233602897270281217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46118476311470529693708289 34588857233602897270281217)
      ·
        refine ⟨25941642925202172952710913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34588857233602897270281217 25941642925202172952710913)
        ·
          refine ⟨19456232193901629714533185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25941642925202172952710913 19456232193901629714533185)
          ·
            refine ⟨14592174145426222285899889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19456232193901629714533185 14592174145426222285899889)
            ·
              refine ⟨10944130609069666714424917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14592174145426222285899889 10944130609069666714424917)
              ·
                refine ⟨128251530575035156809667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10944130609069666714424917 128251530575035156809667)
                ·
                  rfl

theorem cell23_6743762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 8].length) (baseStart_6743762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743762 prefixEnd_6743762 := by exact prefixLift 6743762
  have htrace : WordTrace (prefixWord ++ tailWord_6743762) baseStart_6743762 baseEnd_6743762 := by
    simpa [prefixWord, tailWord_6743762, baseEnd_6743762] using wordTrace_append hprefix tailTrace_6743762
  have hstable : (prefixWord ++ tailWord_6743762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743762).length < 2 ^ (prefixWord ++ tailWord_6743762).sum := by decide
  have hdescent : baseEnd_6743762 < baseStart_6743762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743773 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6743773 : Nat := 118140960795 + 6743773 * 2 ^ 59
def prefixEnd_6743773 : Nat := 4983230072969 + 3 ^ 40 * 6743773 * 2
def baseEnd_6743773 : Nat := 3462796973813148690823459

theorem tailTrace_6743773 : CollatzResearch.WordTrace tailWord_6743773 prefixEnd_6743773 3462796973813148690823459 := by
  unfold tailWord_6743773
  simp only [CollatzResearch.WordTrace]
  refine ⟨245965608197469640578427973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163977072131646427052285315 245965608197469640578427973)
  ·
    refine ⟨46118551537025557608455245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245965608197469640578427973 46118551537025557608455245)
    ·
      refine ⟨17294456826384584103170717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46118551537025557608455245 17294456826384584103170717)
      ·
        refine ⟨6485421309894219038689019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17294456826384584103170717 6485421309894219038689019)
        ·
          refine ⟨9728131964841328558033529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485421309894219038689019 9728131964841328558033529)
          ·
            refine ⟨7296098973630996418525147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9728131964841328558033529 7296098973630996418525147)
            ·
              refine ⟨10944148460446494627787721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296098973630996418525147 10944148460446494627787721)
              ·
                refine ⟨8208111345334870970840791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10944148460446494627787721 8208111345334870970840791)
                ·
                  refine ⟨12312167018002306456261187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208111345334870970840791 12312167018002306456261187)
                  ·
                    refine ⟨18468250527003459684391781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12312167018002306456261187 18468250527003459684391781)
                    ·
                      refine ⟨3462796973813148690823459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18468250527003459684391781 3462796973813148690823459)
                      ·
                        rfl

theorem cell23_6743773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6743773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743773 prefixEnd_6743773 := by exact prefixLift 6743773
  have htrace : WordTrace (prefixWord ++ tailWord_6743773) baseStart_6743773 baseEnd_6743773 := by
    simpa [prefixWord, tailWord_6743773, baseEnd_6743773] using wordTrace_append hprefix tailTrace_6743773
  have hstable : (prefixWord ++ tailWord_6743773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743773).length < 2 ^ (prefixWord ++ tailWord_6743773).sum := by decide
  have hdescent : baseEnd_6743773 < baseStart_6743773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743789 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_6743789 : Nat := 118140960795 + 6743789 * 2 ^ 59
def prefixEnd_6743789 : Nat := 4983230072969 + 3 ^ 40 * 6743789 * 2
def baseEnd_6743789 : Nat := 3462805189503620628223385

theorem tailTrace_6743789 : CollatzResearch.WordTrace tailWord_6743789 prefixEnd_6743789 3462805189503620628223385 := by
  unfold tailWord_6743789
  simp only [CollatzResearch.WordTrace]
  refine ⟨245966191765411675311010421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163977461176941116874006947 245966191765411675311010421)
  ·
    refine ⟨23059330478007344560407227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245966191765411675311010421 23059330478007344560407227)
    ·
      refine ⟨34588995717011016840610841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23059330478007344560407227 34588995717011016840610841)
      ·
        refine ⟨25941746787758262630458131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34588995717011016840610841 25941746787758262630458131)
        ·
          refine ⟨38912620181637393945687197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25941746787758262630458131 38912620181637393945687197)
          ·
            refine ⟨14592232568114022729632699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38912620181637393945687197 14592232568114022729632699)
            ·
              refine ⟨21888348852171034094449049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592232568114022729632699 21888348852171034094449049)
              ·
                refine ⟨16416261639128275570836787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21888348852171034094449049 16416261639128275570836787)
                ·
                  refine ⟨24624392458692413356255181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16416261639128275570836787 24624392458692413356255181)
                  ·
                    refine ⟨9234147172009655008595693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24624392458692413356255181 9234147172009655008595693)
                    ·
                      refine ⟨3462805189503620628223385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234147172009655008595693 3462805189503620628223385)
                      ·
                        rfl

theorem cell23_6743789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_6743789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743789 prefixEnd_6743789 := by exact prefixLift 6743789
  have htrace : WordTrace (prefixWord ++ tailWord_6743789) baseStart_6743789 baseEnd_6743789 := by
    simpa [prefixWord, tailWord_6743789, baseEnd_6743789] using wordTrace_append hprefix tailTrace_6743789
  have hstable : (prefixWord ++ tailWord_6743789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743789).length < 2 ^ (prefixWord ++ tailWord_6743789).sum := by decide
  have hdescent : baseEnd_6743789 < baseStart_6743789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743799 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 1, 3, 2]
def baseStart_6743799 : Nat := 118140960795 + 6743799 * 2 ^ 59
def prefixEnd_6743799 : Nat := 4983230072969 + 3 ^ 40 * 6743799 * 2
def baseEnd_6743799 : Nat := 3462810324310165589098339

theorem tailTrace_6743799 : CollatzResearch.WordTrace tailWord_6743799 prefixEnd_6743799 3462810324310165589098339 := by
  unfold tailWord_6743799
  simp only [CollatzResearch.WordTrace]
  refine ⟨245966556495375447018874451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163977704330250298012582967 245966556495375447018874451)
  ·
    refine ⟨368949834743063170528311677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245966556495375447018874451 368949834743063170528311677)
    ·
      refine ⟨138356188028648688948116879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368949834743063170528311677 138356188028648688948116879)
      ·
        refine ⟨207534282042973033422175319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138356188028648688948116879 207534282042973033422175319)
        ·
          refine ⟨311301423064459550133262979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207534282042973033422175319 311301423064459550133262979)
          ·
            refine ⟨466952134596689325199894469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311301423064459550133262979 466952134596689325199894469)
            ·
              refine ⟨87553525236879248474980213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466952134596689325199894469 87553525236879248474980213)
              ·
                refine ⟨8208142990957429544529395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87553525236879248474980213 8208142990957429544529395)
                ·
                  refine ⟨12312214486436144316794093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208142990957429544529395 12312214486436144316794093)
                  ·
                    refine ⟨4617080432413554118797785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12312214486436144316794093 4617080432413554118797785)
                    ·
                      refine ⟨3462810324310165589098339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617080432413554118797785 3462810324310165589098339)
                      ·
                        rfl

theorem cell23_6743799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_6743799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743799 prefixEnd_6743799 := by exact prefixLift 6743799
  have htrace : WordTrace (prefixWord ++ tailWord_6743799) baseStart_6743799 baseEnd_6743799 := by
    simpa [prefixWord, tailWord_6743799, baseEnd_6743799] using wordTrace_append hprefix tailTrace_6743799
  have hstable : (prefixWord ++ tailWord_6743799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743799).length < 2 ^ (prefixWord ++ tailWord_6743799).sum := by decide
  have hdescent : baseEnd_6743799 < baseStart_6743799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743812 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6743812 : Nat := 118140960795 + 6743812 * 2 ^ 59
def prefixEnd_6743812 : Nat := 4983230072969 + 3 ^ 40 * 6743812 * 2
def baseEnd_6743812 : Nat := 3462816999558674038235779

theorem tailTrace_6743812 : CollatzResearch.WordTrace tailWord_6743812 prefixEnd_6743812 3462816999558674038235779 := by
  unfold tailWord_6743812
  simp only [CollatzResearch.WordTrace]
  refine ⟨122983515322164175119548845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163978020429552233492731793 122983515322164175119548845)
  ·
    refine ⟨46118818245811565669830817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122983515322164175119548845 46118818245811565669830817)
    ·
      refine ⟨34589113684358674252373113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46118818245811565669830817 34589113684358674252373113)
      ·
        refine ⟨25941835263269005689279835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34589113684358674252373113 25941835263269005689279835)
        ·
          refine ⟨38912752894903508533919753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25941835263269005689279835 38912752894903508533919753)
          ·
            refine ⟨29184564671177631400439815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38912752894903508533919753 29184564671177631400439815)
            ·
              refine ⟨43776847006766447100659723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29184564671177631400439815 43776847006766447100659723)
              ·
                refine ⟨65665270510149670650989585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43776847006766447100659723 65665270510149670650989585)
                ·
                  refine ⟨49248952882612252988242189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65665270510149670650989585 49248952882612252988242189)
                  ·
                    refine ⟨18468357330979594870590821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49248952882612252988242189 18468357330979594870590821)
                    ·
                      refine ⟨3462816999558674038235779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18468357330979594870590821 3462816999558674038235779)
                      ·
                        rfl

theorem cell23_6743812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6743812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743812 prefixEnd_6743812 := by exact prefixLift 6743812
  have htrace : WordTrace (prefixWord ++ tailWord_6743812) baseStart_6743812 baseEnd_6743812 := by
    simpa [prefixWord, tailWord_6743812, baseEnd_6743812] using wordTrace_append hprefix tailTrace_6743812
  have hstable : (prefixWord ++ tailWord_6743812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743812).length < 2 ^ (prefixWord ++ tailWord_6743812).sum := by decide
  have hdescent : baseEnd_6743812 < baseStart_6743812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743829 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_6743829 : Nat := 118140960795 + 6743829 * 2 ^ 59
def prefixEnd_6743829 : Nat := 4983230072969 + 3 ^ 40 * 6743829 * 2
def baseEnd_6743829 : Nat := 3462825728729800471723201

theorem tailTrace_6743829 : CollatzResearch.WordTrace tailWord_6743829 prefixEnd_6743829 3462825728729800471723201 := by
  unfold tailWord_6743829
  simp only [CollatzResearch.WordTrace]
  refine ⟨245967650685266762142466541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163978433790177841428311027 245967650685266762142466541)
  ·
    refine ⟨92237869006975035803424953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245967650685266762142466541 92237869006975035803424953)
    ·
      refine ⟨69178401755231276852568715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92237869006975035803424953 69178401755231276852568715)
      ·
        refine ⟨103767602632846915278853073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69178401755231276852568715 103767602632846915278853073)
        ·
          refine ⟨77825701974635186459139805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103767602632846915278853073 77825701974635186459139805)
          ·
            refine ⟨29184638240488194922177427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77825701974635186459139805 29184638240488194922177427)
            ·
              refine ⟨43776957360732292383266141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29184638240488194922177427 43776957360732292383266141)
              ·
                refine ⟨16416359010274609643724803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43776957360732292383266141 16416359010274609643724803)
                ·
                  refine ⟨24624538515411914465587205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16416359010274609643724803 24624538515411914465587205)
                  ·
                    refine ⟨4617100971639733962297601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24624538515411914465587205 4617100971639733962297601)
                    ·
                      refine ⟨3462825728729800471723201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617100971639733962297601 3462825728729800471723201)
                      ·
                        rfl

theorem cell23_6743829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_6743829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743829 prefixEnd_6743829 := by exact prefixLift 6743829
  have htrace : WordTrace (prefixWord ++ tailWord_6743829) baseStart_6743829 baseEnd_6743829 := by
    simpa [prefixWord, tailWord_6743829, baseEnd_6743829] using wordTrace_append hprefix tailTrace_6743829
  have hstable : (prefixWord ++ tailWord_6743829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743829).length < 2 ^ (prefixWord ++ tailWord_6743829).sum := by decide
  have hdescent : baseEnd_6743829 < baseStart_6743829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743835 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 7]
def baseStart_6743835 : Nat := 118140960795 + 6743835 * 2 ^ 59
def prefixEnd_6743835 : Nat := 4983230072969 + 3 ^ 40 * 6743835 * 2
def baseEnd_6743835 : Nat := 384758756623747494249797

theorem tailTrace_6743835 : CollatzResearch.WordTrace tailWord_6743835 prefixEnd_6743835 384758756623747494249797 := by
  unfold tailWord_6743835
  simp only [CollatzResearch.WordTrace]
  refine ⟨245967869523245025167184959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163978579682163350111456639 245967869523245025167184959)
  ·
    refine ⟨368951804284867537750777439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245967869523245025167184959 368951804284867537750777439)
    ·
      refine ⟨553427706427301306626166159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368951804284867537750777439 553427706427301306626166159)
      ·
        refine ⟨830141559640951959939249239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553427706427301306626166159 830141559640951959939249239)
        ·
          refine ⟨1245212339461427939908873859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830141559640951959939249239 1245212339461427939908873859)
          ·
            refine ⟨1867818509192141909863310789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245212339461427939908873859 1867818509192141909863310789)
            ·
              refine ⟨350215970473526608099370773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1867818509192141909863310789 350215970473526608099370773)
              ·
                refine ⟨16416373615946559754658005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 350215970473526608099370773 16416373615946559754658005)
                ·
                  refine ⟨384758756623747494249797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16416373615946559754658005 384758756623747494249797)
                  ·
                    rfl

theorem cell23_6743835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 7].length) (baseStart_6743835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743835 prefixEnd_6743835 := by exact prefixLift 6743835
  have htrace : WordTrace (prefixWord ++ tailWord_6743835) baseStart_6743835 baseEnd_6743835 := by
    simpa [prefixWord, tailWord_6743835, baseEnd_6743835] using wordTrace_append hprefix tailTrace_6743835
  have hstable : (prefixWord ++ tailWord_6743835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743835).length < 2 ^ (prefixWord ++ tailWord_6743835).sum := by decide
  have hdescent : baseEnd_6743835 < baseStart_6743835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743842 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_6743842 : Nat := 118140960795 + 6743842 * 2 ^ 59
def prefixEnd_6743842 : Nat := 4983230072969 + 3 ^ 40 * 6743842 * 2
def baseEnd_6743842 : Nat := 3462832403978308920860641

theorem tailTrace_6743842 : CollatzResearch.WordTrace tailWord_6743842 prefixEnd_6743842 3462832403978308920860641 := by
  unfold tailWord_6743842
  simp only [CollatzResearch.WordTrace]
  refine ⟨61492031208554916340672445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163978749889479776908459853 61492031208554916340672445)
  ·
    refine ⟨23059511703208093627752167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61492031208554916340672445 23059511703208093627752167)
    ·
      refine ⟨34589267554812140441628251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23059511703208093627752167 34589267554812140441628251)
      ·
        refine ⟨51883901332218210662442377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34589267554812140441628251 51883901332218210662442377)
        ·
          refine ⟨38912925999163657996831783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51883901332218210662442377 38912925999163657996831783)
          ·
            refine ⟨58369388998745486995247675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38912925999163657996831783 58369388998745486995247675)
            ·
              refine ⟨87554083498118230492871513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58369388998745486995247675 87554083498118230492871513)
              ·
                refine ⟨65665562623588672869653635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87554083498118230492871513 65665562623588672869653635)
                ·
                  refine ⟨98498343935383009304480453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65665562623588672869653635 98498343935383009304480453)
                  ·
                    refine ⟨18468439487884314244590085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98498343935383009304480453 18468439487884314244590085)
                    ·
                      refine ⟨3462832403978308920860641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18468439487884314244590085 3462832403978308920860641)
                      ·
                        rfl

theorem cell23_6743842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_6743842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743842 prefixEnd_6743842 := by exact prefixLift 6743842
  have htrace : WordTrace (prefixWord ++ tailWord_6743842) baseStart_6743842 baseEnd_6743842 := by
    simpa [prefixWord, tailWord_6743842, baseEnd_6743842] using wordTrace_append hprefix tailTrace_6743842
  have hstable : (prefixWord ++ tailWord_6743842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743842).length < 2 ^ (prefixWord ++ tailWord_6743842).sum := by decide
  have hdescent : baseEnd_6743842 < baseStart_6743842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743869 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 7]
def baseStart_6743869 : Nat := 118140960795 + 6743869 * 2 ^ 59
def prefixEnd_6743869 : Nat := 4983230072969 + 3 ^ 40 * 6743869 * 2
def baseEnd_6743869 : Nat := 384760696439553368358113

theorem tailTrace_6743869 : CollatzResearch.WordTrace tailWord_6743869 prefixEnd_6743869 384760696439553368358113 := by
  unfold tailWord_6743869
  simp only [CollatzResearch.WordTrace]
  refine ⟨245969109605121848973922661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163979406403414565982615107 245969109605121848973922661)
  ·
    refine ⟨46119208050960346682610499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245969109605121848973922661 46119208050960346682610499)
    ·
      refine ⟨69178812076440520023915749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46119208050960346682610499 69178812076440520023915749)
      ·
        refine ⟨12971027264332597504484203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69178812076440520023915749 12971027264332597504484203)
        ·
          refine ⟨19456540896498896256726305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12971027264332597504484203 19456540896498896256726305)
          ·
            refine ⟨14592405672374172192544729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19456540896498896256726305 14592405672374172192544729)
            ·
              refine ⟨10944304254280629144408547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14592405672374172192544729 10944304254280629144408547)
              ·
                refine ⟨16416456381420943716612821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10944304254280629144408547 16416456381420943716612821)
                ·
                  refine ⟨384760696439553368358113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16416456381420943716612821 384760696439553368358113)
                  ·
                    rfl

theorem cell23_6743869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_6743869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743869 prefixEnd_6743869 := by exact prefixLift 6743869
  have htrace : WordTrace (prefixWord ++ tailWord_6743869) baseStart_6743869 baseEnd_6743869 := by
    simpa [prefixWord, tailWord_6743869, baseEnd_6743869] using wordTrace_append hprefix tailTrace_6743869
  have hstable : (prefixWord ++ tailWord_6743869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743869).length < 2 ^ (prefixWord ++ tailWord_6743869).sum := by decide
  have hdescent : baseEnd_6743869 < baseStart_6743869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743926 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6743926 : Nat := 118140960795 + 6743926 * 2 ^ 59
def prefixEnd_6743926 : Nat := 4983230072969 + 3 ^ 40 * 6743926 * 2
def baseEnd_6743926 : Nat := 3462875536353286592210255

theorem tailTrace_6743926 : CollatzResearch.WordTrace tailWord_6743926 prefixEnd_6743926 3462875536353286592210255 := by
  unfold tailWord_6743926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15373199285369709231796727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163980792377276898472498421 15373199285369709231796727)
  ·
    refine ⟨23059798928054563847695091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15373199285369709231796727 23059798928054563847695091)
    ·
      refine ⟨34589698392081845771542637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23059798928054563847695091 34589698392081845771542637)
      ·
        refine ⟨12971136897030692164328489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34589698392081845771542637 12971136897030692164328489)
        ·
          refine ⟨9728352672773019123246367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12971136897030692164328489 9728352672773019123246367)
          ·
            refine ⟨14592529009159528684869551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728352672773019123246367 14592529009159528684869551)
            ·
              refine ⟨21888793513739293027304327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592529009159528684869551 21888793513739293027304327)
              ·
                refine ⟨32833190270608939540956491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21888793513739293027304327 32833190270608939540956491)
                ·
                  refine ⟨49249785405913409311434737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32833190270608939540956491 49249785405913409311434737)
                  ·
                    refine ⟨36937339054435056983576053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49249785405913409311434737 36937339054435056983576053)
                    ·
                      refine ⟨3462875536353286592210255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36937339054435056983576053 3462875536353286592210255)
                      ·
                        rfl

theorem cell23_6743926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6743926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743926 prefixEnd_6743926 := by exact prefixLift 6743926
  have htrace : WordTrace (prefixWord ++ tailWord_6743926) baseStart_6743926 baseEnd_6743926 := by
    simpa [prefixWord, tailWord_6743926, baseEnd_6743926] using wordTrace_append hprefix tailTrace_6743926
  have hstable : (prefixWord ++ tailWord_6743926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743926).length < 2 ^ (prefixWord ++ tailWord_6743926).sum := by decide
  have hdescent : baseEnd_6743926 < baseStart_6743926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743952 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3]
def baseStart_6743952 : Nat := 118140960795 + 6743952 * 2 ^ 59
def prefixEnd_6743952 : Nat := 4983230072969 + 3 ^ 40 * 6743952 * 2
def baseEnd_6743952 : Nat := 3462888886850303490485135

theorem tailTrace_6743952 : CollatzResearch.WordTrace tailWord_6743952 prefixEnd_6743952 3462888886850303490485135 := by
  unfold tailWord_6743952
  simp only [CollatzResearch.WordTrace]
  refine ⟨122986068431910577074597055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163981424575880769432796073 122986068431910577074597055)
  ·
    refine ⟨184479102647865865611895583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122986068431910577074597055 184479102647865865611895583)
    ·
      refine ⟨276718653971798798417843375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184479102647865865611895583 276718653971798798417843375)
      ·
        refine ⟨415077980957698197626765063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276718653971798798417843375 415077980957698197626765063)
        ·
          refine ⟨622616971436547296440147595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415077980957698197626765063 622616971436547296440147595)
          ·
            refine ⟨933925457154820944660221393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622616971436547296440147595 933925457154820944660221393)
            ·
              refine ⟨700444092866115708495166045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933925457154820944660221393 700444092866115708495166045)
              ·
                refine ⟨262666534824793390685687267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 700444092866115708495166045 262666534824793390685687267)
                ·
                  refine ⟨393999802237190086028530901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262666534824793390685687267 393999802237190086028530901)
                  ·
                    refine ⟨9234370364934142641293693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 393999802237190086028530901 9234370364934142641293693)
                    ·
                      refine ⟨3462888886850303490485135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234370364934142641293693 3462888886850303490485135)
                      ·
                        rfl

theorem cell23_6743952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_6743952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743952 prefixEnd_6743952 := by exact prefixLift 6743952
  have htrace : WordTrace (prefixWord ++ tailWord_6743952) baseStart_6743952 baseEnd_6743952 := by
    simpa [prefixWord, tailWord_6743952, baseEnd_6743952] using wordTrace_append hprefix tailTrace_6743952
  have hstable : (prefixWord ++ tailWord_6743952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743952).length < 2 ^ (prefixWord ++ tailWord_6743952).sum := by decide
  have hdescent : baseEnd_6743952 < baseStart_6743952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743956 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_6743956 : Nat := 118140960795 + 6743956 * 2 ^ 59
def prefixEnd_6743956 : Nat := 4983230072969 + 3 ^ 40 * 6743956 * 2
def baseEnd_6743956 : Nat := 3462890940772921474835117

theorem tailTrace_6743956 : CollatzResearch.WordTrace tailWord_6743956 prefixEnd_6743956 3462890940772921474835117 := by
  unfold tailWord_6743956
  simp only [CollatzResearch.WordTrace]
  refine ⟨122986141377903331416169861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163981521837204441888226481 122986141377903331416169861)
  ·
    refine ⟨23059901508356874640531849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122986141377903331416169861 23059901508356874640531849)
    ·
      refine ⟨17294926131267655980398887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23059901508356874640531849 17294926131267655980398887)
      ·
        refine ⟨25942389196901483970598331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17294926131267655980398887 25942389196901483970598331)
        ·
          refine ⟨38913583795352225955897497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25942389196901483970598331 38913583795352225955897497)
          ·
            refine ⟨29185187846514169466923123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38913583795352225955897497 29185187846514169466923123)
            ·
              refine ⟨43777781769771254200384685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29185187846514169466923123 43777781769771254200384685)
              ·
                refine ⟨16416668163664220325144257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43777781769771254200384685 16416668163664220325144257)
                ·
                  refine ⟨12312501122748165243858193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16416668163664220325144257 12312501122748165243858193)
                  ·
                    refine ⟨9234375842061123932893645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12312501122748165243858193 9234375842061123932893645)
                    ·
                      refine ⟨3462890940772921474835117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234375842061123932893645 3462890940772921474835117)
                      ·
                        rfl

theorem cell23_6743956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_6743956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743956 prefixEnd_6743956 := by exact prefixLift 6743956
  have htrace : WordTrace (prefixWord ++ tailWord_6743956) baseStart_6743956 baseEnd_6743956 := by
    simpa [prefixWord, tailWord_6743956, baseEnd_6743956] using wordTrace_append hprefix tailTrace_6743956
  have hstable : (prefixWord ++ tailWord_6743956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743956).length < 2 ^ (prefixWord ++ tailWord_6743956).sum := by decide
  have hdescent : baseEnd_6743956 < baseStart_6743956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6743989 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_6743989 : Nat := 118140960795 + 6743989 * 2 ^ 59
def prefixEnd_6743989 : Nat := 4983230072969 + 3 ^ 40 * 6743989 * 2
def baseEnd_6743989 : Nat := 1154302628544839948574155

theorem tailTrace_6743989 : CollatzResearch.WordTrace tailWord_6743989 prefixEnd_6743989 1154302628544839948574155 := by
  unfold tailWord_6743989
  simp only [CollatzResearch.WordTrace]
  refine ⟨245973486364687109468291021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163982324243124739645527347 245973486364687109468291021)
  ·
    refine ⟨92240057386757666050609133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245973486364687109468291021 92240057386757666050609133)
    ·
      refine ⟨34590021520034124768978425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92240057386757666050609133 34590021520034124768978425)
      ·
        refine ⟨25942516140025593576733819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34590021520034124768978425 25942516140025593576733819)
        ·
          refine ⟨38913774210038390365100729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25942516140025593576733819 38913774210038390365100729)
          ·
            refine ⟨29185330657528792773825547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38913774210038390365100729 29185330657528792773825547)
            ·
              refine ⟨43777995986293189160738321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29185330657528792773825547 43777995986293189160738321)
              ·
                refine ⟨32833496989719891870553741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43777995986293189160738321 32833496989719891870553741)
                ·
                  refine ⟨12312561371144959451457653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32833496989719891870553741 12312561371144959451457653)
                  ·
                    refine ⟨1154302628544839948574155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12312561371144959451457653 1154302628544839948574155)
                    ·
                      rfl

theorem cell23_6743989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_6743989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6743989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6743989 prefixEnd_6743989 := by exact prefixLift 6743989
  have htrace : WordTrace (prefixWord ++ tailWord_6743989) baseStart_6743989 baseEnd_6743989 := by
    simpa [prefixWord, tailWord_6743989, baseEnd_6743989] using wordTrace_append hprefix tailTrace_6743989
  have hstable : (prefixWord ++ tailWord_6743989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6743989).length < 2 ^ (prefixWord ++ tailWord_6743989).sum := by decide
  have hdescent : baseEnd_6743989 < baseStart_6743989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6743989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744009 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 2, 6, 2]
def baseStart_6744009 : Nat := 118140960795 + 6744009 * 2 ^ 59
def prefixEnd_6744009 : Nat := 4983230072969 + 3 ^ 40 * 6744009 * 2
def baseEnd_6744009 : Nat := 3462918155247609767472373

theorem tailTrace_6744009 : CollatzResearch.WordTrace tailWord_6744009 prefixEnd_6744009 3462918155247609767472373 := by
  unfold tailWord_6744009
  simp only [CollatzResearch.WordTrace]
  refine ⟨245974215824614652884019081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163982810549743101922679387 245974215824614652884019081)
  ·
    refine ⟨184480661868460989663014311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245974215824614652884019081 184480661868460989663014311)
    ·
      refine ⟨276720992802691484494521467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184480661868460989663014311 276720992802691484494521467)
      ·
        refine ⟨415081489204037226741782201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276720992802691484494521467 415081489204037226741782201)
        ·
          refine ⟨311311116903027920056336651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415081489204037226741782201 311311116903027920056336651)
          ·
            refine ⟨466966675354541880084504977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311311116903027920056336651 466966675354541880084504977)
            ·
              refine ⟨350225006515906410063378733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466966675354541880084504977 350225006515906410063378733)
              ·
                refine ⟨131334377443464903773767025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350225006515906410063378733 131334377443464903773767025)
                ·
                  refine ⟨98500783082598677830325269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131334377443464903773767025 98500783082598677830325269)
                  ·
                    refine ⟨4617224206996813023296497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98500783082598677830325269 4617224206996813023296497)
                    ·
                      refine ⟨3462918155247609767472373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617224206996813023296497 3462918155247609767472373)
                      ·
                        rfl

theorem cell23_6744009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 6, 2].length) (baseStart_6744009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744009 prefixEnd_6744009 := by exact prefixLift 6744009
  have htrace : WordTrace (prefixWord ++ tailWord_6744009) baseStart_6744009 baseEnd_6744009 := by
    simpa [prefixWord, tailWord_6744009, baseEnd_6744009] using wordTrace_append hprefix tailTrace_6744009
  have hstable : (prefixWord ++ tailWord_6744009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744009).length < 2 ^ (prefixWord ++ tailWord_6744009).sum := by decide
  have hdescent : baseEnd_6744009 < baseStart_6744009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744020 : List Nat := [2, 4, 1, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_6744020 : Nat := 118140960795 + 6744020 * 2 ^ 59
def prefixEnd_6744020 : Nat := 4983230072969 + 3 ^ 40 * 6744020 * 2
def baseEnd_6744020 : Nat := 3462923803534809224434823

theorem tailTrace_6744020 : CollatzResearch.WordTrace tailWord_6744020 prefixEnd_6744020 3462923803534809224434823 := by
  unfold tailWord_6744020
  simp only [CollatzResearch.WordTrace]
  refine ⟨122987308513787400881334757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163983078018383201175113009 122987308513787400881334757)
  ·
    refine ⟨23060120346335137665250267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122987308513787400881334757 23060120346335137665250267)
    ·
      refine ⟨34590180519502706497875401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23060120346335137665250267 34590180519502706497875401)
      ·
        refine ⟨25942635389627029873406551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34590180519502706497875401 25942635389627029873406551)
        ·
          refine ⟨38913953084440544810109827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25942635389627029873406551 38913953084440544810109827)
          ·
            refine ⟨58370929626660817215164741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38913953084440544810109827 58370929626660817215164741)
            ·
              refine ⟨10944549304998903227843389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58370929626660817215164741 10944549304998903227843389)
              ·
                refine ⟨4104205989374588710441271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10944549304998903227843389 4104205989374588710441271)
                ·
                  refine ⟨6156308984061883065661907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104205989374588710441271 6156308984061883065661907)
                  ·
                    refine ⟨9234463476092824598492861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156308984061883065661907 9234463476092824598492861)
                    ·
                      refine ⟨3462923803534809224434823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234463476092824598492861 3462923803534809224434823)
                      ·
                        rfl

theorem cell23_6744020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_6744020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744020 prefixEnd_6744020 := by exact prefixLift 6744020
  have htrace : WordTrace (prefixWord ++ tailWord_6744020) baseStart_6744020 baseEnd_6744020 := by
    simpa [prefixWord, tailWord_6744020, baseEnd_6744020] using wordTrace_append hprefix tailTrace_6744020
  have hstable : (prefixWord ++ tailWord_6744020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744020).length < 2 ^ (prefixWord ++ tailWord_6744020).sum := by decide
  have hdescent : baseEnd_6744020 < baseStart_6744020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744046 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_6744046 : Nat := 118140960795 + 6744046 * 2 ^ 59
def prefixEnd_6744046 : Nat := 4983230072969 + 3 ^ 40 * 6744046 * 2
def baseEnd_6744046 : Nat := 3462937154031826122709703

theorem tailTrace_6744046 : CollatzResearch.WordTrace tailWord_6744046 prefixEnd_6744046 3462937154031826122709703 := by
  unfold tailWord_6744046
  simp only [CollatzResearch.WordTrace]
  refine ⟨30746945665685076025389499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163983710216987072135410661 30746945665685076025389499)
  ·
    refine ⟨46120418498527614038084249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30746945665685076025389499 46120418498527614038084249)
    ·
      refine ⟨34590313873895710528563187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46120418498527614038084249 34590313873895710528563187)
      ·
        refine ⟨51885470810843565792844781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34590313873895710528563187 51885470810843565792844781)
        ·
          refine ⟨19457051554066337172316793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51885470810843565792844781 19457051554066337172316793)
          ·
            refine ⟨14592788665549752879237595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19457051554066337172316793 14592788665549752879237595)
            ·
              refine ⟨21889182998324629318856393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592788665549752879237595 21889182998324629318856393)
              ·
                refine ⟨16416887248743471989142295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21889182998324629318856393 16416887248743471989142295)
                ·
                  refine ⟨24625330873115207983713443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16416887248743471989142295 24625330873115207983713443)
                  ·
                    refine ⟨36937996309672811975570165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24625330873115207983713443 36937996309672811975570165)
                    ·
                      refine ⟨3462937154031826122709703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36937996309672811975570165 3462937154031826122709703)
                      ·
                        rfl

theorem cell23_6744046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_6744046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744046 prefixEnd_6744046 := by exact prefixLift 6744046
  have htrace : WordTrace (prefixWord ++ tailWord_6744046) baseStart_6744046 baseEnd_6744046 := by
    simpa [prefixWord, tailWord_6744046, baseEnd_6744046] using wordTrace_append hprefix tailTrace_6744046
  have hstable : (prefixWord ++ tailWord_6744046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744046).length < 2 ^ (prefixWord ++ tailWord_6744046).sum := by decide
  have hdescent : baseEnd_6744046 < baseStart_6744046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744076 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_6744076 : Nat := 118140960795 + 6744076 * 2 ^ 59
def prefixEnd_6744076 : Nat := 4983230072969 + 3 ^ 40 * 6744076 * 2
def baseEnd_6744076 : Nat := 3462952558451461005334565

theorem tailTrace_6744076 : CollatzResearch.WordTrace tailWord_6744076 prefixEnd_6744076 3462952558451461005334565 := by
  unfold tailWord_6744076
  simp only [CollatzResearch.WordTrace]
  refine ⟨122988329757685961663354041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163984439676914615551138721 122988329757685961663354041)
  ·
    refine ⟨92241247318264471247515531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122988329757685961663354041 92241247318264471247515531)
    ·
      refine ⟨138361870977396706871273297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92241247318264471247515531 138361870977396706871273297)
      ·
        refine ⟨103771403233047530153454973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138361870977396706871273297 103771403233047530153454973)
        ·
          refine ⟨38914276212392823807545615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103771403233047530153454973 38914276212392823807545615)
          ·
            refine ⟨58371414318589235711318423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38914276212392823807545615 58371414318589235711318423)
            ·
              refine ⟨87557121477883853566977635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58371414318589235711318423 87557121477883853566977635)
              ·
                refine ⟨131335682216825780350466453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87557121477883853566977635 131335682216825780350466453)
                ·
                  refine ⟨6156360103913708453928115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131335682216825780350466453 6156360103913708453928115)
                  ·
                    refine ⟨9234540155870562680892173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156360103913708453928115 9234540155870562680892173)
                    ·
                      refine ⟨3462952558451461005334565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234540155870562680892173 3462952558451461005334565)
                      ·
                        rfl

theorem cell23_6744076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_6744076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744076 prefixEnd_6744076 := by exact prefixLift 6744076
  have htrace : WordTrace (prefixWord ++ tailWord_6744076) baseStart_6744076 baseEnd_6744076 := by
    simpa [prefixWord, tailWord_6744076, baseEnd_6744076] using wordTrace_append hprefix tailTrace_6744076
  have hstable : (prefixWord ++ tailWord_6744076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744076).length < 2 ^ (prefixWord ++ tailWord_6744076).sum := by decide
  have hdescent : baseEnd_6744076 < baseStart_6744076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744093 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_6744093 : Nat := 118140960795 + 6744093 * 2 ^ 59
def prefixEnd_6744093 : Nat := 4983230072969 + 3 ^ 40 * 6744093 * 2
def baseEnd_6744093 : Nat := 3462961287622587438821987

theorem tailTrace_6744093 : CollatzResearch.WordTrace tailWord_6744093 prefixEnd_6744093 3462961287622587438821987 := by
  unfold tailWord_6744093
  simp only [CollatzResearch.WordTrace]
  refine ⟨245977279556310335230076933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163984853037540223486717955 245977279556310335230076933)
  ·
    refine ⟨46120739916808187855639425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245977279556310335230076933 46120739916808187855639425)
    ·
      refine ⟨34590554937606140891729569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46120739916808187855639425 34590554937606140891729569)
      ·
        refine ⟨25942916203204605668797177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34590554937606140891729569 25942916203204605668797177)
        ·
          refine ⟨19457187152403454251597883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25942916203204605668797177 19457187152403454251597883)
          ·
            refine ⟨29185780728605181377396825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19457187152403454251597883 29185780728605181377396825)
            ·
              refine ⟨21889335546453886033047619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29185780728605181377396825 21889335546453886033047619)
              ·
                refine ⟨32834003319680829049571429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21889335546453886033047619 32834003319680829049571429)
                ·
                  refine ⟨6156375622440155446794643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32834003319680829049571429 6156375622440155446794643)
                  ·
                    refine ⟨9234563433660233170191965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156375622440155446794643 9234563433660233170191965)
                    ·
                      refine ⟨3462961287622587438821987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234563433660233170191965 3462961287622587438821987)
                      ·
                        rfl

theorem cell23_6744093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_6744093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744093 prefixEnd_6744093 := by exact prefixLift 6744093
  have htrace : WordTrace (prefixWord ++ tailWord_6744093) baseStart_6744093 baseEnd_6744093 := by
    simpa [prefixWord, tailWord_6744093, baseEnd_6744093] using wordTrace_append hprefix tailTrace_6744093
  have hstable : (prefixWord ++ tailWord_6744093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744093).length < 2 ^ (prefixWord ++ tailWord_6744093).sum := by decide
  have hdescent : baseEnd_6744093 < baseStart_6744093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744099 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4]
def baseStart_6744099 : Nat := 118140960795 + 6744099 * 2 ^ 59
def prefixEnd_6744099 : Nat := 4983230072969 + 3 ^ 40 * 6744099 * 2
def baseEnd_6744099 : Nat := 3462964368506514415346959

theorem tailTrace_6744099 : CollatzResearch.WordTrace tailWord_6744099 prefixEnd_6744099 3462964368506514415346959 := by
  unfold tailWord_6744099
  simp only [CollatzResearch.WordTrace]
  refine ⟨245977498394288598254795351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163984998929525732169863567 245977498394288598254795351)
  ·
    refine ⟨368966247591432897382193027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245977498394288598254795351 368966247591432897382193027)
    ·
      refine ⟨553449371387149346073289541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368966247591432897382193027 553449371387149346073289541)
      ·
        refine ⟨103771757135090502388741789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 553449371387149346073289541 103771757135090502388741789)
        ·
          refine ⟨38914408925658938395778171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103771757135090502388741789 38914408925658938395778171)
          ·
            refine ⟨58371613388488407593667257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38914408925658938395778171 58371613388488407593667257)
            ·
              refine ⟨43778710041366305695250443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58371613388488407593667257 43778710041366305695250443)
              ·
                refine ⟨65668065062049458542875665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43778710041366305695250443 65668065062049458542875665)
                ·
                  refine ⟨49251048796537093907156749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65668065062049458542875665 49251048796537093907156749)
                  ·
                    refine ⟨18469143298701410215183781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49251048796537093907156749 18469143298701410215183781)
                    ·
                      refine ⟨3462964368506514415346959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18469143298701410215183781 3462964368506514415346959)
                      ·
                        rfl

theorem cell23_6744099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_6744099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744099 prefixEnd_6744099 := by exact prefixLift 6744099
  have htrace : WordTrace (prefixWord ++ tailWord_6744099) baseStart_6744099 baseEnd_6744099 := by
    simpa [prefixWord, tailWord_6744099, baseEnd_6744099] using wordTrace_append hprefix tailTrace_6744099
  have hstable : (prefixWord ++ tailWord_6744099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744099).length < 2 ^ (prefixWord ++ tailWord_6744099).sum := by decide
  have hdescent : baseEnd_6744099 < baseStart_6744099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744104 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6744104 : Nat := 118140960795 + 6744104 * 2 ^ 59
def prefixEnd_6744104 : Nat := 4983230072969 + 3 ^ 40 * 6744104 * 2
def baseEnd_6744104 : Nat := 1154322311969928965261479

theorem tailTrace_6744104 : CollatzResearch.WordTrace tailWord_6744104 prefixEnd_6744104 1154322311969928965261479 := by
  unfold tailWord_6744104
  simp only [CollatzResearch.WordTrace]
  refine ⟨122988840379635242054363683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163985120506180322739151577 122988840379635242054363683)
  ·
    refine ⟨184483260569452863081545525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122988840379635242054363683 184483260569452863081545525)
    ·
      refine ⟨17295305678386205913894893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184483260569452863081545525 17295305678386205913894893)
      ·
        refine ⟨6485739629394827217710585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17295305678386205913894893 6485739629394827217710585)
        ·
          refine ⟨4864304722046120413282939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6485739629394827217710585 4864304722046120413282939)
          ·
            refine ⟨7296457083069180619924409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864304722046120413282939 7296457083069180619924409)
            ·
              refine ⟨5472342812301885464943307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7296457083069180619924409 5472342812301885464943307)
              ·
                refine ⟨8208514218452828197414961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472342812301885464943307 8208514218452828197414961)
                ·
                  refine ⟨6156385663839621148061221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8208514218452828197414961 6156385663839621148061221)
                  ·
                    refine ⟨1154322311969928965261479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6156385663839621148061221 1154322311969928965261479)
                    ·
                      rfl

theorem cell23_6744104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6744104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744104 prefixEnd_6744104 := by exact prefixLift 6744104
  have htrace : WordTrace (prefixWord ++ tailWord_6744104) baseStart_6744104 baseEnd_6744104 := by
    simpa [prefixWord, tailWord_6744104, baseEnd_6744104] using wordTrace_append hprefix tailTrace_6744104
  have hstable : (prefixWord ++ tailWord_6744104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744104).length < 2 ^ (prefixWord ++ tailWord_6744104).sum := by decide
  have hdescent : baseEnd_6744104 < baseStart_6744104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744110 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_6744110 : Nat := 118140960795 + 6744110 * 2 ^ 59
def prefixEnd_6744110 : Nat := 4983230072969 + 3 ^ 40 * 6744110 * 2
def baseEnd_6744110 : Nat := 3462970016793713872309409

theorem tailTrace_6744110 : CollatzResearch.WordTrace tailWord_6744110 prefixEnd_6744110 3462970016793713872309409 := by
  unfold tailWord_6744110
  simp only [CollatzResearch.WordTrace]
  refine ⟨30747237449656093391680723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163985266398165831422297189 30747237449656093391680723)
  ·
    refine ⟨46120856174484140087521085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30747237449656093391680723 46120856174484140087521085)
    ·
      refine ⟨17295321065431552532820407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46120856174484140087521085 17295321065431552532820407)
      ·
        refine ⟨25942981598147328799230611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17295321065431552532820407 25942981598147328799230611)
        ·
          refine ⟨38914472397220993198845917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25942981598147328799230611 38914472397220993198845917)
          ·
            refine ⟨14592927148957872449567219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38914472397220993198845917 14592927148957872449567219)
            ·
              refine ⟨21889390723436808674350829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592927148957872449567219 21889390723436808674350829)
              ·
                refine ⟨8208521521288803252881561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21889390723436808674350829 8208521521288803252881561)
                ·
                  refine ⟨6156391140966602439661171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8208521521288803252881561 6156391140966602439661171)
                  ·
                    refine ⟨9234586711449903659491757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156391140966602439661171 9234586711449903659491757)
                    ·
                      refine ⟨3462970016793713872309409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234586711449903659491757 3462970016793713872309409)
                      ·
                        rfl

theorem cell23_6744110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_6744110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744110 prefixEnd_6744110 := by exact prefixLift 6744110
  have htrace : WordTrace (prefixWord ++ tailWord_6744110) baseStart_6744110 baseEnd_6744110 := by
    simpa [prefixWord, tailWord_6744110, baseEnd_6744110] using wordTrace_append hprefix tailTrace_6744110
  have hstable : (prefixWord ++ tailWord_6744110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744110).length < 2 ^ (prefixWord ++ tailWord_6744110).sum := by decide
  have hdescent : baseEnd_6744110 < baseStart_6744110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744119 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_6744119 : Nat := 118140960795 + 6744119 * 2 ^ 59
def prefixEnd_6744119 : Nat := 4983230072969 + 3 ^ 40 * 6744119 * 2
def baseEnd_6744119 : Nat := 3462974638119604337096867

theorem tailTrace_6744119 : CollatzResearch.WordTrace tailWord_6744119 prefixEnd_6744119 3462974638119604337096867 := by
  unfold tailWord_6744119
  simp only [CollatzResearch.WordTrace]
  refine ⟨245978227854216141670523411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163985485236144094447015607 245978227854216141670523411)
  ·
    refine ⟨368967341781324212505785117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245978227854216141670523411 368967341781324212505785117)
    ·
      refine ⟨138362753167996579689669419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368967341781324212505785117 138362753167996579689669419)
      ·
        refine ⟨207544129751994869534504129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138362753167996579689669419 207544129751994869534504129)
        ·
          refine ⟨155658097313996152150878097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207544129751994869534504129 155658097313996152150878097)
          ·
            refine ⟨116743572985497114113158573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155658097313996152150878097 116743572985497114113158573)
            ·
              refine ⟨43778839869561417792434465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116743572985497114113158573 43778839869561417792434465)
              ·
                refine ⟨32834129902171063344325849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43778839869561417792434465 32834129902171063344325849)
                ·
                  refine ⟨24625597426628297508244387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32834129902171063344325849 24625597426628297508244387)
                  ·
                    refine ⟨36938396139942446262366581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24625597426628297508244387 36938396139942446262366581)
                    ·
                      refine ⟨3462974638119604337096867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36938396139942446262366581 3462974638119604337096867)
                      ·
                        rfl

theorem cell23_6744119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_6744119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744119 prefixEnd_6744119 := by exact prefixLift 6744119
  have htrace : WordTrace (prefixWord ++ tailWord_6744119) baseStart_6744119 baseEnd_6744119 := by
    simpa [prefixWord, tailWord_6744119, baseEnd_6744119] using wordTrace_append hprefix tailTrace_6744119
  have hstable : (prefixWord ++ tailWord_6744119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744119).length < 2 ^ (prefixWord ++ tailWord_6744119).sum := by decide
  have hdescent : baseEnd_6744119 < baseStart_6744119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744169 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 1, 7]
def baseStart_6744169 : Nat := 118140960795 + 6744169 * 2 ^ 59
def prefixEnd_6744169 : Nat := 4983230072969 + 3 ^ 40 * 6744169 * 2
def baseEnd_6744169 : Nat := 1154333437384109713823879

theorem tailTrace_6744169 : CollatzResearch.WordTrace tailWord_6744169 prefixEnd_6744169 1154333437384109713823879 := by
  unfold tailWord_6744169
  simp only [CollatzResearch.WordTrace]
  refine ⟨245980051504035000209843561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163986701002690000139895707 245980051504035000209843561)
  ·
    refine ⟨184485038628026250157382671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245980051504035000209843561 184485038628026250157382671)
    ·
      refine ⟨276727557942039375236074007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184485038628026250157382671 276727557942039375236074007)
      ·
        refine ⟨415091336913059062854111011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276727557942039375236074007 415091336913059062854111011)
        ·
          refine ⟨622637005369588594281166517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415091336913059062854111011 622637005369588594281166517)
          ·
            refine ⟨58372219253398930713859361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 622637005369588594281166517 58372219253398930713859361)
            ·
              refine ⟨43779164440049198035394521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58372219253398930713859361 43779164440049198035394521)
              ·
                refine ⟨32834373330036898526545891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43779164440049198035394521 32834373330036898526545891)
                ·
                  refine ⟨49251559995055347789818837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32834373330036898526545891 49251559995055347789818837)
                  ·
                    refine ⟨1154333437384109713823879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49251559995055347789818837 1154333437384109713823879)
                    ·
                      rfl

theorem cell23_6744169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_6744169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744169 prefixEnd_6744169 := by exact prefixLift 6744169
  have htrace : WordTrace (prefixWord ++ tailWord_6744169) baseStart_6744169 baseEnd_6744169 := by
    simpa [prefixWord, tailWord_6744169, baseEnd_6744169] using wordTrace_append hprefix tailTrace_6744169
  have hstable : (prefixWord ++ tailWord_6744169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744169).length < 2 ^ (prefixWord ++ tailWord_6744169).sum := by decide
  have hdescent : baseEnd_6744169 < baseStart_6744169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744219 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6]
def baseStart_6744219 : Nat := 118140960795 + 6744219 * 2 ^ 59
def prefixEnd_6744219 : Nat := 4983230072969 + 3 ^ 40 * 6744219 * 2
def baseEnd_6744219 : Nat := 3463025986185053945846407

theorem tailTrace_6744219 : CollatzResearch.WordTrace tailWord_6744219 prefixEnd_6744219 3463025986185053945846407 := by
  unfold tailWord_6744219
  simp only [CollatzResearch.WordTrace]
  refine ⟨245981875153853858749163711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163987916769235905832775807 245981875153853858749163711)
  ·
    refine ⟨368972812730780788123745567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245981875153853858749163711 368972812730780788123745567)
    ·
      refine ⟨553459219096171182185618351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368972812730780788123745567 553459219096171182185618351)
      ·
        refine ⟨830188828644256773278427527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553459219096171182185618351 830188828644256773278427527)
        ·
          refine ⟨1245283242966385159917641291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830188828644256773278427527 1245283242966385159917641291)
          ·
            refine ⟨1867924864449577739876461937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245283242966385159917641291 1867924864449577739876461937)
            ·
              refine ⟨1400943648337183304907346453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867924864449577739876461937 1400943648337183304907346453)
              ·
                refine ⟨65669233515805467417531865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1400943648337183304907346453 65669233515805467417531865)
                ·
                  refine ⟨49251925136854100563148899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65669233515805467417531865 49251925136854100563148899)
                  ·
                    refine ⟨73877887705281150844723349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49251925136854100563148899 73877887705281150844723349)
                    ·
                      refine ⟨3463025986185053945846407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73877887705281150844723349 3463025986185053945846407)
                      ·
                        rfl

theorem cell23_6744219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_6744219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744219 prefixEnd_6744219 := by exact prefixLift 6744219
  have htrace : WordTrace (prefixWord ++ tailWord_6744219) baseStart_6744219 baseEnd_6744219 := by
    simpa [prefixWord, tailWord_6744219, baseEnd_6744219] using wordTrace_append hprefix tailTrace_6744219
  have hstable : (prefixWord ++ tailWord_6744219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744219).length < 2 ^ (prefixWord ++ tailWord_6744219).sum := by decide
  have hdescent : baseEnd_6744219 < baseStart_6744219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744250 : List Nat := [3, 1, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_6744250 : Nat := 118140960795 + 6744250 * 2 ^ 59
def prefixEnd_6744250 : Nat := 4983230072969 + 3 ^ 40 * 6744250 * 2
def baseEnd_6744250 : Nat := 1154347301361781108186255

theorem tailTrace_6744250 : CollatzResearch.WordTrace tailWord_6744250 prefixEnd_6744250 1154347301361781108186255 := by
  unfold tailWord_6744250
  simp only [CollatzResearch.WordTrace]
  refine ⟨61495751454185387760885551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163988670544494367362361469 61495751454185387760885551)
  ·
    refine ⟨92243627181278081641328327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61495751454185387760885551 92243627181278081641328327)
    ·
      refine ⟨138365440771917122461992491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92243627181278081641328327 138365440771917122461992491)
      ·
        refine ⟨207548161157875683692988737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138365440771917122461992491 207548161157875683692988737)
        ·
          refine ⟨155661120868406762769741553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207548161157875683692988737 155661120868406762769741553)
          ·
            refine ⟨116745840651305072077306165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155661120868406762769741553 116745840651305072077306165)
            ·
              refine ⟨10944922561059850507247453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116745840651305072077306165 10944922561059850507247453)
              ·
                refine ⟨4104345960397443940217795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10944922561059850507247453 4104345960397443940217795)
                ·
                  refine ⟨6156518940596165910326693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104345960397443940217795 6156518940596165910326693)
                  ·
                    refine ⟨1154347301361781108186255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6156518940596165910326693 1154347301361781108186255)
                    ·
                      rfl

theorem cell23_6744250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_6744250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744250 prefixEnd_6744250 := by exact prefixLift 6744250
  have htrace : WordTrace (prefixWord ++ tailWord_6744250) baseStart_6744250 baseEnd_6744250 := by
    simpa [prefixWord, tailWord_6744250, baseEnd_6744250] using wordTrace_append hprefix tailTrace_6744250
  have hstable : (prefixWord ++ tailWord_6744250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744250).length < 2 ^ (prefixWord ++ tailWord_6744250).sum := by decide
  have hdescent : baseEnd_6744250 < baseStart_6744250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744259 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 11]
def baseStart_6744259 : Nat := 118140960795 + 6744259 * 2 ^ 59
def prefixEnd_6744259 : Nat := 4983230072969 + 3 ^ 40 * 6744259 * 2
def baseEnd_6744259 : Nat := 1154348841803744596448741

theorem tailTrace_6744259 : CollatzResearch.WordTrace tailWord_6744259 prefixEnd_6744259 1154348841803744596448741 := by
  unfold tailWord_6744259
  simp only [CollatzResearch.WordTrace]
  refine ⟨245983334073708945580619831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163988889382472630387079887 245983334073708945580619831)
  ·
    refine ⟨368975001110563418370929747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245983334073708945580619831 368975001110563418370929747)
    ·
      refine ⟨553462501665845127556394621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368975001110563418370929747 553462501665845127556394621)
      ·
        refine ⟨207548438124691922833647983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553462501665845127556394621 207548438124691922833647983)
        ·
          refine ⟨311322657187037884250471975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207548438124691922833647983 311322657187037884250471975)
          ·
            refine ⟨466983985780556826375707963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311322657187037884250471975 466983985780556826375707963)
            ·
              refine ⟨700475978670835239563561945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466983985780556826375707963 700475978670835239563561945)
              ·
                refine ⟨525356984003126429672671459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700475978670835239563561945 525356984003126429672671459)
                ·
                  refine ⟨788035476004689644509007189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525356984003126429672671459 788035476004689644509007189)
                  ·
                    refine ⟨1154348841803744596448741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 788035476004689644509007189 1154348841803744596448741)
                    ·
                      rfl

theorem cell23_6744259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 11].length) (baseStart_6744259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744259 prefixEnd_6744259 := by exact prefixLift 6744259
  have htrace : WordTrace (prefixWord ++ tailWord_6744259) baseStart_6744259 baseEnd_6744259 := by
    simpa [prefixWord, tailWord_6744259, baseEnd_6744259] using wordTrace_append hprefix tailTrace_6744259
  have hstable : (prefixWord ++ tailWord_6744259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744259).length < 2 ^ (prefixWord ++ tailWord_6744259).sum := by decide
  have hdescent : baseEnd_6744259 < baseStart_6744259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744260 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_6744260 : Nat := 118140960795 + 6744260 * 2 ^ 59
def prefixEnd_6744260 : Nat := 4983230072969 + 3 ^ 40 * 6744260 * 2
def baseEnd_6744260 : Nat := 3463047038891888285433719

theorem tailTrace_6744260 : CollatzResearch.WordTrace tailWord_6744260 prefixEnd_6744260 3463047038891888285433719 := by
  unfold tailWord_6744260
  simp only [CollatzResearch.WordTrace]
  refine ⟨122991685273352661375703117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163988913697803548500937489 122991685273352661375703117)
  ·
    refine ⟨46121881977507248015888669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122991685273352661375703117 46121881977507248015888669)
    ·
      refine ⟨17295705741565218005958251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46121881977507248015888669 17295705741565218005958251)
      ·
        refine ⟨25943558612347827008937377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17295705741565218005958251 25943558612347827008937377)
        ·
          refine ⟨19457668959260870256703033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25943558612347827008937377 19457668959260870256703033)
          ·
            refine ⟨14593251719445652692527275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19457668959260870256703033 14593251719445652692527275)
            ·
              refine ⟨21889877579168479038790913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593251719445652692527275 21889877579168479038790913)
              ·
                refine ⟨16417408184376359279093185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21889877579168479038790913 16417408184376359279093185)
                ·
                  refine ⟨12313056138282269459319889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16417408184376359279093185 12313056138282269459319889)
                  ·
                    refine ⟨9234792103711702094489917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12313056138282269459319889 9234792103711702094489917)
                    ·
                      refine ⟨3463047038891888285433719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234792103711702094489917 3463047038891888285433719)
                      ·
                        rfl

theorem cell23_6744260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_6744260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744260 prefixEnd_6744260 := by exact prefixLift 6744260
  have htrace : WordTrace (prefixWord ++ tailWord_6744260) baseStart_6744260 baseEnd_6744260 := by
    simpa [prefixWord, tailWord_6744260, baseEnd_6744260] using wordTrace_append hprefix tailTrace_6744260
  have hstable : (prefixWord ++ tailWord_6744260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744260).length < 2 ^ (prefixWord ++ tailWord_6744260).sum := by decide
  have hdescent : baseEnd_6744260 < baseStart_6744260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744280 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 6]
def baseStart_6744280 : Nat := 118140960795 + 6744280 * 2 ^ 59
def prefixEnd_6744280 : Nat := 4983230072969 + 3 ^ 40 * 6744280 * 2
def baseEnd_6744280 : Nat := 384784145389442023020403

theorem tailTrace_6744280 : CollatzResearch.WordTrace tailWord_6744280 prefixEnd_6744280 384784145389442023020403 := by
  unfold tailWord_6744280
  simp only [CollatzResearch.WordTrace]
  refine ⟨122992050003316433083567147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163989400004421910778089529 122992050003316433083567147)
  ·
    refine ⟨184488075004974649625350721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122992050003316433083567147 184488075004974649625350721)
    ·
      refine ⟨138366056253730987219013041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184488075004974649625350721 138366056253730987219013041)
      ·
        refine ⟨103774542190298240414259781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138366056253730987219013041 103774542190298240414259781)
        ·
          refine ⟨19457726660680920077673709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103774542190298240414259781 19457726660680920077673709)
          ·
            refine ⟨7296647497755345029127641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19457726660680920077673709 7296647497755345029127641)
            ·
              refine ⟨5472485623316508771845731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7296647497755345029127641 5472485623316508771845731)
              ·
                refine ⟨8208728434974763157768597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472485623316508771845731 8208728434974763157768597)
                ·
                  refine ⟨384784145389442023020403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8208728434974763157768597 384784145389442023020403)
                  ·
                    rfl

theorem cell23_6744280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 6].length) (baseStart_6744280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744280 prefixEnd_6744280 := by exact prefixLift 6744280
  have htrace : WordTrace (prefixWord ++ tailWord_6744280) baseStart_6744280 baseEnd_6744280 := by
    simpa [prefixWord, tailWord_6744280, baseEnd_6744280] using wordTrace_append hprefix tailTrace_6744280
  have hstable : (prefixWord ++ tailWord_6744280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744280).length < 2 ^ (prefixWord ++ tailWord_6744280).sum := by decide
  have hdescent : baseEnd_6744280 < baseStart_6744280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744293 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_6744293 : Nat := 118140960795 + 6744293 * 2 ^ 59
def prefixEnd_6744293 : Nat := 4983230072969 + 3 ^ 40 * 6744293 * 2
def baseEnd_6744293 : Nat := 1154354661251162218773689

theorem tailTrace_6744293 : CollatzResearch.WordTrace tailWord_6744293 prefixEnd_6744293 1154354661251162218773689 := by
  unfold tailWord_6744293
  simp only [CollatzResearch.WordTrace]
  refine ⟨245984574155585769387357533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163989716103723846258238355 245984574155585769387357533)
  ·
    refine ⟨92244215308344663520259075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245984574155585769387357533 92244215308344663520259075)
    ·
      refine ⟨138366322962516995280388613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92244215308344663520259075 138366322962516995280388613)
      ·
        refine ⟨25943685555471936615072865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138366322962516995280388613 25943685555471936615072865)
        ·
          refine ⟨19457764166603952461304649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25943685555471936615072865 19457764166603952461304649)
          ·
            refine ⟨14593323124952964345978487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19457764166603952461304649 14593323124952964345978487)
            ·
              refine ⟨21889984687429446518967731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593323124952964345978487 21889984687429446518967731)
              ·
                refine ⟨32834977031144169778451597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21889984687429446518967731 32834977031144169778451597)
                ·
                  refine ⟨12313116386679063666919349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32834977031144169778451597 12313116386679063666919349)
                  ·
                    refine ⟨1154354661251162218773689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12313116386679063666919349 1154354661251162218773689)
                    ·
                      rfl

theorem cell23_6744293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_6744293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744293 prefixEnd_6744293 := by exact prefixLift 6744293
  have htrace : WordTrace (prefixWord ++ tailWord_6744293) baseStart_6744293 baseEnd_6744293 := by
    simpa [prefixWord, tailWord_6744293, baseEnd_6744293] using wordTrace_append hprefix tailTrace_6744293
  have hstable : (prefixWord ++ tailWord_6744293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744293).length < 2 ^ (prefixWord ++ tailWord_6744293).sum := by decide
  have hdescent : baseEnd_6744293 < baseStart_6744293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744300 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 2, 3, 2]
def baseStart_6744300 : Nat := 118140960795 + 6744300 * 2 ^ 59
def prefixEnd_6744300 : Nat := 4983230072969 + 3 ^ 40 * 6744300 * 2
def baseEnd_6744300 : Nat := 3463067578118068128933535

theorem tailTrace_6744300 : CollatzResearch.WordTrace tailWord_6744300 prefixEnd_6744300 3463067578118068128933535 := by
  unfold tailWord_6744300
  simp only [CollatzResearch.WordTrace]
  refine ⟨122992414733280204791431177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163989886311040273055241569 122992414733280204791431177)
  ·
    refine ⟨92244311049960153593573383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122992414733280204791431177 92244311049960153593573383)
    ·
      refine ⟨138366466574940230390360075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92244311049960153593573383 138366466574940230390360075)
      ·
        refine ⟨207549699862410345585540113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138366466574940230390360075 207549699862410345585540113)
        ·
          refine ⟨155662274896807759189155085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207549699862410345585540113 155662274896807759189155085)
          ·
            refine ⟨58373353086302909695933157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155662274896807759189155085 58373353086302909695933157)
            ·
              refine ⟨10945003703681795567987467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58373353086302909695933157 10945003703681795567987467)
              ·
                refine ⟨16417505555522693351981201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945003703681795567987467 16417505555522693351981201)
                ·
                  refine ⟨12313129166642020013985901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16417505555522693351981201 12313129166642020013985901)
                  ·
                    refine ⟨4617423437490757505244713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12313129166642020013985901 4617423437490757505244713)
                    ·
                      refine ⟨3463067578118068128933535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617423437490757505244713 3463067578118068128933535)
                      ·
                        rfl

theorem cell23_6744300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_6744300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744300 prefixEnd_6744300 := by exact prefixLift 6744300
  have htrace : WordTrace (prefixWord ++ tailWord_6744300) baseStart_6744300 baseEnd_6744300 := by
    simpa [prefixWord, tailWord_6744300, baseEnd_6744300] using wordTrace_append hprefix tailTrace_6744300
  have hstable : (prefixWord ++ tailWord_6744300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744300).length < 2 ^ (prefixWord ++ tailWord_6744300).sum := by decide
  have hdescent : baseEnd_6744300 < baseStart_6744300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744324 : List Nat := [2, 3, 2, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6744324 : Nat := 118140960795 + 6744324 * 2 ^ 59
def prefixEnd_6744324 : Nat := 4983230072969 + 3 ^ 40 * 6744324 * 2
def baseEnd_6744324 : Nat := 3463079901653776035033425

theorem tailTrace_6744324 : CollatzResearch.WordTrace tailWord_6744324 prefixEnd_6744324 3463079901653776035033425 := by
  unfold tailWord_6744324
  simp only [CollatzResearch.WordTrace]
  refine ⟨122992852409236730840868013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163990469878982307787824017 122992852409236730840868013)
  ·
    refine ⟨46122319653463774065325505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122992852409236730840868013 46122319653463774065325505)
    ·
      refine ⟨34591739740097830548994129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46122319653463774065325505 34591739740097830548994129)
      ·
        refine ⟨25943804805073372911745597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34591739740097830548994129 25943804805073372911745597)
        ·
          refine ⟨9728926801902514841904599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25943804805073372911745597 9728926801902514841904599)
          ·
            refine ⟨14593390202853772262856899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728926801902514841904599 14593390202853772262856899)
            ·
              refine ⟨21890085304280658394285349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593390202853772262856899 21890085304280658394285349)
              ·
                refine ⟨4104390994552623448928503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21890085304280658394285349 4104390994552623448928503)
                ·
                  refine ⟨6156586491828935173392755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104390994552623448928503 6156586491828935173392755)
                  ·
                    refine ⟨9234879737743402760089133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156586491828935173392755 9234879737743402760089133)
                    ·
                      refine ⟨3463079901653776035033425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234879737743402760089133 3463079901653776035033425)
                      ·
                        rfl

theorem cell23_6744324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6744324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744324 prefixEnd_6744324 := by exact prefixLift 6744324
  have htrace : WordTrace (prefixWord ++ tailWord_6744324) baseStart_6744324 baseEnd_6744324 := by
    simpa [prefixWord, tailWord_6744324, baseEnd_6744324] using wordTrace_append hprefix tailTrace_6744324
  have hstable : (prefixWord ++ tailWord_6744324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744324).length < 2 ^ (prefixWord ++ tailWord_6744324).sum := by decide
  have hdescent : baseEnd_6744324 < baseStart_6744324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744343 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6744343 : Nat := 118140960795 + 6744343 * 2 ^ 59
def prefixEnd_6744343 : Nat := 4983230072969 + 3 ^ 40 * 6744343 * 2
def baseEnd_6744343 : Nat := 3463089657786211460695837

theorem tailTrace_6744343 : CollatzResearch.WordTrace tailWord_6744343 prefixEnd_6744343 3463089657786211460695837 := by
  unfold tailWord_6744343
  simp only [CollatzResearch.WordTrace]
  refine ⟨245986397805404627926677683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163990931870269751951118455 245986397805404627926677683)
  ·
    refine ⟨368979596708106941890016525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245986397805404627926677683 368979596708106941890016525)
    ·
      refine ⟨138367348765540103208756197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368979596708106941890016525 138367348765540103208756197)
      ·
        refine ⟨25943877893538769351641787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138367348765540103208756197 25943877893538769351641787)
        ·
          refine ⟨38915816840308154027462681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25943877893538769351641787 38915816840308154027462681)
          ·
            refine ⟨29186862630231115520597011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38915816840308154027462681 29186862630231115520597011)
            ·
              refine ⟨43780293945346673280895517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29186862630231115520597011 43780293945346673280895517)
              ·
                refine ⟨16417610229505002480335819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43780293945346673280895517 16417610229505002480335819)
                ·
                  refine ⟨24626415344257503720503729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16417610229505002480335819 24626415344257503720503729)
                  ·
                    refine ⟨18469811508193127790377797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24626415344257503720503729 18469811508193127790377797)
                    ·
                      refine ⟨3463089657786211460695837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18469811508193127790377797 3463089657786211460695837)
                      ·
                        rfl

theorem cell23_6744343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6744343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744343 prefixEnd_6744343 := by exact prefixLift 6744343
  have htrace : WordTrace (prefixWord ++ tailWord_6744343) baseStart_6744343 baseEnd_6744343 := by
    simpa [prefixWord, tailWord_6744343, baseEnd_6744343] using wordTrace_append hprefix tailTrace_6744343
  have hstable : (prefixWord ++ tailWord_6744343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744343).length < 2 ^ (prefixWord ++ tailWord_6744343).sum := by decide
  have hdescent : baseEnd_6744343 < baseStart_6744343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744380 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_6744380 : Nat := 118140960795 + 6744380 * 2 ^ 59
def prefixEnd_6744380 : Nat := 4983230072969 + 3 ^ 40 * 6744380 * 2
def baseEnd_6744380 : Nat := 3463108656570427815933167

theorem tailTrace_6744380 : CollatzResearch.WordTrace tailWord_6744380 prefixEnd_6744380 3463108656570427815933167 := by
  unfold tailWord_6744380
  simp only [CollatzResearch.WordTrace]
  refine ⟨122993873653135291622887297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163991831537513722163849729 122993873653135291622887297)
  ·
    refine ⟨92245405239851468717165473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122993873653135291622887297 92245405239851468717165473)
    ·
      refine ⟨69184053929888601537874105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92245405239851468717165473 69184053929888601537874105)
      ·
        refine ⟨51888040447416451153405579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69184053929888601537874105 51888040447416451153405579)
        ·
          refine ⟨77832060671124676730108369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51888040447416451153405579 77832060671124676730108369)
          ·
            refine ⟨58374045503343507547581277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77832060671124676730108369 58374045503343507547581277)
            ·
              refine ⟨21890267063753815330342979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58374045503343507547581277 21890267063753815330342979)
              ·
                refine ⟨32835400595630722995514469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21890267063753815330342979 32835400595630722995514469)
                ·
                  refine ⟨6156637611680760561658963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32835400595630722995514469 6156637611680760561658963)
                  ·
                    refine ⟨9234956417521140842488445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156637611680760561658963 9234956417521140842488445)
                    ·
                      refine ⟨3463108656570427815933167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9234956417521140842488445 3463108656570427815933167)
                      ·
                        rfl

theorem cell23_6744380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_6744380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744380 prefixEnd_6744380 := by exact prefixLift 6744380
  have htrace : WordTrace (prefixWord ++ tailWord_6744380) baseStart_6744380 baseEnd_6744380 := by
    simpa [prefixWord, tailWord_6744380, baseEnd_6744380] using wordTrace_append hprefix tailTrace_6744380
  have hstable : (prefixWord ++ tailWord_6744380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744380).length < 2 ^ (prefixWord ++ tailWord_6744380).sum := by decide
  have hdescent : baseEnd_6744380 < baseStart_6744380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744407 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 1, 3, 2]
def baseStart_6744407 : Nat := 118140960795 + 6744407 * 2 ^ 59
def prefixEnd_6744407 : Nat := 4983230072969 + 3 ^ 40 * 6744407 * 2
def baseEnd_6744407 : Nat := 3463122520548099210295543

theorem tailTrace_6744407 : CollatzResearch.WordTrace tailWord_6744407 prefixEnd_6744407 3463122520548099210295543 := by
  unfold tailWord_6744407
  simp only [CollatzResearch.WordTrace]
  refine ⟨245988732077172766857007475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163992488051448511238004983 245988732077172766857007475)
  ·
    refine ⟨368983098115759150285511213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245988732077172766857007475 368983098115759150285511213)
    ·
      refine ⟨138368661793409681357066705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368983098115759150285511213 138368661793409681357066705)
      ·
        refine ⟨103776496345057261017800029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138368661793409681357066705 103776496345057261017800029)
        ·
          refine ⟨38916186129396472881675011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103776496345057261017800029 38916186129396472881675011)
          ·
            refine ⟨58374279194094709322512517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38916186129396472881675011 58374279194094709322512517)
            ·
              refine ⟨10945177348892757997971097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58374279194094709322512517 10945177348892757997971097)
              ·
                refine ⟨8208883011669568498478323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10945177348892757997971097 8208883011669568498478323)
                ·
                  refine ⟨12313324517504352747717485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208883011669568498478323 12313324517504352747717485)
                  ·
                    refine ⟨4617496694064132280394057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12313324517504352747717485 4617496694064132280394057)
                    ·
                      refine ⟨3463122520548099210295543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617496694064132280394057 3463122520548099210295543)
                      ·
                        rfl

theorem cell23_6744407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_6744407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744407 prefixEnd_6744407 := by exact prefixLift 6744407
  have htrace : WordTrace (prefixWord ++ tailWord_6744407) baseStart_6744407 baseEnd_6744407 := by
    simpa [prefixWord, tailWord_6744407, baseEnd_6744407] using wordTrace_append hprefix tailTrace_6744407
  have hstable : (prefixWord ++ tailWord_6744407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744407).length < 2 ^ (prefixWord ++ tailWord_6744407).sum := by decide
  have hdescent : baseEnd_6744407 < baseStart_6744407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744420 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_6744420 : Nat := 118140960795 + 6744420 * 2 ^ 59
def prefixEnd_6744420 : Nat := 4983230072969 + 3 ^ 40 * 6744420 * 2
def baseEnd_6744420 : Nat := 3463129195796607659432983

theorem tailTrace_6744420 : CollatzResearch.WordTrace tailWord_6744420 prefixEnd_6744420 3463129195796607659432983 := by
  unfold tailWord_6744420
  simp only [CollatzResearch.WordTrace]
  refine ⟨122994603113062835038615357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163992804150750446718153809 122994603113062835038615357)
  ·
    refine ⟨46122976167398563139480759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122994603113062835038615357 46122976167398563139480759)
    ·
      refine ⟨69184464251097844709221139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46122976167398563139480759 69184464251097844709221139)
      ·
        refine ⟨103776696376646767063831709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69184464251097844709221139 103776696376646767063831709)
        ·
          refine ⟨38916261141242537648936891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103776696376646767063831709 38916261141242537648936891)
          ·
            refine ⟨58374391711863806473405337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38916261141242537648936891 58374391711863806473405337)
            ·
              refine ⟨43780793783897854855054003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58374391711863806473405337 43780793783897854855054003)
              ·
                refine ⟨65671190675846782282581005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43780793783897854855054003 65671190675846782282581005)
                ·
                  refine ⟨24626696503442543355967877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65671190675846782282581005 24626696503442543355967877)
                  ·
                    refine ⟨4617505594395476879243977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24626696503442543355967877 4617505594395476879243977)
                    ·
                      refine ⟨3463129195796607659432983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617505594395476879243977 3463129195796607659432983)
                      ·
                        rfl

theorem cell23_6744420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_6744420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744420 prefixEnd_6744420 := by exact prefixLift 6744420
  have htrace : WordTrace (prefixWord ++ tailWord_6744420) baseStart_6744420 baseEnd_6744420 := by
    simpa [prefixWord, tailWord_6744420, baseEnd_6744420] using wordTrace_append hprefix tailTrace_6744420
  have hstable : (prefixWord ++ tailWord_6744420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744420).length < 2 ^ (prefixWord ++ tailWord_6744420).sum := by decide
  have hdescent : baseEnd_6744420 < baseStart_6744420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744423 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_6744423 : Nat := 118140960795 + 6744423 * 2 ^ 59
def prefixEnd_6744423 : Nat := 4983230072969 + 3 ^ 40 * 6744423 * 2
def baseEnd_6744423 : Nat := 3463130736238571147695469

theorem tailTrace_6744423 : CollatzResearch.WordTrace tailWord_6744423 prefixEnd_6744423 3463130736238571147695469 := by
  unfold tailWord_6744423
  simp only [CollatzResearch.WordTrace]
  refine ⟨245989315645114801589589923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163992877096743201059726615 245989315645114801589589923)
  ·
    refine ⟨368983973467672202384384885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245989315645114801589589923 368983973467672202384384885)
    ·
      refine ⟨34592247512594268973536083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 368983973467672202384384885 34592247512594268973536083)
      ·
        refine ⟨51888371268891403460304125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34592247512594268973536083 51888371268891403460304125)
        ·
          refine ⟨19458139225834276297614047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51888371268891403460304125 19458139225834276297614047)
          ·
            refine ⟨29187208838751414446421071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19458139225834276297614047 29187208838751414446421071)
            ·
              refine ⟨43780813258127121669631607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29187208838751414446421071 43780813258127121669631607)
              ·
                refine ⟨65671219887190682504447411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43780813258127121669631607 65671219887190682504447411)
                ·
                  refine ⟨98506829830786023756671117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65671219887190682504447411 98506829830786023756671117)
                  ·
                    refine ⟨36940061186544758908751669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98506829830786023756671117 36940061186544758908751669)
                    ·
                      refine ⟨3463130736238571147695469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36940061186544758908751669 3463130736238571147695469)
                      ·
                        rfl

theorem cell23_6744423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_6744423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744423 prefixEnd_6744423 := by exact prefixLift 6744423
  have htrace : WordTrace (prefixWord ++ tailWord_6744423) baseStart_6744423 baseEnd_6744423 := by
    simpa [prefixWord, tailWord_6744423, baseEnd_6744423] using wordTrace_append hprefix tailTrace_6744423
  have hstable : (prefixWord ++ tailWord_6744423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744423).length < 2 ^ (prefixWord ++ tailWord_6744423).sum := by decide
  have hdescent : baseEnd_6744423 < baseStart_6744423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744443 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 7]
def baseStart_6744443 : Nat := 118140960795 + 6744443 * 2 ^ 59
def prefixEnd_6744443 : Nat := 4983230072969 + 3 ^ 40 * 6744443 * 2
def baseEnd_6744443 : Nat := 384793445094629007716153

theorem tailTrace_6744443 : CollatzResearch.WordTrace tailWord_6744443 prefixEnd_6744443 384793445094629007716153 := by
  unfold tailWord_6744443
  simp only [CollatzResearch.WordTrace]
  refine ⟨245990045105042345005317983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163993363403361563336878655 245990045105042345005317983)
  ·
    refine ⟨368985067657563517507976975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245990045105042345005317983 368985067657563517507976975)
    ·
      refine ⟨553477601486345276261965463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368985067657563517507976975 553477601486345276261965463)
      ·
        refine ⟨830216402229517914392948195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553477601486345276261965463 830216402229517914392948195)
        ·
          refine ⟨1245324603344276871589422293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830216402229517914392948195 1245324603344276871589422293)
          ·
            refine ⟨29187295390881489177877085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1245324603344276871589422293 29187295390881489177877085)
            ·
              refine ⟨10945235771580558441703907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29187295390881489177877085 10945235771580558441703907)
              ·
                refine ⟨16417853657370837662555861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945235771580558441703907 16417853657370837662555861)
                ·
                  refine ⟨384793445094629007716153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16417853657370837662555861 384793445094629007716153)
                  ·
                    rfl

theorem cell23_6744443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 7].length) (baseStart_6744443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744443 prefixEnd_6744443 := by exact prefixLift 6744443
  have htrace : WordTrace (prefixWord ++ tailWord_6744443) baseStart_6744443 baseEnd_6744443 := by
    simpa [prefixWord, tailWord_6744443, baseEnd_6744443] using wordTrace_append hprefix tailTrace_6744443
  have hstable : (prefixWord ++ tailWord_6744443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744443).length < 2 ^ (prefixWord ++ tailWord_6744443).sum := by decide
  have hdescent : baseEnd_6744443 < baseStart_6744443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744453 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_6744453 : Nat := 118140960795 + 6744453 * 2 ^ 59
def prefixEnd_6744453 : Nat := 4983230072969 + 3 ^ 40 * 6744453 * 2
def baseEnd_6744453 : Nat := 3463146140658206030320331

theorem tailTrace_6744453 : CollatzResearch.WordTrace tailWord_6744453 prefixEnd_6744453 3463146140658206030320331 := by
  unfold tailWord_6744453
  simp only [CollatzResearch.WordTrace]
  refine ⟨245990409835006116713182013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163993606556670744475454675 245990409835006116713182013)
  ·
    refine ⟨92246403688127293767443255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245990409835006116713182013 92246403688127293767443255)
    ·
      refine ⟨138369605532190940651164883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92246403688127293767443255 138369605532190940651164883)
      ·
        refine ⟨207554408298286410976747325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138369605532190940651164883 207554408298286410976747325)
        ·
          refine ⟨77832903111857404116280247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207554408298286410976747325 77832903111857404116280247)
          ·
            refine ⟨116749354667786106174420371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77832903111857404116280247 116749354667786106174420371)
            ·
              refine ⟨175124032001679159261630557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116749354667786106174420371 175124032001679159261630557)
              ·
                refine ⟨65671512000629684723111459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175124032001679159261630557 65671512000629684723111459)
                ·
                  refine ⟨98507268000944527084667189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65671512000629684723111459 98507268000944527084667189)
                  ·
                    refine ⟨9235056375088549414187549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98507268000944527084667189 9235056375088549414187549)
                    ·
                      refine ⟨3463146140658206030320331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9235056375088549414187549 3463146140658206030320331)
                      ·
                        rfl

theorem cell23_6744453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_6744453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744453 prefixEnd_6744453 := by exact prefixLift 6744453
  have htrace : WordTrace (prefixWord ++ tailWord_6744453) baseStart_6744453 baseEnd_6744453 := by
    simpa [prefixWord, tailWord_6744453, baseEnd_6744453] using wordTrace_append hprefix tailTrace_6744453
  have hstable : (prefixWord ++ tailWord_6744453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744453).length < 2 ^ (prefixWord ++ tailWord_6744453).sum := by decide
  have hdescent : baseEnd_6744453 < baseStart_6744453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744458 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6744458 : Nat := 118140960795 + 6744458 * 2 ^ 59
def prefixEnd_6744458 : Nat := 4983230072969 + 3 ^ 40 * 6744458 * 2
def baseEnd_6744458 : Nat := 3463148708061478510757809

theorem tailTrace_6744458 : CollatzResearch.WordTrace tailWord_6744458 prefixEnd_6744458 3463148708061478510757809 := by
  unfold tailWord_6744458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61497648049997000641778507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163993728133325335044742685 61497648049997000641778507)
  ·
    refine ⟨92246472074995500962667761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61497648049997000641778507 92246472074995500962667761)
    ·
      refine ⟨69184854056246625722000821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92246472074995500962667761 69184854056246625722000821)
      ·
        refine ⟨6486080067773121161437577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69184854056246625722000821 6486080067773121161437577)
        ·
          refine ⟨4864560050829840871078183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6486080067773121161437577 4864560050829840871078183)
          ·
            refine ⟨7296840076244761306617275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864560050829840871078183 7296840076244761306617275)
            ·
              refine ⟨10945260114367141959925913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296840076244761306617275 10945260114367141959925913)
              ·
                refine ⟨8208945085775356469944435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10945260114367141959925913 8208945085775356469944435)
                ·
                  refine ⟨12313417628663034704916653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208945085775356469944435 12313417628663034704916653)
                  ·
                    refine ⟨4617531610748638014343745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12313417628663034704916653 4617531610748638014343745)
                    ·
                      refine ⟨3463148708061478510757809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617531610748638014343745 3463148708061478510757809)
                      ·
                        rfl

theorem cell23_6744458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6744458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744458 prefixEnd_6744458 := by exact prefixLift 6744458
  have htrace : WordTrace (prefixWord ++ tailWord_6744458) baseStart_6744458 baseEnd_6744458 := by
    simpa [prefixWord, tailWord_6744458, baseEnd_6744458] using wordTrace_append hprefix tailTrace_6744458
  have hstable : (prefixWord ++ tailWord_6744458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744458).length < 2 ^ (prefixWord ++ tailWord_6744458).sum := by decide
  have hdescent : baseEnd_6744458 < baseStart_6744458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744483 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5]
def baseStart_6744483 : Nat := 118140960795 + 6744483 * 2 ^ 59
def prefixEnd_6744483 : Nat := 4983230072969 + 3 ^ 40 * 6744483 * 2
def baseEnd_6744483 : Nat := 3463161545077840912945193

theorem tailTrace_6744483 : CollatzResearch.WordTrace tailWord_6744483 prefixEnd_6744483 3463161545077840912945193 := by
  unfold tailWord_6744483
  simp only [CollatzResearch.WordTrace]
  refine ⟨245991504024897431836774103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163994336016598287891182735 245991504024897431836774103)
  ·
    refine ⟨368987256037346147755161155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245991504024897431836774103 368987256037346147755161155)
    ·
      refine ⟨553480884056019221632741733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368987256037346147755161155 553480884056019221632741733)
      ·
        refine ⟨103777665760503604056139075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 553480884056019221632741733 103777665760503604056139075)
        ·
          refine ⟨155666498640755406084208613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103777665760503604056139075 155666498640755406084208613)
          ·
            refine ⟨29187468495141638640789115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155666498640755406084208613 29187468495141638640789115)
            ·
              refine ⟨43781202742712457961183673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29187468495141638640789115 43781202742712457961183673)
              ·
                refine ⟨32835902057034343470887755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43781202742712457961183673 32835902057034343470887755)
                ·
                  refine ⟨49253853085551515206331633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32835902057034343470887755 49253853085551515206331633)
                  ·
                    refine ⟨36940389814163636404748725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49253853085551515206331633 36940389814163636404748725)
                    ·
                      refine ⟨3463161545077840912945193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36940389814163636404748725 3463161545077840912945193)
                      ·
                        rfl

theorem cell23_6744483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_6744483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744483 prefixEnd_6744483 := by exact prefixLift 6744483
  have htrace : WordTrace (prefixWord ++ tailWord_6744483) baseStart_6744483 baseEnd_6744483 := by
    simpa [prefixWord, tailWord_6744483, baseEnd_6744483] using wordTrace_append hprefix tailTrace_6744483
  have hstable : (prefixWord ++ tailWord_6744483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744483).length < 2 ^ (prefixWord ++ tailWord_6744483).sum := by decide
  have hdescent : baseEnd_6744483 < baseStart_6744483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744510 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_6744510 : Nat := 118140960795 + 6744510 * 2 ^ 59
def prefixEnd_6744510 : Nat := 4983230072969 + 3 ^ 40 * 6744510 * 2
def baseEnd_6744510 : Nat := 3463175409055512307307569

theorem tailTrace_6744510 : CollatzResearch.WordTrace tailWord_6744510 prefixEnd_6744510 3463175409055512307307569 := by
  unfold tailWord_6744510
  simp only [CollatzResearch.WordTrace]
  refine ⟨30749061099474951931000873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163994992530533076965337989 30749061099474951931000873)
  ·
    refine ⟨23061795824606213948250655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30749061099474951931000873 23061795824606213948250655)
    ·
      refine ⟨34592693736909320922375983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23061795824606213948250655 34592693736909320922375983)
      ·
        refine ⟨51889040605363981383563975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34592693736909320922375983 51889040605363981383563975)
        ·
          refine ⟨77833560908045972075345963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51889040605363981383563975 77833560908045972075345963)
          ·
            refine ⟨116750341362068958113018945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77833560908045972075345963 116750341362068958113018945)
            ·
              refine ⟨87562756021551718584764209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116750341362068958113018945 87562756021551718584764209)
              ·
                refine ⟨65672067016163788938573157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87562756021551718584764209 65672067016163788938573157)
                ·
                  refine ⟨12313512565530710425982467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65672067016163788938573157 12313512565530710425982467)
                  ·
                    refine ⟨18470268848296065638973701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12313512565530710425982467 18470268848296065638973701)
                    ·
                      refine ⟨3463175409055512307307569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18470268848296065638973701 3463175409055512307307569)
                      ·
                        rfl

theorem cell23_6744510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_6744510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744510 prefixEnd_6744510 := by exact prefixLift 6744510
  have htrace : WordTrace (prefixWord ++ tailWord_6744510) baseStart_6744510 baseEnd_6744510 := by
    simpa [prefixWord, tailWord_6744510, baseEnd_6744510] using wordTrace_append hprefix tailTrace_6744510
  have hstable : (prefixWord ++ tailWord_6744510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744510).length < 2 ^ (prefixWord ++ tailWord_6744510).sum := by decide
  have hdescent : baseEnd_6744510 < baseStart_6744510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744520 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 5, 4]
def baseStart_6744520 : Nat := 118140960795 + 6744520 * 2 ^ 59
def prefixEnd_6744520 : Nat := 4983230072969 + 3 ^ 40 * 6744520 * 2
def baseEnd_6744520 : Nat := 1154393514620685756060841

theorem tailTrace_6744520 : CollatzResearch.WordTrace tailWord_6744520 prefixEnd_6744520 1154393514620685756060841 := by
  unfold tailWord_6744520
  simp only [CollatzResearch.WordTrace]
  refine ⟨122996426762881693577935507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163995235683842258103914009 122996426762881693577935507)
  ·
    refine ⟨184494640144322540366903261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122996426762881693577935507 184494640144322540366903261)
    ·
      refine ⟨69185490054120952637588723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184494640144322540366903261 69185490054120952637588723)
      ·
        refine ⟨103778235081181428956383085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69185490054120952637588723 103778235081181428956383085)
        ·
          refine ⟨38916838155443035858643657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103778235081181428956383085 38916838155443035858643657)
          ·
            refine ⟨29187628616582276893982743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38916838155443035858643657 29187628616582276893982743)
            ·
              refine ⟨43781442924873415340974115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29187628616582276893982743 43781442924873415340974115)
              ·
                refine ⟨65672164387310123011461173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43781442924873415340974115 65672164387310123011461173)
                ·
                  refine ⟨6156765411310324032324485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65672164387310123011461173 6156765411310324032324485)
                  ·
                    refine ⟨1154393514620685756060841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6156765411310324032324485 1154393514620685756060841)
                    ·
                      rfl

theorem cell23_6744520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_6744520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744520 prefixEnd_6744520 := by exact prefixLift 6744520
  have htrace : WordTrace (prefixWord ++ tailWord_6744520) baseStart_6744520 baseEnd_6744520 := by
    simpa [prefixWord, tailWord_6744520, baseEnd_6744520] using wordTrace_append hprefix tailTrace_6744520
  have hstable : (prefixWord ++ tailWord_6744520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744520).length < 2 ^ (prefixWord ++ tailWord_6744520).sum := by decide
  have hdescent : baseEnd_6744520 < baseStart_6744520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744524 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_6744524 : Nat := 118140960795 + 6744524 * 2 ^ 59
def prefixEnd_6744524 : Nat := 4983230072969 + 3 ^ 40 * 6744524 * 2
def baseEnd_6744524 : Nat := 1154394199261558417510835

theorem tailTrace_6744524 : CollatzResearch.WordTrace tailWord_6744524 prefixEnd_6744524 1154394199261558417510835 := by
  unfold tailWord_6744524
  simp only [CollatzResearch.WordTrace]
  refine ⟨122996499708874447919508313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163995332945165930559344417 122996499708874447919508313)
  ·
    refine ⟨92247374781655835939631235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122996499708874447919508313 92247374781655835939631235)
    ·
      refine ⟨138371062172483753909446853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92247374781655835939631235 138371062172483753909446853)
      ·
        refine ⟨25944574157340703858021285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138371062172483753909446853 25944574157340703858021285)
        ·
          refine ⟨4864607654501381973378991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25944574157340703858021285 4864607654501381973378991)
          ·
            refine ⟨7296911481752072960068487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864607654501381973378991 7296911481752072960068487)
            ·
              refine ⟨10945367222628109440102731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296911481752072960068487 10945367222628109440102731)
              ·
                refine ⟨16418050833942164160154097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945367222628109440102731 16418050833942164160154097)
                ·
                  refine ⟨12313538125456623120115573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16418050833942164160154097 12313538125456623120115573)
                  ·
                    refine ⟨1154394199261558417510835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12313538125456623120115573 1154394199261558417510835)
                    ·
                      rfl

theorem cell23_6744524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_6744524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744524 prefixEnd_6744524 := by exact prefixLift 6744524
  have htrace : WordTrace (prefixWord ++ tailWord_6744524) baseStart_6744524 baseEnd_6744524 := by
    simpa [prefixWord, tailWord_6744524, baseEnd_6744524] using wordTrace_append hprefix tailTrace_6744524
  have hstable : (prefixWord ++ tailWord_6744524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744524).length < 2 ^ (prefixWord ++ tailWord_6744524).sum := by decide
  have hdescent : baseEnd_6744524 < baseStart_6744524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744554 : List Nat := [3, 1, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_6744554 : Nat := 118140960795 + 6744554 * 2 ^ 59
def prefixEnd_6744554 : Nat := 4983230072969 + 3 ^ 40 * 6744554 * 2
def baseEnd_6744554 : Nat := 1154399334068103378385789

theorem tailTrace_6744554 : CollatzResearch.WordTrace tailWord_6744554 prefixEnd_6744554 1154399334068103378385789 := by
  unfold tailWord_6744554
  simp only [CollatzResearch.WordTrace]
  refine ⟨61498523401910052740652179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163996062405093473975072477 61498523401910052740652179)
  ·
    refine ⟨92247785102865079110978269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61498523401910052740652179 92247785102865079110978269)
    ·
      refine ⟨34592919413574404666616851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92247785102865079110978269 34592919413574404666616851)
      ·
        refine ⟨51889379120361606999925277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34592919413574404666616851 51889379120361606999925277)
        ·
          refine ⟨19458517170135602624971979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51889379120361606999925277 19458517170135602624971979)
          ·
            refine ⟨29187775755203403937457969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19458517170135602624971979 29187775755203403937457969)
            ·
              refine ⟨21890831816402552953093477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29187775755203403937457969 21890831816402552953093477)
              ·
                refine ⟨4104530965575478678705027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21890831816402552953093477 4104530965575478678705027)
                ·
                  refine ⟨6156796448363218018057541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104530965575478678705027 6156796448363218018057541)
                  ·
                    refine ⟨1154399334068103378385789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6156796448363218018057541 1154399334068103378385789)
                    ·
                      rfl

theorem cell23_6744554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_6744554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744554 prefixEnd_6744554 := by exact prefixLift 6744554
  have htrace : WordTrace (prefixWord ++ tailWord_6744554) baseStart_6744554 baseEnd_6744554 := by
    simpa [prefixWord, tailWord_6744554, baseEnd_6744554] using wordTrace_append hprefix tailTrace_6744554
  have hstable : (prefixWord ++ tailWord_6744554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744554).length < 2 ^ (prefixWord ++ tailWord_6744554).sum := by decide
  have hdescent : baseEnd_6744554 < baseStart_6744554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744587 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 1, 5, 2]
def baseStart_6744587 : Nat := 118140960795 + 6744587 * 2 ^ 59
def prefixEnd_6744587 : Nat := 4983230072969 + 3 ^ 40 * 6744587 * 2
def baseEnd_6744587 : Nat := 3463214947065908506044715

theorem tailTrace_6744587 : CollatzResearch.WordTrace tailWord_6744587 prefixEnd_6744587 3463214947065908506044715 := by
  unfold tailWord_6744587
  simp only [CollatzResearch.WordTrace]
  refine ⟨245995297216520657598560015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163996864811013771732373343 245995297216520657598560015)
  ·
    refine ⟨368992945824780986397840023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245995297216520657598560015 368992945824780986397840023)
    ·
      refine ⟨553489418737171479596760035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368992945824780986397840023 553489418737171479596760035)
      ·
        refine ⟨830234128105757219395140053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553489418737171479596760035 830234128105757219395140053)
        ·
          refine ⟨19458612377478684829573595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 830234128105757219395140053 19458612377478684829573595)
          ·
            refine ⟨29187918566218027244360393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19458612377478684829573595 29187918566218027244360393)
            ·
              refine ⟨21890938924663520433270295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29187918566218027244360393 21890938924663520433270295)
              ·
                refine ⟨32836408386995280649905443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21890938924663520433270295 32836408386995280649905443)
                ·
                  refine ⟨49254612580492920974858165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32836408386995280649905443 49254612580492920974858165)
                  ·
                    refine ⟨4617619929421211341392953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49254612580492920974858165 4617619929421211341392953)
                    ·
                      refine ⟨3463214947065908506044715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617619929421211341392953 3463214947065908506044715)
                      ·
                        rfl

theorem cell23_6744587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5, 2].length) (baseStart_6744587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744587 prefixEnd_6744587 := by exact prefixLift 6744587
  have htrace : WordTrace (prefixWord ++ tailWord_6744587) baseStart_6744587 baseEnd_6744587 := by
    simpa [prefixWord, tailWord_6744587, baseEnd_6744587] using wordTrace_append hprefix tailTrace_6744587
  have hstable : (prefixWord ++ tailWord_6744587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744587).length < 2 ^ (prefixWord ++ tailWord_6744587).sum := by decide
  have hdescent : baseEnd_6744587 < baseStart_6744587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744604 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_6744604 : Nat := 118140960795 + 6744604 * 2 ^ 59
def prefixEnd_6744604 : Nat := 4983230072969 + 3 ^ 40 * 6744604 * 2
def baseEnd_6744604 : Nat := 3463223676237034939532137

theorem tailTrace_6744604 : CollatzResearch.WordTrace tailWord_6744604 prefixEnd_6744604 3463223676237034939532137 := by
  unfold tailWord_6744604
  simp only [CollatzResearch.WordTrace]
  refine ⟨122997958628729534750964433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163997278171639379667952577 122997958628729534750964433)
  ·
    refine ⟨92248468971547151063223325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122997958628729534750964433 92248468971547151063223325)
    ·
      refine ⟨34593175864330181648708747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92248468971547151063223325 34593175864330181648708747)
      ·
        refine ⟨51889763796495272473063121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34593175864330181648708747 51889763796495272473063121)
        ·
          refine ⟨38917322847371454354797341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51889763796495272473063121 38917322847371454354797341)
          ·
            refine ⟨14593996067764295383049003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38917322847371454354797341 14593996067764295383049003)
            ·
              refine ⟨21890994101646443074573505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593996067764295383049003 21890994101646443074573505)
              ·
                refine ⟨16418245576234832305930129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21890994101646443074573505 16418245576234832305930129)
                ·
                  refine ⟨12313684182176124229447597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16418245576234832305930129 12313684182176124229447597)
                  ·
                    refine ⟨4617631568316046586042849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12313684182176124229447597 4617631568316046586042849)
                    ·
                      refine ⟨3463223676237034939532137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617631568316046586042849 3463223676237034939532137)
                      ·
                        rfl

theorem cell23_6744604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_6744604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744604 prefixEnd_6744604 := by exact prefixLift 6744604
  have htrace : WordTrace (prefixWord ++ tailWord_6744604) baseStart_6744604 baseEnd_6744604 := by
    simpa [prefixWord, tailWord_6744604, baseEnd_6744604] using wordTrace_append hprefix tailTrace_6744604
  have hstable : (prefixWord ++ tailWord_6744604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744604).length < 2 ^ (prefixWord ++ tailWord_6744604).sum := by decide
  have hdescent : baseEnd_6744604 < baseStart_6744604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744627 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 2, 4]
def baseStart_6744627 : Nat := 118140960795 + 6744627 * 2 ^ 59
def prefixEnd_6744627 : Nat := 4983230072969 + 3 ^ 40 * 6744627 * 2
def baseEnd_6744627 : Nat := 1154411828764029449848177

theorem tailTrace_6744627 : CollatzResearch.WordTrace tailWord_6744627 prefixEnd_6744627 1154411828764029449848177 := by
  unfold tailWord_6744627
  simp only [CollatzResearch.WordTrace]
  refine ⟨245996756136375744430016135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163997837424250496286677423 245996756136375744430016135)
  ·
    refine ⟨368995134204563616645024203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245996756136375744430016135 368995134204563616645024203)
    ·
      refine ⟨553492701306845424967536305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368995134204563616645024203 553492701306845424967536305)
      ·
        refine ⟨415119525980134068725652229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553492701306845424967536305 415119525980134068725652229)
        ·
          refine ⟨77834911121275137886059793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415119525980134068725652229 77834911121275137886059793)
          ·
            refine ⟨58376183340956353414544845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77834911121275137886059793 58376183340956353414544845)
            ·
              refine ⟨21891068752858632530454317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58376183340956353414544845 21891068752858632530454317)
              ·
                refine ⟨8209150782321987198920369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21891068752858632530454317 8209150782321987198920369)
                ·
                  refine ⟨6156863086741490399190277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8209150782321987198920369 6156863086741490399190277)
                  ·
                    refine ⟨1154411828764029449848177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6156863086741490399190277 1154411828764029449848177)
                    ·
                      rfl

theorem cell23_6744627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 4].length) (baseStart_6744627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744627 prefixEnd_6744627 := by exact prefixLift 6744627
  have htrace : WordTrace (prefixWord ++ tailWord_6744627) baseStart_6744627 baseEnd_6744627 := by
    simpa [prefixWord, tailWord_6744627, baseEnd_6744627] using wordTrace_append hprefix tailTrace_6744627
  have hstable : (prefixWord ++ tailWord_6744627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744627).length < 2 ^ (prefixWord ++ tailWord_6744627).sum := by decide
  have hdescent : baseEnd_6744627 < baseStart_6744627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744634 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_6744634 : Nat := 118140960795 + 6744634 * 2 ^ 59
def prefixEnd_6744634 : Nat := 4983230072969 + 3 ^ 40 * 6744634 * 2
def baseEnd_6744634 : Nat := 3463239080656669822156999

theorem tailTrace_6744634 : CollatzResearch.WordTrace tailWord_6744634 prefixEnd_6744634 3463239080656669822156999 := by
  unfold tailWord_6744634
  simp only [CollatzResearch.WordTrace]
  refine ⟨61499252861837596156380239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163998007631566923083680637 61499252861837596156380239)
  ·
    refine ⟨92248879292756394234570359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61499252861837596156380239 92248879292756394234570359)
    ·
      refine ⟨138373318939134591351855539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92248879292756394234570359 138373318939134591351855539)
      ·
        refine ⟨207559978408701887027783309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138373318939134591351855539 207559978408701887027783309)
        ·
          refine ⟨77834991903263207635418741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207559978408701887027783309 77834991903263207635418741)
          ·
            refine ⟨7297030490930925715820507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77834991903263207635418741 7297030490930925715820507)
            ·
              refine ⟨10945545736396388573730761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7297030490930925715820507 10945545736396388573730761)
              ·
                refine ⟨8209159302297291430298071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10945545736396388573730761 8209159302297291430298071)
                ·
                  refine ⟨12313738953445937145447107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8209159302297291430298071 12313738953445937145447107)
                  ·
                    refine ⟨18470608430168905718170661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12313738953445937145447107 18470608430168905718170661)
                    ·
                      refine ⟨3463239080656669822156999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18470608430168905718170661 3463239080656669822156999)
                      ·
                        rfl

theorem cell23_6744634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_6744634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744634 prefixEnd_6744634 := by exact prefixLift 6744634
  have htrace : WordTrace (prefixWord ++ tailWord_6744634) baseStart_6744634 baseEnd_6744634 := by
    simpa [prefixWord, tailWord_6744634, baseEnd_6744634] using wordTrace_append hprefix tailTrace_6744634
  have hstable : (prefixWord ++ tailWord_6744634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744634).length < 2 ^ (prefixWord ++ tailWord_6744634).sum := by decide
  have hdescent : baseEnd_6744634 < baseStart_6744634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744638 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6744638 : Nat := 118140960795 + 6744638 * 2 ^ 59
def prefixEnd_6744638 : Nat := 4983230072969 + 3 ^ 40 * 6744638 * 2
def baseEnd_6744638 : Nat := 3463241134579287806506981

theorem tailTrace_6744638 : CollatzResearch.WordTrace tailWord_6744638 prefixEnd_6744638 3463241134579287806506981 := by
  unfold tailWord_6744638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30749644667416986663583321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163998104892890595539111045 30749644667416986663583321)
  ·
    refine ⟨23062233500562739997687491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30749644667416986663583321 23062233500562739997687491)
    ·
      refine ⟨34593350250844109996531237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23062233500562739997687491 34593350250844109996531237)
      ·
        refine ⟨6486253172033270624349607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34593350250844109996531237 6486253172033270624349607)
        ·
          refine ⟨9729379758049905936524411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6486253172033270624349607 9729379758049905936524411)
          ·
            refine ⟨14594069637074858904786617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729379758049905936524411 14594069637074858904786617)
            ·
              refine ⟨10945552227806144178589963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14594069637074858904786617 10945552227806144178589963)
              ·
                refine ⟨16418328341709216267884945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945552227806144178589963 16418328341709216267884945)
                ·
                  refine ⟨12313746256281912200913709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16418328341709216267884945 12313746256281912200913709)
                  ·
                    refine ⟨4617654846105717075342641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12313746256281912200913709 4617654846105717075342641)
                    ·
                      refine ⟨3463241134579287806506981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4617654846105717075342641 3463241134579287806506981)
                      ·
                        rfl

theorem cell23_6744638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6744638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744638 prefixEnd_6744638 := by exact prefixLift 6744638
  have htrace : WordTrace (prefixWord ++ tailWord_6744638) baseStart_6744638 baseEnd_6744638 := by
    simpa [prefixWord, tailWord_6744638, baseEnd_6744638] using wordTrace_append hprefix tailTrace_6744638
  have hstable : (prefixWord ++ tailWord_6744638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744638).length < 2 ^ (prefixWord ++ tailWord_6744638).sum := by decide
  have hdescent : baseEnd_6744638 < baseStart_6744638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744647 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_6744647 : Nat := 118140960795 + 6744647 * 2 ^ 59
def prefixEnd_6744647 : Nat := 4983230072969 + 3 ^ 40 * 6744647 * 2
def baseEnd_6744647 : Nat := 3463245755905178271294439

theorem tailTrace_6744647 : CollatzResearch.WordTrace tailWord_6744647 prefixEnd_6744647 3463245755905178271294439 := by
  unfold tailWord_6744647
  simp only [CollatzResearch.WordTrace]
  refine ⟨245997485596303287845744195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163998323730868858563829463 245997485596303287845744195)
  ·
    refine ⟨368996228394454931768616293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245997485596303287845744195 368996228394454931768616293)
    ·
      refine ⟨69186792823960299706615555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368996228394454931768616293 69186792823960299706615555)
      ·
        refine ⟨103780189235940449559923333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69186792823960299706615555 103780189235940449559923333)
        ·
          refine ⟨19458785481738834292485625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103780189235940449559923333 19458785481738834292485625)
          ·
            refine ⟨14594089111304125719364219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19458785481738834292485625 14594089111304125719364219)
            ·
              refine ⟨21891133666956188579046329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14594089111304125719364219 21891133666956188579046329)
              ·
                refine ⟨16418350250217141434284747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21891133666956188579046329 16418350250217141434284747)
                ·
                  refine ⟨24627525375325712151427121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16418350250217141434284747 24627525375325712151427121)
                  ·
                    refine ⟨18470644031494284113570341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24627525375325712151427121 18470644031494284113570341)
                    ·
                      refine ⟨3463245755905178271294439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18470644031494284113570341 3463245755905178271294439)
                      ·
                        rfl

theorem cell23_6744647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_6744647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744647 prefixEnd_6744647 := by exact prefixLift 6744647
  have htrace : WordTrace (prefixWord ++ tailWord_6744647) baseStart_6744647 baseEnd_6744647 := by
    simpa [prefixWord, tailWord_6744647, baseEnd_6744647] using wordTrace_append hprefix tailTrace_6744647
  have hstable : (prefixWord ++ tailWord_6744647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744647).length < 2 ^ (prefixWord ++ tailWord_6744647).sum := by decide
  have hdescent : baseEnd_6744647 < baseStart_6744647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744684 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_6744684 : Nat := 118140960795 + 6744684 * 2 ^ 59
def prefixEnd_6744684 : Nat := 4983230072969 + 3 ^ 40 * 6744684 * 2
def baseEnd_6744684 : Nat := 3463264754689394626531769

theorem tailTrace_6744684 : CollatzResearch.WordTrace tailWord_6744684 prefixEnd_6744684 3463264754689394626531769 := by
  unfold tailWord_6744684
  simp only [CollatzResearch.WordTrace]
  refine ⟨122999417548584621582420553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163999223398112828776560737 122999417548584621582420553)
  ·
    refine ⟨92249563161438466186815415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122999417548584621582420553 92249563161438466186815415)
    ·
      refine ⟨138374344742157699280223123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92249563161438466186815415 138374344742157699280223123)
      ·
        refine ⟨207561517113236548920334685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138374344742157699280223123 207561517113236548920334685)
        ·
          refine ⟨77835568917463705845125507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207561517113236548920334685 77835568917463705845125507)
          ·
            refine ⟨116753353376195558767688261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77835568917463705845125507 116753353376195558767688261)
            ·
              refine ⟨21891253758036667268941549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116753353376195558767688261 21891253758036667268941549)
              ·
                refine ⟨8209220159263750225853081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21891253758036667268941549 8209220159263750225853081)
                ·
                  refine ⟨6156915119447812669389811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8209220159263750225853081 6156915119447812669389811)
                  ·
                    refine ⟨9235372679171719004084717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156915119447812669389811 9235372679171719004084717)
                    ·
                      refine ⟨3463264754689394626531769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9235372679171719004084717 3463264754689394626531769)
                      ·
                        rfl

theorem cell23_6744684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_6744684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744684 prefixEnd_6744684 := by exact prefixLift 6744684
  have htrace : WordTrace (prefixWord ++ tailWord_6744684) baseStart_6744684 baseEnd_6744684 := by
    simpa [prefixWord, tailWord_6744684, baseEnd_6744684] using wordTrace_append hprefix tailTrace_6744684
  have hstable : (prefixWord ++ tailWord_6744684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744684).length < 2 ^ (prefixWord ++ tailWord_6744684).sum := by decide
  have hdescent : baseEnd_6744684 < baseStart_6744684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744814 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_6744814 : Nat := 118140960795 + 6744814 * 2 ^ 59
def prefixEnd_6744814 : Nat := 4983230072969 + 3 ^ 40 * 6744814 * 2
def baseEnd_6744814 : Nat := 3463331507174479117906171

theorem tailTrace_6744814 : CollatzResearch.WordTrace tailWord_6744814 prefixEnd_6744814 3463331507174479117906171 := by
  unfold tailWord_6744814
  simp only [CollatzResearch.WordTrace]
  refine ⟨30750447073337284420884187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164002384391132183578048997 30750447073337284420884187)
  ·
    refine ⟨46125670610005926631326281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30750447073337284420884187 46125670610005926631326281)
    ·
      refine ⟨34594252957504444973494711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46125670610005926631326281 34594252957504444973494711)
      ·
        refine ⟨51891379436256667460242067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34594252957504444973494711 51891379436256667460242067)
        ·
          refine ⟨77837069154385001190363101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51891379436256667460242067 77837069154385001190363101)
          ·
            refine ⟨29188900932894375446386163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77837069154385001190363101 29188900932894375446386163)
            ·
              refine ⟨43783351399341563169579245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29188900932894375446386163 43783351399341563169579245)
              ·
                refine ⟨16418756774753086188592217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43783351399341563169579245 16418756774753086188592217)
                ·
                  refine ⟨12314067581064814641444163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16418756774753086188592217 12314067581064814641444163)
                  ·
                    refine ⟨18471101371597221962166245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12314067581064814641444163 18471101371597221962166245)
                    ·
                      refine ⟨3463331507174479117906171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18471101371597221962166245 3463331507174479117906171)
                      ·
                        rfl

theorem cell23_6744814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_6744814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744814 prefixEnd_6744814 := by exact prefixLift 6744814
  have htrace : WordTrace (prefixWord ++ tailWord_6744814) baseStart_6744814 baseEnd_6744814 := by
    simpa [prefixWord, tailWord_6744814, baseEnd_6744814] using wordTrace_append hprefix tailTrace_6744814
  have hstable : (prefixWord ++ tailWord_6744814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744814).length < 2 ^ (prefixWord ++ tailWord_6744814).sum := by decide
  have hdescent : baseEnd_6744814 < baseStart_6744814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744868 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_6744868 : Nat := 118140960795 + 6744868 * 2 ^ 59
def prefixEnd_6744868 : Nat := 4983230072969 + 3 ^ 40 * 6744868 * 2
def baseEnd_6744868 : Nat := 3463359235129821906630923

theorem tailTrace_6744868 : CollatzResearch.WordTrace tailWord_6744868 prefixEnd_6744868 3463359235129821906630923 := by
  unfold tailWord_6744868
  simp only [CollatzResearch.WordTrace]
  refine ⟨123002773064251321294769629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164003697419001761726359505 123002773064251321294769629)
  ·
    refine ⟨46126039899094245485538611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123002773064251321294769629 46126039899094245485538611)
    ·
      refine ⟨69189059848641368228307917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46126039899094245485538611 69189059848641368228307917)
      ·
        refine ⟨25945897443240513085615469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69189059848641368228307917 25945897443240513085615469)
        ·
          refine ⟨9729711541215192407105801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25945897443240513085615469 9729711541215192407105801)
          ·
            refine ⟨7297283655911394305329351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9729711541215192407105801 7297283655911394305329351)
            ·
              refine ⟨10945925483867091457994027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7297283655911394305329351 10945925483867091457994027)
              ·
                refine ⟨16418888225800637186991041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945925483867091457994027 16418888225800637186991041)
                ·
                  refine ⟨12314166169350477890243281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16418888225800637186991041 12314166169350477890243281)
                  ·
                    refine ⟨9235624627012858417682461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12314166169350477890243281 9235624627012858417682461)
                    ·
                      refine ⟨3463359235129821906630923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9235624627012858417682461 3463359235129821906630923)
                      ·
                        rfl

theorem cell23_6744868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_6744868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744868 prefixEnd_6744868 := by exact prefixLift 6744868
  have htrace : WordTrace (prefixWord ++ tailWord_6744868) baseStart_6744868 baseEnd_6744868 := by
    simpa [prefixWord, tailWord_6744868, baseEnd_6744868] using wordTrace_append hprefix tailTrace_6744868
  have hstable : (prefixWord ++ tailWord_6744868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744868).length < 2 ^ (prefixWord ++ tailWord_6744868).sum := by decide
  have hdescent : baseEnd_6744868 < baseStart_6744868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744921 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 4]
def baseStart_6744921 : Nat := 118140960795 + 6744921 * 2 ^ 59
def prefixEnd_6744921 : Nat := 4983230072969 + 3 ^ 40 * 6744921 * 2
def baseEnd_6744921 : Nat := 3463386449604510199268179

theorem tailTrace_6744921 : CollatzResearch.WordTrace tailWord_6744921 prefixEnd_6744921 3463386449604510199268179 := by
  unfold tailWord_6744921
  simp only [CollatzResearch.WordTrace]
  refine ⟨246007479197310632641218617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164004986131540421760812411 246007479197310632641218617)
  ·
    refine ⟨184505609397982974480913963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246007479197310632641218617 184505609397982974480913963)
    ·
      refine ⟨276758414096974461721370945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184505609397982974480913963 276758414096974461721370945)
      ·
        refine ⟨207568810572730846291028209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276758414096974461721370945 207568810572730846291028209)
        ·
          refine ⟨155676607929548134718271157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207568810572730846291028209 155676607929548134718271157)
          ·
            refine ⟨14594681993395137629837921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155676607929548134718271157 14594681993395137629837921)
            ·
              refine ⟨10946011495046353222378441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14594681993395137629837921 10946011495046353222378441)
              ·
                refine ⟨8209508621284764916783831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10946011495046353222378441 8209508621284764916783831)
                ·
                  refine ⟨12314262931927147375175747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8209508621284764916783831 12314262931927147375175747)
                  ·
                    refine ⟨18471394397890721062763621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12314262931927147375175747 18471394397890721062763621)
                    ·
                      refine ⟨3463386449604510199268179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18471394397890721062763621 3463386449604510199268179)
                      ·
                        rfl

theorem cell23_6744921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_6744921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744921 prefixEnd_6744921 := by exact prefixLift 6744921
  have htrace : WordTrace (prefixWord ++ tailWord_6744921) baseStart_6744921 baseEnd_6744921 := by
    simpa [prefixWord, tailWord_6744921, baseEnd_6744921] using wordTrace_append hprefix tailTrace_6744921
  have hstable : (prefixWord ++ tailWord_6744921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744921).length < 2 ^ (prefixWord ++ tailWord_6744921).sum := by decide
  have hdescent : baseEnd_6744921 < baseStart_6744921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744927 : List Nat := [1, 1, 2, 3, 1, 3, 3, 9]
def baseStart_6744927 : Nat := 118140960795 + 6744927 * 2 ^ 59
def prefixEnd_6744927 : Nat := 4983230072969 + 3 ^ 40 * 6744927 * 2
def baseEnd_6744927 : Nat := 128273686314386562066413

theorem tailTrace_6744927 : CollatzResearch.WordTrace tailWord_6744927 prefixEnd_6744927 128273686314386562066413 := by
  unfold tailWord_6744927
  simp only [CollatzResearch.WordTrace]
  refine ⟨246007698035288895665937035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164005132023525930443958023 246007698035288895665937035)
  ·
    refine ⟨369011547052933343498905553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246007698035288895665937035 369011547052933343498905553)
    ·
      refine ⟨276758660289700007624179165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369011547052933343498905553 276758660289700007624179165)
      ·
        refine ⟨103784497608637502859067187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276758660289700007624179165 103784497608637502859067187)
        ·
          refine ⟨155676746412956254288600781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103784497608637502859067187 155676746412956254288600781)
          ·
            refine ⟨58378779904858595358225293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155676746412956254288600781 58378779904858595358225293)
            ·
              refine ⟨21892042464321973259334485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58378779904858595358225293 21892042464321973259334485)
              ·
                refine ⟨128273686314386562066413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21892042464321973259334485 128273686314386562066413)
                ·
                  rfl

theorem cell23_6744927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 9].length) (baseStart_6744927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744927 prefixEnd_6744927 := by exact prefixLift 6744927
  have htrace : WordTrace (prefixWord ++ tailWord_6744927) baseStart_6744927 baseEnd_6744927 := by
    simpa [prefixWord, tailWord_6744927, baseEnd_6744927] using wordTrace_append hprefix tailTrace_6744927
  have hstable : (prefixWord ++ tailWord_6744927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744927).length < 2 ^ (prefixWord ++ tailWord_6744927).sum := by decide
  have hdescent : baseEnd_6744927 < baseStart_6744927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744977 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_6744977 : Nat := 118140960795 + 6744977 * 2 ^ 59
def prefixEnd_6744977 : Nat := 4983230072969 + 3 ^ 40 * 6744977 * 2
def baseEnd_6744977 : Nat := 3463415204521161980167921

theorem tailTrace_6744977 : CollatzResearch.WordTrace tailWord_6744977 prefixEnd_6744977 3463415204521161980167921 := by
  unfold tailWord_6744977
  simp only [CollatzResearch.WordTrace]
  refine ⟨246009521685107754205257185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164006347790071836136838123 246009521685107754205257185)
  ·
    refine ⟨184507141263830815653942889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246009521685107754205257185 184507141263830815653942889)
    ·
      refine ⟨138380355947873111740457167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184507141263830815653942889 138380355947873111740457167)
      ·
        refine ⟨207570533921809667610685751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138380355947873111740457167 207570533921809667610685751)
        ·
          refine ⟨311355800882714501416028627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207570533921809667610685751 311355800882714501416028627)
          ·
            refine ⟨467033701324071752124042941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311355800882714501416028627 467033701324071752124042941)
            ·
              refine ⟨175137637996526907046516103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 467033701324071752124042941 175137637996526907046516103)
              ·
                refine ⟨262706456994790360569774155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175137637996526907046516103 262706456994790360569774155)
                ·
                  refine ⟨394059685492185540854661233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262706456994790360569774155 394059685492185540854661233)
                  ·
                    refine ⟨295544764119139155640995925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 394059685492185540854661233 295544764119139155640995925)
                    ·
                      refine ⟨3463415204521161980167921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 295544764119139155640995925 3463415204521161980167921)
                      ·
                        rfl

theorem cell23_6744977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_6744977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744977 prefixEnd_6744977 := by exact prefixLift 6744977
  have htrace : WordTrace (prefixWord ++ tailWord_6744977) baseStart_6744977 baseEnd_6744977 := by
    simpa [prefixWord, tailWord_6744977, baseEnd_6744977] using wordTrace_append hprefix tailTrace_6744977
  have hstable : (prefixWord ++ tailWord_6744977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744977).length < 2 ^ (prefixWord ++ tailWord_6744977).sum := by decide
  have hdescent : baseEnd_6744977 < baseStart_6744977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6744988 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6744988 : Nat := 118140960795 + 6744988 * 2 ^ 59
def prefixEnd_6744988 : Nat := 4983230072969 + 3 ^ 40 * 6744988 * 2
def baseEnd_6744988 : Nat := 3463420852808361437130371

theorem tailTrace_6744988 : CollatzResearch.WordTrace tailWord_6744988 prefixEnd_6744988 3463420852808361437130371 := by
  unfold tailWord_6744988
  simp only [CollatzResearch.WordTrace]
  refine ⟨123004961444033951541953809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164006615258711935389271745 123004961444033951541953809)
  ·
    refine ⟨92253721083025463656465357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123004961444033951541953809 92253721083025463656465357)
    ·
      refine ⟨34595145406134548871174509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92253721083025463656465357 34595145406134548871174509)
      ·
        refine ⟨12973179527300455826690441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34595145406134548871174509 12973179527300455826690441)
        ·
          refine ⟨9729884645475341870017831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12973179527300455826690441 9729884645475341870017831)
          ·
            refine ⟨14594826968213012805026747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729884645475341870017831 14594826968213012805026747)
            ·
              refine ⟨21892240452319519207540121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14594826968213012805026747 21892240452319519207540121)
              ·
                refine ⟨16419180339239639405655091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21892240452319519207540121 16419180339239639405655091)
                ·
                  refine ⟨24628770508859459108482637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16419180339239639405655091 24628770508859459108482637)
                  ·
                    refine ⟨9235788940822297165680989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24628770508859459108482637 9235788940822297165680989)
                    ·
                      refine ⟨3463420852808361437130371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9235788940822297165680989 3463420852808361437130371)
                      ·
                        rfl

theorem cell23_6744988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6744988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6744988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6744988 prefixEnd_6744988 := by exact prefixLift 6744988
  have htrace : WordTrace (prefixWord ++ tailWord_6744988) baseStart_6744988 baseEnd_6744988 := by
    simpa [prefixWord, tailWord_6744988, baseEnd_6744988] using wordTrace_append hprefix tailTrace_6744988
  have hstable : (prefixWord ++ tailWord_6744988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6744988).length < 2 ^ (prefixWord ++ tailWord_6744988).sum := by decide
  have hdescent : baseEnd_6744988 < baseStart_6744988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6744988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745021 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_6745021 : Nat := 118140960795 + 6745021 * 2 ^ 59
def prefixEnd_6745021 : Nat := 4983230072969 + 3 ^ 40 * 6745021 * 2
def baseEnd_6745021 : Nat := 1154479265889986602672573

theorem tailTrace_6745021 : CollatzResearch.WordTrace tailWord_6745021 prefixEnd_6745021 1154479265889986602672573 := by
  unfold tailWord_6745021
  simp only [CollatzResearch.WordTrace]
  refine ⟨246011126496948349719858917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164007417664632233146572611 246011126496948349719858917)
  ·
    refine ⟨46127086218177815572473547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246011126496948349719858917 46127086218177815572473547)
    ·
      refine ⟨69190629327266723358710321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46127086218177815572473547 69190629327266723358710321)
      ·
        refine ⟨51892971995450042519032741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69190629327266723358710321 51892971995450042519032741)
        ·
          refine ⟨9729932249146882972318639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51892971995450042519032741 9729932249146882972318639)
          ·
            refine ⟨14594898373720324458477959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729932249146882972318639 14594898373720324458477959)
            ·
              refine ⟨21892347560580486687716939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14594898373720324458477959 21892347560580486687716939)
              ·
                refine ⟨32838521340870730031575409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21892347560580486687716939 32838521340870730031575409)
                ·
                  refine ⟨24628891005653047523681557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32838521340870730031575409 24628891005653047523681557)
                  ·
                    refine ⟨1154479265889986602672573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24628891005653047523681557 1154479265889986602672573)
                    ·
                      rfl

theorem cell23_6745021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_6745021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745021 prefixEnd_6745021 := by exact prefixLift 6745021
  have htrace : WordTrace (prefixWord ++ tailWord_6745021) baseStart_6745021 baseEnd_6745021 := by
    simpa [prefixWord, tailWord_6745021, baseEnd_6745021] using wordTrace_append hprefix tailTrace_6745021
  have hstable : (prefixWord ++ tailWord_6745021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745021).length < 2 ^ (prefixWord ++ tailWord_6745021).sum := by decide
  have hdescent : baseEnd_6745021 < baseStart_6745021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745024 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_6745024 : Nat := 118140960795 + 6745024 * 2 ^ 59
def prefixEnd_6745024 : Nat := 4983230072969 + 3 ^ 40 * 6745024 * 2
def baseEnd_6745024 : Nat := 3463439338111923296280205

theorem tailTrace_6745024 : CollatzResearch.WordTrace tailWord_6745024 prefixEnd_6745024 3463439338111923296280205 := by
  unfold tailWord_6745024
  simp only [CollatzResearch.WordTrace]
  refine ⟨123005617957968740616109063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164007490610624987488145417 123005617957968740616109063)
  ·
    refine ⟨184508426936953110924163595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123005617957968740616109063 184508426936953110924163595)
    ·
      refine ⟨276762640405429666386245393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184508426936953110924163595 276762640405429666386245393)
      ·
        refine ⟨207571980304072249789684045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276762640405429666386245393 207571980304072249789684045)
        ·
          refine ⟨77839492614027093671131517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207571980304072249789684045 77839492614027093671131517)
          ·
            refine ⟨29189809730260160126674319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77839492614027093671131517 29189809730260160126674319)
            ·
              refine ⟨43784714595390240190011479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29189809730260160126674319 43784714595390240190011479)
              ·
                refine ⟨65677071893085360285017219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43784714595390240190011479 65677071893085360285017219)
                ·
                  refine ⟨98515607839628040427525829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65677071893085360285017219 98515607839628040427525829)
                  ·
                    refine ⟨18471676469930257580161093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98515607839628040427525829 18471676469930257580161093)
                    ·
                      refine ⟨3463439338111923296280205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18471676469930257580161093 3463439338111923296280205)
                      ·
                        rfl

theorem cell23_6745024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_6745024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745024 prefixEnd_6745024 := by exact prefixLift 6745024
  have htrace : WordTrace (prefixWord ++ tailWord_6745024) baseStart_6745024 baseEnd_6745024 := by
    simpa [prefixWord, tailWord_6745024, baseEnd_6745024] using wordTrace_append hprefix tailTrace_6745024
  have hstable : (prefixWord ++ tailWord_6745024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745024).length < 2 ^ (prefixWord ++ tailWord_6745024).sum := by decide
  have hdescent : baseEnd_6745024 < baseStart_6745024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745058 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6745058 : Nat := 118140960795 + 6745058 * 2 ^ 59
def prefixEnd_6745058 : Nat := 4983230072969 + 3 ^ 40 * 6745058 * 2
def baseEnd_6745058 : Nat := 3463456796454176163255049

theorem tailTrace_6745058 : CollatzResearch.WordTrace tailWord_6745058 prefixEnd_6745058 3463456796454176163255049 := by
  unfold tailWord_6745058
  simp only [CollatzResearch.WordTrace]
  refine ⟨61503118999453576259738957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164008317331876203359303885 61503118999453576259738957)
  ·
    refine ⟨23063669624795091097402109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61503118999453576259738957 23063669624795091097402109)
    ·
      refine ⟨8648876109298159161525791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23063669624795091097402109 8648876109298159161525791)
      ·
        refine ⟨12973314163947238742288687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8648876109298159161525791 12973314163947238742288687)
        ·
          refine ⟨19459971245920858113433031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973314163947238742288687 19459971245920858113433031)
          ·
            refine ⟨29189956868881287170149547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19459971245920858113433031 29189956868881287170149547)
            ·
              refine ⟨43784935303321930755224321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29189956868881287170149547 43784935303321930755224321)
              ·
                refine ⟨32838701477491448066418241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43784935303321930755224321 32838701477491448066418241)
                ·
                  refine ⟨24629026108118586049813681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32838701477491448066418241 24629026108118586049813681)
                  ·
                    refine ⟨18471769581088939537360261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24629026108118586049813681 18471769581088939537360261)
                    ·
                      refine ⟨3463456796454176163255049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18471769581088939537360261 3463456796454176163255049)
                      ·
                        rfl

theorem cell23_6745058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6745058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745058 prefixEnd_6745058 := by exact prefixLift 6745058
  have htrace : WordTrace (prefixWord ++ tailWord_6745058) baseStart_6745058 baseEnd_6745058 := by
    simpa [prefixWord, tailWord_6745058, baseEnd_6745058] using wordTrace_append hprefix tailTrace_6745058
  have hstable : (prefixWord ++ tailWord_6745058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745058).length < 2 ^ (prefixWord ++ tailWord_6745058).sum := by decide
  have hdescent : baseEnd_6745058 < baseStart_6745058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745078 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_6745078 : Nat := 118140960795 + 6745078 * 2 ^ 59
def prefixEnd_6745078 : Nat := 4983230072969 + 3 ^ 40 * 6745078 * 2
def baseEnd_6745078 : Nat := 3463467066067266085004957

theorem tailTrace_6745078 : CollatzResearch.WordTrace tailWord_6745078 prefixEnd_6745078 3463467066067266085004957 := by
  unfold tailWord_6745078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15375825341108865528417743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164008803638494565636455925 15375825341108865528417743)
  ·
    refine ⟨23063738011663298292626615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15375825341108865528417743 23063738011663298292626615)
    ·
      refine ⟨34595607017494947438939923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23063738011663298292626615 34595607017494947438939923)
      ·
        refine ⟨51893410526242421158409885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34595607017494947438939923 51893410526242421158409885)
        ·
          refine ⟨19460028947340907934403707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51893410526242421158409885 19460028947340907934403707)
          ·
            refine ⟨29190043421011361901605561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19460028947340907934403707 29190043421011361901605561)
            ·
              refine ⟨21892532565758521426204171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29190043421011361901605561 21892532565758521426204171)
              ·
                refine ⟨32838798848637782139306257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21892532565758521426204171 32838798848637782139306257)
                ·
                  refine ⟨24629099136478336604479693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32838798848637782139306257 24629099136478336604479693)
                  ·
                    refine ⟨9235912176179376226679885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24629099136478336604479693 9235912176179376226679885)
                    ·
                      refine ⟨3463467066067266085004957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9235912176179376226679885 3463467066067266085004957)
                      ·
                        rfl

theorem cell23_6745078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_6745078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745078 prefixEnd_6745078 := by exact prefixLift 6745078
  have htrace : WordTrace (prefixWord ++ tailWord_6745078) baseStart_6745078 baseEnd_6745078 := by
    simpa [prefixWord, tailWord_6745078, baseEnd_6745078] using wordTrace_append hprefix tailTrace_6745078
  have hstable : (prefixWord ++ tailWord_6745078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745078).length < 2 ^ (prefixWord ++ tailWord_6745078).sum := by decide
  have hdescent : baseEnd_6745078 < baseStart_6745078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745178 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2]
def baseStart_6745178 : Nat := 118140960795 + 6745178 * 2 ^ 59
def prefixEnd_6745178 : Nat := 4983230072969 + 3 ^ 40 * 6745178 * 2
def baseEnd_6745178 : Nat := 3463518414132715693754497

theorem tailTrace_6745178 : CollatzResearch.WordTrace tailWord_6745178 prefixEnd_6745178 3463518414132715693754497 := by
  unfold tailWord_6745178
  simp only [CollatzResearch.WordTrace]
  refine ⟨61504213189344891383331047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164011235171586377022216125 61504213189344891383331047)
  ·
    refine ⟨92256319784017337074996571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61504213189344891383331047 92256319784017337074996571)
    ·
      refine ⟨138384479676026005612494857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92256319784017337074996571 138384479676026005612494857)
      ·
        refine ⟨103788359757019504209371143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138384479676026005612494857 103788359757019504209371143)
        ·
          refine ⟨155682539635529256314056715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103788359757019504209371143 155682539635529256314056715)
          ·
            refine ⟨233523809453293884471085073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155682539635529256314056715 233523809453293884471085073)
            ·
              refine ⟨175142857089970413353313805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233523809453293884471085073 175142857089970413353313805)
              ·
                refine ⟨65678571408738905007492677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175142857089970413353313805 65678571408738905007492677)
                ·
                  refine ⟨12314732139138544688904877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65678571408738905007492677 12314732139138544688904877)
                  ·
                    refine ⟨4618024552176954258339329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12314732139138544688904877 4618024552176954258339329)
                    ·
                      refine ⟨3463518414132715693754497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618024552176954258339329 3463518414132715693754497)
                      ·
                        rfl

theorem cell23_6745178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_6745178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745178 prefixEnd_6745178 := by exact prefixLift 6745178
  have htrace : WordTrace (prefixWord ++ tailWord_6745178) baseStart_6745178 baseEnd_6745178 := by
    simpa [prefixWord, tailWord_6745178, baseEnd_6745178] using wordTrace_append hprefix tailTrace_6745178
  have hstable : (prefixWord ++ tailWord_6745178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745178).length < 2 ^ (prefixWord ++ tailWord_6745178).sum := by decide
  have hdescent : baseEnd_6745178 < baseStart_6745178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745225 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 1, 1, 4]
def baseStart_6745225 : Nat := 118140960795 + 6745225 * 2 ^ 59
def prefixEnd_6745225 : Nat := 4983230072969 + 3 ^ 40 * 6745225 * 2
def baseEnd_6745225 : Nat := 3463542547723477009866781

theorem tailTrace_6745225 : CollatzResearch.WordTrace tailWord_6745225 prefixEnd_6745225 3463542547723477009866781 := by
  unfold tailWord_6745225
  simp only [CollatzResearch.WordTrace]
  refine ⟨246018566988209292560285129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164012377992139528373523419 246018566988209292560285129)
  ·
    refine ⟨184513925241156969420213847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246018566988209292560285129 184513925241156969420213847)
    ·
      refine ⟨276770887861735454130320771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184513925241156969420213847 276770887861735454130320771)
      ·
        refine ⟨415156331792603181195481157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276770887861735454130320771 415156331792603181195481157)
        ·
          refine ⟨77841812211113096474152717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415156331792603181195481157 77841812211113096474152717)
          ·
            refine ⟨29190679579167411177807269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77841812211113096474152717 29190679579167411177807269)
            ·
              refine ⟨5473252421093889595838863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29190679579167411177807269 5473252421093889595838863)
              ·
                refine ⟨8209878631640834393758295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5473252421093889595838863 8209878631640834393758295)
                ·
                  refine ⟨12314817947461251590637443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8209878631640834393758295 12314817947461251590637443)
                  ·
                    refine ⟨18472226921191877385956165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12314817947461251590637443 18472226921191877385956165)
                    ·
                      refine ⟨3463542547723477009866781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18472226921191877385956165 3463542547723477009866781)
                      ·
                        rfl

theorem cell23_6745225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 1, 4].length) (baseStart_6745225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745225 prefixEnd_6745225 := by exact prefixLift 6745225
  have htrace : WordTrace (prefixWord ++ tailWord_6745225) baseStart_6745225 baseEnd_6745225 := by
    simpa [prefixWord, tailWord_6745225, baseEnd_6745225] using wordTrace_append hprefix tailTrace_6745225
  have hstable : (prefixWord ++ tailWord_6745225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745225).length < 2 ^ (prefixWord ++ tailWord_6745225).sum := by decide
  have hdescent : baseEnd_6745225 < baseStart_6745225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745241 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 3]
def baseStart_6745241 : Nat := 118140960795 + 6745241 * 2 ^ 59
def prefixEnd_6745241 : Nat := 4983230072969 + 3 ^ 40 * 6745241 * 2
def baseEnd_6745241 : Nat := 3463550763413948947266707

theorem tailTrace_6745241 : CollatzResearch.WordTrace tailWord_6745241 prefixEnd_6745241 3463550763413948947266707 := by
  unfold tailWord_6745241
  simp only [CollatzResearch.WordTrace]
  refine ⟨246019150556151327292867577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164012767037434218195245051 246019150556151327292867577)
  ·
    refine ⟨184514362917113495469650683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246019150556151327292867577 184514362917113495469650683)
    ·
      refine ⟨276771544375670243204476025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184514362917113495469650683 276771544375670243204476025)
      ·
        refine ⟨207578658281752682403357019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276771544375670243204476025 207578658281752682403357019)
        ·
          refine ⟨311367987422629023605035529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207578658281752682403357019 311367987422629023605035529)
          ·
            refine ⟨233525990566971767703776647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311367987422629023605035529 233525990566971767703776647)
            ·
              refine ⟨350288985850457651555664971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233525990566971767703776647 350288985850457651555664971)
              ·
                refine ⟨525433478775686477333497457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350288985850457651555664971 525433478775686477333497457)
                ·
                  refine ⟨394075109081764858000123093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525433478775686477333497457 394075109081764858000123093)
                  ·
                    refine ⟨9236135369103863859377885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 394075109081764858000123093 9236135369103863859377885)
                    ·
                      refine ⟨3463550763413948947266707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9236135369103863859377885 3463550763413948947266707)
                      ·
                        rfl

theorem cell23_6745241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_6745241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745241 prefixEnd_6745241 := by exact prefixLift 6745241
  have htrace : WordTrace (prefixWord ++ tailWord_6745241) baseStart_6745241 baseEnd_6745241 := by
    simpa [prefixWord, tailWord_6745241, baseEnd_6745241] using wordTrace_append hprefix tailTrace_6745241
  have hstable : (prefixWord ++ tailWord_6745241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745241).length < 2 ^ (prefixWord ++ tailWord_6745241).sum := by decide
  have hdescent : baseEnd_6745241 < baseStart_6745241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745242 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6745242 : Nat := 118140960795 + 6745242 * 2 ^ 59
def prefixEnd_6745242 : Nat := 4983230072969 + 3 ^ 40 * 6745242 * 2
def baseEnd_6745242 : Nat := 3463551276894603443354203

theorem tailTrace_6745242 : CollatzResearch.WordTrace tailWord_6745242 prefixEnd_6745242 3463551276894603443354203 := by
  unfold tailWord_6745242
  simp only [CollatzResearch.WordTrace]
  refine ⟨61504796757286926115913495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164012791352765136309102653 61504796757286926115913495)
  ·
    refine ⟨92257195135930389173870243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61504796757286926115913495 92257195135930389173870243)
    ·
      refine ⟨138385792703895583760805365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92257195135930389173870243 138385792703895583760805365)
      ·
        refine ⟨12973668065990210977575503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138385792703895583760805365 12973668065990210977575503)
        ·
          refine ⟨19460502098985316466363255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973668065990210977575503 19460502098985316466363255)
          ·
            refine ⟨29190753148477974699544883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19460502098985316466363255 29190753148477974699544883)
            ·
              refine ⟨43786129722716962049317325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29190753148477974699544883 43786129722716962049317325)
              ·
                refine ⟨16419798646018860768493997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43786129722716962049317325 16419798646018860768493997)
                ·
                  refine ⟨6157424492257072788185249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16419798646018860768493997 6157424492257072788185249)
                  ·
                    refine ⟨4618068369192804591138937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6157424492257072788185249 4618068369192804591138937)
                    ·
                      refine ⟨3463551276894603443354203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618068369192804591138937 3463551276894603443354203)
                      ·
                        rfl

theorem cell23_6745242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6745242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745242 prefixEnd_6745242 := by exact prefixLift 6745242
  have htrace : WordTrace (prefixWord ++ tailWord_6745242) baseStart_6745242 baseEnd_6745242 := by
    simpa [prefixWord, tailWord_6745242, baseEnd_6745242] using wordTrace_append hprefix tailTrace_6745242
  have hstable : (prefixWord ++ tailWord_6745242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745242).length < 2 ^ (prefixWord ++ tailWord_6745242).sum := by decide
  have hdescent : baseEnd_6745242 < baseStart_6745242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745252 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_6745252 : Nat := 118140960795 + 6745252 * 2 ^ 59
def prefixEnd_6745252 : Nat := 4983230072969 + 3 ^ 40 * 6745252 * 2
def baseEnd_6745252 : Nat := 1154518803900382801409719

theorem tailTrace_6745252 : CollatzResearch.WordTrace tailWord_6745252 prefixEnd_6745252 1154518803900382801409719 := by
  unfold tailWord_6745252
  simp only [CollatzResearch.WordTrace]
  refine ⟨123009775879555738085759005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164013034506074317447678673 123009775879555738085759005)
  ·
    refine ⟨46128665954833401782159627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123009775879555738085759005 46128665954833401782159627)
    ·
      refine ⟨69192998932250102673239441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46128665954833401782159627 69192998932250102673239441)
      ·
        refine ⟨51894749199187577004929581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69192998932250102673239441 51894749199187577004929581)
        ·
          refine ⟨19460530949695341376848593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51894749199187577004929581 19460530949695341376848593)
          ·
            refine ⟨14595398212271506032636445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19460530949695341376848593 14595398212271506032636445)
            ·
              refine ⟨5473274329601814762238667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14595398212271506032636445 5473274329601814762238667)
              ·
                refine ⟨8209911494402722143358001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5473274329601814762238667 8209911494402722143358001)
                ·
                  refine ⟨6157433620802041607518501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8209911494402722143358001 6157433620802041607518501)
                  ·
                    refine ⟨1154518803900382801409719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6157433620802041607518501 1154518803900382801409719)
                    ·
                      rfl

theorem cell23_6745252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_6745252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745252 prefixEnd_6745252 := by exact prefixLift 6745252
  have htrace : WordTrace (prefixWord ++ tailWord_6745252) baseStart_6745252 baseEnd_6745252 := by
    simpa [prefixWord, tailWord_6745252, baseEnd_6745252] using wordTrace_append hprefix tailTrace_6745252
  have hstable : (prefixWord ++ tailWord_6745252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745252).length < 2 ^ (prefixWord ++ tailWord_6745252).sum := by decide
  have hdescent : baseEnd_6745252 < baseStart_6745252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745255 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_6745255 : Nat := 118140960795 + 6745255 * 2 ^ 59
def prefixEnd_6745255 : Nat := 4983230072969 + 3 ^ 40 * 6745255 * 2
def baseEnd_6745255 : Nat := 3463557952143111892491643

theorem tailTrace_6745255 : CollatzResearch.WordTrace tailWord_6745255 prefixEnd_6745255 3463557952143111892491643 := by
  unfold tailWord_6745255
  simp only [CollatzResearch.WordTrace]
  refine ⟨246019661178100607683877219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164013107452067071789251479 246019661178100607683877219)
  ·
    refine ⟨369029491767150911525815829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246019661178100607683877219 369029491767150911525815829)
    ·
      refine ⟨17298257426585198977772617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 369029491767150911525815829 17298257426585198977772617)
      ·
        refine ⟨12973693069938899233329463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17298257426585198977772617 12973693069938899233329463)
        ·
          refine ⟨19460539604908348849994195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973693069938899233329463 19460539604908348849994195)
          ·
            refine ⟨29190809407362523274991293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19460539604908348849994195 29190809407362523274991293)
            ·
              refine ⟨10946553527760946228121735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29190809407362523274991293 10946553527760946228121735)
              ·
                refine ⟨16419830291641419342182603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10946553527760946228121735 16419830291641419342182603)
                ·
                  refine ⟨24629745437462129013273905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16419830291641419342182603 24629745437462129013273905)
                  ·
                    refine ⟨18472309078096596759955429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24629745437462129013273905 18472309078096596759955429)
                    ·
                      refine ⟨3463557952143111892491643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18472309078096596759955429 3463557952143111892491643)
                      ·
                        rfl

theorem cell23_6745255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_6745255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745255 prefixEnd_6745255 := by exact prefixLift 6745255
  have htrace : WordTrace (prefixWord ++ tailWord_6745255) baseStart_6745255 baseEnd_6745255 := by
    simpa [prefixWord, tailWord_6745255, baseEnd_6745255] using wordTrace_append hprefix tailTrace_6745255
  have hstable : (prefixWord ++ tailWord_6745255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745255).length < 2 ^ (prefixWord ++ tailWord_6745255).sum := by decide
  have hdescent : baseEnd_6745255 < baseStart_6745255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745265 : List Nat := [1, 2, 2, 5, 1, 3, 2, 7]
def baseStart_6745265 : Nat := 118140960795 + 6745265 * 2 ^ 59
def prefixEnd_6745265 : Nat := 4983230072969 + 3 ^ 40 * 6745265 * 2
def baseEnd_6745265 : Nat := 128280114331468772346911

theorem tailTrace_6745265 : CollatzResearch.WordTrace tailWord_6745265 prefixEnd_6745265 128280114331468772346911 := by
  unfold tailWord_6745265
  simp only [CollatzResearch.WordTrace]
  refine ⟨246020025908064379391741249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164013350605376252927827499 246020025908064379391741249)
  ·
    refine ⟨184515019431048284543805937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246020025908064379391741249 184515019431048284543805937)
    ·
      refine ⟨138386264573286213407854453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184515019431048284543805937 138386264573286213407854453)
      ·
        refine ⟨12973712303745582506986355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138386264573286213407854453 12973712303745582506986355)
        ·
          refine ⟨19460568455618373760479533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973712303745582506986355 19460568455618373760479533)
          ·
            refine ⟨7297713170856890160179825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19460568455618373760479533 7297713170856890160179825)
            ·
              refine ⟨5473284878142667620134869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7297713170856890160179825 5473284878142667620134869)
              ·
                refine ⟨128280114331468772346911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5473284878142667620134869 128280114331468772346911)
                ·
                  rfl

theorem cell23_6745265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 7].length) (baseStart_6745265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745265 prefixEnd_6745265 := by exact prefixLift 6745265
  have htrace : WordTrace (prefixWord ++ tailWord_6745265) baseStart_6745265 baseEnd_6745265 := by
    simpa [prefixWord, tailWord_6745265, baseEnd_6745265] using wordTrace_append hprefix tailTrace_6745265
  have hstable : (prefixWord ++ tailWord_6745265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745265).length < 2 ^ (prefixWord ++ tailWord_6745265).sum := by decide
  have hdescent : baseEnd_6745265 < baseStart_6745265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745270 : List Nat := [5, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6745270 : Nat := 118140960795 + 6745270 * 2 ^ 59
def prefixEnd_6745270 : Nat := 4983230072969 + 3 ^ 40 * 6745270 * 2
def baseEnd_6745270 : Nat := 3463565654352929333804075

theorem tailTrace_6745270 : CollatzResearch.WordTrace tailWord_6745270 prefixEnd_6745270 3463565654352929333804075 := by
  unfold tailWord_6745270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15376263017065391577854579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164013472182030843497115509 15376263017065391577854579)
  ·
    refine ⟨23064394525598087366781869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15376263017065391577854579 23064394525598087366781869)
    ·
      refine ⟨8649147947099282762543201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23064394525598087366781869 8649147947099282762543201)
      ·
        refine ⟨6486860960324462071907401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8649147947099282762543201 6486860960324462071907401)
        ·
          refine ⟨4865145720243346553930551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6486860960324462071907401 4865145720243346553930551)
          ·
            refine ⟨7297718580365019830895827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865145720243346553930551 7297718580365019830895827)
            ·
              refine ⟨10946577870547529746343741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7297718580365019830895827 10946577870547529746343741)
              ·
                refine ⟨4104966701455323654878903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10946577870547529746343741 4104966701455323654878903)
                ·
                  refine ⟨6157450052182985482318355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104966701455323654878903 6157450052182985482318355)
                  ·
                    refine ⟨9236175078274478223477533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6157450052182985482318355 9236175078274478223477533)
                    ·
                      refine ⟨3463565654352929333804075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9236175078274478223477533 3463565654352929333804075)
                      ·
                        rfl

theorem cell23_6745270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6745270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745270 prefixEnd_6745270 := by exact prefixLift 6745270
  have htrace : WordTrace (prefixWord ++ tailWord_6745270) baseStart_6745270 baseEnd_6745270 := by
    simpa [prefixWord, tailWord_6745270, baseEnd_6745270] using wordTrace_append hprefix tailTrace_6745270
  have hstable : (prefixWord ++ tailWord_6745270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745270).length < 2 ^ (prefixWord ++ tailWord_6745270).sum := by decide
  have hdescent : baseEnd_6745270 < baseStart_6745270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745271 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_6745271 : Nat := 118140960795 + 6745271 * 2 ^ 59
def prefixEnd_6745271 : Nat := 4983230072969 + 3 ^ 40 * 6745271 * 2
def baseEnd_6745271 : Nat := 3463566167833583829891569

theorem tailTrace_6745271 : CollatzResearch.WordTrace tailWord_6745271 prefixEnd_6745271 3463566167833583829891569 := by
  unfold tailWord_6745271
  simp only [CollatzResearch.WordTrace]
  refine ⟨246020244746042642416459667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164013496497361761610973111 246020244746042642416459667)
  ·
    refine ⟨369030367119063963624689501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246020244746042642416459667 369030367119063963624689501)
    ·
      refine ⟨138386387669648986359258563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369030367119063963624689501 138386387669648986359258563)
      ·
        refine ⟨207579581504473479538887845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138386387669648986359258563 207579581504473479538887845)
        ·
          refine ⟨38921171532088777413541471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207579581504473479538887845 38921171532088777413541471)
          ·
            refine ⟨58381757298133166120312207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38921171532088777413541471 58381757298133166120312207)
            ·
              refine ⟨87572635947199749180468311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58381757298133166120312207 87572635947199749180468311)
              ·
                refine ⟨131358953920799623770702467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87572635947199749180468311 131358953920799623770702467)
                ·
                  refine ⟨197038430881199435656053701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131358953920799623770702467 197038430881199435656053701)
                  ·
                    refine ⟨36944705790224894185510069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197038430881199435656053701 36944705790224894185510069)
                    ·
                      refine ⟨3463566167833583829891569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36944705790224894185510069 3463566167833583829891569)
                      ·
                        rfl

theorem cell23_6745271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_6745271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745271 prefixEnd_6745271 := by exact prefixLift 6745271
  have htrace : WordTrace (prefixWord ++ tailWord_6745271) baseStart_6745271 baseEnd_6745271 := by
    simpa [prefixWord, tailWord_6745271, baseEnd_6745271] using wordTrace_append hprefix tailTrace_6745271
  have hstable : (prefixWord ++ tailWord_6745271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745271).length < 2 ^ (prefixWord ++ tailWord_6745271).sum := by decide
  have hdescent : baseEnd_6745271 < baseStart_6745271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745276 : List Nat := [2, 2, 2, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_6745276 : Nat := 118140960795 + 6745276 * 2 ^ 59
def prefixEnd_6745276 : Nat := 4983230072969 + 3 ^ 40 * 6745276 * 2
def baseEnd_6745276 : Nat := 3463568735236856310329047

theorem tailTrace_6745276 : CollatzResearch.WordTrace tailWord_6745276 prefixEnd_6745276 3463568735236856310329047 := by
  unfold tailWord_6745276
  simp only [CollatzResearch.WordTrace]
  refine ⟨123010213555512264135195841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164013618074016352180261121 123010213555512264135195841)
  ·
    refine ⟨92257660166634198101396881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123010213555512264135195841 92257660166634198101396881)
    ·
      refine ⟨69193245124975648576047661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92257660166634198101396881 69193245124975648576047661)
      ·
        refine ⟨25947466921865868216017873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69193245124975648576047661 25947466921865868216017873)
        ·
          refine ⟨19460600191399401162013405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25947466921865868216017873 19460600191399401162013405)
          ·
            refine ⟨7297725071774775435755027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19460600191399401162013405 7297725071774775435755027)
            ·
              refine ⟨10946587607662163153632541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7297725071774775435755027 10946587607662163153632541)
              ·
                refine ⟨4104970352873311182612203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10946587607662163153632541 4104970352873311182612203)
                ·
                  refine ⟨6157455529309966773918305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104970352873311182612203 6157455529309966773918305)
                  ·
                    refine ⟨4618091646982475080438729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6157455529309966773918305 4618091646982475080438729)
                    ·
                      refine ⟨3463568735236856310329047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618091646982475080438729 3463568735236856310329047)
                      ·
                        rfl

theorem cell23_6745276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_6745276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745276 prefixEnd_6745276 := by exact prefixLift 6745276
  have htrace : WordTrace (prefixWord ++ tailWord_6745276) baseStart_6745276 baseEnd_6745276 := by
    simpa [prefixWord, tailWord_6745276, baseEnd_6745276] using wordTrace_append hprefix tailTrace_6745276
  have hstable : (prefixWord ++ tailWord_6745276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745276).length < 2 ^ (prefixWord ++ tailWord_6745276).sum := by decide
  have hdescent : baseEnd_6745276 < baseStart_6745276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745282 : List Nat := [3, 5, 1, 1, 2, 2, 9]
def baseStart_6745282 : Nat := 118140960795 + 6745282 * 2 ^ 59
def prefixEnd_6745282 : Nat := 4983230072969 + 3 ^ 40 * 6745282 * 2
def baseEnd_6745282 : Nat := 42760145878034361566099

theorem tailTrace_6745282 : CollatzResearch.WordTrace tailWord_6745282 prefixEnd_6745282 42760145878034361566099 := by
  unfold tailWord_6745282
  simp only [CollatzResearch.WordTrace]
  refine ⟨61505161487250697823777525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164013763966001860863406733 61505161487250697823777525)
  ·
    refine ⟨5766108889429752920979143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61505161487250697823777525 5766108889429752920979143)
    ·
      refine ⟨8649163334144629381468715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766108889429752920979143 8649163334144629381468715)
      ·
        refine ⟨12973745001216944072203073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8649163334144629381468715 12973745001216944072203073)
        ·
          refine ⟨9730308750912708054152305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12973745001216944072203073 9730308750912708054152305)
          ·
            refine ⟨7297731563184531040614229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9730308750912708054152305 7297731563184531040614229)
            ·
              refine ⟨42760145878034361566099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7297731563184531040614229 42760145878034361566099)
              ·
                rfl

theorem cell23_6745282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 9].length) (baseStart_6745282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745282 prefixEnd_6745282 := by exact prefixLift 6745282
  have htrace : WordTrace (prefixWord ++ tailWord_6745282) baseStart_6745282 baseEnd_6745282 := by
    simpa [prefixWord, tailWord_6745282, baseEnd_6745282] using wordTrace_append hprefix tailTrace_6745282
  have hstable : (prefixWord ++ tailWord_6745282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745282).length < 2 ^ (prefixWord ++ tailWord_6745282).sum := by decide
  have hdescent : baseEnd_6745282 < baseStart_6745282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745291 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 2, 6]
def baseStart_6745291 : Nat := 118140960795 + 6745291 * 2 ^ 59
def prefixEnd_6745291 : Nat := 4983230072969 + 3 ^ 40 * 6745291 * 2
def baseEnd_6745291 : Nat := 1154525479148891250547159

theorem tailTrace_6745291 : CollatzResearch.WordTrace tailWord_6745291 prefixEnd_6745291 1154525479148891250547159 := by
  unfold tailWord_6745291
  simp only [CollatzResearch.WordTrace]
  refine ⟨246020974205970185832187727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164013982803980123888125151 246020974205970185832187727)
  ·
    refine ⟨369031461308955278748281591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246020974205970185832187727 369031461308955278748281591)
    ·
      refine ⟨553547191963432918122422387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369031461308955278748281591 553547191963432918122422387)
      ·
        refine ⟨830320787945149377183633581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553547191963432918122422387 830320787945149377183633581)
        ·
          refine ⟨311370295479431016443862593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830320787945149377183633581 311370295479431016443862593)
          ·
            refine ⟨233527721609573262332896945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311370295479431016443862593 233527721609573262332896945)
            ·
              refine ⟨175145791207179946749672709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233527721609573262332896945 175145791207179946749672709)
              ·
                refine ⟨32839835851346240015563633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175145791207179946749672709 32839835851346240015563633)
                ·
                  refine ⟨24629876888509680011672725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32839835851346240015563633 24629876888509680011672725)
                  ·
                    refine ⟨1154525479148891250547159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24629876888509680011672725 1154525479148891250547159)
                    ·
                      rfl

theorem cell23_6745291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 6].length) (baseStart_6745291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745291 prefixEnd_6745291 := by exact prefixLift 6745291
  have htrace : WordTrace (prefixWord ++ tailWord_6745291) baseStart_6745291 baseEnd_6745291 := by
    simpa [prefixWord, tailWord_6745291, baseEnd_6745291] using wordTrace_append hprefix tailTrace_6745291
  have hstable : (prefixWord ++ tailWord_6745291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745291).length < 2 ^ (prefixWord ++ tailWord_6745291).sum := by decide
  have hdescent : baseEnd_6745291 < baseStart_6745291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745293 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6745293 : Nat := 118140960795 + 6745293 * 2 ^ 59
def prefixEnd_6745293 : Nat := 4983230072969 + 3 ^ 40 * 6745293 * 2
def baseEnd_6745293 : Nat := 3463577464407982743816469

theorem tailTrace_6745293 : CollatzResearch.WordTrace tailWord_6745293 prefixEnd_6745293 3463577464407982743816469 := by
  unfold tailWord_6745293
  simp only [CollatzResearch.WordTrace]
  refine ⟨246021047151962940173760533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164014031434641960115840355 246021047151962940173760533)
  ·
    refine ⟨11532236585248262820645025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246021047151962940173760533 11532236585248262820645025)
    ·
      refine ⟨8649177438936197115483769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11532236585248262820645025 8649177438936197115483769)
      ·
        refine ⟨6486883079202147836612827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8649177438936197115483769 6486883079202147836612827)
        ·
          refine ⟨9730324618803221754919241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6486883079202147836612827 9730324618803221754919241)
          ·
            refine ⟨7297743464102416316189431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9730324618803221754919241 7297743464102416316189431)
            ·
              refine ⟨10946615196153624474284147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7297743464102416316189431 10946615196153624474284147)
              ·
                refine ⟨16419922794230436711426221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10946615196153624474284147 16419922794230436711426221)
                ·
                  refine ⟨6157471047836413766784833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16419922794230436711426221 6157471047836413766784833)
                  ·
                    refine ⟨4618103285877310325088625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6157471047836413766784833 4618103285877310325088625)
                    ·
                      refine ⟨3463577464407982743816469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618103285877310325088625 3463577464407982743816469)
                      ·
                        rfl

theorem cell23_6745293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6745293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745293 prefixEnd_6745293 := by exact prefixLift 6745293
  have htrace : WordTrace (prefixWord ++ tailWord_6745293) baseStart_6745293 baseEnd_6745293 := by
    simpa [prefixWord, tailWord_6745293, baseEnd_6745293] using wordTrace_append hprefix tailTrace_6745293
  have hstable : (prefixWord ++ tailWord_6745293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745293).length < 2 ^ (prefixWord ++ tailWord_6745293).sum := by decide
  have hdescent : baseEnd_6745293 < baseStart_6745293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745298 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6745298 : Nat := 118140960795 + 6745298 * 2 ^ 59
def prefixEnd_6745298 : Nat := 4983230072969 + 3 ^ 40 * 6745298 * 2
def baseEnd_6745298 : Nat := 3463580031811255224253945

theorem tailTrace_6745298 : CollatzResearch.WordTrace tailWord_6745298 prefixEnd_6745298 3463580031811255224253945 := by
  unfold tailWord_6745298
  simp only [CollatzResearch.WordTrace]
  refine ⟨61505307379236206506923137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164014153011296550685128365 61505307379236206506923137)
  ·
    refine ⟨46128980534427154880192353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61505307379236206506923137 46128980534427154880192353)
    ·
      refine ⟨34596735400820366160144265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46128980534427154880192353 34596735400820366160144265)
      ·
        refine ⟨25947551550615274620108199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34596735400820366160144265 25947551550615274620108199)
        ·
          refine ⟨38921327325922911930162299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25947551550615274620108199 38921327325922911930162299)
          ·
            refine ⟨58381990988884367895243449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38921327325922911930162299 58381990988884367895243449)
            ·
              refine ⟨43786493241663275921432587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58381990988884367895243449 43786493241663275921432587)
              ·
                refine ⟨65679739862494913882148881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43786493241663275921432587 65679739862494913882148881)
                ·
                  refine ⟨49259804896871185411611661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65679739862494913882148881 49259804896871185411611661)
                  ·
                    refine ⟨18472426836326694529354373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49259804896871185411611661 18472426836326694529354373)
                    ·
                      refine ⟨3463580031811255224253945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18472426836326694529354373 3463580031811255224253945)
                      ·
                        rfl

theorem cell23_6745298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6745298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745298 prefixEnd_6745298 := by exact prefixLift 6745298
  have htrace : WordTrace (prefixWord ++ tailWord_6745298) baseStart_6745298 baseEnd_6745298 := by
    simpa [prefixWord, tailWord_6745298, baseEnd_6745298] using wordTrace_append hprefix tailTrace_6745298
  have hstable : (prefixWord ++ tailWord_6745298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745298).length < 2 ^ (prefixWord ++ tailWord_6745298).sum := by decide
  have hdescent : baseEnd_6745298 < baseStart_6745298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745309 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6745309 : Nat := 118140960795 + 6745309 * 2 ^ 59
def prefixEnd_6745309 : Nat := 4983230072969 + 3 ^ 40 * 6745309 * 2
def baseEnd_6745309 : Nat := 3463585680098454681216395

theorem tailTrace_6745309 : CollatzResearch.WordTrace tailWord_6745309 prefixEnd_6745309 3463585680098454681216395 := by
  unfold tailWord_6745309
  simp only [CollatzResearch.WordTrace]
  refine ⟨246021630719904974906342981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164014420479936649937561987 246021630719904974906342981)
  ·
    refine ⟨46129055759982182794939309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246021630719904974906342981 46129055759982182794939309)
    ·
      refine ⟨17298395909993318548102241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46129055759982182794939309 17298395909993318548102241)
      ·
        refine ⟨12973796932494988911076681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17298395909993318548102241 12973796932494988911076681)
        ·
          refine ⟨9730347699371241683307511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12973796932494988911076681 9730347699371241683307511)
          ·
            refine ⟨14595521549056862524961267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9730347699371241683307511 14595521549056862524961267)
            ·
              refine ⟨21893282323585293787441901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14595521549056862524961267 21893282323585293787441901)
              ·
                refine ⟨8209980871344485170290713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21893282323585293787441901 8209980871344485170290713)
                ·
                  refine ⟨6157485653508363877718035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8209980871344485170290713 6157485653508363877718035)
                  ·
                    refine ⟨9236228480262545816577053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6157485653508363877718035 9236228480262545816577053)
                    ·
                      refine ⟨3463585680098454681216395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9236228480262545816577053 3463585680098454681216395)
                      ·
                        rfl

theorem cell23_6745309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6745309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745309 prefixEnd_6745309 := by exact prefixLift 6745309
  have htrace : WordTrace (prefixWord ++ tailWord_6745309) baseStart_6745309 baseEnd_6745309 := by
    simpa [prefixWord, tailWord_6745309, baseEnd_6745309] using wordTrace_append hprefix tailTrace_6745309
  have hstable : (prefixWord ++ tailWord_6745309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745309).length < 2 ^ (prefixWord ++ tailWord_6745309).sum := by decide
  have hdescent : baseEnd_6745309 < baseStart_6745309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745355 : List Nat := [1, 1, 1, 1, 5, 4, 1, 4, 5]
def baseStart_6745355 : Nat := 118140960795 + 6745355 * 2 ^ 59
def prefixEnd_6745355 : Nat := 4983230072969 + 3 ^ 40 * 6745355 * 2
def baseEnd_6745355 : Nat := 384845477800951277915687

theorem tailTrace_6745355 : CollatzResearch.WordTrace tailWord_6745355 prefixEnd_6745355 384845477800951277915687 := by
  unfold tailWord_6745355
  simp only [CollatzResearch.WordTrace]
  refine ⟨246023308477738324762517519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164015538985158883175011679 246023308477738324762517519)
  ·
    refine ⟨369034962716607487143776279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246023308477738324762517519 369034962716607487143776279)
    ·
      refine ⟨553552444074911230715664419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369034962716607487143776279 553552444074911230715664419)
      ·
        refine ⟨830328666112366846073496629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553552444074911230715664419 830328666112366846073496629)
        ·
          refine ⟨77843312448034391819390309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 830328666112366846073496629 77843312448034391819390309)
          ·
            refine ⟨14595621084006448466135683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77843312448034391819390309 14595621084006448466135683)
            ·
              refine ⟨21893431626009672699203525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14595621084006448466135683 21893431626009672699203525)
              ·
                refine ⟨4105018429876813631100661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21893431626009672699203525 4105018429876813631100661)
                ·
                  refine ⟨384845477800951277915687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4105018429876813631100661 384845477800951277915687)
                  ·
                    rfl

theorem cell23_6745355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 5].length) (baseStart_6745355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745355 prefixEnd_6745355 := by exact prefixLift 6745355
  have htrace : WordTrace (prefixWord ++ tailWord_6745355) baseStart_6745355 baseEnd_6745355 := by
    simpa [prefixWord, tailWord_6745355, baseEnd_6745355] using wordTrace_append hprefix tailTrace_6745355
  have hstable : (prefixWord ++ tailWord_6745355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745355).length < 2 ^ (prefixWord ++ tailWord_6745355).sum := by decide
  have hdescent : baseEnd_6745355 < baseStart_6745355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745389 : List Nat := [1, 5, 3, 1, 1, 2, 2, 3, 5]
def baseStart_6745389 : Nat := 118140960795 + 6745389 * 2 ^ 59
def prefixEnd_6745389 : Nat := 4983230072969 + 3 ^ 40 * 6745389 * 2
def baseEnd_6745389 : Nat := 384847417616757152024003

theorem tailTrace_6745389 : CollatzResearch.WordTrace tailWord_6745389 prefixEnd_6745389 384847417616757152024003 := by
  unfold tailWord_6745389
  simp only [CollatzResearch.WordTrace]
  refine ⟨246024548559615148569255221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164016365706410099046170147 246024548559615148569255221)
  ·
    refine ⟨23064801427463920178367677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246024548559615148569255221 23064801427463920178367677)
    ·
      refine ⟨8649300535298970066887879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23064801427463920178367677 8649300535298970066887879)
      ·
        refine ⟨12973950802948455100331819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8649300535298970066887879 12973950802948455100331819)
        ·
          refine ⟨19460926204422682650497729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973950802948455100331819 19460926204422682650497729)
          ·
            refine ⟨14595694653317011987873297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19460926204422682650497729 14595694653317011987873297)
            ·
              refine ⟨10946770989987758990904973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14595694653317011987873297 10946770989987758990904973)
              ·
                refine ⟨4105039121245409621589365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10946770989987758990904973 4105039121245409621589365)
                ·
                  refine ⟨384847417616757152024003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4105039121245409621589365 384847417616757152024003)
                  ·
                    rfl

theorem cell23_6745389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_6745389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745389 prefixEnd_6745389 := by exact prefixLift 6745389
  have htrace : WordTrace (prefixWord ++ tailWord_6745389) baseStart_6745389 baseEnd_6745389 := by
    simpa [prefixWord, tailWord_6745389, baseEnd_6745389] using wordTrace_append hprefix tailTrace_6745389
  have hstable : (prefixWord ++ tailWord_6745389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745389).length < 2 ^ (prefixWord ++ tailWord_6745389).sum := by decide
  have hdescent : baseEnd_6745389 < baseStart_6745389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745415 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 3, 4]
def baseStart_6745415 : Nat := 118140960795 + 6745415 * 2 ^ 59
def prefixEnd_6745415 : Nat := 4983230072969 + 3 ^ 40 * 6745415 * 2
def baseEnd_6745415 : Nat := 1154546703015943755496969

theorem tailTrace_6745415 : CollatzResearch.WordTrace tailWord_6745415 prefixEnd_6745415 1154546703015943755496969 := by
  unfold tailWord_6745415
  simp only [CollatzResearch.WordTrace]
  refine ⟨246025496857520955009701699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164016997905013970006467799 246025496857520955009701699)
  ·
    refine ⟨369038245286281432514552549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246025496857520955009701699 369038245286281432514552549)
    ·
      refine ⟨69194670991177768596478603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369038245286281432514552549 69194670991177768596478603)
      ·
        refine ⟨103792006486766652894717905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69194670991177768596478603 103792006486766652894717905)
        ·
          refine ⟨77844004865074989671038429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103792006486766652894717905 77844004865074989671038429)
          ·
            refine ⟨29191501824403121126639411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77844004865074989671038429 29191501824403121126639411)
            ·
              refine ⟨43787252736604681689959117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29191501824403121126639411 43787252736604681689959117)
              ·
                refine ⟨16420219776226755633734669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43787252736604681689959117 16420219776226755633734669)
                ·
                  refine ⟨6157582416085033362650501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16420219776226755633734669 6157582416085033362650501)
                  ·
                    refine ⟨1154546703015943755496969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6157582416085033362650501 1154546703015943755496969)
                    ·
                      rfl

theorem cell23_6745415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_6745415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745415 prefixEnd_6745415 := by exact prefixLift 6745415
  have htrace : WordTrace (prefixWord ++ tailWord_6745415) baseStart_6745415 baseEnd_6745415 := by
    simpa [prefixWord, tailWord_6745415, baseEnd_6745415] using wordTrace_append hprefix tailTrace_6745415
  have hstable : (prefixWord ++ tailWord_6745415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745415).length < 2 ^ (prefixWord ++ tailWord_6745415).sum := by decide
  have hdescent : baseEnd_6745415 < baseStart_6745415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745442 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_6745442 : Nat := 118140960795 + 6745442 * 2 ^ 59
def prefixEnd_6745442 : Nat := 4983230072969 + 3 ^ 40 * 6745442 * 2
def baseEnd_6745442 : Nat := 3463653973025502660853283

theorem tailTrace_6745442 : CollatzResearch.WordTrace tailWord_6745442 prefixEnd_6745442 3463653973025502660853283 := by
  unfold tailWord_6745442
  simp only [CollatzResearch.WordTrace]
  refine ⟨61506620407105784655233645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164017654418948759080623053 61506620407105784655233645)
  ·
    refine ⟨23064982652664669245712617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61506620407105784655233645 23064982652664669245712617)
    ·
      refine ⟨17298736989498501934284463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23064982652664669245712617 17298736989498501934284463)
      ·
        refine ⟨25948105484247752901426695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17298736989498501934284463 25948105484247752901426695)
        ·
          refine ⟨38922158226371629352140043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25948105484247752901426695 38922158226371629352140043)
          ·
            refine ⟨58383237339557444028210065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38922158226371629352140043 58383237339557444028210065)
            ·
              refine ⟨43787428004668083021157549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58383237339557444028210065 43787428004668083021157549)
              ·
                refine ⟨16420285501750531132934081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43787428004668083021157549 16420285501750531132934081)
                ·
                  refine ⟨12315214126312898349700561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16420285501750531132934081 12315214126312898349700561)
                  ·
                    refine ⟨9236410594734673762275421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12315214126312898349700561 9236410594734673762275421)
                    ·
                      refine ⟨3463653973025502660853283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9236410594734673762275421 3463653973025502660853283)
                      ·
                        rfl

theorem cell23_6745442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_6745442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745442 prefixEnd_6745442 := by exact prefixLift 6745442
  have htrace : WordTrace (prefixWord ++ tailWord_6745442) baseStart_6745442 baseEnd_6745442 := by
    simpa [prefixWord, tailWord_6745442, baseEnd_6745442] using wordTrace_append hprefix tailTrace_6745442
  have hstable : (prefixWord ++ tailWord_6745442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745442).length < 2 ^ (prefixWord ++ tailWord_6745442).sum := by decide
  have hdescent : baseEnd_6745442 < baseStart_6745442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745492 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_6745492 : Nat := 118140960795 + 6745492 * 2 ^ 59
def prefixEnd_6745492 : Nat := 4983230072969 + 3 ^ 40 * 6745492 * 2
def baseEnd_6745492 : Nat := 1154559882352742488409351

theorem tailTrace_6745492 : CollatzResearch.WordTrace tailWord_6745492 prefixEnd_6745492 1154559882352742488409351 := by
  unfold tailWord_6745492
  simp only [CollatzResearch.WordTrace]
  refine ⟨123014152639120998580127365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164018870185494664773503153 123014152639120998580127365)
  ·
    refine ⟨23065153619835187233773881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123014152639120998580127365 23065153619835187233773881)
    ·
      refine ⟨17298865214876390425330411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23065153619835187233773881 17298865214876390425330411)
      ·
        refine ⟨25948297822314585637995617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17298865214876390425330411 25948297822314585637995617)
        ·
          refine ⟨19461223366735939228496713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25948297822314585637995617 19461223366735939228496713)
          ·
            refine ⟨14595917525051954421372535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19461223366735939228496713 14595917525051954421372535)
            ·
              refine ⟨21893876287577931632058803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14595917525051954421372535 21893876287577931632058803)
              ·
                refine ⟨32840814431366897448088205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21893876287577931632058803 32840814431366897448088205)
                ·
                  refine ⟨12315305411762586543033077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32840814431366897448088205 12315305411762586543033077)
                  ·
                    refine ⟨1154559882352742488409351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12315305411762586543033077 1154559882352742488409351)
                    ·
                      rfl

theorem cell23_6745492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_6745492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745492 prefixEnd_6745492 := by exact prefixLift 6745492
  have htrace : WordTrace (prefixWord ++ tailWord_6745492) baseStart_6745492 baseEnd_6745492 := by
    simpa [prefixWord, tailWord_6745492, baseEnd_6745492] using wordTrace_append hprefix tailTrace_6745492
  have hstable : (prefixWord ++ tailWord_6745492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745492).length < 2 ^ (prefixWord ++ tailWord_6745492).sum := by decide
  have hdescent : baseEnd_6745492 < baseStart_6745492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745518 : List Nat := [4, 1, 18]
def baseStart_6745518 : Nat := 118140960795 + 6745518 * 2 ^ 59
def prefixEnd_6745518 : Nat := 4983230072969 + 3 ^ 40 * 6745518 * 2
def baseEnd_6745518 : Nat := 527921505495388563253

theorem tailTrace_6745518 : CollatzResearch.WordTrace tailWord_6745518 prefixEnd_6745518 527921505495388563253 := by
  unfold tailWord_6745518
  simp only [CollatzResearch.WordTrace]
  refine ⟨30753656697018475450087651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164019502384098535733800805 30753656697018475450087651)
  ·
    refine ⟨46130485045527713175131477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30753656697018475450087651 46130485045527713175131477)
    ·
      refine ⟨527921505495388563253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 46130485045527713175131477 527921505495388563253)
      ·
        rfl

theorem cell23_6745518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 18].length) (baseStart_6745518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745518 prefixEnd_6745518 := by exact prefixLift 6745518
  have htrace : WordTrace (prefixWord ++ tailWord_6745518) baseStart_6745518 baseEnd_6745518 := by
    simpa [prefixWord, tailWord_6745518, baseEnd_6745518] using wordTrace_append hprefix tailTrace_6745518
  have hstable : (prefixWord ++ tailWord_6745518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745518).length < 2 ^ (prefixWord ++ tailWord_6745518).sum := by decide
  have hdescent : baseEnd_6745518 < baseStart_6745518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745562 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_6745562 : Nat := 118140960795 + 6745562 * 2 ^ 59
def prefixEnd_6745562 : Nat := 4983230072969 + 3 ^ 40 * 6745562 * 2
def baseEnd_6745562 : Nat := 3463715590704042191352731

theorem tailTrace_6745562 : CollatzResearch.WordTrace tailWord_6745562 prefixEnd_6745562 3463715590704042191352731 := by
  unfold tailWord_6745562
  simp only [CollatzResearch.WordTrace]
  refine ⟨61507714596997099778825735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164020572258658932743535293 61507714596997099778825735)
  ·
    refine ⟨92261571895495649668238603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61507714596997099778825735 92261571895495649668238603)
    ·
      refine ⟨138392357843243474502357905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92261571895495649668238603 138392357843243474502357905)
      ·
        refine ⟨103794268382432605876768429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138392357843243474502357905 103794268382432605876768429)
        ·
          refine ⟨38922850643412227203788161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103794268382432605876768429 38922850643412227203788161)
          ·
            refine ⟨29192137982559170402841121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38922850643412227203788161 29192137982559170402841121)
            ·
              refine ⟨21894103486919377802130841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29192137982559170402841121 21894103486919377802130841)
              ·
                refine ⟨16420577615189533351598131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21894103486919377802130841 16420577615189533351598131)
                ·
                  refine ⟨24630866422784300027397197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16420577615189533351598131 24630866422784300027397197)
                  ·
                    refine ⟨9236574908544112510273949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24630866422784300027397197 9236574908544112510273949)
                    ·
                      refine ⟨3463715590704042191352731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9236574908544112510273949 3463715590704042191352731)
                      ·
                        rfl

theorem cell23_6745562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_6745562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745562 prefixEnd_6745562 := by exact prefixLift 6745562
  have htrace : WordTrace (prefixWord ++ tailWord_6745562) baseStart_6745562 baseEnd_6745562 := by
    simpa [prefixWord, tailWord_6745562, baseEnd_6745562] using wordTrace_append hprefix tailTrace_6745562
  have hstable : (prefixWord ++ tailWord_6745562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745562).length < 2 ^ (prefixWord ++ tailWord_6745562).sum := by decide
  have hdescent : baseEnd_6745562 < baseStart_6745562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745605 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_6745605 : Nat := 118140960795 + 6745605 * 2 ^ 59
def prefixEnd_6745605 : Nat := 4983230072969 + 3 ^ 40 * 6745605 * 2
def baseEnd_6745605 : Nat := 3463737670372185523115033

theorem tailTrace_6745605 : CollatzResearch.WordTrace tailWord_6745605 prefixEnd_6745605 3463737670372185523115033 := by
  unfold tailWord_6745605
  simp only [CollatzResearch.WordTrace]
  refine ⟨246032426726832617459118269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164021617817888411639412179 246032426726832617459118269)
  ·
    refine ⟨92262160022562231547169351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246032426726832617459118269 92262160022562231547169351)
    ·
      refine ⟨138393240033843347320754027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92262160022562231547169351 138393240033843347320754027)
      ·
        refine ⟨207589860050765020981131041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138393240033843347320754027 207589860050765020981131041)
        ·
          refine ⟨155692395038073765735848281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207589860050765020981131041 155692395038073765735848281)
          ·
            refine ⟨116769296278555324301886211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155692395038073765735848281 116769296278555324301886211)
            ·
              refine ⟨175153944417832986452829317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116769296278555324301886211 175153944417832986452829317)
              ·
                refine ⟨32841364578343684959905497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175153944417832986452829317 32841364578343684959905497)
                ·
                  refine ⟨24631023433757763719929123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32841364578343684959905497 24631023433757763719929123)
                  ·
                    refine ⟨36946535150636645579893685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24631023433757763719929123 36946535150636645579893685)
                    ·
                      refine ⟨3463737670372185523115033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36946535150636645579893685 3463737670372185523115033)
                      ·
                        rfl

theorem cell23_6745605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_6745605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745605 prefixEnd_6745605 := by exact prefixLift 6745605
  have htrace : WordTrace (prefixWord ++ tailWord_6745605) baseStart_6745605 baseEnd_6745605 := by
    simpa [prefixWord, tailWord_6745605, baseEnd_6745605] using wordTrace_append hprefix tailTrace_6745605
  have hstable : (prefixWord ++ tailWord_6745605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745605).length < 2 ^ (prefixWord ++ tailWord_6745605).sum := by decide
  have hdescent : baseEnd_6745605 < baseStart_6745605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745619 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 4, 2, 2]
def baseStart_6745619 : Nat := 118140960795 + 6745619 * 2 ^ 59
def prefixEnd_6745619 : Nat := 4983230072969 + 3 ^ 40 * 6745619 * 2
def baseEnd_6745619 : Nat := 3463744859101348468339969

theorem tailTrace_6745619 : CollatzResearch.WordTrace tailWord_6745619 prefixEnd_6745619 3463744859101348468339969 := by
  unfold tailWord_6745619
  simp only [CollatzResearch.WordTrace]
  refine ⟨246032937348781897850127911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164021958232521265233418607 246032937348781897850127911)
  ·
    refine ⟨369049406023172846775191867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246032937348781897850127911 369049406023172846775191867)
    ·
      refine ⟨553574109034759270162787801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369049406023172846775191867 553574109034759270162787801)
      ·
        refine ⟨415180581776069452622090851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553574109034759270162787801 415180581776069452622090851)
        ·
          refine ⟨622770872664104178933136277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415180581776069452622090851 622770872664104178933136277)
          ·
            refine ⟨29192384656129883387490763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 622770872664104178933136277 29192384656129883387490763)
            ·
              refine ⟨43788576984194825081236145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29192384656129883387490763 43788576984194825081236145)
              ·
                refine ⟨32841432738146118810927109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43788576984194825081236145 32841432738146118810927109)
                ·
                  refine ⟨6157768638402397277048833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32841432738146118810927109 6157768638402397277048833)
                  ·
                    refine ⟨4618326478801797957786625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6157768638402397277048833 4618326478801797957786625)
                    ·
                      refine ⟨3463744859101348468339969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618326478801797957786625 3463744859101348468339969)
                      ·
                        rfl

theorem cell23_6745619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 2, 2].length) (baseStart_6745619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745619 prefixEnd_6745619 := by exact prefixLift 6745619
  have htrace : WordTrace (prefixWord ++ tailWord_6745619) baseStart_6745619 baseEnd_6745619 := by
    simpa [prefixWord, tailWord_6745619, baseEnd_6745619] using wordTrace_append hprefix tailTrace_6745619
  have hstable : (prefixWord ++ tailWord_6745619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745619).length < 2 ^ (prefixWord ++ tailWord_6745619).sum := by decide
  have hdescent : baseEnd_6745619 < baseStart_6745619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745653 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_6745653 : Nat := 118140960795 + 6745653 * 2 ^ 59
def prefixEnd_6745653 : Nat := 4983230072969 + 3 ^ 40 * 6745653 * 2
def baseEnd_6745653 : Nat := 3463762317443601335314813

theorem tailTrace_6745653 : CollatzResearch.WordTrace tailWord_6745653 prefixEnd_6745653 3463762317443601335314813 := by
  unfold tailWord_6745653
  simp only [CollatzResearch.WordTrace]
  refine ⟨246034177430658721656865613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164022784953772481104577075 246034177430658721656865613)
  ·
    refine ⟨92262816536497020621324605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246034177430658721656865613 92262816536497020621324605)
    ·
      refine ⟨34598556201186382732996727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92262816536497020621324605 34598556201186382732996727)
      ·
        refine ⟨51897834301779574099495091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34598556201186382732996727 51897834301779574099495091)
        ·
          refine ⟨77846751452669361149242637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51897834301779574099495091 77846751452669361149242637)
          ·
            refine ⟨29192531794751010430965989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77846751452669361149242637 29192531794751010430965989)
            ·
              refine ⟨5473599711515814455806123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29192531794751010430965989 5473599711515814455806123)
              ·
                refine ⟨8210399567273721683709185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5473599711515814455806123 8210399567273721683709185)
                ·
                  refine ⟨6157799675455291262781889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8210399567273721683709185 6157799675455291262781889)
                  ·
                    refine ⟨4618349756591468447086417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6157799675455291262781889 4618349756591468447086417)
                    ·
                      refine ⟨3463762317443601335314813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618349756591468447086417 3463762317443601335314813)
                      ·
                        rfl

theorem cell23_6745653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_6745653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745653 prefixEnd_6745653 := by exact prefixLift 6745653
  have htrace : WordTrace (prefixWord ++ tailWord_6745653) baseStart_6745653 baseEnd_6745653 := by
    simpa [prefixWord, tailWord_6745653, baseEnd_6745653] using wordTrace_append hprefix tailTrace_6745653
  have hstable : (prefixWord ++ tailWord_6745653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745653).length < 2 ^ (prefixWord ++ tailWord_6745653).sum := by decide
  have hdescent : baseEnd_6745653 < baseStart_6745653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745682 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_6745682 : Nat := 118140960795 + 6745682 * 2 ^ 59
def prefixEnd_6745682 : Nat := 4983230072969 + 3 ^ 40 * 6745682 * 2
def baseEnd_6745682 : Nat := 3463777208382581721852179

theorem tailTrace_6745682 : CollatzResearch.WordTrace tailWord_6745682 prefixEnd_6745682 3463777208382581721852179 := by
  unfold tailWord_6745682
  simp only [CollatzResearch.WordTrace]
  refine ⟨61508808786888414902417825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164023490098369106406447533 61508808786888414902417825)
  ·
    refine ⟨46131606590166311176813369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61508808786888414902417825 46131606590166311176813369)
    ·
      refine ⟨34598704942624733382610027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46131606590166311176813369 34598704942624733382610027)
      ·
        refine ⟨51898057413937100073915041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34598704942624733382610027 51898057413937100073915041)
        ·
          refine ⟨38923543060452825055436281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51898057413937100073915041 38923543060452825055436281)
          ·
            refine ⟨29192657295339618791577211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38923543060452825055436281 29192657295339618791577211)
            ·
              refine ⟨43788985943009428187365817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29192657295339618791577211 43788985943009428187365817)
              ·
                refine ⟨32841739457257071140524363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43788985943009428187365817 32841739457257071140524363)
                ·
                  refine ⟨49262609185885606710786545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32841739457257071140524363 49262609185885606710786545)
                  ·
                    refine ⟨36946956889414205033089909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49262609185885606710786545 36946956889414205033089909)
                    ·
                      refine ⟨3463777208382581721852179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36946956889414205033089909 3463777208382581721852179)
                      ·
                        rfl

theorem cell23_6745682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_6745682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745682 prefixEnd_6745682 := by exact prefixLift 6745682
  have htrace : WordTrace (prefixWord ++ tailWord_6745682) baseStart_6745682 baseEnd_6745682 := by
    simpa [prefixWord, tailWord_6745682, baseEnd_6745682] using wordTrace_append hprefix tailTrace_6745682
  have hstable : (prefixWord ++ tailWord_6745682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745682).length < 2 ^ (prefixWord ++ tailWord_6745682).sum := by decide
  have hdescent : baseEnd_6745682 < baseStart_6745682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745693 : List Nat := [1, 4, 4, 2, 1, 1, 1, 4, 5]
def baseStart_6745693 : Nat := 118140960795 + 6745693 * 2 ^ 59
def prefixEnd_6745693 : Nat := 4983230072969 + 3 ^ 40 * 6745693 * 2
def baseEnd_6745693 : Nat := 384864761852197908757181

theorem tailTrace_6745693 : CollatzResearch.WordTrace tailWord_6745693 prefixEnd_6745693 384864761852197908757181 := by
  unfold tailWord_6745693
  simp only [CollatzResearch.WordTrace]
  refine ⟨246035636350513808488321733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164023757567009205658881155 246035636350513808488321733)
  ·
    refine ⟨46131681815721339091560325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246035636350513808488321733 46131681815721339091560325)
    ·
      refine ⟨8649690340447751079667561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46131681815721339091560325 8649690340447751079667561)
      ·
        refine ⟨6487267755335813309750671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8649690340447751079667561 6487267755335813309750671)
        ·
          refine ⟨9730901633003719964626007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6487267755335813309750671 9730901633003719964626007)
          ·
            refine ⟨14596352449505579946939011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9730901633003719964626007 14596352449505579946939011)
            ·
              refine ⟨21894528674258369920408517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14596352449505579946939011 21894528674258369920408517)
              ·
                refine ⟨4105224126423444360076597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21894528674258369920408517 4105224126423444360076597)
                ·
                  refine ⟨384864761852197908757181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4105224126423444360076597 384864761852197908757181)
                  ·
                    rfl

theorem cell23_6745693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_6745693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745693 prefixEnd_6745693 := by exact prefixLift 6745693
  have htrace : WordTrace (prefixWord ++ tailWord_6745693) baseStart_6745693 baseEnd_6745693 := by
    simpa [prefixWord, tailWord_6745693, baseEnd_6745693] using wordTrace_append hprefix tailTrace_6745693
  have hstable : (prefixWord ++ tailWord_6745693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745693).length < 2 ^ (prefixWord ++ tailWord_6745693).sum := by decide
  have hdescent : baseEnd_6745693 < baseStart_6745693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745729 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_6745729 : Nat := 118140960795 + 6745729 * 2 ^ 59
def prefixEnd_6745729 : Nat := 4983230072969 + 3 ^ 40 * 6745729 * 2
def baseEnd_6745729 : Nat := 3463801341973343037964463

theorem tailTrace_6745729 : CollatzResearch.WordTrace tailWord_6745729 prefixEnd_6745729 3463801341973343037964463 := by
  unfold tailWord_6745729
  simp only [CollatzResearch.WordTrace]
  refine ⟨246036949378383386636632241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164024632918922257757754827 246036949378383386636632241)
  ·
    refine ⟨184527712033787539977474181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246036949378383386636632241 184527712033787539977474181)
    ·
      refine ⟨34598946006335163745776409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184527712033787539977474181 34598946006335163745776409)
      ·
        refine ⟨25949209504751372809332307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34598946006335163745776409 25949209504751372809332307)
        ·
          refine ⟨38923814257127059213998461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25949209504751372809332307 38923814257127059213998461)
          ·
            refine ⟨14596430346422647205249423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38923814257127059213998461 14596430346422647205249423)
            ·
              refine ⟨21894645519633970807874135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14596430346422647205249423 21894645519633970807874135)
              ·
                refine ⟨32841968279450956211811203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21894645519633970807874135 32841968279450956211811203)
                ·
                  refine ⟨49262952419176434317716805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32841968279450956211811203 49262952419176434317716805)
                  ·
                    refine ⟨9236803578595581434571901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49262952419176434317716805 9236803578595581434571901)
                    ·
                      refine ⟨3463801341973343037964463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9236803578595581434571901 3463801341973343037964463)
                      ·
                        rfl

theorem cell23_6745729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_6745729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745729 prefixEnd_6745729 := by exact prefixLift 6745729
  have htrace : WordTrace (prefixWord ++ tailWord_6745729) baseStart_6745729 baseEnd_6745729 := by
    simpa [prefixWord, tailWord_6745729, baseEnd_6745729] using wordTrace_append hprefix tailTrace_6745729
  have hstable : (prefixWord ++ tailWord_6745729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745729).length < 2 ^ (prefixWord ++ tailWord_6745729).sum := by decide
  have hdescent : baseEnd_6745729 < baseStart_6745729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745752 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6745752 : Nat := 118140960795 + 6745752 * 2 ^ 59
def prefixEnd_6745752 : Nat := 4983230072969 + 3 ^ 40 * 6745752 * 2
def baseEnd_6745752 : Nat := 3463813152028396447976857

theorem tailTrace_6745752 : CollatzResearch.WordTrace tailWord_6745752 prefixEnd_6745752 3463813152028396447976857 := by
  unfold tailWord_6745752
  simp only [CollatzResearch.WordTrace]
  refine ⟨123018894128650030782359755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164025192171533374376479673 123018894128650030782359755)
  ·
    refine ⟨184528341192975046173539633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123018894128650030782359755 184528341192975046173539633)
    ·
      refine ⟨138396255894731284630154725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184528341192975046173539633 138396255894731284630154725)
      ·
        refine ⟨25949297980262115868154011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138396255894731284630154725 25949297980262115868154011)
        ·
          refine ⟨38923946970393173802231017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25949297980262115868154011 38923946970393173802231017)
          ·
            refine ⟨29192960227794880351673263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38923946970393173802231017 29192960227794880351673263)
            ·
              refine ⟨43789440341692320527509895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29192960227794880351673263 43789440341692320527509895)
              ·
                refine ⟨65684160512538480791264843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43789440341692320527509895 65684160512538480791264843)
                ·
                  refine ⟨98526240768807721186897265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65684160512538480791264843 98526240768807721186897265)
                  ·
                    refine ⟨73894680576605790890172949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98526240768807721186897265 73894680576605790890172949)
                    ·
                      refine ⟨3463813152028396447976857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73894680576605790890172949 3463813152028396447976857)
                      ·
                        rfl

theorem cell23_6745752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6745752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745752 prefixEnd_6745752 := by exact prefixLift 6745752
  have htrace : WordTrace (prefixWord ++ tailWord_6745752) baseStart_6745752 baseEnd_6745752 := by
    simpa [prefixWord, tailWord_6745752, baseEnd_6745752] using wordTrace_append hprefix tailTrace_6745752
  have hstable : (prefixWord ++ tailWord_6745752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745752).length < 2 ^ (prefixWord ++ tailWord_6745752).sum := by decide
  have hdescent : baseEnd_6745752 < baseStart_6745752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745779 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 1, 5]
def baseStart_6745779 : Nat := 118140960795 + 6745779 * 2 ^ 59
def prefixEnd_6745779 : Nat := 4983230072969 + 3 ^ 40 * 6745779 * 2
def baseEnd_6745779 : Nat := 1154609005335355947446411

theorem tailTrace_6745779 : CollatzResearch.WordTrace tailWord_6745779 prefixEnd_6745779 1154609005335355947446411 := by
  unfold tailWord_6745779
  simp only [CollatzResearch.WordTrace]
  refine ⟨246038773028202245175952391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164025848685468163450634927 246038773028202245175952391)
  ·
    refine ⟨369058159542303367763928587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246038773028202245175952391 369058159542303367763928587)
    ·
      refine ⟨553587239313455051645892881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369058159542303367763928587 553587239313455051645892881)
      ·
        refine ⟨415190429485091288734419661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553587239313455051645892881 415190429485091288734419661)
        ·
          refine ⟨155696411056909233275407373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415190429485091288734419661 155696411056909233275407373)
          ·
            refine ⟨58386154146340962478277765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155696411056909233275407373 58386154146340962478277765)
            ·
              refine ⟨10947403902438930464677081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58386154146340962478277765 10947403902438930464677081)
              ·
                refine ⟨8210552926829197848507811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10947403902438930464677081 8210552926829197848507811)
                ·
                  refine ⟨12315829390243796772761717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8210552926829197848507811 12315829390243796772761717)
                  ·
                    refine ⟨1154609005335355947446411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12315829390243796772761717 1154609005335355947446411)
                    ·
                      rfl

theorem cell23_6745779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 5].length) (baseStart_6745779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745779 prefixEnd_6745779 := by exact prefixLift 6745779
  have htrace : WordTrace (prefixWord ++ tailWord_6745779) baseStart_6745779 baseEnd_6745779 := by
    simpa [prefixWord, tailWord_6745779, baseEnd_6745779] using wordTrace_append hprefix tailTrace_6745779
  have hstable : (prefixWord ++ tailWord_6745779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745779).length < 2 ^ (prefixWord ++ tailWord_6745779).sum := by decide
  have hdescent : baseEnd_6745779 < baseStart_6745779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745792 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 3, 6]
def baseStart_6745792 : Nat := 118140960795 + 6745792 * 2 ^ 59
def prefixEnd_6745792 : Nat := 4983230072969 + 3 ^ 40 * 6745792 * 2
def baseEnd_6745792 : Nat := 1154611230418192097158891

theorem tailTrace_6745792 : CollatzResearch.WordTrace tailWord_6745792 prefixEnd_6745792 1154611230418192097158891 := by
  unfold tailWord_6745792
  simp only [CollatzResearch.WordTrace]
  refine ⟨123019623588577574198087815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164026164784770098930783753 123019623588577574198087815)
  ·
    refine ⟨184529435382866361297131723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123019623588577574198087815 184529435382866361297131723)
    ·
      refine ⟨276794153074299541945697585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184529435382866361297131723 276794153074299541945697585)
      ·
        refine ⟨207595614805724656459273189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276794153074299541945697585 207595614805724656459273189)
        ·
          refine ⟨38924177776073373086113723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207595614805724656459273189 38924177776073373086113723)
          ·
            refine ⟨58386266664110059629170585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38924177776073373086113723 58386266664110059629170585)
            ·
              refine ⟨43789699998082544721877939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58386266664110059629170585 43789699998082544721877939)
              ·
                refine ⟨65684549997123817082816909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43789699998082544721877939 65684549997123817082816909)
                ·
                  refine ⟨24631706248921431406056341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65684549997123817082816909 24631706248921431406056341)
                  ·
                    refine ⟨1154611230418192097158891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24631706248921431406056341 1154611230418192097158891)
                    ·
                      rfl

theorem cell23_6745792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_6745792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745792 prefixEnd_6745792 := by exact prefixLift 6745792
  have htrace : WordTrace (prefixWord ++ tailWord_6745792) baseStart_6745792 baseEnd_6745792 := by
    simpa [prefixWord, tailWord_6745792, baseEnd_6745792] using wordTrace_append hprefix tailTrace_6745792
  have hstable : (prefixWord ++ tailWord_6745792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745792).length < 2 ^ (prefixWord ++ tailWord_6745792).sum := by decide
  have hdescent : baseEnd_6745792 < baseStart_6745792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745799 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_6745799 : Nat := 118140960795 + 6745799 * 2 ^ 59
def prefixEnd_6745799 : Nat := 4983230072969 + 3 ^ 40 * 6745799 * 2
def baseEnd_6745799 : Nat := 3463837285619157764089141

theorem tailTrace_6745799 : CollatzResearch.WordTrace tailWord_6745799 prefixEnd_6745799 3463837285619157764089141 := by
  unfold tailWord_6745799
  simp only [CollatzResearch.WordTrace]
  refine ⟨246039502488129788591680451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164026334992086525727786967 246039502488129788591680451)
  ·
    refine ⟨369059253732194682887520677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246039502488129788591680451 369059253732194682887520677)
    ·
      refine ⟨69198610074786503041410127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369059253732194682887520677 69198610074786503041410127)
      ·
        refine ⟨103797915112179754562115191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69198610074786503041410127 103797915112179754562115191)
        ·
          refine ⟨155696872668269631843172787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103797915112179754562115191 155696872668269631843172787)
          ·
            refine ⟨233545309002404447764759181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155696872668269631843172787 233545309002404447764759181)
            ·
              refine ⟨87579490875901667911784693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233545309002404447764759181 87579490875901667911784693)
              ·
                refine ⟨8210577269615781366729815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87579490875901667911784693 8210577269615781366729815)
                ·
                  refine ⟨12315865904423672050094723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8210577269615781366729815 12315865904423672050094723)
                  ·
                    refine ⟨18473798856635508075142085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12315865904423672050094723 18473798856635508075142085)
                    ·
                      refine ⟨3463837285619157764089141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18473798856635508075142085 3463837285619157764089141)
                      ·
                        rfl

theorem cell23_6745799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_6745799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745799 prefixEnd_6745799 := by exact prefixLift 6745799
  have htrace : WordTrace (prefixWord ++ tailWord_6745799) baseStart_6745799 baseEnd_6745799 := by
    simpa [prefixWord, tailWord_6745799, baseEnd_6745799] using wordTrace_append hprefix tailTrace_6745799
  have hstable : (prefixWord ++ tailWord_6745799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745799).length < 2 ^ (prefixWord ++ tailWord_6745799).sum := by decide
  have hdescent : baseEnd_6745799 < baseStart_6745799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745809 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 4, 4]
def baseStart_6745809 : Nat := 118140960795 + 6745809 * 2 ^ 59
def prefixEnd_6745809 : Nat := 4983230072969 + 3 ^ 40 * 6745809 * 2
def baseEnd_6745809 : Nat := 1154614140141900908321365

theorem tailTrace_6745809 : CollatzResearch.WordTrace tailWord_6745809 prefixEnd_6745809 1154614140141900908321365 := by
  unfold tailWord_6745809
  simp only [CollatzResearch.WordTrace]
  refine ⟨246039867218093560299544481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164026578145395706866362987 246039867218093560299544481)
  ·
    refine ⟨184529900413570170224658361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246039867218093560299544481 184529900413570170224658361)
    ·
      refine ⟨138397425310177627668493771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184529900413570170224658361 138397425310177627668493771)
      ·
        refine ⟨207596137965266441502740657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138397425310177627668493771 207596137965266441502740657)
        ·
          refine ⟨155697103473949831127055493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207596137965266441502740657 155697103473949831127055493)
          ·
            refine ⟨29193206901365593336322905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155697103473949831127055493 29193206901365593336322905)
            ·
              refine ⟨21894905176024195002242179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29193206901365593336322905 21894905176024195002242179)
              ·
                refine ⟨32842357764036292503363269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21894905176024195002242179 32842357764036292503363269)
                ·
                  refine ⟨6157942080756804844380613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32842357764036292503363269 6157942080756804844380613)
                  ·
                    refine ⟨1154614140141900908321365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6157942080756804844380613 1154614140141900908321365)
                    ·
                      rfl

theorem cell23_6745809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_6745809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745809 prefixEnd_6745809 := by exact prefixLift 6745809
  have htrace : WordTrace (prefixWord ++ tailWord_6745809) baseStart_6745809 baseEnd_6745809 := by
    simpa [prefixWord, tailWord_6745809, baseEnd_6745809] using wordTrace_append hprefix tailTrace_6745809
  have hstable : (prefixWord ++ tailWord_6745809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745809).length < 2 ^ (prefixWord ++ tailWord_6745809).sum := by decide
  have hdescent : baseEnd_6745809 < baseStart_6745809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745829 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6745829 : Nat := 118140960795 + 6745829 * 2 ^ 59
def prefixEnd_6745829 : Nat := 4983230072969 + 3 ^ 40 * 6745829 * 2
def baseEnd_6745829 : Nat := 3463852690038792646714003

theorem tailTrace_6745829 : CollatzResearch.WordTrace tailWord_6745829 prefixEnd_6745829 3463852690038792646714003 := by
  unfold tailWord_6745829
  simp only [CollatzResearch.WordTrace]
  refine ⟨246040596678021103715272541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164027064452014069143515027 246040596678021103715272541)
  ·
    refine ⟨92265223754257913893227203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246040596678021103715272541 92265223754257913893227203)
    ·
      refine ⟨138397835631386870839840805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92265223754257913893227203 138397835631386870839840805)
      ·
        refine ⟨25949594180885038282470151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138397835631386870839840805 25949594180885038282470151)
        ·
          refine ⟨38924391271327557423705227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25949594180885038282470151 38924391271327557423705227)
          ·
            refine ⟨58386586906991336135557841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38924391271327557423705227 58386586906991336135557841)
            ·
              refine ⟨43789940180243502101668381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58386586906991336135557841 43789940180243502101668381)
              ·
                refine ⟨16421227567591313288125643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43789940180243502101668381 16421227567591313288125643)
                ·
                  refine ⟨24631841351386969932188465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16421227567591313288125643 24631841351386969932188465)
                  ·
                    refine ⟨18473881013540227449141349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24631841351386969932188465 18473881013540227449141349)
                    ·
                      refine ⟨3463852690038792646714003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18473881013540227449141349 3463852690038792646714003)
                      ·
                        rfl

theorem cell23_6745829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6745829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745829 prefixEnd_6745829 := by exact prefixLift 6745829
  have htrace : WordTrace (prefixWord ++ tailWord_6745829) baseStart_6745829 baseEnd_6745829 := by
    simpa [prefixWord, tailWord_6745829, baseEnd_6745829] using wordTrace_append hprefix tailTrace_6745829
  have hstable : (prefixWord ++ tailWord_6745829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745829).length < 2 ^ (prefixWord ++ tailWord_6745829).sum := by decide
  have hdescent : baseEnd_6745829 < baseStart_6745829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745836 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_6745836 : Nat := 118140960795 + 6745836 * 2 ^ 59
def prefixEnd_6745836 : Nat := 4983230072969 + 3 ^ 40 * 6745836 * 2
def baseEnd_6745836 : Nat := 3463856284403374119326471

theorem tailTrace_6745836 : CollatzResearch.WordTrace tailWord_6745836 prefixEnd_6745836 3463856284403374119326471 := by
  unfold tailWord_6745836
  simp only [CollatzResearch.WordTrace]
  refine ⟨123020425994497871955388681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164027234659330495940518241 123020425994497871955388681)
  ·
    refine ⟨92265319495873403966541511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123020425994497871955388681 92265319495873403966541511)
    ·
      refine ⟨138397979243810105949812267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92265319495873403966541511 138397979243810105949812267)
      ·
        refine ⟨207596968865715158924718401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138397979243810105949812267 207596968865715158924718401)
        ·
          refine ⟨155697726649286369193538801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207596968865715158924718401 155697726649286369193538801)
          ·
            refine ⟨116773294986964776895154101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155697726649286369193538801 116773294986964776895154101)
            ·
              refine ⟨10947496405027947833920697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116773294986964776895154101 10947496405027947833920697)
              ·
                refine ⟨8210622303770960875440523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10947496405027947833920697 8210622303770960875440523)
                ·
                  refine ⟨12315933455656441313160785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8210622303770960875440523 12315933455656441313160785)
                  ·
                    refine ⟨9236950091742330984870589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12315933455656441313160785 9236950091742330984870589)
                    ·
                      refine ⟨3463856284403374119326471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9236950091742330984870589 3463856284403374119326471)
                      ·
                        rfl

theorem cell23_6745836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_6745836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745836 prefixEnd_6745836 := by exact prefixLift 6745836
  have htrace : WordTrace (prefixWord ++ tailWord_6745836) baseStart_6745836 baseEnd_6745836 := by
    simpa [prefixWord, tailWord_6745836, baseEnd_6745836] using wordTrace_append hprefix tailTrace_6745836
  have hstable : (prefixWord ++ tailWord_6745836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745836).length < 2 ^ (prefixWord ++ tailWord_6745836).sum := by decide
  have hdescent : baseEnd_6745836 < baseStart_6745836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745846 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6745846 : Nat := 118140960795 + 6745846 * 2 ^ 59
def prefixEnd_6745846 : Nat := 4983230072969 + 3 ^ 40 * 6745846 * 2
def baseEnd_6745846 : Nat := 3463861419209919080201425

theorem tailTrace_6745846 : CollatzResearch.WordTrace tailWord_6745846 prefixEnd_6745846 3463861419209919080201425 := by
  unfold tailWord_6745846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15377576044934969726165087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164027477812639677079094261 15377576044934969726165087)
  ·
    refine ⟨23066364067402454589247631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15377576044934969726165087 23066364067402454589247631)
    ·
      refine ⟨34599546101103681883871447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23066364067402454589247631 34599546101103681883871447)
      ·
        refine ⟨51899319151655522825807171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34599546101103681883871447 51899319151655522825807171)
        ·
          refine ⟨77848978727483284238710757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51899319151655522825807171 77848978727483284238710757)
          ·
            refine ⟨14596683511403115794758267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77848978727483284238710757 14596683511403115794758267)
            ·
              refine ⟨21895025267104673692137401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14596683511403115794758267 21895025267104673692137401)
              ·
                refine ⟨16421268950328505269103051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21895025267104673692137401 16421268950328505269103051)
                ·
                  refine ⟨24631903425492757903654577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16421268950328505269103051 24631903425492757903654577)
                  ·
                    refine ⟨18473927569119568427740933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24631903425492757903654577 18473927569119568427740933)
                    ·
                      refine ⟨3463861419209919080201425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18473927569119568427740933 3463861419209919080201425)
                      ·
                        rfl

theorem cell23_6745846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6745846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745846 prefixEnd_6745846 := by exact prefixLift 6745846
  have htrace : WordTrace (prefixWord ++ tailWord_6745846) baseStart_6745846 baseEnd_6745846 := by
    simpa [prefixWord, tailWord_6745846, baseEnd_6745846] using wordTrace_append hprefix tailTrace_6745846
  have hstable : (prefixWord ++ tailWord_6745846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745846).length < 2 ^ (prefixWord ++ tailWord_6745846).sum := by decide
  have hdescent : baseEnd_6745846 < baseStart_6745846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745923 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 4, 2, 2]
def baseStart_6745923 : Nat := 118140960795 + 6745923 * 2 ^ 59
def prefixEnd_6745923 : Nat := 4983230072969 + 3 ^ 40 * 6745923 * 2
def baseEnd_6745923 : Nat := 3463900957220315278938571

theorem tailTrace_6745923 : CollatzResearch.WordTrace tailWord_6745923 prefixEnd_6745923 3463900957220315278938571 := by
  unfold tailWord_6745923
  simp only [CollatzResearch.WordTrace]
  refine ⟨246044025139680557769194423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164029350093120371846129615 246044025139680557769194423)
  ·
    refine ⟨369066037709520836653791635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246044025139680557769194423 369066037709520836653791635)
    ·
      refine ⟨553599056564281254980687453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369066037709520836653791635 553599056564281254980687453)
      ·
        refine ⟨207599646211605470617757795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553599056564281254980687453 207599646211605470617757795)
        ·
          refine ⟨311399469317408205926636693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207599646211605470617757795 311399469317408205926636693)
          ·
            refine ⟨14596850124253509652811095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 311399469317408205926636693 14596850124253509652811095)
            ·
              refine ⟨21895275186380264479216643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14596850124253509652811095 21895275186380264479216643)
              ·
                refine ⟨32842912779570396718824965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21895275186380264479216643 32842912779570396718824965)
                ·
                  refine ⟨6158046146169449384779681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32842912779570396718824965 6158046146169449384779681)
                  ·
                    refine ⟨4618534609627087038584761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6158046146169449384779681 4618534609627087038584761)
                    ·
                      refine ⟨3463900957220315278938571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618534609627087038584761 3463900957220315278938571)
                      ·
                        rfl

theorem cell23_6745923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_6745923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745923 prefixEnd_6745923 := by exact prefixLift 6745923
  have htrace : WordTrace (prefixWord ++ tailWord_6745923) baseStart_6745923 baseEnd_6745923 := by
    simpa [prefixWord, tailWord_6745923, baseEnd_6745923] using wordTrace_append hprefix tailTrace_6745923
  have hstable : (prefixWord ++ tailWord_6745923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745923).length < 2 ^ (prefixWord ++ tailWord_6745923).sum := by decide
  have hdescent : baseEnd_6745923 < baseStart_6745923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745929 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 7]
def baseStart_6745929 : Nat := 118140960795 + 6745929 * 2 ^ 59
def prefixEnd_6745929 : Nat := 4983230072969 + 3 ^ 40 * 6745929 * 2
def baseEnd_6745929 : Nat := 384878226456026917273727

theorem tailTrace_6745929 : CollatzResearch.WordTrace tailWord_6745929 prefixEnd_6745929 384878226456026917273727 := by
  unfold tailWord_6745929
  simp only [CollatzResearch.WordTrace]
  refine ⟨246044243977658820793912841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164029495985105880529275227 246044243977658820793912841)
  ·
    refine ⟨184533182983244115595434631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246044243977658820793912841 184533182983244115595434631)
    ·
      refine ⟨276799774474866173393151947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184533182983244115595434631 276799774474866173393151947)
      ·
        refine ⟨415199661712299260089727921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276799774474866173393151947 415199661712299260089727921)
        ·
          refine ⟨311399746284224445067295941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415199661712299260089727921 311399746284224445067295941)
          ·
            refine ⟨58387452428292083450117989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311399746284224445067295941 58387452428292083450117989)
            ·
              refine ⟨10947647330304765646897123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58387452428292083450117989 10947647330304765646897123)
              ·
                refine ⟨16421470995457148470345685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10947647330304765646897123 16421470995457148470345685)
                ·
                  refine ⟨384878226456026917273727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16421470995457148470345685 384878226456026917273727)
                  ·
                    rfl

theorem cell23_6745929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 7].length) (baseStart_6745929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745929 prefixEnd_6745929 := by exact prefixLift 6745929
  have htrace : WordTrace (prefixWord ++ tailWord_6745929) baseStart_6745929 baseEnd_6745929 := by
    simpa [prefixWord, tailWord_6745929, baseEnd_6745929] using wordTrace_append hprefix tailTrace_6745929
  have hstable : (prefixWord ++ tailWord_6745929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745929).length < 2 ^ (prefixWord ++ tailWord_6745929).sum := by decide
  have hdescent : baseEnd_6745929 < baseStart_6745929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745940 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_6745940 : Nat := 118140960795 + 6745940 * 2 ^ 59
def prefixEnd_6745940 : Nat := 4983230072969 + 3 ^ 40 * 6745940 * 2
def baseEnd_6745940 : Nat := 3463909686391441712425993

theorem tailTrace_6745940 : CollatzResearch.WordTrace tailWord_6745940 prefixEnd_6745940 3463909686391441712425993 := by
  unfold tailWord_6745940
  simp only [CollatzResearch.WordTrace]
  refine ⟨123022322590309484836281637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164029763453745979781708849 123022322590309484836281637)
  ·
    refine ⟨23066685485683028406802807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123022322590309484836281637 23066685485683028406802807)
    ·
      refine ⟨34600028228524542610204211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23066685485683028406802807 34600028228524542610204211)
      ·
        refine ⟨51900042342786813915306317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34600028228524542610204211 51900042342786813915306317)
        ·
          refine ⟨19462515878545055218239869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51900042342786813915306317 19462515878545055218239869)
          ·
            refine ⟨7298443454454395706839951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19462515878545055218239869 7298443454454395706839951)
            ·
              refine ⟨10947665181681593560259927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298443454454395706839951 10947665181681593560259927)
              ·
                refine ⟨16421497772522390340389891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10947665181681593560259927 16421497772522390340389891)
                ·
                  refine ⟨24632246658783585510584837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16421497772522390340389891 24632246658783585510584837)
                  ·
                    refine ⟨4618546248521922283234657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24632246658783585510584837 4618546248521922283234657)
                    ·
                      refine ⟨3463909686391441712425993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618546248521922283234657 3463909686391441712425993)
                      ·
                        rfl

theorem cell23_6745940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_6745940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745940 prefixEnd_6745940 := by exact prefixLift 6745940
  have htrace : WordTrace (prefixWord ++ tailWord_6745940) baseStart_6745940 baseEnd_6745940 := by
    simpa [prefixWord, tailWord_6745940, baseEnd_6745940] using wordTrace_append hprefix tailTrace_6745940
  have hstable : (prefixWord ++ tailWord_6745940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745940).length < 2 ^ (prefixWord ++ tailWord_6745940).sum := by decide
  have hdescent : baseEnd_6745940 < baseStart_6745940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745959 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 1, 7]
def baseStart_6745959 : Nat := 118140960795 + 6745959 * 2 ^ 59
def prefixEnd_6745959 : Nat := 4983230072969 + 3 ^ 40 * 6745959 * 2
def baseEnd_6745959 : Nat := 1154639814174625712696135

theorem tailTrace_6745959 : CollatzResearch.WordTrace tailWord_6745959 prefixEnd_6745959 1154639814174625712696135 := by
  unfold tailWord_6745959
  simp only [CollatzResearch.WordTrace]
  refine ⟨246045338167550135917504931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164030225445033423945003287 246045338167550135917504931)
  ·
    refine ⟨369068007251325203876257397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246045338167550135917504931 369068007251325203876257397)
    ·
      refine ⟨34600125679811737863399131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 369068007251325203876257397 34600125679811737863399131)
      ·
        refine ⟨51900188519717606795098697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34600125679811737863399131 51900188519717606795098697)
        ·
          refine ⟨38925141389788205096324023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51900188519717606795098697 38925141389788205096324023)
          ·
            refine ⟨58387712084682307644486035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38925141389788205096324023 58387712084682307644486035)
            ·
              refine ⟨87581568127023461466729053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58387712084682307644486035 87581568127023461466729053)
              ·
                refine ⟨32843088047633798050023395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87581568127023461466729053 32843088047633798050023395)
                ·
                  refine ⟨49264632071450697075035093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32843088047633798050023395 49264632071450697075035093)
                  ·
                    refine ⟨1154639814174625712696135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49264632071450697075035093 1154639814174625712696135)
                    ·
                      rfl

theorem cell23_6745959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_6745959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745959 prefixEnd_6745959 := by exact prefixLift 6745959
  have htrace : WordTrace (prefixWord ++ tailWord_6745959) baseStart_6745959 baseEnd_6745959 := by
    simpa [prefixWord, tailWord_6745959, baseEnd_6745959] using wordTrace_append hprefix tailTrace_6745959
  have hstable : (prefixWord ++ tailWord_6745959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745959).length < 2 ^ (prefixWord ++ tailWord_6745959).sum := by decide
  have hdescent : baseEnd_6745959 < baseStart_6745959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745969 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_6745969 : Nat := 118140960795 + 6745969 * 2 ^ 59
def prefixEnd_6745969 : Nat := 4983230072969 + 3 ^ 40 * 6745969 * 2
def baseEnd_6745969 : Nat := 3463924577330422098963359

theorem tailTrace_6745969 : CollatzResearch.WordTrace tailWord_6745969 prefixEnd_6745969 3463924577330422098963359 := by
  unfold tailWord_6745969
  simp only [CollatzResearch.WordTrace]
  refine ⟨246045702897513907625368961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164030468598342605083579307 246045702897513907625368961)
  ·
    refine ⟨184534277173135430719026721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246045702897513907625368961 184534277173135430719026721)
    ·
      refine ⟨138400707879851573039270041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184534277173135430719026721 138400707879851573039270041)
      ·
        refine ⟨103800530909888679779452531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138400707879851573039270041 103800530909888679779452531)
        ·
          refine ⟨155700796364833019669178797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103800530909888679779452531 155700796364833019669178797)
          ·
            refine ⟨58387798636812382375942049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155700796364833019669178797 58387798636812382375942049)
            ·
              refine ⟨43790848977609286781956537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58387798636812382375942049 43790848977609286781956537)
              ·
                refine ⟨32843136733206965086467403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43790848977609286781956537 32843136733206965086467403)
                ·
                  refine ⟨49264705099810447629701105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32843136733206965086467403 49264705099810447629701105)
                  ·
                    refine ⟨36948528824857835722275829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49264705099810447629701105 36948528824857835722275829)
                    ·
                      refine ⟨3463924577330422098963359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36948528824857835722275829 3463924577330422098963359)
                      ·
                        rfl

theorem cell23_6745969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_6745969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745969 prefixEnd_6745969 := by exact prefixLift 6745969
  have htrace : WordTrace (prefixWord ++ tailWord_6745969) baseStart_6745969 baseEnd_6745969 := by
    simpa [prefixWord, tailWord_6745969, baseEnd_6745969] using wordTrace_append hprefix tailTrace_6745969
  have hstable : (prefixWord ++ tailWord_6745969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745969).length < 2 ^ (prefixWord ++ tailWord_6745969).sum := by decide
  have hdescent : baseEnd_6745969 < baseStart_6745969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6745996 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 1, 6, 2]
def baseStart_6745996 : Nat := 118140960795 + 6745996 * 2 ^ 59
def prefixEnd_6745996 : Nat := 4983230072969 + 3 ^ 40 * 6745996 * 2
def baseEnd_6745996 : Nat := 3463938441308093493325735

theorem tailTrace_6745996 : CollatzResearch.WordTrace tailWord_6745996 prefixEnd_6745996 3463938441308093493325735 := by
  unfold tailWord_6745996
  simp only [CollatzResearch.WordTrace]
  refine ⟨123023343834208045618300921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164031125112277394157734561 123023343834208045618300921)
  ·
    refine ⟨92267507875656034213725691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123023343834208045618300921 92267507875656034213725691)
    ·
      refine ⟨138401261813484051320588537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92267507875656034213725691 138401261813484051320588537)
      ·
        refine ⟨103800946360113038490441403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138401261813484051320588537 103800946360113038490441403)
        ·
          refine ⟨155701419540169557735662105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103800946360113038490441403 155701419540169557735662105)
          ·
            refine ⟨116776064655127168301746579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155701419540169557735662105 116776064655127168301746579)
            ·
              refine ⟨175164096982690752452619869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116776064655127168301746579 175164096982690752452619869)
              ·
                refine ⟨65686536368509032169732451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175164096982690752452619869 65686536368509032169732451)
                ·
                  refine ⟨98529804552763548254598677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65686536368509032169732451 98529804552763548254598677)
                  ·
                    refine ⟨4618584588410791324434313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98529804552763548254598677 4618584588410791324434313)
                    ·
                      refine ⟨3463938441308093493325735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618584588410791324434313 3463938441308093493325735)
                      ·
                        rfl

theorem cell23_6745996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_6745996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6745996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6745996 prefixEnd_6745996 := by exact prefixLift 6745996
  have htrace : WordTrace (prefixWord ++ tailWord_6745996) baseStart_6745996 baseEnd_6745996 := by
    simpa [prefixWord, tailWord_6745996, baseEnd_6745996] using wordTrace_append hprefix tailTrace_6745996
  have hstable : (prefixWord ++ tailWord_6745996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6745996).length < 2 ^ (prefixWord ++ tailWord_6745996).sum := by decide
  have hdescent : baseEnd_6745996 < baseStart_6745996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6745996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746009 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_6746009 : Nat := 118140960795 + 6746009 * 2 ^ 59
def prefixEnd_6746009 : Nat := 4983230072969 + 3 ^ 40 * 6746009 * 2
def baseEnd_6746009 : Nat := 3463945116556601942463175

theorem tailTrace_6746009 : CollatzResearch.WordTrace tailWord_6746009 prefixEnd_6746009 3463945116556601942463175 := by
  unfold tailWord_6746009
  simp only [CollatzResearch.WordTrace]
  refine ⟨246047161817368994456825081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164031441211579329637883387 246047161817368994456825081)
  ·
    refine ⟨184535371363026745842618811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246047161817368994456825081 184535371363026745842618811)
    ·
      refine ⟨276803057044540118763928217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184535371363026745842618811 276803057044540118763928217)
      ·
        refine ⟨207602292783405089072946163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276803057044540118763928217 207602292783405089072946163)
        ·
          refine ⟨311403439175107633609419245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207602292783405089072946163 311403439175107633609419245)
          ·
            refine ⟨116776289690665362603532217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311403439175107633609419245 116776289690665362603532217)
            ·
              refine ⟨87582217267999021952649163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116776289690665362603532217 87582217267999021952649163)
              ·
                refine ⟨131373325901998532928973745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87582217267999021952649163 131373325901998532928973745)
                ·
                  refine ⟨98529994426498899696730309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131373325901998532928973745 98529994426498899696730309)
                  ·
                    refine ⟨18474373954968543693136933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98529994426498899696730309 18474373954968543693136933)
                    ·
                      refine ⟨3463945116556601942463175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18474373954968543693136933 3463945116556601942463175)
                      ·
                        rfl

theorem cell23_6746009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_6746009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746009 prefixEnd_6746009 := by exact prefixLift 6746009
  have htrace : WordTrace (prefixWord ++ tailWord_6746009) baseStart_6746009 baseEnd_6746009 := by
    simpa [prefixWord, tailWord_6746009, baseEnd_6746009] using wordTrace_append hprefix tailTrace_6746009
  have hstable : (prefixWord ++ tailWord_6746009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746009).length < 2 ^ (prefixWord ++ tailWord_6746009).sum := by decide
  have hdescent : baseEnd_6746009 < baseStart_6746009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746013 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_6746013 : Nat := 118140960795 + 6746013 * 2 ^ 59
def prefixEnd_6746013 : Nat := 4983230072969 + 3 ^ 40 * 6746013 * 2
def baseEnd_6746013 : Nat := 3463947170479219926813157

theorem tailTrace_6746013 : CollatzResearch.WordTrace tailWord_6746013 prefixEnd_6746013 3463947170479219926813157 := by
  unfold tailWord_6746013
  simp only [CollatzResearch.WordTrace]
  refine ⟨246047307709354503139970693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164031538472903002093313795 246047307709354503139970693)
  ·
    refine ⟨46133870195503969338744505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246047307709354503139970693 46133870195503969338744505)
    ·
      refine ⟨34600402646627977004058379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46133870195503969338744505 34600402646627977004058379)
      ·
        refine ⟨51900603969941965506087569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34600402646627977004058379 51900603969941965506087569)
        ·
          refine ⟨38925452977456474129565677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51900603969941965506087569 38925452977456474129565677)
          ·
            refine ⟨14597044866546177798587129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38925452977456474129565677 14597044866546177798587129)
            ·
              refine ⟨10947783649909633348940347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14597044866546177798587129 10947783649909633348940347)
              ·
                refine ⟨16421675474864450023410521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10947783649909633348940347 16421675474864450023410521)
                ·
                  refine ⟨12316256606148337517557891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16421675474864450023410521 12316256606148337517557891)
                  ·
                    refine ⟨18474384909222506276336837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12316256606148337517557891 18474384909222506276336837)
                    ·
                      refine ⟨3463947170479219926813157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18474384909222506276336837 3463947170479219926813157)
                      ·
                        rfl

theorem cell23_6746013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_6746013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746013 prefixEnd_6746013 := by exact prefixLift 6746013
  have htrace : WordTrace (prefixWord ++ tailWord_6746013) baseStart_6746013 baseEnd_6746013 := by
    simpa [prefixWord, tailWord_6746013, baseEnd_6746013] using wordTrace_append hprefix tailTrace_6746013
  have hstable : (prefixWord ++ tailWord_6746013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746013).length < 2 ^ (prefixWord ++ tailWord_6746013).sum := by decide
  have hdescent : baseEnd_6746013 < baseStart_6746013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746033 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_6746033 : Nat := 118140960795 + 6746033 * 2 ^ 59
def prefixEnd_6746033 : Nat := 4983230072969 + 3 ^ 40 * 6746033 * 2
def baseEnd_6746033 : Nat := 3463957440092309848563065

theorem tailTrace_6746033 : CollatzResearch.WordTrace tailWord_6746033 prefixEnd_6746033 3463957440092309848563065 := by
  unfold tailWord_6746033
  simp only [CollatzResearch.WordTrace]
  refine ⟨246048037169282046555698753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164032024779521364370465835 246048037169282046555698753)
  ·
    refine ⟨184536027876961534916774065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246048037169282046555698753 184536027876961534916774065)
    ·
      refine ⟨138402020907721151187580549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184536027876961534916774065 138402020907721151187580549)
      ·
        refine ⟨25950378920197715847671353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138402020907721151187580549 25950378920197715847671353)
        ·
          refine ⟨19462784190148286885753515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25950378920197715847671353 19462784190148286885753515)
          ·
            refine ⟨29194176285222430328630273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19462784190148286885753515 29194176285222430328630273)
            ·
              refine ⟨21895632213916822746472705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29194176285222430328630273 21895632213916822746472705)
              ·
                refine ⟨16421724160437617059854529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21895632213916822746472705 16421724160437617059854529)
                ·
                  refine ⟨12316293120328212794890897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16421724160437617059854529 12316293120328212794890897)
                  ·
                    refine ⟨9237219840246159596168173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12316293120328212794890897 9237219840246159596168173)
                    ·
                      refine ⟨3463957440092309848563065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9237219840246159596168173 3463957440092309848563065)
                      ·
                        rfl

theorem cell23_6746033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_6746033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746033 prefixEnd_6746033 := by exact prefixLift 6746033
  have htrace : WordTrace (prefixWord ++ tailWord_6746033) baseStart_6746033 baseEnd_6746033 := by
    simpa [prefixWord, tailWord_6746033, baseEnd_6746033] using wordTrace_append hprefix tailTrace_6746033
  have hstable : (prefixWord ++ tailWord_6746033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746033).length < 2 ^ (prefixWord ++ tailWord_6746033).sum := by decide
  have hdescent : baseEnd_6746033 < baseStart_6746033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746039 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_6746039 : Nat := 118140960795 + 6746039 * 2 ^ 59
def prefixEnd_6746039 : Nat := 4983230072969 + 3 ^ 40 * 6746039 * 2
def baseEnd_6746039 : Nat := 3463960520976236825088037

theorem tailTrace_6746039 : CollatzResearch.WordTrace tailWord_6746039 prefixEnd_6746039 3463960520976236825088037 := by
  unfold tailWord_6746039
  simp only [CollatzResearch.WordTrace]
  refine ⟨246048256007260309580417171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164032170671506873053611447 246048256007260309580417171)
  ·
    refine ⟨369072384010890464370625757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246048256007260309580417171 369072384010890464370625757)
    ·
      refine ⟨138402144004083924138984659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369072384010890464370625757 138402144004083924138984659)
      ·
        refine ⟨207603216006125886208476989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138402144004083924138984659 207603216006125886208476989)
        ·
          refine ⟨77851206002297207328178871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207603216006125886208476989 77851206002297207328178871)
          ·
            refine ⟨116776809003445810992268307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77851206002297207328178871 116776809003445810992268307)
            ·
              refine ⟨175165213505168716488402461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116776809003445810992268307 175165213505168716488402461)
              ·
                refine ⟨65686955064438268683150923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175165213505168716488402461 65686955064438268683150923)
                ·
                  refine ⟨98530432596657403024726385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65686955064438268683150923 98530432596657403024726385)
                  ·
                    refine ⟨73897824447493052268544789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98530432596657403024726385 73897824447493052268544789)
                    ·
                      refine ⟨3463960520976236825088037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73897824447493052268544789 3463960520976236825088037)
                      ·
                        rfl

theorem cell23_6746039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_6746039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746039 prefixEnd_6746039 := by exact prefixLift 6746039
  have htrace : WordTrace (prefixWord ++ tailWord_6746039) baseStart_6746039 baseEnd_6746039 := by
    simpa [prefixWord, tailWord_6746039, baseEnd_6746039] using wordTrace_append hprefix tailTrace_6746039
  have hstable : (prefixWord ++ tailWord_6746039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746039).length < 2 ^ (prefixWord ++ tailWord_6746039).sum := by decide
  have hdescent : baseEnd_6746039 < baseStart_6746039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746059 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7]
def baseStart_6746059 : Nat := 118140960795 + 6746059 * 2 ^ 59
def prefixEnd_6746059 : Nat := 4983230072969 + 3 ^ 40 * 6746059 * 2
def baseEnd_6746059 : Nat := 3463970790589326746837945

theorem tailTrace_6746059 : CollatzResearch.WordTrace tailWord_6746059 prefixEnd_6746059 3463970790589326746837945 := by
  unfold tailWord_6746059
  simp only [CollatzResearch.WordTrace]
  refine ⟨246048985467187852996145231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164032656978125235330763487 246048985467187852996145231)
  ·
    refine ⟨369073478200781779494217847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246048985467187852996145231 369073478200781779494217847)
    ·
      refine ⟨553610217301172669241326771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369073478200781779494217847 553610217301172669241326771)
      ·
        refine ⟨830415325951759003861990157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553610217301172669241326771 830415325951759003861990157)
        ·
          refine ⟨311405747231909626448246309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830415325951759003861990157 311405747231909626448246309)
          ·
            refine ⟨58388577605983054959046183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311405747231909626448246309 58388577605983054959046183)
            ·
              refine ⟨87582866408974582438569275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58388577605983054959046183 87582866408974582438569275)
              ·
                refine ⟨131374299613461873657853913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87582866408974582438569275 131374299613461873657853913)
                ·
                  refine ⟨98530724710096405243390435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131374299613461873657853913 98530724710096405243390435)
                  ·
                    refine ⟨147796087065144607865085653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98530724710096405243390435 147796087065144607865085653)
                    ·
                      refine ⟨3463970790589326746837945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147796087065144607865085653 3463970790589326746837945)
                      ·
                        rfl

theorem cell23_6746059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_6746059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746059 prefixEnd_6746059 := by exact prefixLift 6746059
  have htrace : WordTrace (prefixWord ++ tailWord_6746059) baseStart_6746059 baseEnd_6746059 := by
    simpa [prefixWord, tailWord_6746059, baseEnd_6746059] using wordTrace_append hprefix tailTrace_6746059
  have hstable : (prefixWord ++ tailWord_6746059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746059).length < 2 ^ (prefixWord ++ tailWord_6746059).sum := by decide
  have hdescent : baseEnd_6746059 < baseStart_6746059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746063 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 3]
def baseStart_6746063 : Nat := 118140960795 + 6746063 * 2 ^ 59
def prefixEnd_6746063 : Nat := 4983230072969 + 3 ^ 40 * 6746063 * 2
def baseEnd_6746063 : Nat := 3463972844511944731187927

theorem tailTrace_6746063 : CollatzResearch.WordTrace tailWord_6746063 prefixEnd_6746063 3463972844511944731187927 := by
  unfold tailWord_6746063
  simp only [CollatzResearch.WordTrace]
  refine ⟨246049131359173361679290843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164032754239448907786193895 246049131359173361679290843)
  ·
    refine ⟨369073697038760042518936265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246049131359173361679290843 369073697038760042518936265)
    ·
      refine ⟨276805272779070031889202199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369073697038760042518936265 276805272779070031889202199)
      ·
        refine ⟨415207909168605047833803299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276805272779070031889202199 415207909168605047833803299)
        ·
          refine ⟨622811863752907571750704949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415207909168605047833803299 622811863752907571750704949)
          ·
            refine ⟨58388612226835084851628589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 622811863752907571750704949 58388612226835084851628589)
            ·
              refine ⟨21895729585063156819360721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58388612226835084851628589 21895729585063156819360721)
              ·
                refine ⟨16421797188797367614520541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21895729585063156819360721 16421797188797367614520541)
                ·
                  refine ⟨6158173945799012855445203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16421797188797367614520541 6158173945799012855445203)
                  ·
                    refine ⟨9237260918698519283167805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6158173945799012855445203 9237260918698519283167805)
                    ·
                      refine ⟨3463972844511944731187927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9237260918698519283167805 3463972844511944731187927)
                      ·
                        rfl

theorem cell23_6746063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 3].length) (baseStart_6746063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746063 prefixEnd_6746063 := by exact prefixLift 6746063
  have htrace : WordTrace (prefixWord ++ tailWord_6746063) baseStart_6746063 baseEnd_6746063 := by
    simpa [prefixWord, tailWord_6746063, baseEnd_6746063] using wordTrace_append hprefix tailTrace_6746063
  have hstable : (prefixWord ++ tailWord_6746063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746063).length < 2 ^ (prefixWord ++ tailWord_6746063).sum := by decide
  have hdescent : baseEnd_6746063 < baseStart_6746063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746083 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 1, 5]
def baseStart_6746083 : Nat := 118140960795 + 6746083 * 2 ^ 59
def prefixEnd_6746083 : Nat := 4983230072969 + 3 ^ 40 * 6746083 * 2
def baseEnd_6746083 : Nat := 1154661038041678217645945

theorem tailTrace_6746083 : CollatzResearch.WordTrace tailWord_6746083 prefixEnd_6746083 1154661038041678217645945 := by
  unfold tailWord_6746083
  simp only [CollatzResearch.WordTrace]
  refine ⟨246049860819100905095018903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164033240546067270063345935 246049860819100905095018903)
  ·
    refine ⟨369074791228651357642528355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246049860819100905095018903 369074791228651357642528355)
    ·
      refine ⟨553612186842977036463792533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369074791228651357642528355 553612186842977036463792533)
      ·
        refine ⟨25950571258264548584240275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 553612186842977036463792533 25950571258264548584240275)
        ·
          refine ⟨38925856887396822876360413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25950571258264548584240275 38925856887396822876360413)
          ·
            refine ⟨14597196332773808578635155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38925856887396822876360413 14597196332773808578635155)
            ·
              refine ⟨21895794499160712867952733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14597196332773808578635155 21895794499160712867952733)
              ·
                refine ⟨8210922937185267325482275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21895794499160712867952733 8210922937185267325482275)
                ·
                  refine ⟨12316384405777900988223413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8210922937185267325482275 12316384405777900988223413)
                  ·
                    refine ⟨1154661038041678217645945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12316384405777900988223413 1154661038041678217645945)
                    ·
                      rfl

theorem cell23_6746083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 5].length) (baseStart_6746083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746083 prefixEnd_6746083 := by exact prefixLift 6746083
  have htrace : WordTrace (prefixWord ++ tailWord_6746083) baseStart_6746083 baseEnd_6746083 := by
    simpa [prefixWord, tailWord_6746083, baseEnd_6746083] using wordTrace_append hprefix tailTrace_6746083
  have hstable : (prefixWord ++ tailWord_6746083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746083).length < 2 ^ (prefixWord ++ tailWord_6746083).sum := by decide
  have hdescent : baseEnd_6746083 < baseStart_6746083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746120 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_6746120 : Nat := 118140960795 + 6746120 * 2 ^ 59
def prefixEnd_6746120 : Nat := 4983230072969 + 3 ^ 40 * 6746120 * 2
def baseEnd_6746120 : Nat := 3464002112909251008175165

theorem tailTrace_6746120 : CollatzResearch.WordTrace tailWord_6746120 prefixEnd_6746120 3464002112909251008175165 := by
  unfold tailWord_6746120
  simp only [CollatzResearch.WordTrace]
  refine ⟨123025605159983430207057907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164034140213311240276077209 123025605159983430207057907)
  ·
    refine ⟨184538407739975145310586861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123025605159983430207057907 184538407739975145310586861)
    ·
      refine ⟨69201902902490679491470073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184538407739975145310586861 69201902902490679491470073)
      ·
        refine ⟨51901427176868009618602555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69201902902490679491470073 51901427176868009618602555)
        ·
          refine ⟨77852140765302014427903833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51901427176868009618602555 77852140765302014427903833)
          ·
            refine ⟨58389105573976510820927875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77852140765302014427903833 58389105573976510820927875)
            ·
              refine ⟨87583658360964766231391813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58389105573976510820927875 87583658360964766231391813)
              ·
                refine ⟨16421935942680893668385965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87583658360964766231391813 16421935942680893668385965)
                ·
                  refine ⟨6158225978505335125644737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16421935942680893668385965 6158225978505335125644737)
                  ·
                    refine ⟨4618669483879001344233553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6158225978505335125644737 4618669483879001344233553)
                    ·
                      refine ⟨3464002112909251008175165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618669483879001344233553 3464002112909251008175165)
                      ·
                        rfl

theorem cell23_6746120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_6746120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746120 prefixEnd_6746120 := by exact prefixLift 6746120
  have htrace : WordTrace (prefixWord ++ tailWord_6746120) baseStart_6746120 baseEnd_6746120 := by
    simpa [prefixWord, tailWord_6746120, baseEnd_6746120] using wordTrace_append hprefix tailTrace_6746120
  have hstable : (prefixWord ++ tailWord_6746120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746120).length < 2 ^ (prefixWord ++ tailWord_6746120).sum := by decide
  have hdescent : baseEnd_6746120 < baseStart_6746120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746126 : List Nat := [4, 1, 1, 2, 2, 1, 3, 9]
def baseStart_6746126 : Nat := 118140960795 + 6746126 * 2 ^ 59
def prefixEnd_6746126 : Nat := 4983230072969 + 3 ^ 40 * 6746126 * 2
def baseEnd_6746126 : Nat := 128296488659006592025931

theorem tailTrace_6746126 : CollatzResearch.WordTrace tailWord_6746126 prefixEnd_6746126 128296488659006592025931 := by
  unfold tailWord_6746126
  simp only [CollatzResearch.WordTrace]
  refine ⟨30756428644743140429854279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164034286105296748959222821 30756428644743140429854279)
  ·
    refine ⟨46134642967114710644781419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30756428644743140429854279 46134642967114710644781419)
    ·
      refine ⟨69201964450672065967172129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46134642967114710644781419 69201964450672065967172129)
      ·
        refine ⟨51901473338004049475379097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69201964450672065967172129 51901473338004049475379097)
        ·
          refine ⟨38926105003503037106534323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51901473338004049475379097 38926105003503037106534323)
          ·
            refine ⟨58389157505254555659801485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38926105003503037106534323 58389157505254555659801485)
            ·
              refine ⟨21895934064470458372425557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58389157505254555659801485 21895934064470458372425557)
              ·
                refine ⟨128296488659006592025931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21895934064470458372425557 128296488659006592025931)
                ·
                  rfl

theorem cell23_6746126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_6746126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746126 prefixEnd_6746126 := by exact prefixLift 6746126
  have htrace : WordTrace (prefixWord ++ tailWord_6746126) baseStart_6746126 baseEnd_6746126 := by
    simpa [prefixWord, tailWord_6746126, baseEnd_6746126] using wordTrace_append hprefix tailTrace_6746126
  have hstable : (prefixWord ++ tailWord_6746126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746126).length < 2 ^ (prefixWord ++ tailWord_6746126).sum := by decide
  have hdescent : baseEnd_6746126 < baseStart_6746126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746140 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_6746140 : Nat := 118140960795 + 6746140 * 2 ^ 59
def prefixEnd_6746140 : Nat := 4983230072969 + 3 ^ 40 * 6746140 * 2
def baseEnd_6746140 : Nat := 3464012382522340929925073

theorem tailTrace_6746140 : CollatzResearch.WordTrace tailWord_6746140 prefixEnd_6746140 3464012382522340929925073 := by
  unfold tailWord_6746140
  simp only [CollatzResearch.WordTrace]
  refine ⟨123025969889947201914921937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164034626519929602553229249 123025969889947201914921937)
  ·
    refine ⟨92269477417460401436191453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123025969889947201914921937 92269477417460401436191453)
    ·
      refine ⟨34601054031547650538571795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92269477417460401436191453 34601054031547650538571795)
      ·
        refine ⟨51901581047321475807857693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34601054031547650538571795 51901581047321475807857693)
        ·
          refine ⟨19463092892745553427946635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51901581047321475807857693 19463092892745553427946635)
          ·
            refine ⟨29194639339118330141919953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19463092892745553427946635 29194639339118330141919953)
            ·
              refine ⟨21895979504338747606439965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29194639339118330141919953 21895979504338747606439965)
              ·
                refine ⟨8210992314127030352414987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21895979504338747606439965 8210992314127030352414987)
                ·
                  refine ⟨12316488471190545528622481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8210992314127030352414987 12316488471190545528622481)
                  ·
                    refine ⟨9237366353392909146466861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12316488471190545528622481 9237366353392909146466861)
                    ·
                      refine ⟨3464012382522340929925073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9237366353392909146466861 3464012382522340929925073)
                      ·
                        rfl

theorem cell23_6746140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_6746140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746140 prefixEnd_6746140 := by exact prefixLift 6746140
  have htrace : WordTrace (prefixWord ++ tailWord_6746140) baseStart_6746140 baseEnd_6746140 := by
    simpa [prefixWord, tailWord_6746140, baseEnd_6746140] using wordTrace_append hprefix tailTrace_6746140
  have hstable : (prefixWord ++ tailWord_6746140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746140).length < 2 ^ (prefixWord ++ tailWord_6746140).sum := by decide
  have hdescent : baseEnd_6746140 < baseStart_6746140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746154 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_6746154 : Nat := 118140960795 + 6746154 * 2 ^ 59
def prefixEnd_6746154 : Nat := 4983230072969 + 3 ^ 40 * 6746154 * 2
def baseEnd_6746154 : Nat := 3464019571251503875150009

theorem tailTrace_6746154 : CollatzResearch.WordTrace tailWord_6746154 prefixEnd_6746154 3464019571251503875150009 := by
  unfold tailWord_6746154
  simp only [CollatzResearch.WordTrace]
  refine ⟨61513112600460921055213379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164034966934562456147235677 61513112600460921055213379)
  ·
    refine ⟨92269668900691381582820069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61513112600460921055213379 92269668900691381582820069)
    ·
      refine ⟨17300562918879634046778763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92269668900691381582820069 17300562918879634046778763)
      ·
        refine ⟨25950844378319451070168145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17300562918879634046778763 25950844378319451070168145)
        ·
          refine ⟨19463133283739588302626109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25950844378319451070168145 19463133283739588302626109)
          ·
            refine ⟨7298674981402345613484791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19463133283739588302626109 7298674981402345613484791)
            ·
              refine ⟨10948012472103518420227187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298674981402345613484791 10948012472103518420227187)
              ·
                refine ⟨16422018708155277630340781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10948012472103518420227187 16422018708155277630340781)
                ·
                  refine ⟨6158257015558229111377793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16422018708155277630340781 6158257015558229111377793)
                  ·
                    refine ⟨4618692761668671833533345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6158257015558229111377793 4618692761668671833533345)
                    ·
                      refine ⟨3464019571251503875150009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618692761668671833533345 3464019571251503875150009)
                      ·
                        rfl

theorem cell23_6746154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_6746154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746154 prefixEnd_6746154 := by exact prefixLift 6746154
  have htrace : WordTrace (prefixWord ++ tailWord_6746154) baseStart_6746154 baseEnd_6746154 := by
    simpa [prefixWord, tailWord_6746154, baseEnd_6746154] using wordTrace_append hprefix tailTrace_6746154
  have hstable : (prefixWord ++ tailWord_6746154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746154).length < 2 ^ (prefixWord ++ tailWord_6746154).sum := by decide
  have hdescent : baseEnd_6746154 < baseStart_6746154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746174 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_6746174 : Nat := 118140960795 + 6746174 * 2 ^ 59
def prefixEnd_6746174 : Nat := 4983230072969 + 3 ^ 40 * 6746174 * 2
def baseEnd_6746174 : Nat := 3464029840864593796899917

theorem tailTrace_6746174 : CollatzResearch.WordTrace tailWord_6746174 prefixEnd_6746174 3464029840864593796899917 := by
  unfold tailWord_6746174
  simp only [CollatzResearch.WordTrace]
  refine ⟨30756647482721403454572697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164035453241180818424387717 30756647482721403454572697)
  ·
    refine ⟨23067485612041052590929523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30756647482721403454572697 23067485612041052590929523)
    ·
      refine ⟨34601228418061578886394285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23067485612041052590929523 34601228418061578886394285)
      ·
        refine ⟨12975460656773092082397857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34601228418061578886394285 12975460656773092082397857)
        ·
          refine ⟨9731595492579819061798393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12975460656773092082397857 9731595492579819061798393)
          ·
            refine ⟨7298696619434864296348795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9731595492579819061798393 7298696619434864296348795)
            ·
              refine ⟨10948044929152296444523193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298696619434864296348795 10948044929152296444523193)
              ·
                refine ⟨8211033696864222333392395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10948044929152296444523193 8211033696864222333392395)
                ·
                  refine ⟨12316550545296333500088593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211033696864222333392395 12316550545296333500088593)
                  ·
                    refine ⟨9237412908972250125066445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12316550545296333500088593 9237412908972250125066445)
                    ·
                      refine ⟨3464029840864593796899917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9237412908972250125066445 3464029840864593796899917)
                      ·
                        rfl

theorem cell23_6746174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_6746174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746174 prefixEnd_6746174 := by exact prefixLift 6746174
  have htrace : WordTrace (prefixWord ++ tailWord_6746174) baseStart_6746174 baseEnd_6746174 := by
    simpa [prefixWord, tailWord_6746174, baseEnd_6746174] using wordTrace_append hprefix tailTrace_6746174
  have hstable : (prefixWord ++ tailWord_6746174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746174).length < 2 ^ (prefixWord ++ tailWord_6746174).sum := by decide
  have hdescent : baseEnd_6746174 < baseStart_6746174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746186 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_6746186 : Nat := 118140960795 + 6746186 * 2 ^ 59
def prefixEnd_6746186 : Nat := 4983230072969 + 3 ^ 40 * 6746186 * 2
def baseEnd_6746186 : Nat := 1154678667544149249983287

theorem tailTrace_6746186 : CollatzResearch.WordTrace tailWord_6746186 prefixEnd_6746186 1154678667544149249983287 := by
  unfold tailWord_6746186
  simp only [CollatzResearch.WordTrace]
  refine ⟨61513404384431938421504603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164035745025151835790678941 61513404384431938421504603)
  ·
    refine ⟨92270106576647907632256905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61513404384431938421504603 92270106576647907632256905)
    ·
      refine ⟨69202579932485930724192679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92270106576647907632256905 69202579932485930724192679)
      ·
        refine ⟨103803869898728896086289019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69202579932485930724192679 103803869898728896086289019)
        ·
          refine ⟨155705804848093344129433529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103803869898728896086289019 155705804848093344129433529)
          ·
            refine ⟨116779353636070008097075147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155705804848093344129433529 116779353636070008097075147)
            ·
              refine ⟨175169030454105012145612721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116779353636070008097075147 175169030454105012145612721)
              ·
                refine ⟨131376772840578759109209541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175169030454105012145612721 131376772840578759109209541)
                ·
                  refine ⟨24633144907608517332976789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131376772840578759109209541 24633144907608517332976789)
                  ·
                    refine ⟨1154678667544149249983287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24633144907608517332976789 1154678667544149249983287)
                    ·
                      rfl

theorem cell23_6746186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_6746186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746186 prefixEnd_6746186 := by exact prefixLift 6746186
  have htrace : WordTrace (prefixWord ++ tailWord_6746186) baseStart_6746186 baseEnd_6746186 := by
    simpa [prefixWord, tailWord_6746186, baseEnd_6746186] using wordTrace_append hprefix tailTrace_6746186
  have hstable : (prefixWord ++ tailWord_6746186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746186).length < 2 ^ (prefixWord ++ tailWord_6746186).sum := by decide
  have hdescent : baseEnd_6746186 < baseStart_6746186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746213 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_6746213 : Nat := 118140960795 + 6746213 * 2 ^ 59
def prefixEnd_6746213 : Nat := 4983230072969 + 3 ^ 40 * 6746213 * 2
def baseEnd_6746213 : Nat := 3464049866610119144312237

theorem tailTrace_6746213 : CollatzResearch.WordTrace tailWord_6746213 prefixEnd_6746213 3464049866610119144312237 := by
  unfold tailWord_6746213
  simp only [CollatzResearch.WordTrace]
  refine ⟨246054602308629937297251293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164036401539086624864834195 246054602308629937297251293)
  ·
    refine ⟨92270475865736226486469235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246054602308629937297251293 92270475865736226486469235)
    ·
      refine ⟨138405713798604339729703853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92270475865736226486469235 138405713798604339729703853)
      ·
        refine ⟨51902142674476627398638945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138405713798604339729703853 51902142674476627398638945)
        ·
          refine ⟨38926607005857470548979209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51902142674476627398638945 38926607005857470548979209)
          ·
            refine ⟨29194955254393102911734407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38926607005857470548979209 29194955254393102911734407)
            ·
              refine ⟨43792432881589654367601611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29194955254393102911734407 43792432881589654367601611)
              ·
                refine ⟨65688649322384481551402417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43792432881589654367601611 65688649322384481551402417)
                ·
                  refine ⟨49266486991788361163551813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65688649322384481551402417 49266486991788361163551813)
                  ·
                    refine ⟨9237466310960317718165965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49266486991788361163551813 9237466310960317718165965)
                    ·
                      refine ⟨3464049866610119144312237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9237466310960317718165965 3464049866610119144312237)
                      ·
                        rfl

theorem cell23_6746213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_6746213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746213 prefixEnd_6746213 := by exact prefixLift 6746213
  have htrace : WordTrace (prefixWord ++ tailWord_6746213) baseStart_6746213 baseEnd_6746213 := by
    simpa [prefixWord, tailWord_6746213, baseEnd_6746213] using wordTrace_append hprefix tailTrace_6746213
  have hstable : (prefixWord ++ tailWord_6746213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746213).length < 2 ^ (prefixWord ++ tailWord_6746213).sum := by decide
  have hdescent : baseEnd_6746213 < baseStart_6746213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746223 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_6746223 : Nat := 118140960795 + 6746223 * 2 ^ 59
def prefixEnd_6746223 : Nat := 4983230072969 + 3 ^ 40 * 6746223 * 2
def baseEnd_6746223 : Nat := 3464055001416664105187191

theorem tailTrace_6746223 : CollatzResearch.WordTrace tailWord_6746223 prefixEnd_6746223 3464055001416664105187191 := by
  unfold tailWord_6746223
  simp only [CollatzResearch.WordTrace]
  refine ⟨246054967038593709005115323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164036644692395806003410215 246054967038593709005115323)
  ·
    refine ⟨369082450557890563507672985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246054967038593709005115323 369082450557890563507672985)
    ·
      refine ⟨276811837918417922630754739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369082450557890563507672985 276811837918417922630754739)
      ·
        refine ⟨415217756877626883946132109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276811837918417922630754739 415217756877626883946132109)
        ·
          refine ⟨155706658829110081479799541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415217756877626883946132109 155706658829110081479799541)
          ·
            refine ⟨14597499265229070138731207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155706658829110081479799541 14597499265229070138731207)
            ·
              refine ⟨21896248897843605208096811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14597499265229070138731207 21896248897843605208096811)
              ·
                refine ⟨32844373346765407812145217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21896248897843605208096811 32844373346765407812145217)
                ·
                  refine ⟨24633280010074055859108913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32844373346765407812145217 24633280010074055859108913)
                  ·
                    refine ⟨18474960007555541894331685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24633280010074055859108913 18474960007555541894331685)
                    ·
                      refine ⟨3464055001416664105187191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18474960007555541894331685 3464055001416664105187191)
                      ·
                        rfl

theorem cell23_6746223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_6746223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746223 prefixEnd_6746223 := by exact prefixLift 6746223
  have htrace : WordTrace (prefixWord ++ tailWord_6746223) baseStart_6746223 baseEnd_6746223 := by
    simpa [prefixWord, tailWord_6746223, baseEnd_6746223] using wordTrace_append hprefix tailTrace_6746223
  have hstable : (prefixWord ++ tailWord_6746223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746223).length < 2 ^ (prefixWord ++ tailWord_6746223).sum := by decide
  have hdescent : baseEnd_6746223 < baseStart_6746223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746233 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 7]
def baseStart_6746233 : Nat := 118140960795 + 6746233 * 2 ^ 59
def prefixEnd_6746233 : Nat := 4983230072969 + 3 ^ 40 * 6746233 * 2
def baseEnd_6746233 : Nat := 384895570691467674006905

theorem tailTrace_6746233 : CollatzResearch.WordTrace tailWord_6746233 prefixEnd_6746233 384895570691467674006905 := by
  unfold tailWord_6746233
  simp only [CollatzResearch.WordTrace]
  refine ⟨246055331768557480712979353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164036887845704987141986235 246055331768557480712979353)
  ·
    refine ⟨184541498826418110534734515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246055331768557480712979353 184541498826418110534734515)
    ·
      refine ⟨276812248239627165802101773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184541498826418110534734515 276812248239627165802101773)
      ·
        refine ⟨103804593089860187175788165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276812248239627165802101773 103804593089860187175788165)
        ·
          refine ⟨19463361204348785095460281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103804593089860187175788165 19463361204348785095460281)
          ·
            refine ⟨14597520903261588821595211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19463361204348785095460281 14597520903261588821595211)
            ·
              refine ⟨21896281354892383232392817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14597520903261588821595211 21896281354892383232392817)
              ·
                refine ⟨16422211016169287424294613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21896281354892383232392817 16422211016169287424294613)
                ·
                  refine ⟨384895570691467674006905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16422211016169287424294613 384895570691467674006905)
                  ·
                    rfl

theorem cell23_6746233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_6746233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746233 prefixEnd_6746233 := by exact prefixLift 6746233
  have htrace : WordTrace (prefixWord ++ tailWord_6746233) baseStart_6746233 baseEnd_6746233 := by
    simpa [prefixWord, tailWord_6746233, baseEnd_6746233] using wordTrace_append hprefix tailTrace_6746233
  have hstable : (prefixWord ++ tailWord_6746233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746233).length < 2 ^ (prefixWord ++ tailWord_6746233).sum := by decide
  have hdescent : baseEnd_6746233 < baseStart_6746233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746250 : List Nat := [3, 1, 2, 3, 1, 2, 1, 5, 5]
def baseStart_6746250 : Nat := 118140960795 + 6746250 * 2 ^ 59
def prefixEnd_6746250 : Nat := 4983230072969 + 3 ^ 40 * 6746250 * 2
def baseEnd_6746250 : Nat := 384896540599370611061063

theorem tailTrace_6746250 : CollatzResearch.WordTrace tailWord_6746250 prefixEnd_6746250 384896540599370611061063 := by
  unfold tailWord_6746250
  simp only [CollatzResearch.WordTrace]
  refine ⟨61513987952373973154087051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164037301206330595077565469 61513987952373973154087051)
  ·
    refine ⟨92270981928560959731130577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61513987952373973154087051 92270981928560959731130577)
    ·
      refine ⟨69203236446420719798347933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92270981928560959731130577 69203236446420719798347933)
      ·
        refine ⟨25951213667407769924380475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69203236446420719798347933 25951213667407769924380475)
        ·
          refine ⟨38926820501111654886570713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25951213667407769924380475 38926820501111654886570713)
          ·
            refine ⟨29195115375833741164928035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38926820501111654886570713 29195115375833741164928035)
            ·
              refine ⟨43792673063750611747392053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29195115375833741164928035 43792673063750611747392053)
              ·
                refine ⟨4105563099726619851318005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43792673063750611747392053 4105563099726619851318005)
                ·
                  refine ⟨384896540599370611061063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4105563099726619851318005 384896540599370611061063)
                  ·
                    rfl

theorem cell23_6746250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_6746250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746250 prefixEnd_6746250 := by exact prefixLift 6746250
  have htrace : WordTrace (prefixWord ++ tailWord_6746250) baseStart_6746250 baseEnd_6746250 := by
    simpa [prefixWord, tailWord_6746250, baseEnd_6746250] using wordTrace_append hprefix tailTrace_6746250
  have hstable : (prefixWord ++ tailWord_6746250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746250).length < 2 ^ (prefixWord ++ tailWord_6746250).sum := by decide
  have hdescent : baseEnd_6746250 < baseStart_6746250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746360 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 1, 5, 2]
def baseStart_6746360 : Nat := 118140960795 + 6746360 * 2 ^ 59
def prefixEnd_6746360 : Nat := 4983230072969 + 3 ^ 40 * 6746360 * 2
def baseEnd_6746360 : Nat := 3464125348266330069174061

theorem tailTrace_6746360 : CollatzResearch.WordTrace tailWord_6746360 prefixEnd_6746360 3464125348266330069174061 := by
  unfold tailWord_6746360
  simp only [CollatzResearch.WordTrace]
  refine ⟨123029981919548690701426267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164039975892731587601901689 123029981919548690701426267)
  ·
    refine ⟨184544972879323036052139401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123029981919548690701426267 184544972879323036052139401)
    ·
      refine ⟨138408729659492277039104551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184544972879323036052139401 138408729659492277039104551)
      ·
        refine ⟨207613094489238415558656827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138408729659492277039104551 207613094489238415558656827)
        ·
          refine ⟨311419641733857623337985241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207613094489238415558656827 311419641733857623337985241)
          ·
            refine ⟨233564731300393217503488931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311419641733857623337985241 233564731300393217503488931)
            ·
              refine ⟨350347096950589826255233397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233564731300393217503488931 350347096950589826255233397)
              ·
                refine ⟨32845040339117796211428131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350347096950589826255233397 32845040339117796211428131)
                ·
                  refine ⟨49267560508676694317142197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32845040339117796211428131 49267560508676694317142197)
                  ·
                    refine ⟨4618833797688440092232081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49267560508676694317142197 4618833797688440092232081)
                    ·
                      refine ⟨3464125348266330069174061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618833797688440092232081 3464125348266330069174061)
                      ·
                        rfl

theorem cell23_6746360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_6746360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746360 prefixEnd_6746360 := by exact prefixLift 6746360
  have htrace : WordTrace (prefixWord ++ tailWord_6746360) baseStart_6746360 baseEnd_6746360 := by
    simpa [prefixWord, tailWord_6746360, baseEnd_6746360] using wordTrace_append hprefix tailTrace_6746360
  have hstable : (prefixWord ++ tailWord_6746360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746360).length < 2 ^ (prefixWord ++ tailWord_6746360).sum := by decide
  have hdescent : baseEnd_6746360 < baseStart_6746360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746377 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 2, 3, 2]
def baseStart_6746377 : Nat := 118140960795 + 6746377 * 2 ^ 59
def prefixEnd_6746377 : Nat := 4983230072969 + 3 ^ 40 * 6746377 * 2
def baseEnd_6746377 : Nat := 3464134077437456502661483

theorem tailTrace_6746377 : CollatzResearch.WordTrace tailWord_6746377 prefixEnd_6746377 3464134077437456502661483 := by
  unfold tailWord_6746377
  simp only [CollatzResearch.WordTrace]
  refine ⟨246060583880035793306221385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164040389253357195537480923 246060583880035793306221385)
  ·
    refine ⟨184545437910026844979666039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246060583880035793306221385 184545437910026844979666039)
    ·
      refine ⟨276818156865040267469499059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184545437910026844979666039 276818156865040267469499059)
      ·
        refine ⟨415227235297560401204248589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276818156865040267469499059 415227235297560401204248589)
        ·
          refine ⟨155710213236585150451593221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415227235297560401204248589 155710213236585150451593221)
          ·
            refine ⟨29195664981859715709673729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155710213236585150451593221 29195664981859715709673729)
            ·
              refine ⟨21896748736394786782255297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29195664981859715709673729 21896748736394786782255297)
              ·
                refine ⟨16422561552296090086691473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21896748736394786782255297 16422561552296090086691473)
                ·
                  refine ⟨12316921164222067565018605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16422561552296090086691473 12316921164222067565018605)
                  ·
                    refine ⟨4618845436583275336881977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12316921164222067565018605 4618845436583275336881977)
                    ·
                      refine ⟨3464134077437456502661483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4618845436583275336881977 3464134077437456502661483)
                      ·
                        rfl

theorem cell23_6746377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 3, 2].length) (baseStart_6746377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746377 prefixEnd_6746377 := by exact prefixLift 6746377
  have htrace : WordTrace (prefixWord ++ tailWord_6746377) baseStart_6746377 baseEnd_6746377 := by
    simpa [prefixWord, tailWord_6746377, baseEnd_6746377] using wordTrace_append hprefix tailTrace_6746377
  have hstable : (prefixWord ++ tailWord_6746377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746377).length < 2 ^ (prefixWord ++ tailWord_6746377).sum := by decide
  have hdescent : baseEnd_6746377 < baseStart_6746377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746400 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 1, 6]
def baseStart_6746400 : Nat := 118140960795 + 6746400 * 2 ^ 59
def prefixEnd_6746400 : Nat := 4983230072969 + 3 ^ 40 * 6746400 * 2
def baseEnd_6746400 : Nat := 1154715295830836637557959

theorem tailTrace_6746400 : CollatzResearch.WordTrace tailWord_6746400 prefixEnd_6746400 1154715295830836637557959 := by
  unfold tailWord_6746400
  simp only [CollatzResearch.WordTrace]
  refine ⟨123030711379476234117154327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164040948505968312156205769 123030711379476234117154327)
  ·
    refine ⟨184546067069214351175731491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123030711379476234117154327 184546067069214351175731491)
    ·
      refine ⟨276819100603821526763597237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184546067069214351175731491 276819100603821526763597237)
      ·
        refine ⟨25951790681608268134087241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276819100603821526763597237 25951790681608268134087241)
        ·
          refine ⟨19463843011206201100565431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25951790681608268134087241 19463843011206201100565431)
          ·
            refine ⟨29195764516809301650848147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19463843011206201100565431 29195764516809301650848147)
            ·
              refine ⟨43793646775213952476272221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29195764516809301650848147 43793646775213952476272221)
              ·
                refine ⟨16422617540705232178602083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43793646775213952476272221 16422617540705232178602083)
                ·
                  refine ⟨24633926311057848267903125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16422617540705232178602083 24633926311057848267903125)
                  ·
                    refine ⟨1154715295830836637557959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24633926311057848267903125 1154715295830836637557959)
                    ·
                      rfl

theorem cell23_6746400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_6746400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746400 prefixEnd_6746400 := by exact prefixLift 6746400
  have htrace : WordTrace (prefixWord ++ tailWord_6746400) baseStart_6746400 baseEnd_6746400 := by
    simpa [prefixWord, tailWord_6746400, baseEnd_6746400] using wordTrace_append hprefix tailTrace_6746400
  have hstable : (prefixWord ++ tailWord_6746400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746400).length < 2 ^ (prefixWord ++ tailWord_6746400).sum := by decide
  have hdescent : baseEnd_6746400 < baseStart_6746400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746430 : List Nat := [4, 2, 1, 2, 1, 3, 10]
def baseStart_6746430 : Nat := 118140960795 + 6746430 * 2 ^ 59
def prefixEnd_6746430 : Nat := 4983230072969 + 3 ^ 40 * 6746430 * 2
def baseEnd_6746430 : Nat := 42767423356940059201219

theorem tailTrace_6746430 : CollatzResearch.WordTrace tailWord_6746430 prefixEnd_6746430 42767423356940059201219 := by
  unfold tailWord_6746430
  simp only [CollatzResearch.WordTrace]
  refine ⟨30757814618605472919737593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164041677965895855571933829 30757814618605472919737593)
  ·
    refine ⟨23068360963954104689803195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30757814618605472919737593 23068360963954104689803195)
    ·
      refine ⟨34602541445931157034704793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23068360963954104689803195 34602541445931157034704793)
      ·
        refine ⟨25951906084448367776028595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34602541445931157034704793 25951906084448367776028595)
        ·
          refine ⟨38927859126672551664042893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25951906084448367776028595 38927859126672551664042893)
          ·
            refine ⟨14597947172502206874016085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38927859126672551664042893 14597947172502206874016085)
            ·
              refine ⟨42767423356940059201219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14597947172502206874016085 42767423356940059201219)
              ·
                rfl

theorem cell23_6746430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 10].length) (baseStart_6746430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746430 prefixEnd_6746430 := by exact prefixLift 6746430
  have htrace : WordTrace (prefixWord ++ tailWord_6746430) baseStart_6746430 baseEnd_6746430 := by
    simpa [prefixWord, tailWord_6746430, baseEnd_6746430] using wordTrace_append hprefix tailTrace_6746430
  have hstable : (prefixWord ++ tailWord_6746430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746430).length < 2 ^ (prefixWord ++ tailWord_6746430).sum := by decide
  have hdescent : baseEnd_6746430 < baseStart_6746430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746440 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_6746440 : Nat := 118140960795 + 6746440 * 2 ^ 59
def prefixEnd_6746440 : Nat := 4983230072969 + 3 ^ 40 * 6746440 * 2
def baseEnd_6746440 : Nat := 3464166426718689756173693

theorem tailTrace_6746440 : CollatzResearch.WordTrace tailWord_6746440 prefixEnd_6746440 3464166426718689756173693 := by
  unfold tailWord_6746440
  simp only [CollatzResearch.WordTrace]
  refine ⟨123031440839403777532882387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164041921119205036710509849 123031440839403777532882387)
  ·
    refine ⟨184547161259105666299323581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123031440839403777532882387 184547161259105666299323581)
    ·
      refine ⟨69205185472164624862246343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184547161259105666299323581 69205185472164624862246343)
      ·
        refine ⟨103807778208246937293369515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69205185472164624862246343 103807778208246937293369515)
        ·
          refine ⟨155711667312370405940054273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103807778208246937293369515 155711667312370405940054273)
          ·
            refine ⟨116783750484277804455040705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155711667312370405940054273 116783750484277804455040705)
            ·
              refine ⟨87587812863208353341280529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116783750484277804455040705 87587812863208353341280529)
              ·
                refine ⟨65690859647406265005960397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87587812863208353341280529 65690859647406265005960397)
                ·
                  refine ⟨24634072367777349377235149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65690859647406265005960397 24634072367777349377235149)
                  ·
                    refine ⟨9237777137916506016463181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24634072367777349377235149 9237777137916506016463181)
                    ·
                      refine ⟨3464166426718689756173693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9237777137916506016463181 3464166426718689756173693)
                      ·
                        rfl

theorem cell23_6746440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_6746440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746440 prefixEnd_6746440 := by exact prefixLift 6746440
  have htrace : WordTrace (prefixWord ++ tailWord_6746440) baseStart_6746440 baseEnd_6746440 := by
    simpa [prefixWord, tailWord_6746440, baseEnd_6746440] using wordTrace_append hprefix tailTrace_6746440
  have hstable : (prefixWord ++ tailWord_6746440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746440).length < 2 ^ (prefixWord ++ tailWord_6746440).sum := by decide
  have hdescent : baseEnd_6746440 < baseStart_6746440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746443 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 2, 7]
def baseStart_6746443 : Nat := 118140960795 + 6746443 * 2 ^ 59
def prefixEnd_6746443 : Nat := 4983230072969 + 3 ^ 40 * 6746443 * 2
def baseEnd_6746443 : Nat := 1154722655720217748145393

theorem tailTrace_6746443 : CollatzResearch.WordTrace tailWord_6746443 prefixEnd_6746443 1154722655720217748145393 := by
  unfold tailWord_6746443
  simp only [CollatzResearch.WordTrace]
  refine ⟨246062991097796686578123983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164041994065197791052082655 246062991097796686578123983)
  ·
    refine ⟨369094486646695029867185975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246062991097796686578123983 369094486646695029867185975)
    ·
      refine ⟨553641729970042544800778963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369094486646695029867185975 553641729970042544800778963)
      ·
        refine ⟨830462594955063817201168445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553641729970042544800778963 830462594955063817201168445)
        ·
          refine ⟨311423473108148931450438167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830462594955063817201168445 311423473108148931450438167)
          ·
            refine ⟨467135209662223397175657251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311423473108148931450438167 467135209662223397175657251)
            ·
              refine ⟨700702814493335095763485877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467135209662223397175657251 700702814493335095763485877)
              ·
                refine ⟨65690888858750165227826801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 700702814493335095763485877 65690888858750165227826801)
                ·
                  refine ⟨49268166644062623920870101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65690888858750165227826801 49268166644062623920870101)
                  ·
                    refine ⟨1154722655720217748145393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49268166644062623920870101 1154722655720217748145393)
                    ·
                      rfl

theorem cell23_6746443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_6746443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746443 prefixEnd_6746443 := by exact prefixLift 6746443
  have htrace : WordTrace (prefixWord ++ tailWord_6746443) baseStart_6746443 baseEnd_6746443 := by
    simpa [prefixWord, tailWord_6746443, baseEnd_6746443] using wordTrace_append hprefix tailTrace_6746443
  have hstable : (prefixWord ++ tailWord_6746443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746443).length < 2 ^ (prefixWord ++ tailWord_6746443).sum := by decide
  have hdescent : baseEnd_6746443 < baseStart_6746443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746464 : List Nat := [2, 1, 1, 3, 6, 1, 2, 7]
def baseStart_6746464 : Nat := 118140960795 + 6746464 * 2 ^ 59
def prefixEnd_6746464 : Nat := 4983230072969 + 3 ^ 40 * 6746464 * 2
def baseEnd_6746464 : Nat := 128302916676088802306429

theorem tailTrace_6746464 : CollatzResearch.WordTrace tailWord_6746464 prefixEnd_6746464 128302916676088802306429 := by
  unfold tailWord_6746464
  simp only [CollatzResearch.WordTrace]
  refine ⟨123031878515360303582319223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164042504687147071443092297 123031878515360303582319223)
  ·
    refine ⟨184547817773040455373478835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123031878515360303582319223 184547817773040455373478835)
    ·
      refine ⟨276821726659560683060218253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184547817773040455373478835 276821726659560683060218253)
      ·
        refine ⟨103808147497335256147581845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276821726659560683060218253 103808147497335256147581845)
        ·
          refine ⟨4866006913937590131917899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103808147497335256147581845 4866006913937590131917899)
          ·
            refine ⟨7299010370906385197876849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866006913937590131917899 7299010370906385197876849)
            ·
              refine ⟨5474257778179788898407637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7299010370906385197876849 5474257778179788898407637)
              ·
                refine ⟨128302916676088802306429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5474257778179788898407637 128302916676088802306429)
                ·
                  rfl

theorem cell23_6746464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 7].length) (baseStart_6746464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746464 prefixEnd_6746464 := by exact prefixLift 6746464
  have htrace : WordTrace (prefixWord ++ tailWord_6746464) baseStart_6746464 baseEnd_6746464 := by
    simpa [prefixWord, tailWord_6746464, baseEnd_6746464] using wordTrace_append hprefix tailTrace_6746464
  have hstable : (prefixWord ++ tailWord_6746464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746464).length < 2 ^ (prefixWord ++ tailWord_6746464).sum := by decide
  have hdescent : baseEnd_6746464 < baseStart_6746464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746474 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6746474 : Nat := 118140960795 + 6746474 * 2 ^ 59
def prefixEnd_6746474 : Nat := 4983230072969 + 3 ^ 40 * 6746474 * 2
def baseEnd_6746474 : Nat := 3464183885060942623148537

theorem tailTrace_6746474 : CollatzResearch.WordTrace tailWord_6746474 prefixEnd_6746474 3464183885060942623148537 := by
  unfold tailWord_6746474
  simp only [CollatzResearch.WordTrace]
  refine ⟨61516030440171094718125619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164042747840456252581668317 61516030440171094718125619)
  ·
    refine ⟨92274045660256642077188429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61516030440171094718125619 92274045660256642077188429)
    ·
      refine ⟨34602767122596240778945661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92274045660256642077188429 34602767122596240778945661)
      ·
        refine ⟨12976037670973590292104623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34602767122596240778945661 12976037670973590292104623)
        ·
          refine ⟨19464056506460385438156935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12976037670973590292104623 19464056506460385438156935)
          ·
            refine ⟨29196084759690578157235403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19464056506460385438156935 29196084759690578157235403)
            ·
              refine ⟨43794127139535867235853105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29196084759690578157235403 43794127139535867235853105)
              ·
                refine ⟨32845595354651900426889829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43794127139535867235853105 32845595354651900426889829)
                ·
                  refine ⟨6158549128997231330041843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32845595354651900426889829 6158549128997231330041843)
                  ·
                    refine ⟨9237823693495846995062765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6158549128997231330041843 9237823693495846995062765)
                    ·
                      refine ⟨3464183885060942623148537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9237823693495846995062765 3464183885060942623148537)
                      ·
                        rfl

theorem cell23_6746474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6746474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746474 prefixEnd_6746474 := by exact prefixLift 6746474
  have htrace : WordTrace (prefixWord ++ tailWord_6746474) baseStart_6746474 baseEnd_6746474 := by
    simpa [prefixWord, tailWord_6746474, baseEnd_6746474] using wordTrace_append hprefix tailTrace_6746474
  have hstable : (prefixWord ++ tailWord_6746474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746474).length < 2 ^ (prefixWord ++ tailWord_6746474).sum := by decide
  have hdescent : baseEnd_6746474 < baseStart_6746474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746500 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6746500 : Nat := 118140960795 + 6746500 * 2 ^ 59
def prefixEnd_6746500 : Nat := 4983230072969 + 3 ^ 40 * 6746500 * 2
def baseEnd_6746500 : Nat := 3464197235557959521423417

theorem tailTrace_6746500 : CollatzResearch.WordTrace tailWord_6746500 prefixEnd_6746500 3464197235557959521423417 := by
  unfold tailWord_6746500
  simp only [CollatzResearch.WordTrace]
  refine ⟨123032535029295092656474477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164043380039060123541965969 123032535029295092656474477)
  ·
    refine ⟨46137200635985659746177929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123032535029295092656474477 46137200635985659746177929)
    ·
      refine ⟨34602900476989244809633447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46137200635985659746177929 34602900476989244809633447)
      ·
        refine ⟨51904350715483867214450171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34602900476989244809633447 51904350715483867214450171)
        ·
          refine ⟨77856526073225800821675257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51904350715483867214450171 77856526073225800821675257)
          ·
            refine ⟨58392394554919350616256443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77856526073225800821675257 58392394554919350616256443)
            ·
              refine ⟨87588591832379025924384665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58392394554919350616256443 87588591832379025924384665)
              ·
                refine ⟨65691443874284269443288499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87588591832379025924384665 65691443874284269443288499)
                ·
                  refine ⟨98537165811426404164932749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65691443874284269443288499 98537165811426404164932749)
                  ·
                    refine ⟨36951437179284901561849781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98537165811426404164932749 36951437179284901561849781)
                    ·
                      refine ⟨3464197235557959521423417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36951437179284901561849781 3464197235557959521423417)
                      ·
                        rfl

theorem cell23_6746500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6746500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746500 prefixEnd_6746500 := by exact prefixLift 6746500
  have htrace : WordTrace (prefixWord ++ tailWord_6746500) baseStart_6746500 baseEnd_6746500 := by
    simpa [prefixWord, tailWord_6746500, baseEnd_6746500] using wordTrace_append hprefix tailTrace_6746500
  have hstable : (prefixWord ++ tailWord_6746500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746500).length < 2 ^ (prefixWord ++ tailWord_6746500).sum := by decide
  have hdescent : baseEnd_6746500 < baseStart_6746500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746607 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 3]
def baseStart_6746607 : Nat := 118140960795 + 6746607 * 2 ^ 59
def prefixEnd_6746607 : Nat := 4983230072969 + 3 ^ 40 * 6746607 * 2
def baseEnd_6746607 : Nat := 3464252177987990602785425

theorem tailTrace_6746607 : CollatzResearch.WordTrace tailWord_6746607 prefixEnd_6746607 3464252177987990602785425 := by
  unfold tailWord_6746607
  simp only [CollatzResearch.WordTrace]
  refine ⟨246068972669202542587094075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164045981779468361724729383 246068972669202542587094075)
  ·
    refine ⟨369103459003803813880641113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246068972669202542587094075 369103459003803813880641113)
    ·
      refine ⟨276827594252852860410480835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369103459003803813880641113 276827594252852860410480835)
      ·
        refine ⟨415241391379279290615721253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276827594252852860410480835 415241391379279290615721253)
        ·
          refine ⟨77857760883614866990447735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415241391379279290615721253 77857760883614866990447735)
          ·
            refine ⟨116786641325422300485671603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77857760883614866990447735 116786641325422300485671603)
            ·
              refine ⟨175179961988133450728507405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116786641325422300485671603 175179961988133450728507405)
              ·
                refine ⟨65692485745550044023190277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175179961988133450728507405 65692485745550044023190277)
                ·
                  refine ⟨12317341077290633254348177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65692485745550044023190277 12317341077290633254348177)
                  ·
                    refine ⟨9238005807967974940761133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12317341077290633254348177 9238005807967974940761133)
                    ·
                      refine ⟨3464252177987990602785425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9238005807967974940761133 3464252177987990602785425)
                      ·
                        rfl

theorem cell23_6746607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_6746607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746607 prefixEnd_6746607 := by exact prefixLift 6746607
  have htrace : WordTrace (prefixWord ++ tailWord_6746607) baseStart_6746607 baseEnd_6746607 := by
    simpa [prefixWord, tailWord_6746607, baseEnd_6746607] using wordTrace_append hprefix tailTrace_6746607
  have hstable : (prefixWord ++ tailWord_6746607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746607).length < 2 ^ (prefixWord ++ tailWord_6746607).sum := by decide
  have hdescent : baseEnd_6746607 < baseStart_6746607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746644 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 8]
def baseStart_6746644 : Nat := 118140960795 + 6746644 * 2 ^ 59
def prefixEnd_6746644 : Nat := 4983230072969 + 3 ^ 40 * 6746644 * 2
def baseEnd_6746644 : Nat := 384919019641356328669195

theorem tailTrace_6746644 : CollatzResearch.WordTrace tailWord_6746644 prefixEnd_6746644 384919019641356328669195 := by
  unfold tailWord_6746644
  simp only [CollatzResearch.WordTrace]
  refine ⟨123035161085034248953095493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164046881446712331937460657 123035161085034248953095493)
  ·
    refine ⟨23069092703443921678705405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123035161085034248953095493 23069092703443921678705405)
    ·
      refine ⟨8650909763791470629514527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23069092703443921678705405 8650909763791470629514527)
      ·
        refine ⟨12976364645687205944271791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8650909763791470629514527 12976364645687205944271791)
        ·
          refine ⟨19464546968530808916407687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12976364645687205944271791 19464546968530808916407687)
          ·
            refine ⟨29196820452796213374611531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19464546968530808916407687 29196820452796213374611531)
            ·
              refine ⟨43795230679194320061917297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29196820452796213374611531 43795230679194320061917297)
              ·
                refine ⟨32846423009395740046437973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43795230679194320061917297 32846423009395740046437973)
                ·
                  refine ⟨384919019641356328669195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32846423009395740046437973 384919019641356328669195)
                  ·
                    rfl

theorem cell23_6746644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_6746644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746644 prefixEnd_6746644 := by exact prefixLift 6746644
  have htrace : WordTrace (prefixWord ++ tailWord_6746644) baseStart_6746644 baseEnd_6746644 := by
    simpa [prefixWord, tailWord_6746644, baseEnd_6746644] using wordTrace_append hprefix tailTrace_6746644
  have hstable : (prefixWord ++ tailWord_6746644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746644).length < 2 ^ (prefixWord ++ tailWord_6746644).sum := by decide
  have hdescent : baseEnd_6746644 < baseStart_6746644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746648 : List Nat := [2, 1, 2, 3, 3, 3, 1, 3, 1, 4]
def baseStart_6746648 : Nat := 118140960795 + 6746648 * 2 ^ 59
def prefixEnd_6746648 : Nat := 4983230072969 + 3 ^ 40 * 6746648 * 2
def baseEnd_6746648 : Nat := 1154757743564941647457579

theorem tailTrace_6746648 : CollatzResearch.WordTrace tailWord_6746648 prefixEnd_6746648 1154757743564941647457579 := by
  unfold tailWord_6746648
  simp only [CollatzResearch.WordTrace]
  refine ⟨123035234031027003294668299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164046978708036004392891065 123035234031027003294668299)
  ·
    refine ⟨184552851046540504942002449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123035234031027003294668299 184552851046540504942002449)
    ·
      refine ⟨138414638284905378706501837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184552851046540504942002449 138414638284905378706501837)
      ·
        refine ⟨51905489356839517014938189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138414638284905378706501837 51905489356839517014938189)
        ·
          refine ⟨19464558508814818880601821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51905489356839517014938189 19464558508814818880601821)
          ·
            refine ⟨7299209440805557080225683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19464558508814818880601821 7299209440805557080225683)
            ·
              refine ⟨10948814161208335620338525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7299209440805557080225683 10948814161208335620338525)
              ·
                refine ⟨4105805310453125857626947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10948814161208335620338525 4105805310453125857626947)
                ·
                  refine ⟨6158707965679688786440421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105805310453125857626947 6158707965679688786440421)
                  ·
                    refine ⟨1154757743564941647457579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6158707965679688786440421 1154757743564941647457579)
                    ·
                      rfl

theorem cell23_6746648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_6746648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746648 prefixEnd_6746648 := by exact prefixLift 6746648
  have htrace : WordTrace (prefixWord ++ tailWord_6746648) baseStart_6746648 baseEnd_6746648 := by
    simpa [prefixWord, tailWord_6746648, baseEnd_6746648] using wordTrace_append hprefix tailTrace_6746648
  have hstable : (prefixWord ++ tailWord_6746648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746648).length < 2 ^ (prefixWord ++ tailWord_6746648).sum := by decide
  have hdescent : baseEnd_6746648 < baseStart_6746648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746678 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_6746678 : Nat := 118140960795 + 6746678 * 2 ^ 59
def prefixEnd_6746678 : Nat := 4983230072969 + 3 ^ 40 * 6746678 * 2
def baseEnd_6746678 : Nat := 384920959457162202777511

theorem tailTrace_6746678 : CollatzResearch.WordTrace tailWord_6746678 prefixEnd_6746678 384920959457162202777511 := by
  unfold tailWord_6746678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15379472640746582607058043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164047708167963547808619125 15379472640746582607058043)
  ·
    refine ⟨23069208961119873910587065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15379472640746582607058043 23069208961119873910587065)
    ·
      refine ⟨17301906720839905432940299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23069208961119873910587065 17301906720839905432940299)
      ·
        refine ⟨25952860081259858149410449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17301906720839905432940299 25952860081259858149410449)
        ·
          refine ⟨19464645060944893612057837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25952860081259858149410449 19464645060944893612057837)
          ·
            refine ⟨7299241897854335104521689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19464645060944893612057837 7299241897854335104521689)
            ·
              refine ⟨5474431423390751328391267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7299241897854335104521689 5474431423390751328391267)
              ·
                refine ⟨8211647135086126992586901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474431423390751328391267 8211647135086126992586901)
                ·
                  refine ⟨384920959457162202777511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8211647135086126992586901 384920959457162202777511)
                  ·
                    rfl

theorem cell23_6746678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_6746678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746678 prefixEnd_6746678 := by exact prefixLift 6746678
  have htrace : WordTrace (prefixWord ++ tailWord_6746678) baseStart_6746678 baseEnd_6746678 := by
    simpa [prefixWord, tailWord_6746678, baseEnd_6746678] using wordTrace_append hprefix tailTrace_6746678
  have hstable : (prefixWord ++ tailWord_6746678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746678).length < 2 ^ (prefixWord ++ tailWord_6746678).sum := by decide
  have hdescent : baseEnd_6746678 < baseStart_6746678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746687 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 1, 6]
def baseStart_6746687 : Nat := 118140960795 + 6746687 * 2 ^ 59
def prefixEnd_6746687 : Nat := 4983230072969 + 3 ^ 40 * 6746687 * 2
def baseEnd_6746687 : Nat := 1154764418813450096595019

theorem tailTrace_6746687 : CollatzResearch.WordTrace tailWord_6746687 prefixEnd_6746687 1154764418813450096595019 := by
  unfold tailWord_6746687
  simp only [CollatzResearch.WordTrace]
  refine ⟨246071890508912716250006315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164047927005941810833337543 246071890508912716250006315)
  ·
    refine ⟨369107835763369074375009473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246071890508912716250006315 369107835763369074375009473)
    ·
      refine ⟨276830876822526805781257105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369107835763369074375009473 276830876822526805781257105)
      ·
        refine ⟨207623157616895104335942829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276830876822526805781257105 207623157616895104335942829)
        ·
          refine ⟨77858684106335664125978561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207623157616895104335942829 77858684106335664125978561)
          ·
            refine ⟨58394013079751748094483921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77858684106335664125978561 58394013079751748094483921)
            ·
              refine ⟨43795509809813811070862941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58394013079751748094483921 43795509809813811070862941)
              ·
                refine ⟨16423316178680179151573603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43795509809813811070862941 16423316178680179151573603)
                ·
                  refine ⟨24634974268020268727360405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16423316178680179151573603 24634974268020268727360405)
                  ·
                    refine ⟨1154764418813450096595019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24634974268020268727360405 1154764418813450096595019)
                    ·
                      rfl

theorem cell23_6746687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_6746687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746687 prefixEnd_6746687 := by exact prefixLift 6746687
  have htrace : WordTrace (prefixWord ++ tailWord_6746687) baseStart_6746687 baseEnd_6746687 := by
    simpa [prefixWord, tailWord_6746687, baseEnd_6746687] using wordTrace_append hprefix tailTrace_6746687
  have hstable : (prefixWord ++ tailWord_6746687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746687).length < 2 ^ (prefixWord ++ tailWord_6746687).sum := by decide
  have hdescent : baseEnd_6746687 < baseStart_6746687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746711 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 1, 1, 4]
def baseStart_6746711 : Nat := 118140960795 + 6746711 * 2 ^ 59
def prefixEnd_6746711 : Nat := 4983230072969 + 3 ^ 40 * 6746711 * 2
def baseEnd_6746711 : Nat := 3464305579976058195884947

theorem tailTrace_6746711 : CollatzResearch.WordTrace tailWord_6746711 prefixEnd_6746711 3464305579976058195884947 := by
  unfold tailWord_6746711
  simp only [CollatzResearch.WordTrace]
  refine ⟨246072765860825768348879987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164048510573883845565919991 246072765860825768348879987)
  ·
    refine ⟨369109148791238652523319981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246072765860825768348879987 369109148791238652523319981)
    ·
      refine ⟨138415930796714494696244993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369109148791238652523319981 138415930796714494696244993)
      ·
        refine ⟨103811948097535871022183745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138415930796714494696244993 103811948097535871022183745)
        ·
          refine ⟨77858961073151903266637809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103811948097535871022183745 77858961073151903266637809)
          ·
            refine ⟨58394220804863927449978357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77858961073151903266637809 58394220804863927449978357)
            ·
              refine ⟨5474458200455993198435471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58394220804863927449978357 5474458200455993198435471)
              ·
                refine ⟨8211687300683989797653207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474458200455993198435471 8211687300683989797653207)
                ·
                  refine ⟨12317530951025984696479811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211687300683989797653207 12317530951025984696479811)
                  ·
                    refine ⟨18476296426538977044719717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12317530951025984696479811 18476296426538977044719717)
                    ·
                      refine ⟨3464305579976058195884947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18476296426538977044719717 3464305579976058195884947)
                      ·
                        rfl

theorem cell23_6746711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_6746711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746711 prefixEnd_6746711 := by exact prefixLift 6746711
  have htrace : WordTrace (prefixWord ++ tailWord_6746711) baseStart_6746711 baseEnd_6746711 := by
    simpa [prefixWord, tailWord_6746711, baseEnd_6746711] using wordTrace_append hprefix tailTrace_6746711
  have hstable : (prefixWord ++ tailWord_6746711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746711).length < 2 ^ (prefixWord ++ tailWord_6746711).sum := by decide
  have hdescent : baseEnd_6746711 < baseStart_6746711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746717 : List Nat := [1, 4, 4, 14]
def baseStart_6746717 : Nat := 118140960795 + 6746717 * 2 ^ 59
def prefixEnd_6746717 : Nat := 4983230072969 + 3 ^ 40 * 6746717 * 2
def baseEnd_6746717 : Nat := 1584046026913573467037

theorem tailTrace_6746717 : CollatzResearch.WordTrace tailWord_6746717 prefixEnd_6746717 1584046026913573467037 := by
  unfold tailWord_6746717
  simp only [CollatzResearch.WordTrace]
  refine ⟨246072984698804031373598405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164048656465869354249065603 246072984698804031373598405)
  ·
    refine ⟨46138684631025755882549701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246072984698804031373598405 46138684631025755882549701)
    ·
      refine ⟨8651003368317329227978069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46138684631025755882549701 8651003368317329227978069)
      ·
        refine ⟨1584046026913573467037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8651003368317329227978069 1584046026913573467037)
        ·
          rfl

theorem cell23_6746717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 14].length) (baseStart_6746717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746717 prefixEnd_6746717 := by exact prefixLift 6746717
  have htrace : WordTrace (prefixWord ++ tailWord_6746717) baseStart_6746717 baseEnd_6746717 := by
    simpa [prefixWord, tailWord_6746717, baseEnd_6746717] using wordTrace_append hprefix tailTrace_6746717
  have hstable : (prefixWord ++ tailWord_6746717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746717).length < 2 ^ (prefixWord ++ tailWord_6746717).sum := by decide
  have hdescent : baseEnd_6746717 < baseStart_6746717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746721 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 2, 4]
def baseStart_6746721 : Nat := 118140960795 + 6746721 * 2 ^ 59
def prefixEnd_6746721 : Nat := 4983230072969 + 3 ^ 40 * 6746721 * 2
def baseEnd_6746721 : Nat := 1154770238260867718919967

theorem tailTrace_6746721 : CollatzResearch.WordTrace tailWord_6746721 prefixEnd_6746721 1154770238260867718919967 := by
  unfold tailWord_6746721
  simp only [CollatzResearch.WordTrace]
  refine ⟨246073130590789540056744017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164048753727193026704496011 246073130590789540056744017)
  ·
    refine ⟨184554847943092155042558013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246073130590789540056744017 184554847943092155042558013)
    ·
      refine ⟨69208067978659558140959255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184554847943092155042558013 69208067978659558140959255)
      ·
        refine ⟨103812101967989337211438883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69208067978659558140959255 103812101967989337211438883)
        ·
          refine ⟨155718152951984005817158325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103812101967989337211438883 155718152951984005817158325)
          ·
            refine ⟨14598576839248500545358593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155718152951984005817158325 14598576839248500545358593)
            ·
              refine ⟨10948932629436375409018945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14598576839248500545358593 10948932629436375409018945)
              ·
                refine ⟨8211699472077281556764209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10948932629436375409018945 8211699472077281556764209)
                ·
                  refine ⟨6158774604057961167573157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8211699472077281556764209 6158774604057961167573157)
                  ·
                    refine ⟨1154770238260867718919967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6158774604057961167573157 1154770238260867718919967)
                    ·
                      rfl

theorem cell23_6746721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_6746721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746721 prefixEnd_6746721 := by exact prefixLift 6746721
  have htrace : WordTrace (prefixWord ++ tailWord_6746721) baseStart_6746721 baseEnd_6746721 := by
    simpa [prefixWord, tailWord_6746721, baseEnd_6746721] using wordTrace_append hprefix tailTrace_6746721
  have hstable : (prefixWord ++ tailWord_6746721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746721).length < 2 ^ (prefixWord ++ tailWord_6746721).sum := by decide
  have hdescent : baseEnd_6746721 < baseStart_6746721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746722 : List Nat := [3, 3, 2, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6746722 : Nat := 118140960795 + 6746722 * 2 ^ 59
def prefixEnd_6746722 : Nat := 4983230072969 + 3 ^ 40 * 6746722 * 2
def baseEnd_6746722 : Nat := 3464311228263257652847397

theorem tailTrace_6746722 : CollatzResearch.WordTrace tailWord_6746722 prefixEnd_6746722 3464311228263257652847397 := by
  unfold tailWord_6746722
  simp only [CollatzResearch.WordTrace]
  refine ⟨61518291765946479306882605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164048778042523944818353613 61518291765946479306882605)
  ·
    refine ⟨23069359412229929740080977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61518291765946479306882605 23069359412229929740080977)
    ·
      refine ⟨17302019559172447305060733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23069359412229929740080977 17302019559172447305060733)
      ·
        refine ⟨6488257334689667739397775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17302019559172447305060733 6488257334689667739397775)
        ·
          refine ⟨9732386002034501609096663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488257334689667739397775 9732386002034501609096663)
          ·
            refine ⟨14598579003051752413644995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9732386002034501609096663 14598579003051752413644995)
            ·
              refine ⟨21897868504577628620467493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14598579003051752413644995 21897868504577628620467493)
              ·
                refine ⟨4105850344608305366337655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21897868504577628620467493 4105850344608305366337655)
                ·
                  refine ⟨6158775516912458049506483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105850344608305366337655 6158775516912458049506483)
                  ·
                    refine ⟨9238163275368687074259725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6158775516912458049506483 9238163275368687074259725)
                    ·
                      refine ⟨3464311228263257652847397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9238163275368687074259725 3464311228263257652847397)
                      ·
                        rfl

theorem cell23_6746722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6746722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746722 prefixEnd_6746722 := by exact prefixLift 6746722
  have htrace : WordTrace (prefixWord ++ tailWord_6746722) baseStart_6746722 baseEnd_6746722 := by
    simpa [prefixWord, tailWord_6746722, baseEnd_6746722] using wordTrace_append hprefix tailTrace_6746722
  have hstable : (prefixWord ++ tailWord_6746722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746722).length < 2 ^ (prefixWord ++ tailWord_6746722).sum := by decide
  have hdescent : baseEnd_6746722 < baseStart_6746722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746734 : List Nat := [4, 1, 2, 2, 2, 1, 3, 8]
def baseStart_6746734 : Nat := 118140960795 + 6746734 * 2 ^ 59
def prefixEnd_6746734 : Nat := 4983230072969 + 3 ^ 40 * 6746734 * 2
def baseEnd_6746734 : Nat := 128308051482633763181383

theorem tailTrace_6746734 : CollatzResearch.WordTrace tailWord_6746734 prefixEnd_6746734 128308051482633763181383 := by
  unfold tailWord_6746734
  simp only [CollatzResearch.WordTrace]
  refine ⟨30759200592467805409620907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164049069826494962184644837 30759200592467805409620907)
  ·
    refine ⟨46138800888701708114431361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30759200592467805409620907 46138800888701708114431361)
    ·
      refine ⟨34604100666526281085823521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46138800888701708114431361 34604100666526281085823521)
      ·
        refine ⟨25953075499894710814367641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34604100666526281085823521 25953075499894710814367641)
        ·
          refine ⟨19464806624921033110775731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25953075499894710814367641 19464806624921033110775731)
          ·
            refine ⟨29197209937381549666163597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19464806624921033110775731 29197209937381549666163597)
            ·
              refine ⟨10948953726518081124811349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29197209937381549666163597 10948953726518081124811349)
              ·
                refine ⟨128308051482633763181383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10948953726518081124811349 128308051482633763181383)
                ·
                  rfl

theorem cell23_6746734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_6746734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746734 prefixEnd_6746734 := by exact prefixLift 6746734
  have htrace : WordTrace (prefixWord ++ tailWord_6746734) baseStart_6746734 baseEnd_6746734 := by
    simpa [prefixWord, tailWord_6746734, baseEnd_6746734] using wordTrace_append hprefix tailTrace_6746734
  have hstable : (prefixWord ++ tailWord_6746734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746734).length < 2 ^ (prefixWord ++ tailWord_6746734).sum := by decide
  have hdescent : baseEnd_6746734 < baseStart_6746734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746762 : List Nat := [3, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_6746762 : Nat := 118140960795 + 6746762 * 2 ^ 59
def prefixEnd_6746762 : Nat := 4983230072969 + 3 ^ 40 * 6746762 * 2
def baseEnd_6746762 : Nat := 3464331767489437496347213

theorem tailTrace_6746762 : CollatzResearch.WordTrace tailWord_6746762 prefixEnd_6746762 3464331767489437496347213 := by
  unfold tailWord_6746762
  simp only [CollatzResearch.WordTrace]
  refine ⟨61518656495910251014746635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164049750655760669372657693 61518656495910251014746635)
  ·
    refine ⟨92277984743865376522119953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61518656495910251014746635 92277984743865376522119953)
    ·
      refine ⟨69208488557899032391589965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92277984743865376522119953 69208488557899032391589965)
      ·
        refine ⟨25953183209212137146846237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69208488557899032391589965 25953183209212137146846237)
        ·
          refine ⟨9732443703454551430067339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25953183209212137146846237 9732443703454551430067339)
          ·
            refine ⟨14598665555181827145101009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9732443703454551430067339 14598665555181827145101009)
            ·
              refine ⟨10948999166386370358825757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14598665555181827145101009 10948999166386370358825757)
              ·
                refine ⟨4105874687394888884559659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10948999166386370358825757 4105874687394888884559659)
                ·
                  refine ⟨6158812031092333326839489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105874687394888884559659 6158812031092333326839489)
                  ·
                    refine ⟨4619109023319249995129617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6158812031092333326839489 4619109023319249995129617)
                    ·
                      refine ⟨3464331767489437496347213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619109023319249995129617 3464331767489437496347213)
                      ·
                        rfl

theorem cell23_6746762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_6746762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746762 prefixEnd_6746762 := by exact prefixLift 6746762
  have htrace : WordTrace (prefixWord ++ tailWord_6746762) baseStart_6746762 baseEnd_6746762 := by
    simpa [prefixWord, tailWord_6746762, baseEnd_6746762] using wordTrace_append hprefix tailTrace_6746762
  have hstable : (prefixWord ++ tailWord_6746762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746762).length < 2 ^ (prefixWord ++ tailWord_6746762).sum := by decide
  have hdescent : baseEnd_6746762 < baseStart_6746762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746767 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_6746767 : Nat := 118140960795 + 6746767 * 2 ^ 59
def prefixEnd_6746767 : Nat := 4983230072969 + 3 ^ 40 * 6746767 * 2
def baseEnd_6746767 : Nat := 3464334334892709976784689

theorem tailTrace_6746767 : CollatzResearch.WordTrace tailWord_6746767 prefixEnd_6746767 3464334334892709976784689 := by
  unfold tailWord_6746767
  simp only [CollatzResearch.WordTrace]
  refine ⟨246074808348622889912918555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164049872232415259941945703 246074808348622889912918555)
  ·
    refine ⟨369112212522934334869377833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246074808348622889912918555 369112212522934334869377833)
    ·
      refine ⟨276834159392200751152033375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369112212522934334869377833 276834159392200751152033375)
      ·
        refine ⟨415251239088301126728050063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276834159392200751152033375 415251239088301126728050063)
        ·
          refine ⟨622876858632451690092075095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415251239088301126728050063 622876858632451690092075095)
          ·
            refine ⟨934315287948677535138112643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622876858632451690092075095 934315287948677535138112643)
            ·
              refine ⟨1401472931923016302707168965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934315287948677535138112643 1401472931923016302707168965)
              ·
                refine ⟨262776174735565556757594181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1401472931923016302707168965 262776174735565556757594181)
                ·
                  refine ⟨49270532762918541892048909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262776174735565556757594181 49270532762918541892048909)
                  ·
                    refine ⟨18476449786094453209518341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49270532762918541892048909 18476449786094453209518341)
                    ·
                      refine ⟨3464334334892709976784689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18476449786094453209518341 3464334334892709976784689)
                      ·
                        rfl

theorem cell23_6746767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_6746767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746767 prefixEnd_6746767 := by exact prefixLift 6746767
  have htrace : WordTrace (prefixWord ++ tailWord_6746767) baseStart_6746767 baseEnd_6746767 := by
    simpa [prefixWord, tailWord_6746767, baseEnd_6746767] using wordTrace_append hprefix tailTrace_6746767
  have hstable : (prefixWord ++ tailWord_6746767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746767).length < 2 ^ (prefixWord ++ tailWord_6746767).sum := by decide
  have hdescent : baseEnd_6746767 < baseStart_6746767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746771 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 1, 3, 2]
def baseStart_6746771 : Nat := 118140960795 + 6746771 * 2 ^ 59
def prefixEnd_6746771 : Nat := 4983230072969 + 3 ^ 40 * 6746771 * 2
def baseEnd_6746771 : Nat := 3464336388815327961134671

theorem tailTrace_6746771 : CollatzResearch.WordTrace tailWord_6746771 prefixEnd_6746771 3464336388815327961134671 := by
  unfold tailWord_6746771
  simp only [CollatzResearch.WordTrace]
  refine ⟨246074954240608398596064167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164049969493738932397376111 246074954240608398596064167)
  ·
    refine ⟨369112431360912597894096251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246074954240608398596064167 369112431360912597894096251)
    ·
      refine ⟨553668647041368896841144377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369112431360912597894096251 553668647041368896841144377)
      ·
        refine ⟨415251485281026672630858283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553668647041368896841144377 415251485281026672630858283)
        ·
          refine ⟨622877227921540008946287425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415251485281026672630858283 622877227921540008946287425)
          ·
            refine ⟨467157920941155006709715569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622877227921540008946287425 467157920941155006709715569)
            ·
              refine ⟨350368440705866255032286677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467157920941155006709715569 350368440705866255032286677)
              ·
                refine ⟨8211760329043740352319219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 350368440705866255032286677 8211760329043740352319219)
                ·
                  refine ⟨12317640493565610528478829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211760329043740352319219 12317640493565610528478829)
                  ·
                    refine ⟨4619115185087103948179561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12317640493565610528478829 4619115185087103948179561)
                    ·
                      refine ⟨3464336388815327961134671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619115185087103948179561 3464336388815327961134671)
                      ·
                        rfl

theorem cell23_6746771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 3, 2].length) (baseStart_6746771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746771 prefixEnd_6746771 := by exact prefixLift 6746771
  have htrace : WordTrace (prefixWord ++ tailWord_6746771) baseStart_6746771 baseEnd_6746771 := by
    simpa [prefixWord, tailWord_6746771, baseEnd_6746771] using wordTrace_append hprefix tailTrace_6746771
  have hstable : (prefixWord ++ tailWord_6746771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746771).length < 2 ^ (prefixWord ++ tailWord_6746771).sum := by decide
  have hdescent : baseEnd_6746771 < baseStart_6746771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746777 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 4, 6]
def baseStart_6746777 : Nat := 118140960795 + 6746777 * 2 ^ 59
def prefixEnd_6746777 : Nat := 4983230072969 + 3 ^ 40 * 6746777 * 2
def baseEnd_6746777 : Nat := 1154779823233084979219881

theorem tailTrace_6746777 : CollatzResearch.WordTrace tailWord_6746777 prefixEnd_6746777 1154779823233084979219881 := by
  unfold tailWord_6746777
  simp only [CollatzResearch.WordTrace]
  refine ⟨246075173078586661620782585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164050115385724441080521723 246075173078586661620782585)
  ·
    refine ⟨184556379808939996215586939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246075173078586661620782585 184556379808939996215586939)
    ·
      refine ⟨276834569713409994323380409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184556379808939996215586939 276834569713409994323380409)
      ·
        refine ⟨207625927285057495742535307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276834569713409994323380409 207625927285057495742535307)
        ·
          refine ⟨311438890927586243613802961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207625927285057495742535307 311438890927586243613802961)
          ·
            refine ⟨233579168195689682710352221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311438890927586243613802961 233579168195689682710352221)
            ·
              refine ⟨87592188073383631016382083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233579168195689682710352221 87592188073383631016382083)
              ·
                refine ⟨131388282110075446524573125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87592188073383631016382083 131388282110075446524573125)
                ·
                  refine ⟨24635302895639146223357461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131388282110075446524573125 24635302895639146223357461)
                  ·
                    refine ⟨1154779823233084979219881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24635302895639146223357461 1154779823233084979219881)
                    ·
                      rfl

theorem cell23_6746777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_6746777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746777 prefixEnd_6746777 := by exact prefixLift 6746777
  have htrace : WordTrace (prefixWord ++ tailWord_6746777) baseStart_6746777 baseEnd_6746777 := by
    simpa [prefixWord, tailWord_6746777, baseEnd_6746777] using wordTrace_append hprefix tailTrace_6746777
  have hstable : (prefixWord ++ tailWord_6746777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746777).length < 2 ^ (prefixWord ++ tailWord_6746777).sum := by decide
  have hdescent : baseEnd_6746777 < baseStart_6746777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746787 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5]
def baseStart_6746787 : Nat := 118140960795 + 6746787 * 2 ^ 59
def prefixEnd_6746787 : Nat := 4983230072969 + 3 ^ 40 * 6746787 * 2
def baseEnd_6746787 : Nat := 3464344604505799898534597

theorem tailTrace_6746787 : CollatzResearch.WordTrace tailWord_6746787 prefixEnd_6746787 3464344604505799898534597 := by
  unfold tailWord_6746787
  simp only [CollatzResearch.WordTrace]
  refine ⟨246075537808550433328646615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164050358539033622219097743 246075537808550433328646615)
  ·
    refine ⟨369113306712825649992969923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246075537808550433328646615 369113306712825649992969923)
    ·
      refine ⟨553669960069238474989454885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369113306712825649992969923 553669960069238474989454885)
      ·
        refine ⟨103813117512982214060522791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 553669960069238474989454885 103813117512982214060522791)
        ·
          refine ⟨155719676269473321090784187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103813117512982214060522791 155719676269473321090784187)
          ·
            refine ⟨233579514404209981636176281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155719676269473321090784187 233579514404209981636176281)
            ·
              refine ⟨175184635803157486227132211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233579514404209981636176281 175184635803157486227132211)
              ·
                refine ⟨262776953704736229340698317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175184635803157486227132211 262776953704736229340698317)
                ·
                  refine ⟨98541357639276086002761869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262776953704736229340698317 98541357639276086002761869)
                  ·
                    refine ⟨36953009114728532251035701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98541357639276086002761869 36953009114728532251035701)
                    ·
                      refine ⟨3464344604505799898534597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36953009114728532251035701 3464344604505799898534597)
                      ·
                        rfl

theorem cell23_6746787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_6746787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746787 prefixEnd_6746787 := by exact prefixLift 6746787
  have htrace : WordTrace (prefixWord ++ tailWord_6746787) baseStart_6746787 baseEnd_6746787 := by
    simpa [prefixWord, tailWord_6746787, baseEnd_6746787] using wordTrace_append hprefix tailTrace_6746787
  have hstable : (prefixWord ++ tailWord_6746787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746787).length < 2 ^ (prefixWord ++ tailWord_6746787).sum := by decide
  have hdescent : baseEnd_6746787 < baseStart_6746787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746805 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_6746805 : Nat := 118140960795 + 6746805 * 2 ^ 59
def prefixEnd_6746805 : Nat := 4983230072969 + 3 ^ 40 * 6746805 * 2
def baseEnd_6746805 : Nat := 3464353847157580828109515

theorem tailTrace_6746805 : CollatzResearch.WordTrace tailWord_6746805 prefixEnd_6746805 3464353847157580828109515 := by
  unfold tailWord_6746805
  simp only [CollatzResearch.WordTrace]
  refine ⟨246076194322485222402801869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164050796214990148268534579 246076194322485222402801869)
  ·
    refine ⟨92278572870931958401050701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246076194322485222402801869 92278572870931958401050701)
    ·
      refine ⟨34604464826599484400394013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92278572870931958401050701 34604464826599484400394013)
      ·
        refine ⟨12976674309974806650147755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34604464826599484400394013 12976674309974806650147755)
        ·
          refine ⟨19465011464962209975221633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12976674309974806650147755 19465011464962209975221633)
          ·
            refine ⟨14598758598721657481416225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19465011464962209975221633 14598758598721657481416225)
            ·
              refine ⟨10949068949041243111062169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14598758598721657481416225 10949068949041243111062169)
              ·
                refine ⟨8211801711780932333296627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10949068949041243111062169 8211801711780932333296627)
                ·
                  refine ⟨12317702567671398499944941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211801711780932333296627 12317702567671398499944941)
                  ·
                    refine ⟨4619138462876774437479353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12317702567671398499944941 4619138462876774437479353)
                    ·
                      refine ⟨3464353847157580828109515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619138462876774437479353 3464353847157580828109515)
                      ·
                        rfl

theorem cell23_6746805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_6746805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746805 prefixEnd_6746805 := by exact prefixLift 6746805
  have htrace : WordTrace (prefixWord ++ tailWord_6746805) baseStart_6746805 baseEnd_6746805 := by
    simpa [prefixWord, tailWord_6746805, baseEnd_6746805] using wordTrace_append hprefix tailTrace_6746805
  have hstable : (prefixWord ++ tailWord_6746805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746805).length < 2 ^ (prefixWord ++ tailWord_6746805).sum := by decide
  have hdescent : baseEnd_6746805 < baseStart_6746805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746827 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6]
def baseStart_6746827 : Nat := 118140960795 + 6746827 * 2 ^ 59
def prefixEnd_6746827 : Nat := 4983230072969 + 3 ^ 40 * 6746827 * 2
def baseEnd_6746827 : Nat := 3464365143731979742034413

theorem tailTrace_6746827 : CollatzResearch.WordTrace tailWord_6746827 prefixEnd_6746827 3464365143731979742034413 := by
  unfold tailWord_6746827
  simp only [CollatzResearch.WordTrace]
  refine ⟨246076996728405520160102735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164051331152270346773401823 246076996728405520160102735)
  ·
    refine ⟨369115495092608280240154103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246076996728405520160102735 369115495092608280240154103)
    ·
      refine ⟨553673242638912420360231155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369115495092608280240154103 553673242638912420360231155)
      ·
        refine ⟨830509863958368630540346733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553673242638912420360231155 830509863958368630540346733)
        ·
          refine ⟨311441198984388236452630025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830509863958368630540346733 311441198984388236452630025)
          ·
            refine ⟨233580899238291177339472519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311441198984388236452630025 233580899238291177339472519)
            ·
              refine ⟨350371348857436766009208779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233580899238291177339472519 350371348857436766009208779)
              ·
                refine ⟨525557023286155149013813169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350371348857436766009208779 525557023286155149013813169)
                ·
                  refine ⟨394167767464616361760359877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525557023286155149013813169 394167767464616361760359877)
                  ·
                    refine ⟨73906456399615567830067477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 394167767464616361760359877 73906456399615567830067477)
                    ·
                      refine ⟨3464365143731979742034413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73906456399615567830067477 3464365143731979742034413)
                      ·
                        rfl

theorem cell23_6746827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_6746827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746827 prefixEnd_6746827 := by exact prefixLift 6746827
  have htrace : WordTrace (prefixWord ++ tailWord_6746827) baseStart_6746827 baseEnd_6746827 := by
    simpa [prefixWord, tailWord_6746827, baseEnd_6746827] using wordTrace_append hprefix tailTrace_6746827
  have hstable : (prefixWord ++ tailWord_6746827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746827).length < 2 ^ (prefixWord ++ tailWord_6746827).sum := by decide
  have hdescent : baseEnd_6746827 < baseStart_6746827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746852 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_6746852 : Nat := 118140960795 + 6746852 * 2 ^ 59
def prefixEnd_6746852 : Nat := 4983230072969 + 3 ^ 40 * 6746852 * 2
def baseEnd_6746852 : Nat := 3464377980748342144221799

theorem tailTrace_6746852 : CollatzResearch.WordTrace tailWord_6746852 prefixEnd_6746852 3464377980748342144221799 := by
  unfold tailWord_6746852
  simp only [CollatzResearch.WordTrace]
  refine ⟨123038954276657474714881405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164051939035543299619841873 123038954276657474714881405)
  ·
    refine ⟨46139607853746553018080527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123038954276657474714881405 46139607853746553018080527)
    ·
      refine ⟨69209411780619829527120791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46139607853746553018080527 69209411780619829527120791)
      ·
        refine ⟨103814117670929744290681187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69209411780619829527120791 103814117670929744290681187)
        ·
          refine ⟨155721176506394616436021781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103814117670929744290681187 155721176506394616436021781)
          ·
            refine ⟨7299430148737247645438521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155721176506394616436021781 7299430148737247645438521)
            ·
              refine ⟨5474572611552935734078891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7299430148737247645438521 5474572611552935734078891)
              ·
                refine ⟨8211858917329403601118337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474572611552935734078891 8211858917329403601118337)
                ·
                  refine ⟨6158894187997052700838753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8211858917329403601118337 6158894187997052700838753)
                  ·
                    refine ⟨4619170640997789525629065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6158894187997052700838753 4619170640997789525629065)
                    ·
                      refine ⟨3464377980748342144221799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619170640997789525629065 3464377980748342144221799)
                      ·
                        rfl

theorem cell23_6746852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_6746852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746852 prefixEnd_6746852 := by exact prefixLift 6746852
  have htrace : WordTrace (prefixWord ++ tailWord_6746852) baseStart_6746852 baseEnd_6746852 := by
    simpa [prefixWord, tailWord_6746852, baseEnd_6746852] using wordTrace_append hprefix tailTrace_6746852
  have hstable : (prefixWord ++ tailWord_6746852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746852).length < 2 ^ (prefixWord ++ tailWord_6746852).sum := by decide
  have hdescent : baseEnd_6746852 < baseStart_6746852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746874 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_6746874 : Nat := 118140960795 + 6746874 * 2 ^ 59
def prefixEnd_6746874 : Nat := 4983230072969 + 3 ^ 40 * 6746874 * 2
def baseEnd_6746874 : Nat := 3464389277322741058146697

theorem tailTrace_6746874 : CollatzResearch.WordTrace tailWord_6746874 prefixEnd_6746874 3464389277322741058146697 := by
  unfold tailWord_6746874
  simp only [CollatzResearch.WordTrace]
  refine ⟨61519677739808811796765919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164052473972823498124709117 61519677739808811796765919)
  ·
    refine ⟨92279516609713217695148879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61519677739808811796765919 92279516609713217695148879)
    ·
      refine ⟨138419274914569826542723319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92279516609713217695148879 138419274914569826542723319)
      ·
        refine ⟨207628912371854739814084979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138419274914569826542723319 207628912371854739814084979)
        ·
          refine ⟨311443368557782109721127469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207628912371854739814084979 311443368557782109721127469)
          ·
            refine ⟨116791263209168291145422801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311443368557782109721127469 116791263209168291145422801)
            ·
              refine ⟨87593447406876218359067101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116791263209168291145422801 87593447406876218359067101)
              ·
                refine ⟨32847542777578581884650163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87593447406876218359067101 32847542777578581884650163)
                ·
                  refine ⟨49271314166367872826975245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32847542777578581884650163 49271314166367872826975245)
                  ·
                    refine ⟨18476742812387952310115717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49271314166367872826975245 18476742812387952310115717)
                    ·
                      refine ⟨3464389277322741058146697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18476742812387952310115717 3464389277322741058146697)
                      ·
                        rfl

theorem cell23_6746874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_6746874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746874 prefixEnd_6746874 := by exact prefixLift 6746874
  have htrace : WordTrace (prefixWord ++ tailWord_6746874) baseStart_6746874 baseEnd_6746874 := by
    simpa [prefixWord, tailWord_6746874, baseEnd_6746874] using wordTrace_append hprefix tailTrace_6746874
  have hstable : (prefixWord ++ tailWord_6746874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746874).length < 2 ^ (prefixWord ++ tailWord_6746874).sum := by decide
  have hdescent : baseEnd_6746874 < baseStart_6746874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746891 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 2, 4, 2]
def baseStart_6746891 : Nat := 118140960795 + 6746891 * 2 ^ 59
def prefixEnd_6746891 : Nat := 4983230072969 + 3 ^ 40 * 6746891 * 2
def baseEnd_6746891 : Nat := 3464398006493867491634119

theorem tailTrace_6746891 : CollatzResearch.WordTrace tailWord_6746891 prefixEnd_6746891 3464398006493867491634119 := by
  unfold tailWord_6746891
  simp only [CollatzResearch.WordTrace]
  refine ⟨246079331000173659090432527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164052887333449106060288351 246079331000173659090432527)
  ·
    refine ⟨369118996500260488635648791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246079331000173659090432527 369118996500260488635648791)
    ·
      refine ⟨553678494750390732953473187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369118996500260488635648791 553678494750390732953473187)
      ·
        refine ⟨830517742125586099430209781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553678494750390732953473187 830517742125586099430209781)
        ·
          refine ⟨77861038324273696821582167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 830517742125586099430209781 77861038324273696821582167)
          ·
            refine ⟨116791557486410545232373251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77861038324273696821582167 116791557486410545232373251)
            ·
              refine ⟨175187336229615817848559877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116791557486410545232373251 175187336229615817848559877)
              ·
                refine ⟨32847625543052965846604977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175187336229615817848559877 32847625543052965846604977)
                ·
                  refine ⟨24635719157289724384953733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32847625543052965846604977 24635719157289724384953733)
                  ·
                    refine ⟨4619197341991823322178825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24635719157289724384953733 4619197341991823322178825)
                    ·
                      refine ⟨3464398006493867491634119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4619197341991823322178825 3464398006493867491634119)
                      ·
                        rfl

theorem cell23_6746891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4, 2].length) (baseStart_6746891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746891 prefixEnd_6746891 := by exact prefixLift 6746891
  have htrace : WordTrace (prefixWord ++ tailWord_6746891) baseStart_6746891 baseEnd_6746891 := by
    simpa [prefixWord, tailWord_6746891, baseEnd_6746891] using wordTrace_append hprefix tailTrace_6746891
  have hstable : (prefixWord ++ tailWord_6746891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746891).length < 2 ^ (prefixWord ++ tailWord_6746891).sum := by decide
  have hdescent : baseEnd_6746891 < baseStart_6746891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6746894 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6746894 : Nat := 118140960795 + 6746894 * 2 ^ 59
def prefixEnd_6746894 : Nat := 4983230072969 + 3 ^ 40 * 6746894 * 2
def baseEnd_6746894 : Nat := 3464399546935830979896605

theorem tailTrace_6746894 : CollatzResearch.WordTrace tailWord_6746894 prefixEnd_6746894 3464399546935830979896605 := by
  unfold tailWord_6746894
  simp only [CollatzResearch.WordTrace]
  refine ⟨30759930052395348825348967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164052960279441860401861157 30759930052395348825348967)
  ·
    refine ⟨46139895078593023238023451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30759930052395348825348967 46139895078593023238023451)
    ·
      refine ⟨69209842617889534857035177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46139895078593023238023451 69209842617889534857035177)
      ·
        refine ⟨51907381963417151142776383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69209842617889534857035177 51907381963417151142776383)
        ·
          refine ⟨77861072945125726714164575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51907381963417151142776383 77861072945125726714164575)
          ·
            refine ⟨116791609417688590071246863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77861072945125726714164575 116791609417688590071246863)
            ·
              refine ⟨175187414126532885106870295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116791609417688590071246863 175187414126532885106870295)
              ·
                refine ⟨262781121189799327660305443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175187414126532885106870295 262781121189799327660305443)
                ·
                  refine ⟨394171681784698991490458165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262781121189799327660305443 394171681784698991490458165)
                  ·
                    refine ⟨36953595167315530452230453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 394171681784698991490458165 36953595167315530452230453)
                    ·
                      refine ⟨3464399546935830979896605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36953595167315530452230453 3464399546935830979896605)
                      ·
                        rfl

theorem cell23_6746894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6746894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6746894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6746894 prefixEnd_6746894 := by exact prefixLift 6746894
  have htrace : WordTrace (prefixWord ++ tailWord_6746894) baseStart_6746894 baseEnd_6746894 := by
    simpa [prefixWord, tailWord_6746894, baseEnd_6746894] using wordTrace_append hprefix tailTrace_6746894
  have hstable : (prefixWord ++ tailWord_6746894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6746894).length < 2 ^ (prefixWord ++ tailWord_6746894).sum := by decide
  have hdescent : baseEnd_6746894 < baseStart_6746894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6746894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
