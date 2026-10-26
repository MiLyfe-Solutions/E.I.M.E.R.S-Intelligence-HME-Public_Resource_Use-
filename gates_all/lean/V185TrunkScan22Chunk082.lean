import V185TrunkScan22Chunk081

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_736398 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_736398 : Nat := 118140960795 + 736398 * 2 ^ 59
def prefixEnd_736398 : Nat := 4983230072969 + 3 ^ 40 * 736398 * 2
def baseEnd_736398 : Nat := 84028028224381127364083

theorem tailTrace_736398 : CollatzResearch.WordTrace tailWord_736398 prefixEnd_736398 84028028224381127364083 := by
  unfold tailWord_736398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357330198270410951338231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17905761057442191740470565 3357330198270410951338231)
  ·
    refine ⟨5035995297405616427007347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357330198270410951338231 5035995297405616427007347)
    ·
      refine ⟨7553992946108424640511021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5035995297405616427007347 7553992946108424640511021)
      ·
        refine ⟨2832747354790659240191633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7553992946108424640511021 2832747354790659240191633)
        ·
          refine ⟨2124560516092994430143725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2832747354790659240191633 2124560516092994430143725)
          ·
            refine ⟨796710193534872911303897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2124560516092994430143725 796710193534872911303897)
            ·
              refine ⟨597532645151154683477923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796710193534872911303897 597532645151154683477923)
              ·
                refine ⟨896298967726732025216885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597532645151154683477923 896298967726732025216885)
                ·
                  refine ⟨84028028224381127364083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 896298967726732025216885 84028028224381127364083)
                  ·
                    rfl

theorem cell22_736398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_736398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736398 prefixEnd_736398 := by exact prefixLift 736398
  have htrace : WordTrace (prefixWord ++ tailWord_736398) baseStart_736398 baseEnd_736398 := by
    simpa [prefixWord, tailWord_736398, baseEnd_736398] using wordTrace_append hprefix tailTrace_736398
  have hstable : (prefixWord ++ tailWord_736398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736398).length < 2 ^ (prefixWord ++ tailWord_736398).sum := by decide
  have hdescent : baseEnd_736398 < baseStart_736398 := by decide
  rcases family_descends (prefixWord ++ tailWord_736398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736437 : List Nat := [1, 3, 3, 15]
def baseStart_736437 : Nat := 118140960795 + 736437 * 2 ^ 59
def prefixEnd_736437 : Nat := 4983230072969 + 3 ^ 40 * 736437 * 2
def baseEnd_736437 : Nat := 345812668271824801601

theorem tailTrace_736437 : CollatzResearch.WordTrace tailWord_736437 prefixEnd_736437 345812668271824801601 := by
  unfold tailWord_736437
  simp only [CollatzResearch.WordTrace]
  refine ⟨26860064033021997271375565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17906709355347998180917043 26860064033021997271375565)
  ·
    refine ⟨10072524012383248976765837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26860064033021997271375565 10072524012383248976765837)
    ·
      refine ⟨3777196504643718366287189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10072524012383248976765837 3777196504643718366287189)
      ·
        refine ⟨345812668271824801601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 3777196504643718366287189 345812668271824801601)
        ·
          rfl

theorem cell22_736437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 15].length) (baseStart_736437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736437 prefixEnd_736437 := by exact prefixLift 736437
  have htrace : WordTrace (prefixWord ++ tailWord_736437) baseStart_736437 baseEnd_736437 := by
    simpa [prefixWord, tailWord_736437, baseEnd_736437] using wordTrace_append hprefix tailTrace_736437
  have hstable : (prefixWord ++ tailWord_736437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736437).length < 2 ^ (prefixWord ++ tailWord_736437).sum := by decide
  have hdescent : baseEnd_736437 < baseStart_736437 := by decide
  rcases family_descends (prefixWord ++ tailWord_736437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736439 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 2, 4]
def baseStart_736439 : Nat := 118140960795 + 736439 * 2 ^ 59
def prefixEnd_736439 : Nat := 4983230072969 + 3 ^ 40 * 736439 * 2
def baseEnd_736439 : Nat := 252098119811032941817123

theorem tailTrace_736439 : CollatzResearch.WordTrace tailWord_736439 prefixEnd_736439 252098119811032941817123 := by
  unfold tailWord_736439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26860136979014751612948371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17906757986009834408632247 26860136979014751612948371)
  ·
    refine ⟨40290205468522127419422557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26860136979014751612948371 40290205468522127419422557)
    ·
      refine ⟨15108827050695797782283459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40290205468522127419422557 15108827050695797782283459)
      ·
        refine ⟨22663240576043696673425189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15108827050695797782283459 22663240576043696673425189)
        ·
          refine ⟨4249357608008193126267223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22663240576043696673425189 4249357608008193126267223)
          ·
            refine ⟨6374036412012289689400835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249357608008193126267223 6374036412012289689400835)
            ·
              refine ⟨9561054618018434534101253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6374036412012289689400835 9561054618018434534101253)
              ·
                refine ⟨1792697740878456475143985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9561054618018434534101253 1792697740878456475143985)
                ·
                  refine ⟨1344523305658842356357989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1792697740878456475143985 1344523305658842356357989)
                  ·
                    refine ⟨252098119811032941817123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344523305658842356357989 252098119811032941817123)
                    ·
                      rfl

theorem cell22_736439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_736439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736439 prefixEnd_736439 := by exact prefixLift 736439
  have htrace : WordTrace (prefixWord ++ tailWord_736439) baseStart_736439 baseEnd_736439 := by
    simpa [prefixWord, tailWord_736439, baseEnd_736439] using wordTrace_append hprefix tailTrace_736439
  have hstable : (prefixWord ++ tailWord_736439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736439).length < 2 ^ (prefixWord ++ tailWord_736439).sum := by decide
  have hdescent : baseEnd_736439 < baseStart_736439 := by decide
  rcases family_descends (prefixWord ++ tailWord_736439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736441 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 2, 3]
def baseStart_736441 : Nat := 118140960795 + 736441 * 2 ^ 59
def prefixEnd_736441 : Nat := 4983230072969 + 3 ^ 40 * 736441 * 2
def baseEnd_736441 : Nat := 252098804451905603267117

theorem tailTrace_736441 : CollatzResearch.WordTrace tailWord_736441 prefixEnd_736441 252098804451905603267117 := by
  unfold tailWord_736441
  simp only [CollatzResearch.WordTrace]
  refine ⟨26860209925007505954521177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17906806616671670636347451 26860209925007505954521177)
  ·
    refine ⟨20145157443755629465890883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26860209925007505954521177 20145157443755629465890883)
    ·
      refine ⟨30217736165633444198836325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20145157443755629465890883 30217736165633444198836325)
      ·
        refine ⟨5665825531056270787281811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30217736165633444198836325 5665825531056270787281811)
        ·
          refine ⟨8498738296584406180922717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665825531056270787281811 8498738296584406180922717)
          ·
            refine ⟨3187026861219152317846019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8498738296584406180922717 3187026861219152317846019)
            ·
              refine ⟨4780540291828728476769029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187026861219152317846019 4780540291828728476769029)
              ·
                refine ⟨896351304717886589394193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4780540291828728476769029 896351304717886589394193)
                ·
                  refine ⟨672263478538414942045645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896351304717886589394193 672263478538414942045645)
                  ·
                    refine ⟨252098804451905603267117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 672263478538414942045645 252098804451905603267117)
                    ·
                      rfl

theorem cell22_736441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_736441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736441 prefixEnd_736441 := by exact prefixLift 736441
  have htrace : WordTrace (prefixWord ++ tailWord_736441) baseStart_736441 baseEnd_736441 := by
    simpa [prefixWord, tailWord_736441, baseEnd_736441] using wordTrace_append hprefix tailTrace_736441
  have hstable : (prefixWord ++ tailWord_736441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736441).length < 2 ^ (prefixWord ++ tailWord_736441).sum := by decide
  have hdescent : baseEnd_736441 < baseStart_736441 := by decide
  rcases family_descends (prefixWord ++ tailWord_736441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736499 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 7]
def baseStart_736499 : Nat := 118140960795 + 736499 * 2 ^ 59
def prefixEnd_736499 : Nat := 4983230072969 + 3 ^ 40 * 736499 * 2
def baseEnd_736499 : Nat := 84039553012404261772313

theorem tailTrace_736499 : CollatzResearch.WordTrace tailWord_736499 prefixEnd_736499 84039553012404261772313 := by
  unfold tailWord_736499
  simp only [CollatzResearch.WordTrace]
  refine ⟨26862325358797381860132551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17908216905864921240088367 26862325358797381860132551)
  ·
    refine ⟨40293488038196072790198827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26862325358797381860132551 40293488038196072790198827)
    ·
      refine ⟨60440232057294109185298241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40293488038196072790198827 60440232057294109185298241)
      ·
        refine ⟨45330174042970581888973681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60440232057294109185298241 45330174042970581888973681)
        ·
          refine ⟨33997630532227936416730261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45330174042970581888973681 33997630532227936416730261)
          ·
            refine ⟨1593638931198184519534231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33997630532227936416730261 1593638931198184519534231)
            ·
              refine ⟨2390458396797276779301347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593638931198184519534231 2390458396797276779301347)
              ·
                refine ⟨3585687595195915168952021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390458396797276779301347 3585687595195915168952021)
                ·
                  refine ⟨84039553012404261772313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3585687595195915168952021 84039553012404261772313)
                  ·
                    rfl

theorem cell22_736499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 7].length) (baseStart_736499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736499 prefixEnd_736499 := by exact prefixLift 736499
  have htrace : WordTrace (prefixWord ++ tailWord_736499) baseStart_736499 baseEnd_736499 := by
    simpa [prefixWord, tailWord_736499, baseEnd_736499] using wordTrace_append hprefix tailTrace_736499
  have hstable : (prefixWord ++ tailWord_736499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736499).length < 2 ^ (prefixWord ++ tailWord_736499).sum := by decide
  have hdescent : baseEnd_736499 < baseStart_736499 := by decide
  rcases family_descends (prefixWord ++ tailWord_736499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736561 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 6]
def baseStart_736561 : Nat := 118140960795 + 736561 * 2 ^ 59
def prefixEnd_736561 : Nat := 4983230072969 + 3 ^ 40 * 736561 * 2
def baseEnd_736561 : Nat := 84046627634755096755583

theorem tailTrace_736561 : CollatzResearch.WordTrace tailWord_736561 prefixEnd_736561 84046627634755096755583 := by
  unfold tailWord_736561
  simp only [CollatzResearch.WordTrace]
  refine ⟨26864586684572766448889537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17909724456381844299259691 26864586684572766448889537)
  ·
    refine ⟨20148440013429574836667153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26864586684572766448889537 20148440013429574836667153)
    ·
      refine ⟨15111330010072181127500365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20148440013429574836667153 15111330010072181127500365)
      ·
        refine ⟨5666748753777067922812637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15111330010072181127500365 5666748753777067922812637)
        ·
          refine ⟨2125030782666400471054739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5666748753777067922812637 2125030782666400471054739)
          ·
            refine ⟨3187546173999600706582109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125030782666400471054739 3187546173999600706582109)
            ·
              refine ⟨1195329815249850264968291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3187546173999600706582109 1195329815249850264968291)
              ·
                refine ⟨1792994722874775397452437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195329815249850264968291 1792994722874775397452437)
                ·
                  refine ⟨84046627634755096755583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1792994722874775397452437 84046627634755096755583)
                  ·
                    rfl

theorem cell22_736561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_736561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736561 prefixEnd_736561 := by exact prefixLift 736561
  have htrace : WordTrace (prefixWord ++ tailWord_736561) baseStart_736561 baseEnd_736561 := by
    simpa [prefixWord, tailWord_736561, baseEnd_736561] using wordTrace_append hprefix tailTrace_736561
  have hstable : (prefixWord ++ tailWord_736561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736561).length < 2 ^ (prefixWord ++ tailWord_736561).sum := by decide
  have hdescent : baseEnd_736561 < baseStart_736561 := by decide
  rcases family_descends (prefixWord ++ tailWord_736561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736580 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_736580 : Nat := 118140960795 + 736580 * 2 ^ 59
def prefixEnd_736580 : Nat := 4983230072969 + 3 ^ 40 * 736580 * 2
def baseEnd_736580 : Nat := 252146386992555574041691

theorem tailTrace_736580 : CollatzResearch.WordTrace tailWord_736580 prefixEnd_736580 252146386992555574041691 := by
  unfold tailWord_736580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432639835751966346915597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17910186447669288462554129 13432639835751966346915597)
  ·
    refine ⟨5037239938406987380093349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13432639835751966346915597 5037239938406987380093349)
    ·
      refine ⟨944482488451310133767503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5037239938406987380093349 944482488451310133767503)
      ·
        refine ⟨1416723732676965200651255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944482488451310133767503 1416723732676965200651255)
        ·
          refine ⟨2125085599015447800976883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416723732676965200651255 2125085599015447800976883)
          ·
            refine ⟨3187628398523171701465325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125085599015447800976883 3187628398523171701465325)
            ·
              refine ⟨1195360649446189388049497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3187628398523171701465325 1195360649446189388049497)
              ·
                refine ⟨896520487084642041037123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195360649446189388049497 896520487084642041037123)
                ·
                  refine ⟨1344780730626963061555685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896520487084642041037123 1344780730626963061555685)
                  ·
                    refine ⟨252146386992555574041691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344780730626963061555685 252146386992555574041691)
                    ·
                      rfl

theorem cell22_736580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_736580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736580 prefixEnd_736580 := by exact prefixLift 736580
  have htrace : WordTrace (prefixWord ++ tailWord_736580) baseStart_736580 baseEnd_736580 := by
    simpa [prefixWord, tailWord_736580, baseEnd_736580] using wordTrace_append hprefix tailTrace_736580
  have hstable : (prefixWord ++ tailWord_736580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736580).length < 2 ^ (prefixWord ++ tailWord_736580).sum := by decide
  have hdescent : baseEnd_736580 < baseStart_736580 := by decide
  rcases family_descends (prefixWord ++ tailWord_736580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736610 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_736610 : Nat := 118140960795 + 736610 * 2 ^ 59
def prefixEnd_736610 : Nat := 4983230072969 + 3 ^ 40 * 736610 * 2
def baseEnd_736610 : Nat := 252156656605645495791599

theorem tailTrace_736610 : CollatzResearch.WordTrace tailWord_736610 prefixEnd_736610 252156656605645495791599 := by
  unfold tailWord_736610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716593465348811954355821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17910915907596831878282189 6716593465348811954355821)
  ·
    refine ⟨2518722549505804482883433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6716593465348811954355821 2518722549505804482883433)
    ·
      refine ⟨1889041912129353362162575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2518722549505804482883433 1889041912129353362162575)
      ·
        refine ⟨2833562868194030043243863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889041912129353362162575 2833562868194030043243863)
        ·
          refine ⟨4250344302291045064865795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833562868194030043243863 4250344302291045064865795)
          ·
            refine ⟨6375516453436567597298693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250344302291045064865795 6375516453436567597298693)
            ·
              refine ⟨1195409335019356424493505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6375516453436567597298693 1195409335019356424493505)
              ·
                refine ⟨896557001264517318370129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195409335019356424493505 896557001264517318370129)
                ·
                  refine ⟨672417750948387988777597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896557001264517318370129 672417750948387988777597)
                  ·
                    refine ⟨252156656605645495791599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 672417750948387988777597 252156656605645495791599)
                    ·
                      rfl

theorem cell22_736610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_736610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736610 prefixEnd_736610 := by exact prefixLift 736610
  have htrace : WordTrace (prefixWord ++ tailWord_736610) baseStart_736610 baseEnd_736610 := by
    simpa [prefixWord, tailWord_736610, baseEnd_736610] using wordTrace_append hprefix tailTrace_736610
  have hstable : (prefixWord ++ tailWord_736610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736610).length < 2 ^ (prefixWord ++ tailWord_736610).sum := by decide
  have hdescent : baseEnd_736610 < baseStart_736610 := by decide
  rcases family_descends (prefixWord ++ tailWord_736610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736642 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_736642 : Nat := 118140960795 + 736642 * 2 ^ 59
def prefixEnd_736642 : Nat := 4983230072969 + 3 ^ 40 * 736642 * 2
def baseEnd_736642 : Nat := 252167610859608078991501

theorem tailTrace_736642 : CollatzResearch.WordTrace tailWord_736642 prefixEnd_736642 252167610859608078991501 := by
  unfold tailWord_736642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716885249319829320647045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17911693998186211521725453 6716885249319829320647045)
  ·
    refine ⟨1259415984247467997621321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6716885249319829320647045 1259415984247467997621321)
    ·
      refine ⟨944561988185600998215991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1259415984247467997621321 944561988185600998215991)
      ·
        refine ⟨1416842982278401497323987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944561988185600998215991 1416842982278401497323987)
        ·
          refine ⟨2125264473417602245985981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416842982278401497323987 2125264473417602245985981)
          ·
            refine ⟨796974177531600842244743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2125264473417602245985981 796974177531600842244743)
            ·
              refine ⟨1195461266297401263367115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796974177531600842244743 1195461266297401263367115)
              ·
                refine ⟨1793191899446101895050673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195461266297401263367115 1793191899446101895050673)
                ·
                  refine ⟨1344893924584576421288005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1793191899446101895050673 1344893924584576421288005)
                  ·
                    refine ⟨252167610859608078991501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344893924584576421288005 252167610859608078991501)
                    ·
                      rfl

theorem cell22_736642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_736642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736642 prefixEnd_736642 := by exact prefixLift 736642
  have htrace : WordTrace (prefixWord ++ tailWord_736642) baseStart_736642 baseEnd_736642 := by
    simpa [prefixWord, tailWord_736642, baseEnd_736642] using wordTrace_append hprefix tailTrace_736642
  have hstable : (prefixWord ++ tailWord_736642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736642).length < 2 ^ (prefixWord ++ tailWord_736642).sum := by decide
  have hdescent : baseEnd_736642 < baseStart_736642 := by decide
  rcases family_descends (prefixWord ++ tailWord_736642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736666 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_736666 : Nat := 118140960795 + 736666 * 2 ^ 59
def prefixEnd_736666 : Nat := 4983230072969 + 3 ^ 40 * 736666 * 2
def baseEnd_736666 : Nat := 252175826550080016391427

theorem tailTrace_736666 : CollatzResearch.WordTrace tailWord_736666 prefixEnd_736666 252175826550080016391427 := by
  unfold tailWord_736666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6717104087298092345365463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17912277566128246254307901 6717104087298092345365463)
  ·
    refine ⟨10075656130947138518048195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6717104087298092345365463 10075656130947138518048195)
    ·
      refine ⟨15113484196420707777072293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10075656130947138518048195 15113484196420707777072293)
      ·
        refine ⟨2833778286828882708201055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15113484196420707777072293 2833778286828882708201055)
        ·
          refine ⟨4250667430243324062301583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833778286828882708201055 4250667430243324062301583)
          ·
            refine ⟨6376001145364986093452375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250667430243324062301583 6376001145364986093452375)
            ·
              refine ⟨9564001718047479140178563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376001145364986093452375 9564001718047479140178563)
              ·
                refine ⟨14346002577071218710267845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9564001718047479140178563 14346002577071218710267845)
                ·
                  refine ⟨2689875483200853508175221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14346002577071218710267845 2689875483200853508175221)
                  ·
                    refine ⟨252175826550080016391427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2689875483200853508175221 252175826550080016391427)
                    ·
                      rfl

theorem cell22_736666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_736666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736666 prefixEnd_736666 := by exact prefixLift 736666
  have htrace : WordTrace (prefixWord ++ tailWord_736666) baseStart_736666 baseEnd_736666 := by
    simpa [prefixWord, tailWord_736666, baseEnd_736666] using wordTrace_append hprefix tailTrace_736666
  have hstable : (prefixWord ++ tailWord_736666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736666).length < 2 ^ (prefixWord ++ tailWord_736666).sum := by decide
  have hdescent : baseEnd_736666 < baseStart_736666 := by decide
  rcases family_descends (prefixWord ++ tailWord_736666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736696 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 6]
def baseStart_736696 : Nat := 118140960795 + 736696 * 2 ^ 59
def prefixEnd_736696 : Nat := 4983230072969 + 3 ^ 40 * 736696 * 2
def baseEnd_736696 : Nat := 84062032054389979380445

theorem tailTrace_736696 : CollatzResearch.WordTrace tailWord_736696 prefixEnd_736696 84062032054389979380445 := by
  unfold tailWord_736696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13434755269541842252526971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17913007026055789670035961 13434755269541842252526971)
  ·
    refine ⟨20152132904312763378790457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13434755269541842252526971 20152132904312763378790457)
    ·
      refine ⟨15114099678234572534092843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20152132904312763378790457 15114099678234572534092843)
      ·
        refine ⟨22671149517351858801139265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15114099678234572534092843 22671149517351858801139265)
        ·
          refine ⟨17003362138013894100854449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22671149517351858801139265 17003362138013894100854449)
          ·
            refine ⟨12752521603510420575640837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17003362138013894100854449 12752521603510420575640837)
            ·
              refine ⟨2391097800658203857932657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12752521603510420575640837 2391097800658203857932657)
              ·
                refine ⟨1793323350493652893449493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391097800658203857932657 1793323350493652893449493)
                ·
                  refine ⟨84062032054389979380445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1793323350493652893449493 84062032054389979380445)
                  ·
                    rfl

theorem cell22_736696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_736696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736696 prefixEnd_736696 := by exact prefixLift 736696
  have htrace : WordTrace (prefixWord ++ tailWord_736696) baseStart_736696 baseEnd_736696 := by
    simpa [prefixWord, tailWord_736696, baseEnd_736696] using wordTrace_append hprefix tailTrace_736696
  have hstable : (prefixWord ++ tailWord_736696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736696).length < 2 ^ (prefixWord ++ tailWord_736696).sum := by decide
  have hdescent : baseEnd_736696 < baseStart_736696 := by decide
  rcases family_descends (prefixWord ++ tailWord_736696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736711 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 3, 5]
def baseStart_736711 : Nat := 118140960795 + 736711 * 2 ^ 59
def prefixEnd_736711 : Nat := 4983230072969 + 3 ^ 40 * 736711 * 2
def baseEnd_736711 : Nat := 252191230969714899016289

theorem tailTrace_736711 : CollatzResearch.WordTrace tailWord_736711 prefixEnd_736711 252191230969714899016289 := by
  unfold tailWord_736711
  simp only [CollatzResearch.WordTrace]
  refine ⟨26870057634029342066849987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17913371756019561377899991 26870057634029342066849987)
  ·
    refine ⟨40305086451044013100274981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26870057634029342066849987 40305086451044013100274981)
    ·
      refine ⟨7557203709570752456301559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40305086451044013100274981 7557203709570752456301559)
      ·
        refine ⟨11335805564356128684452339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7557203709570752456301559 11335805564356128684452339)
        ·
          refine ⟨17003708346534193026678509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11335805564356128684452339 17003708346534193026678509)
          ·
            refine ⟨6376390629950322385004441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17003708346534193026678509 6376390629950322385004441)
            ·
              refine ⟨4782292972462741788753331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6376390629950322385004441 4782292972462741788753331)
              ·
                refine ⟨7173439458694112683129997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782292972462741788753331 7173439458694112683129997)
                ·
                  refine ⟨2690039797010292256173749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7173439458694112683129997 2690039797010292256173749)
                  ·
                    refine ⟨252191230969714899016289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2690039797010292256173749 252191230969714899016289)
                    ·
                      rfl

theorem cell22_736711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_736711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736711 prefixEnd_736711 := by exact prefixLift 736711
  have htrace : WordTrace (prefixWord ++ tailWord_736711) baseStart_736711 baseEnd_736711 := by
    simpa [prefixWord, tailWord_736711, baseEnd_736711] using wordTrace_append hprefix tailTrace_736711
  have hstable : (prefixWord ++ tailWord_736711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736711).length < 2 ^ (prefixWord ++ tailWord_736711).sum := by decide
  have hdescent : baseEnd_736711 < baseStart_736711 := by decide
  rcases family_descends (prefixWord ++ tailWord_736711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736728 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 4, 3]
def baseStart_736728 : Nat := 118140960795 + 736728 * 2 ^ 59
def prefixEnd_736728 : Nat := 4983230072969 + 3 ^ 40 * 736728 * 2
def baseEnd_736728 : Nat := 252197050417132521341237

theorem tailTrace_736728 : CollatzResearch.WordTrace tailWord_736728 prefixEnd_736728 252197050417132521341237 := by
  unfold tailWord_736728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13435338837483876985109419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17913785116645169313479225 13435338837483876985109419)
  ·
    refine ⟨20153008256225815477664129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13435338837483876985109419 20153008256225815477664129)
    ·
      refine ⟨15114756192169361608248097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20153008256225815477664129 15114756192169361608248097)
      ·
        refine ⟨11336067144127021206186073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15114756192169361608248097 11336067144127021206186073)
        ·
          refine ⟨8502050358095265904639555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11336067144127021206186073 8502050358095265904639555)
          ·
            refine ⟨12753075537142898856959333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8502050358095265904639555 12753075537142898856959333)
            ·
              refine ⟨2391201663214293535679875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12753075537142898856959333 2391201663214293535679875)
              ·
                refine ⟨3586802494821440303519813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391201663214293535679875 3586802494821440303519813)
                ·
                  refine ⟨672525467779020056909965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3586802494821440303519813 672525467779020056909965)
                  ·
                    refine ⟨252197050417132521341237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 672525467779020056909965 252197050417132521341237)
                    ·
                      rfl

theorem cell22_736728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_736728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736728 prefixEnd_736728 := by exact prefixLift 736728
  have htrace : WordTrace (prefixWord ++ tailWord_736728) baseStart_736728 baseEnd_736728 := by
    simpa [prefixWord, tailWord_736728, baseEnd_736728] using wordTrace_append hprefix tailTrace_736728
  have hstable : (prefixWord ++ tailWord_736728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736728).length < 2 ^ (prefixWord ++ tailWord_736728).sum := by decide
  have hdescent : baseEnd_736728 < baseStart_736728 := by decide
  rcases family_descends (prefixWord ++ tailWord_736728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736749 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_736749 : Nat := 118140960795 + 736749 * 2 ^ 59
def prefixEnd_736749 : Nat := 4983230072969 + 3 ^ 40 * 736749 * 2
def baseEnd_736749 : Nat := 252204239146295466566173

theorem tailTrace_736749 : CollatzResearch.WordTrace tailWord_736749 prefixEnd_736749 252204239146295466566173 := by
  unfold tailWord_736749
  simp only [CollatzResearch.WordTrace]
  refine ⟨26871443607891674556733301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17914295738594449704488867 26871443607891674556733301)
  ·
    refine ⟨2519197838239844489693747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26871443607891674556733301 2519197838239844489693747)
    ·
      refine ⟨3778796757359766734540621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519197838239844489693747 3778796757359766734540621)
      ·
        refine ⟨1417048784009912525452733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3778796757359766734540621 1417048784009912525452733)
        ·
          refine ⟨531393294003717197044775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1417048784009912525452733 531393294003717197044775)
          ·
            refine ⟨797089941005575795567163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531393294003717197044775 797089941005575795567163)
            ·
              refine ⟨1195634911508363693350745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797089941005575795567163 1195634911508363693350745)
              ·
                refine ⟨896726183631272770013059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195634911508363693350745 896726183631272770013059)
                ·
                  refine ⟨1345089275446909155019589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896726183631272770013059 1345089275446909155019589)
                  ·
                    refine ⟨252204239146295466566173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1345089275446909155019589 252204239146295466566173)
                    ·
                      rfl

theorem cell22_736749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_736749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736749 prefixEnd_736749 := by exact prefixLift 736749
  have htrace : WordTrace (prefixWord ++ tailWord_736749) baseStart_736749 baseEnd_736749 := by
    simpa [prefixWord, tailWord_736749, baseEnd_736749] using wordTrace_append hprefix tailTrace_736749
  have hstable : (prefixWord ++ tailWord_736749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736749).length < 2 ^ (prefixWord ++ tailWord_736749).sum := by decide
  have hdescent : baseEnd_736749 < baseStart_736749 := by decide
  rcases family_descends (prefixWord ++ tailWord_736749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736758 : List Nat := [5, 1, 1, 1, 2, 2, 2, 8]
def baseStart_736758 : Nat := 118140960795 + 736758 * 2 ^ 59
def prefixEnd_736758 : Nat := 4983230072969 + 3 ^ 40 * 736758 * 2
def baseEnd_736758 : Nat := 28023035558913604787905

theorem tailTrace_736758 : CollatzResearch.WordTrace tailWord_736758 prefixEnd_736758 28023035558913604787905 := by
  unfold tailWord_736758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679485741553691818363183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17914514576572712729207285 1679485741553691818363183)
  ·
    refine ⟨2519228612330537727544775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1679485741553691818363183 2519228612330537727544775)
    ·
      refine ⟨3778842918495806591317163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519228612330537727544775 3778842918495806591317163)
      ·
        refine ⟨5668264377743709886975745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778842918495806591317163 5668264377743709886975745)
        ·
          refine ⟨4251198283307782415231809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668264377743709886975745 4251198283307782415231809)
          ·
            refine ⟨3188398712480836811423857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4251198283307782415231809 3188398712480836811423857)
            ·
              refine ⟨2391299034360627608567893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3188398712480836811423857 2391299034360627608567893)
              ·
                refine ⟨28023035558913604787905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2391299034360627608567893 28023035558913604787905)
                ·
                  rfl

theorem cell22_736758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_736758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736758 prefixEnd_736758 := by exact prefixLift 736758
  have htrace : WordTrace (prefixWord ++ tailWord_736758) baseStart_736758 baseEnd_736758 := by
    simpa [prefixWord, tailWord_736758, baseEnd_736758] using wordTrace_append hprefix tailTrace_736758
  have hstable : (prefixWord ++ tailWord_736758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736758).length < 2 ^ (prefixWord ++ tailWord_736758).sum := by decide
  have hdescent : baseEnd_736758 < baseStart_736758 := by decide
  rcases family_descends (prefixWord ++ tailWord_736758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736848 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 6]
def baseStart_736848 : Nat := 118140960795 + 736848 * 2 ^ 59
def prefixEnd_736848 : Nat := 4983230072969 + 3 ^ 40 * 736848 * 2
def baseEnd_736848 : Nat := 84079376289830736113623

theorem tailTrace_736848 : CollatzResearch.WordTrace tailWord_736848 prefixEnd_736848 84079376289830736113623 := by
  unfold tailWord_736848
  simp only [CollatzResearch.WordTrace]
  refine ⟨13437527217266507232293599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17916702956355342976391465 13437527217266507232293599)
  ·
    refine ⟨20156290825899760848440399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13437527217266507232293599 20156290825899760848440399)
    ·
      refine ⟨30234436238849641272660599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20156290825899760848440399 30234436238849641272660599)
      ·
        refine ⟨45351654358274461908990899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30234436238849641272660599 45351654358274461908990899)
        ·
          refine ⟨68027481537411692863486349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45351654358274461908990899 68027481537411692863486349)
          ·
            refine ⟨25510305576529384823807381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68027481537411692863486349 25510305576529384823807381)
            ·
              refine ⟨1195795573899814913615971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25510305576529384823807381 1195795573899814913615971)
              ·
                refine ⟨1793693360849722370423957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195795573899814913615971 1793693360849722370423957)
                ·
                  refine ⟨84079376289830736113623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1793693360849722370423957 84079376289830736113623)
                  ·
                    rfl

theorem cell22_736848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_736848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736848 prefixEnd_736848 := by exact prefixLift 736848
  have htrace : WordTrace (prefixWord ++ tailWord_736848) baseStart_736848 baseEnd_736848 := by
    simpa [prefixWord, tailWord_736848, baseEnd_736848] using wordTrace_append hprefix tailTrace_736848
  have hstable : (prefixWord ++ tailWord_736848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736848).length < 2 ^ (prefixWord ++ tailWord_736848).sum := by decide
  have hdescent : baseEnd_736848 < baseStart_736848 := by decide
  rcases family_descends (prefixWord ++ tailWord_736848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736880 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 4, 3]
def baseStart_736880 : Nat := 118140960795 + 736880 * 2 ^ 59
def prefixEnd_736880 : Nat := 4983230072969 + 3 ^ 40 * 736880 * 2
def baseEnd_736880 : Nat := 252249083123454791540771

theorem tailTrace_736880 : CollatzResearch.WordTrace tailWord_736880 prefixEnd_736880 252249083123454791540771 := by
  unfold tailWord_736880
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438110785208541964876047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17917481046944722619834729 13438110785208541964876047)
  ·
    refine ⟨20157166177812812947314071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13438110785208541964876047 20157166177812812947314071)
    ·
      refine ⟨30235749266719219420971107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20157166177812812947314071 30235749266719219420971107)
      ·
        refine ⟨45353623900078829131456661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30235749266719219420971107 45353623900078829131456661)
        ·
          refine ⟨2125951120316195115537031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45353623900078829131456661 2125951120316195115537031)
          ·
            refine ⟨3188926680474292673305547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125951120316195115537031 3188926680474292673305547)
            ·
              refine ⟨4783390020711439009958321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188926680474292673305547 4783390020711439009958321)
              ·
                refine ⟨3587542515533579257468741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783390020711439009958321 3587542515533579257468741)
                ·
                  refine ⟨672664221662546110775389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3587542515533579257468741 672664221662546110775389)
                  ·
                    refine ⟨252249083123454791540771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 672664221662546110775389 252249083123454791540771)
                    ·
                      rfl

theorem cell22_736880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_736880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736880 prefixEnd_736880 := by exact prefixLift 736880
  have htrace : WordTrace (prefixWord ++ tailWord_736880) baseStart_736880 baseEnd_736880 := by
    simpa [prefixWord, tailWord_736880, baseEnd_736880] using wordTrace_append hprefix tailTrace_736880
  have hstable : (prefixWord ++ tailWord_736880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736880).length < 2 ^ (prefixWord ++ tailWord_736880).sum := by decide
  have hdescent : baseEnd_736880 < baseStart_736880 := by decide
  rcases family_descends (prefixWord ++ tailWord_736880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736882 : List Nat := [3, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_736882 : Nat := 118140960795 + 736882 * 2 ^ 59
def prefixEnd_736882 : Nat := 4983230072969 + 3 ^ 40 * 736882 * 2
def baseEnd_736882 : Nat := 84083255921442484330255

theorem tailTrace_736882 : CollatzResearch.WordTrace tailWord_736882 prefixEnd_736882 84083255921442484330255 := by
  unfold tailWord_736882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719073629102459567831225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17917529677606558847549933 6719073629102459567831225)
  ·
    refine ⟨5039305221826844675873419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6719073629102459567831225 5039305221826844675873419)
    ·
      refine ⟨7558957832740267013810129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5039305221826844675873419 7558957832740267013810129)
      ·
        refine ⟨5669218374555200260357597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7558957832740267013810129 5669218374555200260357597)
        ·
          refine ⟨2125956890458200097634099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5669218374555200260357597 2125956890458200097634099)
          ·
            refine ⟨3188935335687300146451149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125956890458200097634099 3188935335687300146451149)
            ·
              refine ⟨1195850750882737554919181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3188935335687300146451149 1195850750882737554919181)
              ·
                refine ⟨448444031581026583094693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1195850750882737554919181 448444031581026583094693)
                ·
                  refine ⟨84083255921442484330255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448444031581026583094693 84083255921442484330255)
                  ·
                    rfl

theorem cell22_736882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_736882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736882 prefixEnd_736882 := by exact prefixLift 736882
  have htrace : WordTrace (prefixWord ++ tailWord_736882) baseStart_736882 baseEnd_736882 := by
    simpa [prefixWord, tailWord_736882, baseEnd_736882] using wordTrace_append hprefix tailTrace_736882
  have hstable : (prefixWord ++ tailWord_736882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736882).length < 2 ^ (prefixWord ++ tailWord_736882).sum := by decide
  have hdescent : baseEnd_736882 < baseStart_736882 := by decide
  rcases family_descends (prefixWord ++ tailWord_736882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736893 : List Nat := [1, 4, 1, 1, 4, 1, 10]
def baseStart_736893 : Nat := 118140960795 + 736893 * 2 ^ 59
def prefixEnd_736893 : Nat := 4983230072969 + 3 ^ 40 * 736893 * 2
def baseEnd_736893 : Nat := 9342723455152855220953

theorem tailTrace_736893 : CollatzResearch.WordTrace tailWord_736893 prefixEnd_736893 9342723455152855220953 := by
  unfold tailWord_736893
  simp only [CollatzResearch.WordTrace]
  refine ⟨26876695719369987149975333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17917797146246658099983555 26876695719369987149975333)
  ·
    refine ⟨5039380447381872590620375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26876695719369987149975333 5039380447381872590620375)
    ·
      refine ⟨7559070671072808885930563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5039380447381872590620375 7559070671072808885930563)
      ·
        refine ⟨11338606006609213328895845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7559070671072808885930563 11338606006609213328895845)
        ·
          refine ⟨2125988626239227499167971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11338606006609213328895845 2125988626239227499167971)
          ·
            refine ⟨3188982939358841248751957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125988626239227499167971 3188982939358841248751957)
            ·
              refine ⟨9342723455152855220953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3188982939358841248751957 9342723455152855220953)
              ·
                rfl

theorem cell22_736893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 10].length) (baseStart_736893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736893 prefixEnd_736893 := by exact prefixLift 736893
  have htrace : WordTrace (prefixWord ++ tailWord_736893) baseStart_736893 baseEnd_736893 := by
    simpa [prefixWord, tailWord_736893, baseEnd_736893] using wordTrace_append hprefix tailTrace_736893
  have hstable : (prefixWord ++ tailWord_736893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736893).length < 2 ^ (prefixWord ++ tailWord_736893).sum := by decide
  have hdescent : baseEnd_736893 < baseStart_736893 := by decide
  rcases family_descends (prefixWord ++ tailWord_736893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736910 : List Nat := [4, 1, 1, 3, 1, 3, 2, 7]
def baseStart_736910 : Nat := 118140960795 + 736910 * 2 ^ 59
def prefixEnd_736910 : Nat := 4983230072969 + 3 ^ 40 * 736910 * 2
def baseEnd_736910 : Nat := 28028816970727190365631

theorem tailTrace_736910 : CollatzResearch.WordTrace tailWord_736910 prefixEnd_736910 28028816970727190365631 := by
  unfold tailWord_736910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359664470038549881668023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17918210506872266035562789 3359664470038549881668023)
  ·
    refine ⟨5039496705057824822502035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3359664470038549881668023 5039496705057824822502035)
    ·
      refine ⟨7559245057586737233753053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5039496705057824822502035 7559245057586737233753053)
      ·
        refine ⟨2834716896595026462657395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7559245057586737233753053 2834716896595026462657395)
        ·
          refine ⟨4252075344892539693986093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834716896595026462657395 4252075344892539693986093)
          ·
            refine ⟨1594528254334702385244785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4252075344892539693986093 1594528254334702385244785)
            ·
              refine ⟨1195896190751026788933589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594528254334702385244785 1195896190751026788933589)
              ·
                refine ⟨28028816970727190365631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1195896190751026788933589 28028816970727190365631)
                ·
                  rfl

theorem cell22_736910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_736910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736910 prefixEnd_736910 := by exact prefixLift 736910
  have htrace : WordTrace (prefixWord ++ tailWord_736910) baseStart_736910 baseEnd_736910 := by
    simpa [prefixWord, tailWord_736910, baseEnd_736910] using wordTrace_append hprefix tailTrace_736910
  have hstable : (prefixWord ++ tailWord_736910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736910).length < 2 ^ (prefixWord ++ tailWord_736910).sum := by decide
  have hdescent : baseEnd_736910 < baseStart_736910 := by decide
  rcases family_descends (prefixWord ++ tailWord_736910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736914 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_736914 : Nat := 118140960795 + 736914 * 2 ^ 59
def prefixEnd_736914 : Nat := 4983230072969 + 3 ^ 40 * 736914 * 2
def baseEnd_736914 : Nat := 252260722018290036190667

theorem tailTrace_736914 : CollatzResearch.WordTrace tailWord_736914 prefixEnd_736914 252260722018290036190667 := by
  unfold tailWord_736914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719365413073476934122449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17918307768195938490993197 6719365413073476934122449)
  ·
    refine ⟨5039524059805107700591837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6719365413073476934122449 5039524059805107700591837)
    ·
      refine ⟨1889821522426915387721939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5039524059805107700591837 1889821522426915387721939)
      ·
        refine ⟨2834732283640373081582909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889821522426915387721939 2834732283640373081582909)
        ·
          refine ⟨1063024606365139905593591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2834732283640373081582909 1063024606365139905593591)
          ·
            refine ⟨1594536909547709858390387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063024606365139905593591 1594536909547709858390387)
            ·
              refine ⟨2391805364321564787585581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594536909547709858390387 2391805364321564787585581)
              ·
                refine ⟨896927011620586795344593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2391805364321564787585581 896927011620586795344593)
                ·
                  refine ⟨672695258715440096508445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896927011620586795344593 672695258715440096508445)
                  ·
                    refine ⟨252260722018290036190667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 672695258715440096508445 252260722018290036190667)
                    ·
                      rfl

theorem cell22_736914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_736914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736914 prefixEnd_736914 := by exact prefixLift 736914
  have htrace : WordTrace (prefixWord ++ tailWord_736914) baseStart_736914 baseEnd_736914 := by
    simpa [prefixWord, tailWord_736914, baseEnd_736914] using wordTrace_append hprefix tailTrace_736914
  have hstable : (prefixWord ++ tailWord_736914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736914).length < 2 ^ (prefixWord ++ tailWord_736914).sum := by decide
  have hdescent : baseEnd_736914 < baseStart_736914 := by decide
  rcases family_descends (prefixWord ++ tailWord_736914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736925 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_736925 : Nat := 118140960795 + 736925 * 2 ^ 59
def prefixEnd_736925 : Nat := 4983230072969 + 3 ^ 40 * 736925 * 2
def baseEnd_736925 : Nat := 252264487543089674165633

theorem tailTrace_736925 : CollatzResearch.WordTrace tailWord_736925 prefixEnd_736925 252264487543089674165633 := by
  unfold tailWord_736925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26877862855254056615140229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17918575236836037743426819 26877862855254056615140229)
  ·
    refine ⟨5039599285360135615338793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26877862855254056615140229 5039599285360135615338793)
    ·
      refine ⟨3779699464020101711504095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5039599285360135615338793 3779699464020101711504095)
      ·
        refine ⟨5669549196030152567256143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779699464020101711504095 5669549196030152567256143)
        ·
          refine ⟨8504323794045228850884215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669549196030152567256143 8504323794045228850884215)
          ·
            refine ⟨12756485691067843276326323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8504323794045228850884215 12756485691067843276326323)
            ·
              refine ⟨19134728536601764914489485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12756485691067843276326323 19134728536601764914489485)
              ·
                refine ⟨7175523201225661842933557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19134728536601764914489485 7175523201225661842933557)
                ·
                  refine ⟨672705300114905797775021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7175523201225661842933557 672705300114905797775021)
                  ·
                    refine ⟨252264487543089674165633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 672705300114905797775021 252264487543089674165633)
                    ·
                      rfl

theorem cell22_736925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_736925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736925 prefixEnd_736925 := by exact prefixLift 736925
  have htrace : WordTrace (prefixWord ++ tailWord_736925) baseStart_736925 baseEnd_736925 := by
    simpa [prefixWord, tailWord_736925, baseEnd_736925] using wordTrace_append hprefix tailTrace_736925
  have hstable : (prefixWord ++ tailWord_736925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736925).length < 2 ^ (prefixWord ++ tailWord_736925).sum := by decide
  have hdescent : baseEnd_736925 < baseStart_736925 := by decide
  rcases family_descends (prefixWord ++ tailWord_736925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736985 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_736985 : Nat := 118140960795 + 736985 * 2 ^ 59
def prefixEnd_736985 : Nat := 4983230072969 + 3 ^ 40 * 736985 * 2
def baseEnd_736985 : Nat := 252285026769269517665449

theorem tailTrace_736985 : CollatzResearch.WordTrace tailWord_736985 prefixEnd_736985 252285026769269517665449 := by
  unfold tailWord_736985
  simp only [CollatzResearch.WordTrace]
  refine ⟨26880051235036686862324409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17920034156691124574882939 26880051235036686862324409)
  ·
    refine ⟨20160038426277515146743307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26880051235036686862324409 20160038426277515146743307)
    ·
      refine ⟨30240057639416272720114961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20160038426277515146743307 30240057639416272720114961)
      ·
        refine ⟨22680043229562204540086221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30240057639416272720114961 22680043229562204540086221)
        ·
          refine ⟨8505016211085826702532333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22680043229562204540086221 8505016211085826702532333)
          ·
            refine ⟨3189381079157185013449625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8505016211085826702532333 3189381079157185013449625)
            ·
              refine ⟨2392035809367888760087219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189381079157185013449625 2392035809367888760087219)
              ·
                refine ⟨3588053714051833140130829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392035809367888760087219 3588053714051833140130829)
                ·
                  refine ⟨1345520142769437427549061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3588053714051833140130829 1345520142769437427549061)
                  ·
                    refine ⟨252285026769269517665449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1345520142769437427549061 252285026769269517665449)
                    ·
                      rfl

theorem cell22_736985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_736985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_736985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_736985 prefixEnd_736985 := by exact prefixLift 736985
  have htrace : WordTrace (prefixWord ++ tailWord_736985) baseStart_736985 baseEnd_736985 := by
    simpa [prefixWord, tailWord_736985, baseEnd_736985] using wordTrace_append hprefix tailTrace_736985
  have hstable : (prefixWord ++ tailWord_736985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736985).length < 2 ^ (prefixWord ++ tailWord_736985).sum := by decide
  have hdescent : baseEnd_736985 < baseStart_736985 := by decide
  rcases family_descends (prefixWord ++ tailWord_736985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737045 : List Nat := [1, 3, 2, 1, 2, 4, 1, 8]
def baseStart_737045 : Nat := 118140960795 + 737045 * 2 ^ 59
def prefixEnd_737045 : Nat := 4983230072969 + 3 ^ 40 * 737045 * 2
def baseEnd_737045 : Nat := 28033951777272151240585

theorem tailTrace_737045 : CollatzResearch.WordTrace tailWord_737045 prefixEnd_737045 28033951777272151240585 := by
  unfold tailWord_737045
  simp only [CollatzResearch.WordTrace]
  refine ⟨26882239614819317109508589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17921493076546211406339059 26882239614819317109508589)
  ·
    refine ⟨10080839855557243916065721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26882239614819317109508589 10080839855557243916065721)
    ·
      refine ⟨7560629891667932937049291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10080839855557243916065721 7560629891667932937049291)
      ·
        refine ⟨11340944837501899405573937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7560629891667932937049291 11340944837501899405573937)
        ·
          refine ⟨8505708628126424554180453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11340944837501899405573937 8505708628126424554180453)
          ·
            refine ⟨1594820367773704603908835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8505708628126424554180453 1594820367773704603908835)
            ·
              refine ⟨2392230551660556905863253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594820367773704603908835 2392230551660556905863253)
              ·
                refine ⟨28033951777272151240585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2392230551660556905863253 28033951777272151240585)
                ·
                  rfl

theorem cell22_737045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 8].length) (baseStart_737045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737045 prefixEnd_737045 := by exact prefixLift 737045
  have htrace : WordTrace (prefixWord ++ tailWord_737045) baseStart_737045 baseEnd_737045 := by
    simpa [prefixWord, tailWord_737045, baseEnd_737045] using wordTrace_append hprefix tailTrace_737045
  have hstable : (prefixWord ++ tailWord_737045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737045).length < 2 ^ (prefixWord ++ tailWord_737045).sum := by decide
  have hdescent : baseEnd_737045 < baseStart_737045 := by decide
  rcases family_descends (prefixWord ++ tailWord_737045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737124 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 5]
def baseStart_737124 : Nat := 118140960795 + 737124 * 2 ^ 59
def prefixEnd_737124 : Nat := 4983230072969 + 3 ^ 40 * 737124 * 2
def baseEnd_737124 : Nat := 84110869769973162813341

theorem tailTrace_737124 : CollatzResearch.WordTrace tailWord_737124 prefixEnd_737124 84110869769973162813341 := by
  unfold tailWord_737124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13442560490766556800817213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17923413987688742401089617 13442560490766556800817213)
  ·
    refine ⟨5040960184037458800306455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13442560490766556800817213 5040960184037458800306455)
    ·
      refine ⟨7561440276056188200459683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040960184037458800306455 7561440276056188200459683)
      ·
        refine ⟨11342160414084282300689525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7561440276056188200459683 11342160414084282300689525)
        ·
          refine ⟨1063327538820401465689643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11342160414084282300689525 1063327538820401465689643)
          ·
            refine ⟨1594991308230602198534465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063327538820401465689643 1594991308230602198534465)
            ·
              refine ⟨1196243481172951648900849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594991308230602198534465 1196243481172951648900849)
              ·
                refine ⟨897182610879713736675637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196243481172951648900849 897182610879713736675637)
                ·
                  refine ⟨84110869769973162813341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897182610879713736675637 84110869769973162813341)
                  ·
                    rfl

theorem cell22_737124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_737124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737124 prefixEnd_737124 := by exact prefixLift 737124
  have htrace : WordTrace (prefixWord ++ tailWord_737124) baseStart_737124 baseEnd_737124 := by
    simpa [prefixWord, tailWord_737124, baseEnd_737124] using wordTrace_append hprefix tailTrace_737124
  have hstable : (prefixWord ++ tailWord_737124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737124).length < 2 ^ (prefixWord ++ tailWord_737124).sum := by decide
  have hdescent : baseEnd_737124 < baseStart_737124 := by decide
  rcases family_descends (prefixWord ++ tailWord_737124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737195 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 4, 7]
def baseStart_737195 : Nat := 118140960795 + 737195 * 2 ^ 59
def prefixEnd_737195 : Nat := 4983230072969 + 3 ^ 40 * 737195 * 2
def baseEnd_737195 : Nat := 252356914060898969914805

theorem tailTrace_737195 : CollatzResearch.WordTrace tailWord_737195 prefixEnd_737195 252356914060898969914805 := by
  unfold tailWord_737195
  simp only [CollatzResearch.WordTrace]
  refine ⟨26887710564275892727469039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17925140376183928484979359 26887710564275892727469039)
  ·
    refine ⟨40331565846413839091203559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26887710564275892727469039 40331565846413839091203559)
    ·
      refine ⟨60497348769620758636805339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40331565846413839091203559 60497348769620758636805339)
      ·
        refine ⟨90746023154431137955208009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60497348769620758636805339 90746023154431137955208009)
        ·
          refine ⟨68059517365823353466406007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90746023154431137955208009 68059517365823353466406007)
          ·
            refine ⟨102089276048735030199609011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68059517365823353466406007 102089276048735030199609011)
            ·
              refine ⟨153133914073102545299413517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102089276048735030199609011 153133914073102545299413517)
              ·
                refine ⟨57425217777413454487280069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153133914073102545299413517 57425217777413454487280069)
                ·
                  refine ⟨10767228333265022716365013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57425217777413454487280069 10767228333265022716365013)
                  ·
                    refine ⟨252356914060898969914805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10767228333265022716365013 252356914060898969914805)
                    ·
                      rfl

theorem cell22_737195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_737195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737195 prefixEnd_737195 := by exact prefixLift 737195
  have htrace : WordTrace (prefixWord ++ tailWord_737195) baseStart_737195 baseEnd_737195 := by
    simpa [prefixWord, tailWord_737195, baseEnd_737195] using wordTrace_append hprefix tailTrace_737195
  have hstable : (prefixWord ++ tailWord_737195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737195).length < 2 ^ (prefixWord ++ tailWord_737195).sum := by decide
  have hdescent : baseEnd_737195 < baseStart_737195 := by decide
  rcases family_descends (prefixWord ++ tailWord_737195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737214 : List Nat := [4, 2, 1, 1, 1, 3, 4, 6]
def baseStart_737214 : Nat := 118140960795 + 737214 * 2 ^ 59
def prefixEnd_737214 : Nat := 4983230072969 + 3 ^ 40 * 737214 * 2
def baseEnd_737214 : Nat := 28040379794354361521083

theorem tailTrace_737214 : CollatzResearch.WordTrace tailWord_737214 prefixEnd_737214 28040379794354361521083 := by
  unfold tailWord_737214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361050443900882371551337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17925602367471372648273797 3361050443900882371551337)
  ·
    refine ⟨2520787832925661778663503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3361050443900882371551337 2520787832925661778663503)
    ·
      refine ⟨3781181749388492667995255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2520787832925661778663503 3781181749388492667995255)
      ·
        refine ⟨5671772624082739001992883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781181749388492667995255 5671772624082739001992883)
        ·
          refine ⟨8507658936124108502989325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671772624082739001992883 8507658936124108502989325)
          ·
            refine ⟨3190372101046540688620997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8507658936124108502989325 3190372101046540688620997)
            ·
              refine ⟨598194768946226379116437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3190372101046540688620997 598194768946226379116437)
              ·
                refine ⟨28040379794354361521083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 598194768946226379116437 28040379794354361521083)
                ·
                  rfl

theorem cell22_737214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_737214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737214 prefixEnd_737214 := by exact prefixLift 737214
  have htrace : WordTrace (prefixWord ++ tailWord_737214) baseStart_737214 baseEnd_737214 := by
    simpa [prefixWord, tailWord_737214, baseEnd_737214] using wordTrace_append hprefix tailTrace_737214
  have hstable : (prefixWord ++ tailWord_737214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737214).length < 2 ^ (prefixWord ++ tailWord_737214).sum := by decide
  have hdescent : baseEnd_737214 < baseStart_737214 := by decide
  rcases family_descends (prefixWord ++ tailWord_737214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737381 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_737381 : Nat := 118140960795 + 737381 * 2 ^ 59
def prefixEnd_737381 : Nat := 4983230072969 + 3 ^ 40 * 737381 * 2
def baseEnd_737381 : Nat := 252420585662056484764235

theorem tailTrace_737381 : CollatzResearch.WordTrace tailWord_737381 prefixEnd_737381 252420585662056484764235 := by
  unfold tailWord_737381
  simp only [CollatzResearch.WordTrace]
  refine ⟨26894494541602046493739997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17929663027734697662493331 26894494541602046493739997)
  ·
    refine ⟨10085435453100767435152499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26894494541602046493739997 10085435453100767435152499)
    ·
      refine ⟨15128153179651151152728749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085435453100767435152499 15128153179651151152728749)
      ·
        refine ⟨5673057442369181682273281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15128153179651151152728749 5673057442369181682273281)
        ·
          refine ⟨4254793081776886261704961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5673057442369181682273281 4254793081776886261704961)
          ·
            refine ⟨3191094811332664696278721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4254793081776886261704961 3191094811332664696278721)
            ·
              refine ⟨2393321108499498522209041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191094811332664696278721 2393321108499498522209041)
              ·
                refine ⟨1794990831374623891656781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393321108499498522209041 1794990831374623891656781)
                ·
                  refine ⟨673121561765483959371293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1794990831374623891656781 673121561765483959371293)
                  ·
                    refine ⟨252420585662056484764235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673121561765483959371293 252420585662056484764235)
                    ·
                      rfl

theorem cell22_737381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_737381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737381 prefixEnd_737381 := by exact prefixLift 737381
  have htrace : WordTrace (prefixWord ++ tailWord_737381) baseStart_737381 baseEnd_737381 := by
    simpa [prefixWord, tailWord_737381, baseEnd_737381] using wordTrace_append hprefix tailTrace_737381
  have hstable : (prefixWord ++ tailWord_737381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737381).length < 2 ^ (prefixWord ++ tailWord_737381).sum := by decide
  have hdescent : baseEnd_737381 < baseStart_737381 := by decide
  rcases family_descends (prefixWord ++ tailWord_737381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737394 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_737394 : Nat := 118140960795 + 737394 * 2 ^ 59
def prefixEnd_737394 : Nat := 4983230072969 + 3 ^ 40 * 737394 * 2
def baseEnd_737394 : Nat := 84141678609242928063065

theorem tailTrace_737394 : CollatzResearch.WordTrace tailWord_737394 prefixEnd_737394 84141678609242928063065 := by
  unfold tailWord_737394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723742172638737428490809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17929979127036633142642157 6723742172638737428490809)
  ·
    refine ⟨5042806629479053071368107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6723742172638737428490809 5042806629479053071368107)
    ·
      refine ⟨7564209944218579607052161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5042806629479053071368107 7564209944218579607052161)
      ·
        refine ⟨5673157458163934705289121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7564209944218579607052161 5673157458163934705289121)
        ·
          refine ⟨4254868093622951028966841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5673157458163934705289121 4254868093622951028966841)
          ·
            refine ⟨3191151070217213271725131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4254868093622951028966841 3191151070217213271725131)
            ·
              refine ⟨4786726605325819907587697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191151070217213271725131 4786726605325819907587697)
              ·
                refine ⟨3590044953994364930690773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786726605325819907587697 3590044953994364930690773)
                ·
                  refine ⟨84141678609242928063065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3590044953994364930690773 84141678609242928063065)
                  ·
                    rfl

theorem cell22_737394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_737394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737394 prefixEnd_737394 := by exact prefixLift 737394
  have htrace : WordTrace (prefixWord ++ tailWord_737394) baseStart_737394 baseEnd_737394 := by
    simpa [prefixWord, tailWord_737394, baseEnd_737394] using wordTrace_append hprefix tailTrace_737394
  have hstable : (prefixWord ++ tailWord_737394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737394).length < 2 ^ (prefixWord ++ tailWord_737394).sum := by decide
  have hdescent : baseEnd_737394 < baseStart_737394 := by decide
  rcases family_descends (prefixWord ++ tailWord_737394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737424 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_737424 : Nat := 118140960795 + 737424 * 2 ^ 59
def prefixEnd_737424 : Nat := 4983230072969 + 3 ^ 40 * 737424 * 2
def baseEnd_737424 : Nat := 252435305440818705939103

theorem tailTrace_737424 : CollatzResearch.WordTrace tailWord_737424 prefixEnd_737424 252435305440818705939103 := by
  unfold tailWord_737424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13448031440223132418777663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17930708586964176558370217 13448031440223132418777663)
  ·
    refine ⟨20172047160334698628166495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13448031440223132418777663 20172047160334698628166495)
    ·
      refine ⟨30258070740502047942249743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20172047160334698628166495 30258070740502047942249743)
      ·
        refine ⟨45387106110753071913374615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30258070740502047942249743 45387106110753071913374615)
        ·
          refine ⟨68080659166129607870061923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45387106110753071913374615 68080659166129607870061923)
          ·
            refine ⟨102120988749194411805092885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68080659166129607870061923 102120988749194411805092885)
            ·
              refine ⟨4786921347618488053363729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102120988749194411805092885 4786921347618488053363729)
              ·
                refine ⟨3590191010713866040022797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786921347618488053363729 3590191010713866040022797)
                ·
                  refine ⟨1346321629017699765008549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3590191010713866040022797 1346321629017699765008549)
                  ·
                    refine ⟨252435305440818705939103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1346321629017699765008549 252435305440818705939103)
                    ·
                      rfl

theorem cell22_737424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_737424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737424 prefixEnd_737424 := by exact prefixLift 737424
  have htrace : WordTrace (prefixWord ++ tailWord_737424) baseStart_737424 baseEnd_737424 := by
    simpa [prefixWord, tailWord_737424, baseEnd_737424] using wordTrace_append hprefix tailTrace_737424
  have hstable : (prefixWord ++ tailWord_737424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737424).length < 2 ^ (prefixWord ++ tailWord_737424).sum := by decide
  have hdescent : baseEnd_737424 < baseStart_737424 := by decide
  rcases family_descends (prefixWord ++ tailWord_737424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737441 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_737441 : Nat := 118140960795 + 737441 * 2 ^ 59
def prefixEnd_737441 : Nat := 4983230072969 + 3 ^ 40 * 737441 * 2
def baseEnd_737441 : Nat := 252441124888236328264051

theorem tailTrace_737441 : CollatzResearch.WordTrace tailWord_737441 prefixEnd_737441 252441124888236328264051 := by
  unfold tailWord_737441
  simp only [CollatzResearch.WordTrace]
  refine ⟨26896682921384676740924177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17931121947589784493949451 26896682921384676740924177)
  ·
    refine ⟨20172512191038507555693133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26896682921384676740924177 20172512191038507555693133)
    ·
      refine ⟨7564692071639440333384925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20172512191038507555693133 7564692071639440333384925)
      ·
        refine ⟨2836759526864790125019347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7564692071639440333384925 2836759526864790125019347)
        ·
          refine ⟨4255139290297185187529021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2836759526864790125019347 4255139290297185187529021)
          ·
            refine ⟨1595677233861444445323383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4255139290297185187529021 1595677233861444445323383)
            ·
              refine ⟨2393515850792166667985075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595677233861444445323383 2393515850792166667985075)
              ·
                refine ⟨3590273776188250001977613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393515850792166667985075 3590273776188250001977613)
                ·
                  refine ⟨1346352666070593750741605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3590273776188250001977613 1346352666070593750741605)
                  ·
                    refine ⟨252441124888236328264051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1346352666070593750741605 252441124888236328264051)
                    ·
                      rfl

theorem cell22_737441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_737441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737441 prefixEnd_737441 := by exact prefixLift 737441
  have htrace : WordTrace (prefixWord ++ tailWord_737441) baseStart_737441 baseEnd_737441 := by
    simpa [prefixWord, tailWord_737441, baseEnd_737441] using wordTrace_append hprefix tailTrace_737441
  have hstable : (prefixWord ++ tailWord_737441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737441).length < 2 ^ (prefixWord ++ tailWord_737441).sum := by decide
  have hdescent : baseEnd_737441 < baseStart_737441 := by decide
  rcases family_descends (prefixWord ++ tailWord_737441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737458 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_737458 : Nat := 118140960795 + 737458 * 2 ^ 59
def prefixEnd_737458 : Nat := 4983230072969 + 3 ^ 40 * 737458 * 2
def baseEnd_737458 : Nat := 252446944335653950588999

theorem tailTrace_737458 : CollatzResearch.WordTrace tailWord_737458 prefixEnd_737458 252446944335653950588999 := by
  unfold tailWord_737458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6724325740580772161073257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17931535308215392429528685 6724325740580772161073257)
  ·
    refine ⟨5043244305435579120804943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6724325740580772161073257 5043244305435579120804943)
    ·
      refine ⟨7564866458153368681207415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043244305435579120804943 7564866458153368681207415)
      ·
        refine ⟨11347299687230053021811123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7564866458153368681207415 11347299687230053021811123)
        ·
          refine ⟨17020949530845079532716685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11347299687230053021811123 17020949530845079532716685)
          ·
            refine ⟨6382856074066904824768757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17020949530845079532716685 6382856074066904824768757)
            ·
              refine ⟨598392756943772327322071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6382856074066904824768757 598392756943772327322071)
              ·
                refine ⟨897589135415658490983107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598392756943772327322071 897589135415658490983107)
                ·
                  refine ⟨1346383703123487736474661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897589135415658490983107 1346383703123487736474661)
                  ·
                    refine ⟨252446944335653950588999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1346383703123487736474661 252446944335653950588999)
                    ·
                      rfl

theorem cell22_737458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_737458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737458 prefixEnd_737458 := by exact prefixLift 737458
  have htrace : WordTrace (prefixWord ++ tailWord_737458) baseStart_737458 baseEnd_737458 := by
    simpa [prefixWord, tailWord_737458, baseEnd_737458] using wordTrace_append hprefix tailTrace_737458
  have hstable : (prefixWord ++ tailWord_737458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737458).length < 2 ^ (prefixWord ++ tailWord_737458).sum := by decide
  have hdescent : baseEnd_737458 < baseStart_737458 := by decide
  rcases family_descends (prefixWord ++ tailWord_737458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737469 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_737469 : Nat := 118140960795 + 737469 * 2 ^ 59
def prefixEnd_737469 : Nat := 4983230072969 + 3 ^ 40 * 737469 * 2
def baseEnd_737469 : Nat := 252450709860453588563965

theorem tailTrace_737469 : CollatzResearch.WordTrace tailWord_737469 prefixEnd_737469 252450709860453588563965 := by
  unfold tailWord_737469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26897704165283237522943461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17931802776855491681962307 26897704165283237522943461)
  ·
    refine ⟨5043319530990607035551899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26897704165283237522943461 5043319530990607035551899)
    ·
      refine ⟨7564979296485910553327849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043319530990607035551899 7564979296485910553327849)
      ·
        refine ⟨5673734472364432914995887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7564979296485910553327849 5673734472364432914995887)
        ·
          refine ⟨8510601708546649372493831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5673734472364432914995887 8510601708546649372493831)
          ·
            refine ⟨12765902562819974058740747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8510601708546649372493831 12765902562819974058740747)
            ·
              refine ⟨19148853844229961088111121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12765902562819974058740747 19148853844229961088111121)
              ·
                refine ⟨14361640383172470816083341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19148853844229961088111121 14361640383172470816083341)
                ·
                  refine ⟨5385615143689676556031253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14361640383172470816083341 5385615143689676556031253)
                  ·
                    refine ⟨252450709860453588563965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5385615143689676556031253 252450709860453588563965)
                    ·
                      rfl

theorem cell22_737469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_737469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737469 prefixEnd_737469 := by exact prefixLift 737469
  have htrace : WordTrace (prefixWord ++ tailWord_737469) baseStart_737469 baseEnd_737469 := by
    simpa [prefixWord, tailWord_737469, baseEnd_737469] using wordTrace_append hprefix tailTrace_737469
  have hstable : (prefixWord ++ tailWord_737469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737469).length < 2 ^ (prefixWord ++ tailWord_737469).sum := by decide
  have hdescent : baseEnd_737469 < baseStart_737469 := by decide
  rcases family_descends (prefixWord ++ tailWord_737469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737516 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_737516 : Nat := 118140960795 + 737516 * 2 ^ 59
def prefixEnd_737516 : Nat := 4983230072969 + 3 ^ 40 * 737516 * 2
def baseEnd_737516 : Nat := 252466798920961132638821

theorem tailTrace_737516 : CollatzResearch.WordTrace tailWord_737516 prefixEnd_737516 252466798920961132638821 := by
  unfold tailWord_737516
  simp only [CollatzResearch.WordTrace]
  refine ⟨13449709198056482274952201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17932945597408643033269601 13449709198056482274952201)
  ·
    refine ⟨10087281898542361706214151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13449709198056482274952201 10087281898542361706214151)
    ·
      refine ⟨15130922847813542559321227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087281898542361706214151 15130922847813542559321227)
      ·
        refine ⟨22696384271720313838981841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15130922847813542559321227 22696384271720313838981841)
        ·
          refine ⟨17022288203790235379236381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22696384271720313838981841 17022288203790235379236381)
          ·
            refine ⟨6383358076421338267213643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17022288203790235379236381 6383358076421338267213643)
            ·
              refine ⟨9575037114632007400820465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6383358076421338267213643 9575037114632007400820465)
              ·
                refine ⟨7181277835974005550615349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9575037114632007400820465 7181277835974005550615349)
                ·
                  refine ⟨673244797122563020370189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7181277835974005550615349 673244797122563020370189)
                  ·
                    refine ⟨252466798920961132638821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673244797122563020370189 252466798920961132638821)
                    ·
                      rfl

theorem cell22_737516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_737516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737516 prefixEnd_737516 := by exact prefixLift 737516
  have htrace : WordTrace (prefixWord ++ tailWord_737516) baseStart_737516 baseEnd_737516 := by
    simpa [prefixWord, tailWord_737516, baseEnd_737516] using wordTrace_append hprefix tailTrace_737516
  have hstable : (prefixWord ++ tailWord_737516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737516).length < 2 ^ (prefixWord ++ tailWord_737516).sum := by decide
  have hdescent : baseEnd_737516 < baseStart_737516 := by decide
  rcases family_descends (prefixWord ++ tailWord_737516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737546 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_737546 : Nat := 118140960795 + 737546 * 2 ^ 59
def prefixEnd_737546 : Nat := 4983230072969 + 3 ^ 40 * 737546 * 2
def baseEnd_737546 : Nat := 84159022844683684796243

theorem tailTrace_737546 : CollatzResearch.WordTrace tailWord_737546 prefixEnd_737546 84159022844683684796243 := by
  unfold tailWord_737546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725128146501069918374123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17933675057336186448997661 6725128146501069918374123)
  ·
    refine ⟨10087692219751604877561185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6725128146501069918374123 10087692219751604877561185)
    ·
      refine ⟨7565769164813703658170889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10087692219751604877561185 7565769164813703658170889)
      ·
        refine ⟨5674326873610277743628167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7565769164813703658170889 5674326873610277743628167)
        ·
          refine ⟨8511490310415416615442251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5674326873610277743628167 8511490310415416615442251)
          ·
            refine ⟨12767235465623124923163377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8511490310415416615442251 12767235465623124923163377)
            ·
              refine ⟨9575426599217343692372533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12767235465623124923163377 9575426599217343692372533)
              ·
                refine ⟨897696243676625971159925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9575426599217343692372533 897696243676625971159925)
                ·
                  refine ⟨84159022844683684796243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897696243676625971159925 84159022844683684796243)
                  ·
                    rfl

theorem cell22_737546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_737546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737546 prefixEnd_737546 := by exact prefixLift 737546
  have htrace : WordTrace (prefixWord ++ tailWord_737546) baseStart_737546 baseEnd_737546 := by
    simpa [prefixWord, tailWord_737546, baseEnd_737546] using wordTrace_append hprefix tailTrace_737546
  have hstable : (prefixWord ++ tailWord_737546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737546).length < 2 ^ (prefixWord ++ tailWord_737546).sum := by decide
  have hdescent : baseEnd_737546 < baseStart_737546 := by decide
  rcases family_descends (prefixWord ++ tailWord_737546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737567 : List Nat := [1, 1, 2, 4, 3, 3, 1, 3, 1, 3]
def baseStart_737567 : Nat := 118140960795 + 737567 * 2 ^ 59
def prefixEnd_737567 : Nat := 4983230072969 + 3 ^ 40 * 737567 * 2
def baseEnd_737567 : Nat := 252484257263213999613665

theorem tailTrace_737567 : CollatzResearch.WordTrace tailWord_737567 prefixEnd_737567 252484257263213999613665 := by
  unfold tailWord_737567
  simp only [CollatzResearch.WordTrace]
  refine ⟨26901278518928200260010955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17934185679285466840007303 26901278518928200260010955)
  ·
    refine ⟨40351917778392300390016433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26901278518928200260010955 40351917778392300390016433)
    ·
      refine ⟨30263938333794225292512325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40351917778392300390016433 30263938333794225292512325)
      ·
        refine ⟨5674488437586417242346061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30263938333794225292512325 5674488437586417242346061)
        ·
          refine ⟨2127933164094906465879773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5674488437586417242346061 2127933164094906465879773)
          ·
            refine ⟨797974936535589924704915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2127933164094906465879773 797974936535589924704915)
            ·
              refine ⟨1196962404803384887057373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797974936535589924704915 1196962404803384887057373)
              ·
                refine ⟨448860901801269332646515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196962404803384887057373 448860901801269332646515)
                ·
                  refine ⟨673291352701903998969773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448860901801269332646515 673291352701903998969773)
                  ·
                    refine ⟨252484257263213999613665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673291352701903998969773 252484257263213999613665)
                    ·
                      rfl

theorem cell22_737567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 3].length) (baseStart_737567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737567 prefixEnd_737567 := by exact prefixLift 737567
  have htrace : WordTrace (prefixWord ++ tailWord_737567) baseStart_737567 baseEnd_737567 := by
    simpa [prefixWord, tailWord_737567, baseEnd_737567] using wordTrace_append hprefix tailTrace_737567
  have hstable : (prefixWord ++ tailWord_737567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737567).length < 2 ^ (prefixWord ++ tailWord_737567).sum := by decide
  have hdescent : baseEnd_737567 < baseStart_737567 := by decide
  rcases family_descends (prefixWord ++ tailWord_737567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737640 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 2, 3]
def baseStart_737640 : Nat := 118140960795 + 737640 * 2 ^ 59
def prefixEnd_737640 : Nat := 4983230072969 + 3 ^ 40 * 737640 * 2
def baseEnd_737640 : Nat := 252509246655066142538441

theorem tailTrace_737640 : CollatzResearch.WordTrace tailWord_737640 prefixEnd_737640 252509246655066142538441 := by
  unfold tailWord_737640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13451970523831866863709187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17935960698442489151612249 13451970523831866863709187)
  ·
    refine ⟨20177955785747800295563781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13451970523831866863709187 20177955785747800295563781)
    ·
      refine ⟨3783366709827712555418209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20177955785747800295563781 3783366709827712555418209)
      ·
        refine ⟨2837525032370784416563657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3783366709827712555418209 2837525032370784416563657)
        ·
          refine ⟨2128143774278088312422743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2837525032370784416563657 2128143774278088312422743)
          ·
            refine ⟨3192215661417132468634115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128143774278088312422743 3192215661417132468634115)
            ·
              refine ⟨4788323492125698702951173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3192215661417132468634115 4788323492125698702951173)
              ·
                refine ⟨897810654773568506803345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4788323492125698702951173 897810654773568506803345)
                ·
                  refine ⟨673357991080176380102509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 897810654773568506803345 673357991080176380102509)
                  ·
                    refine ⟨252509246655066142538441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673357991080176380102509 252509246655066142538441)
                    ·
                      rfl

theorem cell22_737640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_737640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737640 prefixEnd_737640 := by exact prefixLift 737640
  have htrace : WordTrace (prefixWord ++ tailWord_737640) baseStart_737640 baseEnd_737640 := by
    simpa [prefixWord, tailWord_737640, baseEnd_737640] using wordTrace_append hprefix tailTrace_737640
  have hstable : (prefixWord ++ tailWord_737640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737640).length < 2 ^ (prefixWord ++ tailWord_737640).sum := by decide
  have hdescent : baseEnd_737640 < baseStart_737640 := by decide
  rcases family_descends (prefixWord ++ tailWord_737640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737642 : List Nat := [3, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_737642 : Nat := 118140960795 + 737642 * 2 ^ 59
def prefixEnd_737642 : Nat := 4983230072969 + 3 ^ 40 * 737642 * 2
def baseEnd_737642 : Nat := 84169977098646267996145

theorem tailTrace_737642 : CollatzResearch.WordTrace tailWord_737642 prefixEnd_737642 84169977098646267996145 := by
  unfold tailWord_737642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726003498414122017247795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17936009329104325379327453 6726003498414122017247795)
  ·
    refine ⟨10089005247621183025871693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6726003498414122017247795 10089005247621183025871693)
    ·
      refine ⟨3783376967857943634701885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10089005247621183025871693 3783376967857943634701885)
      ·
        refine ⟨1418766362946728863013207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3783376967857943634701885 1418766362946728863013207)
        ·
          refine ⟨2128149544420093294519811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418766362946728863013207 2128149544420093294519811)
          ·
            refine ⟨3192224316630139941779717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128149544420093294519811 3192224316630139941779717)
            ·
              refine ⟨598542059368151239083697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3192224316630139941779717 598542059368151239083697)
              ·
                refine ⟨448906544526113429312773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598542059368151239083697 448906544526113429312773)
                ·
                  refine ⟨84169977098646267996145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448906544526113429312773 84169977098646267996145)
                  ·
                    rfl

theorem cell22_737642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_737642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737642 prefixEnd_737642 := by exact prefixLift 737642
  have htrace : WordTrace (prefixWord ++ tailWord_737642) baseStart_737642 baseEnd_737642 := by
    simpa [prefixWord, tailWord_737642, baseEnd_737642] using wordTrace_append hprefix tailTrace_737642
  have hstable : (prefixWord ++ tailWord_737642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737642).length < 2 ^ (prefixWord ++ tailWord_737642).sum := by decide
  have hdescent : baseEnd_737642 < baseStart_737642 := by decide
  rcases family_descends (prefixWord ++ tailWord_737642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737653 : List Nat := [1, 3, 4, 1, 2, 1, 3, 7]
def baseStart_737653 : Nat := 118140960795 + 737653 * 2 ^ 59
def prefixEnd_737653 : Nat := 4983230072969 + 3 ^ 40 * 737653 * 2
def baseEnd_737653 : Nat := 28057077424526493551489

theorem tailTrace_737653 : CollatzResearch.WordTrace tailWord_737653 prefixEnd_737653 28057077424526493551489 := by
  unfold tailWord_737653
  simp only [CollatzResearch.WordTrace]
  refine ⟨26904415196616636947641613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17936276797744424631761075 26904415196616636947641613)
  ·
    refine ⟨10089155698731238855365605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26904415196616636947641613 10089155698731238855365605)
    ·
      refine ⟨1891716693512107285381051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10089155698731238855365605 1891716693512107285381051)
      ·
        refine ⟨2837575040268160928071577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891716693512107285381051 2837575040268160928071577)
        ·
          refine ⟨2128181280201120696053683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2837575040268160928071577 2128181280201120696053683)
          ·
            refine ⟨3192271920301681044080525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128181280201120696053683 3192271920301681044080525)
            ·
              refine ⟨1197101970113130391530197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3192271920301681044080525 1197101970113130391530197)
              ·
                refine ⟨28057077424526493551489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1197101970113130391530197 28057077424526493551489)
                ·
                  rfl

theorem cell22_737653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 7].length) (baseStart_737653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737653 prefixEnd_737653 := by exact prefixLift 737653
  have htrace : WordTrace (prefixWord ++ tailWord_737653) baseStart_737653 baseEnd_737653 := by
    simpa [prefixWord, tailWord_737653, baseEnd_737653] using wordTrace_append hprefix tailTrace_737653
  have hstable : (prefixWord ++ tailWord_737653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737653).length < 2 ^ (prefixWord ++ tailWord_737653).sum := by decide
  have hdescent : baseEnd_737653 < baseStart_737653 := by decide
  rcases family_descends (prefixWord ++ tailWord_737653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737698 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_737698 : Nat := 118140960795 + 737698 * 2 ^ 59
def prefixEnd_737698 : Nat := 4983230072969 + 3 ^ 40 * 737698 * 2
def baseEnd_737698 : Nat := 84176367080124441529421

theorem tailTrace_737698 : CollatzResearch.WordTrace tailWord_737698 prefixEnd_737698 84176367080124441529421 := by
  unfold tailWord_737698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726514120363402408257437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17937370987635739755353165 6726514120363402408257437)
  ·
    refine ⟨2522442795136275903096539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6726514120363402408257437 2522442795136275903096539)
    ·
      refine ⟨3783664192704413854644809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522442795136275903096539 3783664192704413854644809)
      ·
        refine ⟨2837748144528310390983607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3783664192704413854644809 2837748144528310390983607)
        ·
          refine ⟨4256622216792465586475411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837748144528310390983607 4256622216792465586475411)
          ·
            refine ⟨6384933325188698379713117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256622216792465586475411 6384933325188698379713117)
            ·
              refine ⟨2394349996945761892392419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6384933325188698379713117 2394349996945761892392419)
              ·
                refine ⟨3591524995418642838588629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394349996945761892392419 3591524995418642838588629)
                ·
                  refine ⟨84176367080124441529421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3591524995418642838588629 84176367080124441529421)
                  ·
                    rfl

theorem cell22_737698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_737698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737698 prefixEnd_737698 := by exact prefixLift 737698
  have htrace : WordTrace (prefixWord ++ tailWord_737698) baseStart_737698 baseEnd_737698 := by
    simpa [prefixWord, tailWord_737698, baseEnd_737698] using wordTrace_append hprefix tailTrace_737698
  have hstable : (prefixWord ++ tailWord_737698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737698).length < 2 ^ (prefixWord ++ tailWord_737698).sum := by decide
  have hdescent : baseEnd_737698 < baseStart_737698 := by decide
  rcases family_descends (prefixWord ++ tailWord_737698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737713 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_737713 : Nat := 118140960795 + 737713 * 2 ^ 59
def prefixEnd_737713 : Nat := 4983230072969 + 3 ^ 40 * 737713 * 2
def baseEnd_737713 : Nat := 252534236046918285463217

theorem tailTrace_737713 : CollatzResearch.WordTrace tailWord_737713 prefixEnd_737713 252534236046918285463217 := by
  unfold tailWord_737713
  simp only [CollatzResearch.WordTrace]
  refine ⟨26906603576399267194825793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17937735717599511463217195 26906603576399267194825793)
  ·
    refine ⟨20179952682299450396119345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26906603576399267194825793 20179952682299450396119345)
    ·
      refine ⟨15134964511724587797089509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20179952682299450396119345 15134964511724587797089509)
      ·
        refine ⟨2837805845948360211954283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15134964511724587797089509 2837805845948360211954283)
        ·
          refine ⟨4256708768922540317931425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837805845948360211954283 4256708768922540317931425)
          ·
            refine ⟨3192531576691905238448569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4256708768922540317931425 3192531576691905238448569)
            ·
              refine ⟨2394398682518928928836427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192531576691905238448569 2394398682518928928836427)
              ·
                refine ⟨3591598023778393393254641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394398682518928928836427 3591598023778393393254641)
                ·
                  refine ⟨2693698517833795044940981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3591598023778393393254641 2693698517833795044940981)
                  ·
                    refine ⟨252534236046918285463217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2693698517833795044940981 252534236046918285463217)
                    ·
                      rfl

theorem cell22_737713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_737713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737713 prefixEnd_737713 := by exact prefixLift 737713
  have htrace : WordTrace (prefixWord ++ tailWord_737713) baseStart_737713 baseEnd_737713 := by
    simpa [prefixWord, tailWord_737713, baseEnd_737713] using wordTrace_append hprefix tailTrace_737713
  have hstable : (prefixWord ++ tailWord_737713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737713).length < 2 ^ (prefixWord ++ tailWord_737713).sum := by decide
  have hdescent : baseEnd_737713 < baseStart_737713 := by decide
  rcases family_descends (prefixWord ++ tailWord_737713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737818 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_737818 : Nat := 118140960795 + 737818 * 2 ^ 59
def prefixEnd_737818 : Nat := 4983230072969 + 3 ^ 40 * 737818 * 2
def baseEnd_737818 : Nat := 252570179692733011587895

theorem tailTrace_737818 : CollatzResearch.WordTrace tailWord_737818 prefixEnd_737818 252570179692733011587895 := by
  unfold tailWord_737818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727608310254717531849527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17940288827345913418265405 6727608310254717531849527)
  ·
    refine ⟨10091412465382076297774291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727608310254717531849527 10091412465382076297774291)
    ·
      refine ⟨15137118698073114446661437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10091412465382076297774291 15137118698073114446661437)
      ·
        refine ⟨5676419511777417917498039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15137118698073114446661437 5676419511777417917498039)
        ·
          refine ⟨8514629267666126876247059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676419511777417917498039 8514629267666126876247059)
          ·
            refine ⟨12771943901499190314370589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8514629267666126876247059 12771943901499190314370589)
            ·
              refine ⟨4789478963062196367888971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12771943901499190314370589 4789478963062196367888971)
              ·
                refine ⟨7184218444593294551833457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4789478963062196367888971 7184218444593294551833457)
                ·
                  refine ⟨5388163833444970913875093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7184218444593294551833457 5388163833444970913875093)
                  ·
                    refine ⟨252570179692733011587895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5388163833444970913875093 252570179692733011587895)
                    ·
                      rfl

theorem cell22_737818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_737818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737818 prefixEnd_737818 := by exact prefixLift 737818
  have htrace : WordTrace (prefixWord ++ tailWord_737818) baseStart_737818 baseEnd_737818 := by
    simpa [prefixWord, tailWord_737818, baseEnd_737818] using wordTrace_append hprefix tailTrace_737818
  have hstable : (prefixWord ++ tailWord_737818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737818).length < 2 ^ (prefixWord ++ tailWord_737818).sum := by decide
  have hdescent : baseEnd_737818 < baseStart_737818 := by decide
  rcases family_descends (prefixWord ++ tailWord_737818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737848 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_737848 : Nat := 118140960795 + 737848 * 2 ^ 59
def prefixEnd_737848 : Nat := 4983230072969 + 3 ^ 40 * 737848 * 2
def baseEnd_737848 : Nat := 252580449305822933337803

theorem tailTrace_737848 : CollatzResearch.WordTrace tailWord_737848 prefixEnd_737848 252580449305822933337803 := by
  unfold tailWord_737848
  simp only [CollatzResearch.WordTrace]
  refine ⟨13455763715455092625495099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17941018287273456833993465 13455763715455092625495099)
  ·
    refine ⟨20183645573182638938242649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13455763715455092625495099 20183645573182638938242649)
    ·
      refine ⟨15137734179886979203681987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20183645573182638938242649 15137734179886979203681987)
      ·
        refine ⟨22706601269830468805522981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15137734179886979203681987 22706601269830468805522981)
        ·
          refine ⟨4257487738093212901035559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22706601269830468805522981 4257487738093212901035559)
          ·
            refine ⟨6386231607139819351553339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4257487738093212901035559 6386231607139819351553339)
            ·
              refine ⟨9579347410709729027330009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6386231607139819351553339 9579347410709729027330009)
              ·
                refine ⟨7184510558032296770497507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9579347410709729027330009 7184510558032296770497507)
                ·
                  refine ⟨10776765837048445155746261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7184510558032296770497507 10776765837048445155746261)
                  ·
                    refine ⟨252580449305822933337803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10776765837048445155746261 252580449305822933337803)
                    ·
                      rfl

theorem cell22_737848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_737848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737848 prefixEnd_737848 := by exact prefixLift 737848
  have htrace : WordTrace (prefixWord ++ tailWord_737848) baseStart_737848 baseEnd_737848 := by
    simpa [prefixWord, tailWord_737848, baseEnd_737848] using wordTrace_append hprefix tailTrace_737848
  have hstable : (prefixWord ++ tailWord_737848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737848).length < 2 ^ (prefixWord ++ tailWord_737848).sum := by decide
  have hdescent : baseEnd_737848 < baseStart_737848 := by decide
  rcases family_descends (prefixWord ++ tailWord_737848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737860 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_737860 : Nat := 118140960795 + 737860 * 2 ^ 59
def prefixEnd_737860 : Nat := 4983230072969 + 3 ^ 40 * 737860 * 2
def baseEnd_737860 : Nat := 252584557151058902037767

theorem tailTrace_737860 : CollatzResearch.WordTrace tailWord_737860 prefixEnd_737860 252584557151058902037767 := by
  unfold tailWord_737860
  simp only [CollatzResearch.WordTrace]
  refine ⟨13455982553433355650213517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17941310071244474200284689 13455982553433355650213517)
  ·
    refine ⟨5045993457537508368830069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13455982553433355650213517 5045993457537508368830069)
    ·
      refine ⟨473061886644141409577819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5045993457537508368830069 473061886644141409577819)
      ·
        refine ⟨709592829966212114366729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473061886644141409577819 709592829966212114366729)
        ·
          refine ⟨532194622474659085775047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709592829966212114366729 532194622474659085775047)
          ·
            refine ⟨798291933711988628662571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532194622474659085775047 798291933711988628662571)
            ·
              refine ⟨1197437900567982942993857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798291933711988628662571 1197437900567982942993857)
              ·
                refine ⟨898078425425987207245393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197437900567982942993857 898078425425987207245393)
                ·
                  refine ⟨673558819069490405434045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 898078425425987207245393 673558819069490405434045)
                  ·
                    refine ⟨252584557151058902037767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673558819069490405434045 252584557151058902037767)
                    ·
                      rfl

theorem cell22_737860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_737860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737860 prefixEnd_737860 := by exact prefixLift 737860
  have htrace : WordTrace (prefixWord ++ tailWord_737860) baseStart_737860 baseEnd_737860 := by
    simpa [prefixWord, tailWord_737860, baseEnd_737860] using wordTrace_append hprefix tailTrace_737860
  have hstable : (prefixWord ++ tailWord_737860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737860).length < 2 ^ (prefixWord ++ tailWord_737860).sum := by decide
  have hdescent : baseEnd_737860 < baseStart_737860 := by decide
  rcases family_descends (prefixWord ++ tailWord_737860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737884 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 5]
def baseStart_737884 : Nat := 118140960795 + 737884 * 2 ^ 59
def prefixEnd_737884 : Nat := 4983230072969 + 3 ^ 40 * 737884 * 2
def baseEnd_737884 : Nat := 84197590947176946479231

theorem tailTrace_737884 : CollatzResearch.WordTrace tailWord_737884 prefixEnd_737884 84197590947176946479231 := by
  unfold tailWord_737884
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456420229389881699650353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17941893639186508932867137 13456420229389881699650353)
  ·
    refine ⟨10092315172042411274737765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13456420229389881699650353 10092315172042411274737765)
    ·
      refine ⟨1892309094757952114013331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10092315172042411274737765 1892309094757952114013331)
      ·
        refine ⟨2838463642136928171019997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892309094757952114013331 2838463642136928171019997)
        ·
          refine ⟨1064423865801348064132499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2838463642136928171019997 1064423865801348064132499)
          ·
            refine ⟨1596635798702022096198749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064423865801348064132499 1596635798702022096198749)
            ·
              refine ⟨598738424513258286074531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1596635798702022096198749 598738424513258286074531)
              ·
                refine ⟨898107636769887429111797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598738424513258286074531 898107636769887429111797)
                ·
                  refine ⟨84197590947176946479231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 898107636769887429111797 84197590947176946479231)
                  ·
                    rfl

theorem cell22_737884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_737884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737884 prefixEnd_737884 := by exact prefixLift 737884
  have htrace : WordTrace (prefixWord ++ tailWord_737884) baseStart_737884 baseEnd_737884 := by
    simpa [prefixWord, tailWord_737884, baseEnd_737884] using wordTrace_append hprefix tailTrace_737884
  have hstable : (prefixWord ++ tailWord_737884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737884).length < 2 ^ (prefixWord ++ tailWord_737884).sum := by decide
  have hdescent : baseEnd_737884 < baseStart_737884 := by decide
  rcases family_descends (prefixWord ++ tailWord_737884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737922 : List Nat := [3, 4, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_737922 : Nat := 118140960795 + 737922 * 2 ^ 59
def prefixEnd_737922 : Nat := 4983230072969 + 3 ^ 40 * 737922 * 2
def baseEnd_737922 : Nat := 252605781018111406987577

theorem tailTrace_737922 : CollatzResearch.WordTrace tailWord_737922 prefixEnd_737922 252605781018111406987577 := by
  unfold tailWord_737922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6728556608160523972296005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17942817621761397259456013 6728556608160523972296005)
  ·
    refine ⟨1261604364030098244805501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6728556608160523972296005 1261604364030098244805501)
    ·
      refine ⟨473101636511286841802063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1261604364030098244805501 473101636511286841802063)
      ·
        refine ⟨709652454766930262703095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473101636511286841802063 709652454766930262703095)
        ·
          refine ⟨1064478682150395394054643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709652454766930262703095 1064478682150395394054643)
          ·
            refine ⟨1596718023225593091081965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064478682150395394054643 1596718023225593091081965)
            ·
              refine ⟨598769258709597409155737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1596718023225593091081965 598769258709597409155737)
              ·
                refine ⟨449076944032198056866803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598769258709597409155737 449076944032198056866803)
                ·
                  refine ⟨673615416048297085300205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449076944032198056866803 673615416048297085300205)
                  ·
                    refine ⟨252605781018111406987577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673615416048297085300205 252605781018111406987577)
                    ·
                      rfl

theorem cell22_737922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_737922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737922 prefixEnd_737922 := by exact prefixLift 737922
  have htrace : WordTrace (prefixWord ++ tailWord_737922) baseStart_737922 baseEnd_737922 := by
    simpa [prefixWord, tailWord_737922, baseEnd_737922] using wordTrace_append hprefix tailTrace_737922
  have hstable : (prefixWord ++ tailWord_737922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737922).length < 2 ^ (prefixWord ++ tailWord_737922).sum := by decide
  have hdescent : baseEnd_737922 < baseStart_737922 := by decide
  rcases family_descends (prefixWord ++ tailWord_737922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737923 : List Nat := [1, 1, 1, 3, 3, 1, 12]
def baseStart_737923 : Nat := 118140960795 + 737923 * 2 ^ 59
def prefixEnd_737923 : Nat := 4983230072969 + 3 ^ 40 * 737923 * 2
def baseEnd_737923 : Nat := 9355782345872138433799

theorem tailTrace_737923 : CollatzResearch.WordTrace tailWord_737923 prefixEnd_737923 9355782345872138433799 := by
  unfold tailWord_737923
  simp only [CollatzResearch.WordTrace]
  refine ⟨26914262905638473059970423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17942841937092315373313615 26914262905638473059970423)
  ·
    refine ⟨40371394358457709589955635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26914262905638473059970423 40371394358457709589955635)
    ·
      refine ⟨60557091537686564384933453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40371394358457709589955635 60557091537686564384933453)
      ·
        refine ⟨22708909326632461644350045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60557091537686564384933453 22708909326632461644350045)
        ·
          refine ⟨8515840997487173116631267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22708909326632461644350045 8515840997487173116631267)
          ·
            refine ⟨12773761496230759674946901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8515840997487173116631267 12773761496230759674946901)
            ·
              refine ⟨9355782345872138433799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 12773761496230759674946901 9355782345872138433799)
              ·
                rfl

theorem cell22_737923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 12].length) (baseStart_737923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737923 prefixEnd_737923 := by exact prefixLift 737923
  have htrace : WordTrace (prefixWord ++ tailWord_737923) baseStart_737923 baseEnd_737923 := by
    simpa [prefixWord, tailWord_737923, baseEnd_737923] using wordTrace_append hprefix tailTrace_737923
  have hstable : (prefixWord ++ tailWord_737923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737923).length < 2 ^ (prefixWord ++ tailWord_737923).sum := by decide
  have hdescent : baseEnd_737923 < baseStart_737923 := by decide
  rcases family_descends (prefixWord ++ tailWord_737923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737925 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_737925 : Nat := 118140960795 + 737925 * 2 ^ 59
def prefixEnd_737925 : Nat := 4983230072969 + 3 ^ 40 * 737925 * 2
def baseEnd_737925 : Nat := 252606807979420399162567

theorem tailTrace_737925 : CollatzResearch.WordTrace tailWord_737925 prefixEnd_737925 252606807979420399162567 := by
  unfold tailWord_737925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26914335851631227401543229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17942890567754151601028819 26914335851631227401543229)
  ·
    refine ⟨10092875944361710275578711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26914335851631227401543229 10092875944361710275578711)
    ·
      refine ⟨15139313916542565413368067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10092875944361710275578711 15139313916542565413368067)
      ·
        refine ⟨22708970874813848120052101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15139313916542565413368067 22708970874813848120052101)
        ·
          refine ⟨4257932039027596522509769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22708970874813848120052101 4257932039027596522509769)
          ·
            refine ⟨3193449029270697391882327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4257932039027596522509769 3193449029270697391882327)
            ·
              refine ⟨4790173543906046087823491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193449029270697391882327 4790173543906046087823491)
              ·
                refine ⟨7185260315859069131735237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790173543906046087823491 7185260315859069131735237)
                ·
                  refine ⟨1347236309223575462200357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7185260315859069131735237 1347236309223575462200357)
                  ·
                    refine ⟨252606807979420399162567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347236309223575462200357 252606807979420399162567)
                    ·
                      rfl

theorem cell22_737925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_737925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737925 prefixEnd_737925 := by exact prefixLift 737925
  have htrace : WordTrace (prefixWord ++ tailWord_737925) baseStart_737925 baseEnd_737925 := by
    simpa [prefixWord, tailWord_737925, baseEnd_737925] using wordTrace_append hprefix tailTrace_737925
  have hstable : (prefixWord ++ tailWord_737925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737925).length < 2 ^ (prefixWord ++ tailWord_737925).sum := by decide
  have hdescent : baseEnd_737925 < baseStart_737925 := by decide
  rcases family_descends (prefixWord ++ tailWord_737925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737927 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 2, 3]
def baseStart_737927 : Nat := 118140960795 + 737927 * 2 ^ 59
def prefixEnd_737927 : Nat := 4983230072969 + 3 ^ 40 * 737927 * 2
def baseEnd_737927 : Nat := 252607492620293060612561

theorem tailTrace_737927 : CollatzResearch.WordTrace tailWord_737927 prefixEnd_737927 252607492620293060612561 := by
  unfold tailWord_737927
  simp only [CollatzResearch.WordTrace]
  refine ⟨26914408797623981743116035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17942939198415987828744023 26914408797623981743116035)
  ·
    refine ⟨40371613196435972614674053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26914408797623981743116035 40371613196435972614674053)
    ·
      refine ⟨7569677474331744865251385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40371613196435972614674053 7569677474331744865251385)
      ·
        refine ⟨5677258105748808648938539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7569677474331744865251385 5677258105748808648938539)
        ·
          refine ⟨8515887158623212973407809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5677258105748808648938539 8515887158623212973407809)
          ·
            refine ⟨6386915368967409730055857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8515887158623212973407809 6386915368967409730055857)
            ·
              refine ⟨4790186526725557297541893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6386915368967409730055857 4790186526725557297541893)
              ·
                refine ⟨898159973761041993289105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4790186526725557297541893 898159973761041993289105)
                ·
                  refine ⟨673619980320781494966829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 898159973761041993289105 673619980320781494966829)
                  ·
                    refine ⟨252607492620293060612561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673619980320781494966829 252607492620293060612561)
                    ·
                      rfl

theorem cell22_737927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_737927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737927 prefixEnd_737927 := by exact prefixLift 737927
  have htrace : WordTrace (prefixWord ++ tailWord_737927) baseStart_737927 baseEnd_737927 := by
    simpa [prefixWord, tailWord_737927, baseEnd_737927] using wordTrace_append hprefix tailTrace_737927
  have hstable : (prefixWord ++ tailWord_737927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737927).length < 2 ^ (prefixWord ++ tailWord_737927).sum := by decide
  have hdescent : baseEnd_737927 < baseStart_737927 := by decide
  rcases family_descends (prefixWord ++ tailWord_737927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737974 : List Nat := [5, 1, 3, 1, 3, 9]
def baseStart_737974 : Nat := 118140960795 + 737974 * 2 ^ 59
def prefixEnd_737974 : Nat := 4983230072969 + 3 ^ 40 * 737974 * 2
def baseEnd_737974 : Nat := 3118809650380254378857

theorem tailTrace_737974 : CollatzResearch.WordTrace tailWord_737974 prefixEnd_737974 3118809650380254378857 := by
  unfold tailWord_737974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682257689278356798129811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17944082018969139180051317 1682257689278356798129811)
  ·
    refine ⟨2523386533917535197194717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682257689278356798129811 2523386533917535197194717)
    ·
      refine ⟨946269950219075698948019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2523386533917535197194717 946269950219075698948019)
      ·
        refine ⟨1419404925328613548422029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946269950219075698948019 1419404925328613548422029)
        ·
          refine ⟨532276846998230080658261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1419404925328613548422029 532276846998230080658261)
          ·
            refine ⟨3118809650380254378857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 532276846998230080658261 3118809650380254378857)
            ·
              rfl

theorem cell22_737974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 9].length) (baseStart_737974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_737974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_737974 prefixEnd_737974 := by exact prefixLift 737974
  have htrace : WordTrace (prefixWord ++ tailWord_737974) baseStart_737974 baseEnd_737974 := by
    simpa [prefixWord, tailWord_737974, baseEnd_737974] using wordTrace_append hprefix tailTrace_737974
  have hstable : (prefixWord ++ tailWord_737974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737974).length < 2 ^ (prefixWord ++ tailWord_737974).sum := by decide
  have hdescent : baseEnd_737974 < baseStart_737974 := by decide
  rcases family_descends (prefixWord ++ tailWord_737974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738032 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_738032 : Nat := 118140960795 + 738032 * 2 ^ 59
def prefixEnd_738032 : Nat := 4983230072969 + 3 ^ 40 * 738032 * 2
def baseEnd_738032 : Nat := 252643436266107786737239

theorem tailTrace_738032 : CollatzResearch.WordTrace tailWord_738032 prefixEnd_738032 252643436266107786737239 := by
  unfold tailWord_738032
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459119231121792337844175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17945492308162389783792233 13459119231121792337844175)
  ·
    refine ⟨20188678846682688506766263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13459119231121792337844175 20188678846682688506766263)
    ·
      refine ⟨30283018270024032760149395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20188678846682688506766263 30283018270024032760149395)
      ·
        refine ⟨45424527405036049140224093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30283018270024032760149395 45424527405036049140224093)
        ·
          refine ⟨17034197776888518427584035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45424527405036049140224093 17034197776888518427584035)
          ·
            refine ⟨25551296665332777641376053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17034197776888518427584035 25551296665332777641376053)
            ·
              refine ⟨2395434062374947903879005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25551296665332777641376053 2395434062374947903879005)
              ·
                refine ⟨898287773390605463954627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2395434062374947903879005 898287773390605463954627)
                ·
                  refine ⟨1347431660085908195931941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898287773390605463954627 1347431660085908195931941)
                  ·
                    refine ⟨252643436266107786737239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347431660085908195931941 252643436266107786737239)
                    ·
                      rfl

theorem cell22_738032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_738032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738032 prefixEnd_738032 := by exact prefixLift 738032
  have htrace : WordTrace (prefixWord ++ tailWord_738032) baseStart_738032 baseEnd_738032 := by
    simpa [prefixWord, tailWord_738032, baseEnd_738032] using wordTrace_append hprefix tailTrace_738032
  have hstable : (prefixWord ++ tailWord_738032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738032).length < 2 ^ (prefixWord ++ tailWord_738032).sum := by decide
  have hdescent : baseEnd_738032 < baseStart_738032 := by decide
  rcases family_descends (prefixWord ++ tailWord_738032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738036 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 7]
def baseStart_738036 : Nat := 118140960795 + 738036 * 2 ^ 59
def prefixEnd_738036 : Nat := 4983230072969 + 3 ^ 40 * 738036 * 2
def baseEnd_738036 : Nat := 84214935182617703212409

theorem tailTrace_738036 : CollatzResearch.WordTrace tailWord_738036 prefixEnd_738036 84214935182617703212409 := by
  unfold tailWord_738036
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459192177114546679416981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17945589569486062239222641 13459192177114546679416981)
  ·
    refine ⟨630899633302244375597671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13459192177114546679416981 630899633302244375597671)
    ·
      refine ⟨946349449953366563396507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630899633302244375597671 946349449953366563396507)
      ·
        refine ⟨1419524174930049845094761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946349449953366563396507 1419524174930049845094761)
        ·
          refine ⟨1064643131197537383821071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419524174930049845094761 1064643131197537383821071)
          ·
            refine ⟨1596964696796306075731607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064643131197537383821071 1596964696796306075731607)
            ·
              refine ⟨2395447045194459113597411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596964696796306075731607 2395447045194459113597411)
              ·
                refine ⟨3593170567791688670396117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395447045194459113597411 3593170567791688670396117)
                ·
                  refine ⟨84214935182617703212409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3593170567791688670396117 84214935182617703212409)
                  ·
                    rfl

theorem cell22_738036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_738036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738036 prefixEnd_738036 := by exact prefixLift 738036
  have htrace : WordTrace (prefixWord ++ tailWord_738036) baseStart_738036 baseEnd_738036 := by
    simpa [prefixWord, tailWord_738036, baseEnd_738036] using wordTrace_append hprefix tailTrace_738036
  have hstable : (prefixWord ++ tailWord_738036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738036).length < 2 ^ (prefixWord ++ tailWord_738036).sum := by decide
  have hdescent : baseEnd_738036 < baseStart_738036 := by decide
  rcases family_descends (prefixWord ++ tailWord_738036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738094 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_738094 : Nat := 118140960795 + 738094 * 2 ^ 59
def prefixEnd_738094 : Nat := 4983230072969 + 3 ^ 40 * 738094 * 2
def baseEnd_738094 : Nat := 252664660133160291687049

theorem tailTrace_738094 : CollatzResearch.WordTrace tailWord_738094 prefixEnd_738094 252664660133160291687049 := by
  unfold tailWord_738094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365062473502371158055667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17946999858679312842963557 3365062473502371158055667)
  ·
    refine ⟨5047593710253556737083501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3365062473502371158055667 5047593710253556737083501)
    ·
      refine ⟨1892847641345083776406313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5047593710253556737083501 1892847641345083776406313)
      ·
        refine ⟨1419635731008812832304735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1892847641345083776406313 1419635731008812832304735)
        ·
          refine ⟨2129453596513219248457103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419635731008812832304735 2129453596513219248457103)
          ·
            refine ⟨3194180394769828872685655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129453596513219248457103 3194180394769828872685655)
            ·
              refine ⟨4791270592154743309028483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194180394769828872685655 4791270592154743309028483)
              ·
                refine ⟨7186905888232114963542725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791270592154743309028483 7186905888232114963542725)
                ·
                  refine ⟨1347544854043521555664261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7186905888232114963542725 1347544854043521555664261)
                  ·
                    refine ⟨252664660133160291687049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347544854043521555664261 252664660133160291687049)
                    ·
                      rfl

theorem cell22_738094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_738094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738094 prefixEnd_738094 := by exact prefixLift 738094
  have htrace : WordTrace (prefixWord ++ tailWord_738094) baseStart_738094 baseEnd_738094 := by
    simpa [prefixWord, tailWord_738094, baseEnd_738094] using wordTrace_append hprefix tailTrace_738094
  have hstable : (prefixWord ++ tailWord_738094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738094).length < 2 ^ (prefixWord ++ tailWord_738094).sum := by decide
  have hdescent : baseEnd_738094 < baseStart_738094 := by decide
  rcases family_descends (prefixWord ++ tailWord_738094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738109 : List Nat := [1, 4, 1, 4, 2, 1, 2, 7]
def baseStart_738109 : Nat := 118140960795 + 738109 * 2 ^ 59
def prefixEnd_738109 : Nat := 4983230072969 + 3 ^ 40 * 738109 * 2
def baseEnd_738109 : Nat := 28074421659967250284667

theorem tailTrace_738109 : CollatzResearch.WordTrace tailWord_738109 prefixEnd_738109 28074421659967250284667 := by
  unfold tailWord_738109
  simp only [CollatzResearch.WordTrace]
  refine ⟨26921046882964626826241381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17947364588643084550827587 26921046882964626826241381)
  ·
    refine ⟨5047696290555867529920259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26921046882964626826241381 5047696290555867529920259)
    ·
      refine ⟨7571544435833801294880389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5047696290555867529920259 7571544435833801294880389)
      ·
        refine ⟨1419664581718837742790073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7571544435833801294880389 1419664581718837742790073)
        ·
          refine ⟨1064748436289128307092555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419664581718837742790073 1064748436289128307092555)
          ·
            refine ⟨1597122654433692460638833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064748436289128307092555 1597122654433692460638833)
            ·
              refine ⟨1197841990825269345479125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597122654433692460638833 1197841990825269345479125)
              ·
                refine ⟨28074421659967250284667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1197841990825269345479125 28074421659967250284667)
                ·
                  rfl

theorem cell22_738109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 7].length) (baseStart_738109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738109 prefixEnd_738109 := by exact prefixLift 738109
  have htrace : WordTrace (prefixWord ++ tailWord_738109) baseStart_738109 baseEnd_738109 := by
    simpa [prefixWord, tailWord_738109, baseEnd_738109] using wordTrace_append hprefix tailTrace_738109
  have hstable : (prefixWord ++ tailWord_738109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738109).length < 2 ^ (prefixWord ++ tailWord_738109).sum := by decide
  have hdescent : baseEnd_738109 < baseStart_738109 := by decide
  rcases family_descends (prefixWord ++ tailWord_738109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738113 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 2, 3]
def baseStart_738113 : Nat := 118140960795 + 738113 * 2 ^ 59
def prefixEnd_738113 : Nat := 4983230072969 + 3 ^ 40 * 738113 * 2
def baseEnd_738113 : Nat := 252671164221450575461991

theorem tailTrace_738113 : CollatzResearch.WordTrace tailWord_738113 prefixEnd_738113 252671164221450575461991 := by
  unfold tailWord_738113
  simp only [CollatzResearch.WordTrace]
  refine ⟨26921192774950135509386993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17947461849966757006257995 26921192774950135509386993)
  ·
    refine ⟨20190894581212601632040245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26921192774950135509386993 20190894581212601632040245)
    ·
      refine ⟨1892896366988681403003773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20190894581212601632040245 1892896366988681403003773)
      ·
        refine ⟨709836137620755526126415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1892896366988681403003773 709836137620755526126415)
        ·
          refine ⟨1064754206431133289189623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709836137620755526126415 1064754206431133289189623)
          ·
            refine ⟨1597131309646699933784435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064754206431133289189623 1597131309646699933784435)
            ·
              refine ⟨2395696964470049900676653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597131309646699933784435 2395696964470049900676653)
              ·
                refine ⟨898386361676268712753745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2395696964470049900676653 898386361676268712753745)
                ·
                  refine ⟨673789771257201534565309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 898386361676268712753745 673789771257201534565309)
                  ·
                    refine ⟨252671164221450575461991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673789771257201534565309 252671164221450575461991)
                    ·
                      rfl

theorem cell22_738113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_738113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738113 prefixEnd_738113 := by exact prefixLift 738113
  have htrace : WordTrace (prefixWord ++ tailWord_738113) baseStart_738113 baseEnd_738113 := by
    simpa [prefixWord, tailWord_738113, baseEnd_738113] using wordTrace_append hprefix tailTrace_738113
  have hstable : (prefixWord ++ tailWord_738113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738113).length < 2 ^ (prefixWord ++ tailWord_738113).sum := by decide
  have hdescent : baseEnd_738113 < baseStart_738113 := by decide
  rcases family_descends (prefixWord ++ tailWord_738113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738184 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_738184 : Nat := 118140960795 + 738184 * 2 ^ 59
def prefixEnd_738184 : Nat := 4983230072969 + 3 ^ 40 * 738184 * 2
def baseEnd_738184 : Nat := 252695468972430056936773

theorem tailTrace_738184 : CollatzResearch.WordTrace tailWord_738184 prefixEnd_738184 252695468972430056936773 := by
  unfold tailWord_738184
  simp only [CollatzResearch.WordTrace]
  refine ⟨13461891178846457317610803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17949188238461943090147737 13461891178846457317610803)
  ·
    refine ⟨20192836768269685976416205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13461891178846457317610803 20192836768269685976416205)
    ·
      refine ⟨7572313788101132241156077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20192836768269685976416205 7572313788101132241156077)
      ·
        refine ⟨2839617670537924590433529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7572313788101132241156077 2839617670537924590433529)
        ·
          refine ⟨2129713252903443442825147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2839617670537924590433529 2129713252903443442825147)
          ·
            refine ⟨3194569879355165164237721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129713252903443442825147 3194569879355165164237721)
            ·
              refine ⟨2395927409516373873178291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3194569879355165164237721 2395927409516373873178291)
              ·
                refine ⟨3593891114274560809767437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2395927409516373873178291 3593891114274560809767437)
                ·
                  refine ⟨1347709167852960303662789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3593891114274560809767437 1347709167852960303662789)
                  ·
                    refine ⟨252695468972430056936773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347709167852960303662789 252695468972430056936773)
                    ·
                      rfl

theorem cell22_738184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_738184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738184 prefixEnd_738184 := by exact prefixLift 738184
  have htrace : WordTrace (prefixWord ++ tailWord_738184) baseStart_738184 baseEnd_738184 := by
    simpa [prefixWord, tailWord_738184, baseEnd_738184] using wordTrace_append hprefix tailTrace_738184
  have hstable : (prefixWord ++ tailWord_738184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738184).length < 2 ^ (prefixWord ++ tailWord_738184).sum := by decide
  have hdescent : baseEnd_738184 < baseStart_738184 := by decide
  rcases family_descends (prefixWord ++ tailWord_738184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738261 : List Nat := [1, 3, 2, 3, 4, 1, 8]
def baseStart_738261 : Nat := 118140960795 + 738261 * 2 ^ 59
def prefixEnd_738261 : Nat := 4983230072969 + 3 ^ 40 * 738261 * 2
def baseEnd_738261 : Nat := 9360067690593611954131

theorem tailTrace_738261 : CollatzResearch.WordTrace tailWord_738261 prefixEnd_738261 9360067690593611954131 := by
  unfold tailWord_738261
  simp only [CollatzResearch.WordTrace]
  refine ⟨26926590778413956785774637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17951060518942637857183091 26926590778413956785774637)
  ·
    refine ⟨10097471541905233794665489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26926590778413956785774637 10097471541905233794665489)
    ·
      refine ⟨7573103656428925345999117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10097471541905233794665489 7573103656428925345999117)
      ·
        refine ⟨2839913871160847004749669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7573103656428925345999117 2839913871160847004749669)
        ·
          refine ⟨532483850842658813390563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2839913871160847004749669 532483850842658813390563)
          ·
            refine ⟨798725776263988220085845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532483850842658813390563 798725776263988220085845)
            ·
              refine ⟨9360067690593611954131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 798725776263988220085845 9360067690593611954131)
              ·
                rfl

theorem cell22_738261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 8].length) (baseStart_738261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738261 prefixEnd_738261 := by exact prefixLift 738261
  have htrace : WordTrace (prefixWord ++ tailWord_738261) baseStart_738261 baseEnd_738261 := by
    simpa [prefixWord, tailWord_738261, baseEnd_738261] using wordTrace_append hprefix tailTrace_738261
  have hstable : (prefixWord ++ tailWord_738261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738261).length < 2 ^ (prefixWord ++ tailWord_738261).sum := by decide
  have hdescent : baseEnd_738261 < baseStart_738261 := by decide
  rcases family_descends (prefixWord ++ tailWord_738261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738327 : List Nat := [1, 1, 3, 5, 1, 3, 2, 2, 1, 3]
def baseStart_738327 : Nat := 118140960795 + 738327 * 2 ^ 59
def prefixEnd_738327 : Nat := 4983230072969 + 3 ^ 40 * 738327 * 2
def baseEnd_738327 : Nat := 252744420794825350611335

theorem tailTrace_738327 : CollatzResearch.WordTrace tailWord_738327 prefixEnd_738327 252744420794825350611335 := by
  unfold tailWord_738327
  simp only [CollatzResearch.WordTrace]
  refine ⟨26928997996174850057677235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17952665330783233371784823 26928997996174850057677235)
  ·
    refine ⟨40393496994262275086515853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26928997996174850057677235 40393496994262275086515853)
    ·
      refine ⟨15147561372848353157443445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40393496994262275086515853 15147561372848353157443445)
      ·
        refine ⟨1420083878704533108510323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15147561372848353157443445 1420083878704533108510323)
        ·
          refine ⟨2130125818056799662765485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420083878704533108510323 2130125818056799662765485)
          ·
            refine ⟨798797181771299873537057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2130125818056799662765485 798797181771299873537057)
            ·
              refine ⟨599097886328474905152793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798797181771299873537057 599097886328474905152793)
              ·
                refine ⟨449323414746356178864595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599097886328474905152793 449323414746356178864595)
                ·
                  refine ⟨673985122119534268296893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449323414746356178864595 673985122119534268296893)
                  ·
                    refine ⟨252744420794825350611335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673985122119534268296893 252744420794825350611335)
                    ·
                      rfl

theorem cell22_738327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_738327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738327 prefixEnd_738327 := by exact prefixLift 738327
  have htrace : WordTrace (prefixWord ++ tailWord_738327) baseStart_738327 baseEnd_738327 := by
    simpa [prefixWord, tailWord_738327, baseEnd_738327] using wordTrace_append hprefix tailTrace_738327
  have hstable : (prefixWord ++ tailWord_738327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738327).length < 2 ^ (prefixWord ++ tailWord_738327).sum := by decide
  have hdescent : baseEnd_738327 < baseStart_738327 := by decide
  rcases family_descends (prefixWord ++ tailWord_738327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738413 : List Nat := [1, 5, 1, 1, 2, 4, 2, 6]
def baseStart_738413 : Nat := 118140960795 + 738413 * 2 ^ 59
def prefixEnd_738413 : Nat := 4983230072969 + 3 ^ 40 * 738413 * 2
def baseEnd_738413 : Nat := 28085984483594421440119

theorem tailTrace_738413 : CollatzResearch.WordTrace tailWord_738413 prefixEnd_738413 28085984483594421440119 := by
  unfold tailWord_738413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26932134673863286745307893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17954756449242191163538595 26932134673863286745307893)
  ·
    refine ⟨2524887625674683132372615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26932134673863286745307893 2524887625674683132372615)
    ·
      refine ⟨3787331438512024698558923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524887625674683132372615 3787331438512024698558923)
      ·
        refine ⟨5680997157768037047838385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787331438512024698558923 5680997157768037047838385)
        ·
          refine ⟨4260747868326027785878789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5680997157768037047838385 4260747868326027785878789)
          ·
            refine ⟨798890225311130209852273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4260747868326027785878789 798890225311130209852273)
            ·
              refine ⟨599167668983347657389205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798890225311130209852273 599167668983347657389205)
              ·
                refine ⟨28085984483594421440119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 599167668983347657389205 28085984483594421440119)
                ·
                  rfl

theorem cell22_738413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 6].length) (baseStart_738413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738413 prefixEnd_738413 := by exact prefixLift 738413
  have htrace : WordTrace (prefixWord ++ tailWord_738413) baseStart_738413 baseEnd_738413 := by
    simpa [prefixWord, tailWord_738413, baseEnd_738413] using wordTrace_append hprefix tailTrace_738413
  have hstable : (prefixWord ++ tailWord_738413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738413).length < 2 ^ (prefixWord ++ tailWord_738413).sum := by decide
  have hdescent : baseEnd_738413 < baseStart_738413 := by decide
  rcases family_descends (prefixWord ++ tailWord_738413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738424 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 7]
def baseStart_738424 : Nat := 118140960795 + 738424 * 2 ^ 59
def prefixEnd_738424 : Nat := 4983230072969 + 3 ^ 40 * 738424 * 2
def baseEnd_738424 : Nat := 84259208625716476978679

theorem tailTrace_738424 : CollatzResearch.WordTrace tailWord_738424 prefixEnd_738424 84259208625716476978679 := by
  unfold tailWord_738424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466267938411717811979163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17955023917882290415972217 13466267938411717811979163)
  ·
    refine ⟨20199401907617576717968745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13466267938411717811979163 20199401907617576717968745)
    ·
      refine ⟨15149551430713182538476559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20199401907617576717968745 15149551430713182538476559)
      ·
        refine ⟨22724327146069773807714839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15149551430713182538476559 22724327146069773807714839)
        ·
          refine ⟨34086490719104660711572259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22724327146069773807714839 34086490719104660711572259)
          ·
            refine ⟨51129736078656991067358389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34086490719104660711572259 51129736078656991067358389)
            ·
              refine ⟨4793412757374092912564849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51129736078656991067358389 4793412757374092912564849)
              ·
                refine ⟨3595059568030569684423637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4793412757374092912564849 3595059568030569684423637)
                ·
                  refine ⟨84259208625716476978679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3595059568030569684423637 84259208625716476978679)
                  ·
                    rfl

theorem cell22_738424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_738424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738424 prefixEnd_738424 := by exact prefixLift 738424
  have htrace : WordTrace (prefixWord ++ tailWord_738424) baseStart_738424 baseEnd_738424 := by
    simpa [prefixWord, tailWord_738424, baseEnd_738424] using wordTrace_append hprefix tailTrace_738424
  have hstable : (prefixWord ++ tailWord_738424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738424).length < 2 ^ (prefixWord ++ tailWord_738424).sum := by decide
  have hdescent : baseEnd_738424 < baseStart_738424 := by decide
  rcases family_descends (prefixWord ++ tailWord_738424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738458 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_738458 : Nat := 118140960795 + 738458 * 2 ^ 59
def prefixEnd_738458 : Nat := 4983230072969 + 3 ^ 40 * 738458 * 2
def baseEnd_738458 : Nat := 84263088257328225195311

theorem tailTrace_738458 : CollatzResearch.WordTrace tailWord_738458 prefixEnd_738458 84263088257328225195311 := by
  unfold tailWord_738458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733443989675064857674007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17955850639133506287130685 6733443989675064857674007)
  ·
    refine ⟨10100165984512597286511011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6733443989675064857674007 10100165984512597286511011)
    ·
      refine ⟨15150248976768895929766517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10100165984512597286511011 15150248976768895929766517)
      ·
        refine ⟨1420335841572083993415611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15150248976768895929766517 1420335841572083993415611)
        ·
          refine ⟨2130503762358125990123417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420335841572083993415611 2130503762358125990123417)
          ·
            refine ⟨1597877821768594492592563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2130503762358125990123417 1597877821768594492592563)
            ·
              refine ⟨2396816732652891738888845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597877821768594492592563 2396816732652891738888845)
              ·
                refine ⟨898806274744834402083317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2396816732652891738888845 898806274744834402083317)
                ·
                  refine ⟨84263088257328225195311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 898806274744834402083317 84263088257328225195311)
                  ·
                    rfl

theorem cell22_738458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_738458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738458 prefixEnd_738458 := by exact prefixLift 738458
  have htrace : WordTrace (prefixWord ++ tailWord_738458) baseStart_738458 baseEnd_738458 := by
    simpa [prefixWord, tailWord_738458, baseEnd_738458] using wordTrace_append hprefix tailTrace_738458
  have hstable : (prefixWord ++ tailWord_738458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738458).length < 2 ^ (prefixWord ++ tailWord_738458).sum := by decide
  have hdescent : baseEnd_738458 < baseStart_738458 := by decide
  rcases family_descends (prefixWord ++ tailWord_738458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738533 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_738533 : Nat := 118140960795 + 738533 * 2 ^ 59
def prefixEnd_738533 : Nat := 4983230072969 + 3 ^ 40 * 738533 * 2
def baseEnd_738533 : Nat := 252814938804709479960703

theorem tailTrace_738533 : CollatzResearch.WordTrace tailWord_738533 prefixEnd_738533 252814938804709479960703 := by
  unfold tailWord_738533
  simp only [CollatzResearch.WordTrace]
  refine ⟨26936511433428547239676253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17957674288952364826450835 26936511433428547239676253)
  ·
    refine ⟨10101191787535705214878595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26936511433428547239676253 10101191787535705214878595)
    ·
      refine ⟨15151787681303557822317893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10101191787535705214878595 15151787681303557822317893)
      ·
        refine ⟨2840960190244417091684605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15151787681303557822317893 2840960190244417091684605)
        ·
          refine ⟨1065360071341656409381727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2840960190244417091684605 1065360071341656409381727)
          ·
            refine ⟨1598040107012484614072591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065360071341656409381727 1598040107012484614072591)
            ·
              refine ⟨2397060160518726921108887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598040107012484614072591 2397060160518726921108887)
              ·
                refine ⟨3595590240778090381663331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397060160518726921108887 3595590240778090381663331)
                ·
                  refine ⟨5393385361167135572494997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595590240778090381663331 5393385361167135572494997)
                  ·
                    refine ⟨252814938804709479960703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5393385361167135572494997 252814938804709479960703)
                    ·
                      rfl

theorem cell22_738533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_738533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738533 prefixEnd_738533 := by exact prefixLift 738533
  have htrace : WordTrace (prefixWord ++ tailWord_738533) baseStart_738533 baseEnd_738533 := by
    simpa [prefixWord, tailWord_738533, baseEnd_738533] using wordTrace_append hprefix tailTrace_738533
  have hstable : (prefixWord ++ tailWord_738533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738533).length < 2 ^ (prefixWord ++ tailWord_738533).sum := by decide
  have hdescent : baseEnd_738533 < baseStart_738533 := by decide
  rcases family_descends (prefixWord ++ tailWord_738533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738563 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 3, 3]
def baseStart_738563 : Nat := 118140960795 + 738563 * 2 ^ 59
def prefixEnd_738563 : Nat := 4983230072969 + 3 ^ 40 * 738563 * 2
def baseEnd_738563 : Nat := 252825208417799401710611

theorem tailTrace_738563 : CollatzResearch.WordTrace tailWord_738563 prefixEnd_738563 252825208417799401710611 := by
  unfold tailWord_738563
  simp only [CollatzResearch.WordTrace]
  refine ⟨26937605623319862363268343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17958403748879908242178895 26937605623319862363268343)
  ·
    refine ⟨40406408434979793544902515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26937605623319862363268343 40406408434979793544902515)
    ·
      refine ⟨60609612652469690317353773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40406408434979793544902515 60609612652469690317353773)
      ·
        refine ⟨22728604744676133869007665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60609612652469690317353773 22728604744676133869007665)
        ·
          refine ⟨17046453558507100401755749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22728604744676133869007665 17046453558507100401755749)
          ·
            refine ⟨3196210042220081325329203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17046453558507100401755749 3196210042220081325329203)
            ·
              refine ⟨4794315063330121987993805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196210042220081325329203 4794315063330121987993805)
              ·
                refine ⟨1797868148748795745497677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4794315063330121987993805 1797868148748795745497677)
                ·
                  refine ⟨674200555780798404561629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1797868148748795745497677 674200555780798404561629)
                  ·
                    refine ⟨252825208417799401710611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674200555780798404561629 252825208417799401710611)
                    ·
                      rfl

theorem cell22_738563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 3].length) (baseStart_738563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738563 prefixEnd_738563 := by exact prefixLift 738563
  have htrace : WordTrace (prefixWord ++ tailWord_738563) baseStart_738563 baseEnd_738563 := by
    simpa [prefixWord, tailWord_738563, baseEnd_738563] using wordTrace_append hprefix tailTrace_738563
  have hstable : (prefixWord ++ tailWord_738563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738563).length < 2 ^ (prefixWord ++ tailWord_738563).sum := by decide
  have hdescent : baseEnd_738563 < baseStart_738563 := by decide
  rcases family_descends (prefixWord ++ tailWord_738563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738597 : List Nat := [1, 3, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_738597 : Nat := 118140960795 + 738597 * 2 ^ 59
def prefixEnd_738597 : Nat := 4983230072969 + 3 ^ 40 * 738597 * 2
def baseEnd_738597 : Nat := 252836847312634646360507

theorem tailTrace_738597 : CollatzResearch.WordTrace tailWord_738597 prefixEnd_738597 252836847312634646360507 := by
  unfold tailWord_738597
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938845705196686170006045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17959230470131124113337363 26938845705196686170006045)
  ·
    refine ⟨10102067139448757313752267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26938845705196686170006045 10102067139448757313752267)
    ·
      refine ⟨15153100709173135970628401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10102067139448757313752267 15153100709173135970628401)
      ·
        refine ⟨11364825531879851977971301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15153100709173135970628401 11364825531879851977971301)
        ·
          refine ⟨2130904787227472245869619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11364825531879851977971301 2130904787227472245869619)
          ·
            refine ⟨3196357180841208368804429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130904787227472245869619 3196357180841208368804429)
            ·
              refine ⟨1198633942815453138301661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3196357180841208368804429 1198633942815453138301661)
              ·
                refine ⟨449487728555794926863123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198633942815453138301661 449487728555794926863123)
                ·
                  refine ⟨674231592833692390294685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449487728555794926863123 674231592833692390294685)
                  ·
                    refine ⟨252836847312634646360507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674231592833692390294685 252836847312634646360507)
                    ·
                      rfl

theorem cell22_738597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_738597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738597 prefixEnd_738597 := by exact prefixLift 738597
  have htrace : WordTrace (prefixWord ++ tailWord_738597) baseStart_738597 baseEnd_738597 := by
    simpa [prefixWord, tailWord_738597, baseEnd_738597] using wordTrace_append hprefix tailTrace_738597
  have hstable : (prefixWord ++ tailWord_738597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738597).length < 2 ^ (prefixWord ++ tailWord_738597).sum := by decide
  have hdescent : baseEnd_738597 < baseStart_738597 := by decide
  rcases family_descends (prefixWord ++ tailWord_738597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738732 : List Nat := [2, 2, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_738732 : Nat := 118140960795 + 738732 * 2 ^ 59
def prefixEnd_738732 : Nat := 4983230072969 + 3 ^ 40 * 738732 * 2
def baseEnd_738732 : Nat := 252883060571539294235093

theorem tailTrace_738732 : CollatzResearch.WordTrace tailWord_738732 prefixEnd_738732 252883060571539294235093 := by
  unfold tailWord_738732
  simp only [CollatzResearch.WordTrace]
  refine ⟨13471884779853802113085225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17962513039805069484113633 13471884779853802113085225)
  ·
    refine ⟨10103913584890351584813919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13471884779853802113085225 10103913584890351584813919)
    ·
      refine ⟨15155870377335527377220879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10103913584890351584813919 15155870377335527377220879)
      ·
        refine ⟨22733805566003291065831319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15155870377335527377220879 22733805566003291065831319)
        ·
          refine ⟨34100708349004936598746979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22733805566003291065831319 34100708349004936598746979)
          ·
            refine ⟨51151062523507404898120469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34100708349004936598746979 51151062523507404898120469)
            ·
              refine ⟨2397706055789409604599397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51151062523507404898120469 2397706055789409604599397)
              ·
                refine ⟨449569885460514300862387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2397706055789409604599397 449569885460514300862387)
                ·
                  refine ⟨674354828190771451293581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449569885460514300862387 674354828190771451293581)
                  ·
                    refine ⟨252883060571539294235093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674354828190771451293581 252883060571539294235093)
                    ·
                      rfl

theorem cell22_738732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_738732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738732 prefixEnd_738732 := by exact prefixLift 738732
  have htrace : WordTrace (prefixWord ++ tailWord_738732) baseStart_738732 baseEnd_738732 := by
    simpa [prefixWord, tailWord_738732, baseEnd_738732] using wordTrace_append hprefix tailTrace_738732
  have hstable : (prefixWord ++ tailWord_738732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738732).length < 2 ^ (prefixWord ++ tailWord_738732).sum := by decide
  have hdescent : baseEnd_738732 < baseStart_738732 := by decide
  rcases family_descends (prefixWord ++ tailWord_738732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738743 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 2, 5]
def baseStart_738743 : Nat := 118140960795 + 738743 * 2 ^ 59
def prefixEnd_738743 : Nat := 4983230072969 + 3 ^ 40 * 738743 * 2
def baseEnd_738743 : Nat := 252886826096338932210059

theorem tailTrace_738743 : CollatzResearch.WordTrace tailWord_738743 prefixEnd_738743 252886826096338932210059 := by
  unfold tailWord_738743
  simp only [CollatzResearch.WordTrace]
  refine ⟨26944170762667753104820883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17962780508445168736547255 26944170762667753104820883)
  ·
    refine ⟨40416256144001629657231325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26944170762667753104820883 40416256144001629657231325)
    ·
      refine ⟨15156096054000611121461747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40416256144001629657231325 15156096054000611121461747)
      ·
        refine ⟨22734144081000916682192621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15156096054000611121461747 22734144081000916682192621)
        ·
          refine ⟨8525304030375343755822233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22734144081000916682192621 8525304030375343755822233)
          ·
            refine ⟨6393978022781507816866675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8525304030375343755822233 6393978022781507816866675)
            ·
              refine ⟨9590967034172261725300013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6393978022781507816866675 9590967034172261725300013)
              ·
                refine ⟨3596612637814598146987505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9590967034172261725300013 3596612637814598146987505)
                ·
                  refine ⟨2697459478360948610240629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3596612637814598146987505 2697459478360948610240629)
                  ·
                    refine ⟨252886826096338932210059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2697459478360948610240629 252886826096338932210059)
                    ·
                      rfl

theorem cell22_738743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_738743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738743 prefixEnd_738743 := by exact prefixLift 738743
  have htrace : WordTrace (prefixWord ++ tailWord_738743) baseStart_738743 baseEnd_738743 := by
    simpa [prefixWord, tailWord_738743, baseEnd_738743] using wordTrace_append hprefix tailTrace_738743
  have hstable : (prefixWord ++ tailWord_738743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738743).length < 2 ^ (prefixWord ++ tailWord_738743).sum := by decide
  have hdescent : baseEnd_738743 < baseStart_738743 := by decide
  rcases family_descends (prefixWord ++ tailWord_738743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738803 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 1, 6]
def baseStart_738803 : Nat := 118140960795 + 738803 * 2 ^ 59
def prefixEnd_738803 : Nat := 4983230072969 + 3 ^ 40 * 738803 * 2
def baseEnd_738803 : Nat := 252907365322518775709875

theorem tailTrace_738803 : CollatzResearch.WordTrace tailWord_738803 prefixEnd_738803 252907365322518775709875 := by
  unfold tailWord_738803
  simp only [CollatzResearch.WordTrace]
  refine ⟨26946359142450383352005063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17964239428300255568003375 26946359142450383352005063)
  ·
    refine ⟨40419538713675575028007595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26946359142450383352005063 40419538713675575028007595)
    ·
      refine ⟨60629308070513362542011393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40419538713675575028007595 60629308070513362542011393)
      ·
        refine ⟨45471981052885021906508545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60629308070513362542011393 45471981052885021906508545)
        ·
          refine ⟨34103985789663766429881409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45471981052885021906508545 34103985789663766429881409)
          ·
            refine ⟨25577989342247824822411057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34103985789663766429881409 25577989342247824822411057)
            ·
              refine ⟨19183492006685868616808293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25577989342247824822411057 19183492006685868616808293)
              ·
                refine ⟨3596904751253600365651555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19183492006685868616808293 3596904751253600365651555)
                ·
                  refine ⟨5395357126880400548477333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596904751253600365651555 5395357126880400548477333)
                  ·
                    refine ⟨252907365322518775709875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5395357126880400548477333 252907365322518775709875)
                    ·
                      rfl

theorem cell22_738803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_738803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738803 prefixEnd_738803 := by exact prefixLift 738803
  have htrace : WordTrace (prefixWord ++ tailWord_738803) baseStart_738803 baseEnd_738803 := by
    simpa [prefixWord, tailWord_738803, baseEnd_738803] using wordTrace_append hprefix tailTrace_738803
  have hstable : (prefixWord ++ tailWord_738803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738803).length < 2 ^ (prefixWord ++ tailWord_738803).sum := by decide
  have hdescent : baseEnd_738803 < baseStart_738803 := by decide
  rcases family_descends (prefixWord ++ tailWord_738803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738867 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 3, 3]
def baseStart_738867 : Nat := 118140960795 + 738867 * 2 ^ 59
def prefixEnd_738867 : Nat := 4983230072969 + 3 ^ 40 * 738867 * 2
def baseEnd_738867 : Nat := 252929273830443942109679

theorem tailTrace_738867 : CollatzResearch.WordTrace tailWord_738867 prefixEnd_738867 252929273830443942109679 := by
  unfold tailWord_738867
  simp only [CollatzResearch.WordTrace]
  refine ⟨26948693414218522282334855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17965795609479014854889903 26948693414218522282334855)
  ·
    refine ⟨40423040121327783423502283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26948693414218522282334855 40423040121327783423502283)
    ·
      refine ⟨60634560181991675135253425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40423040121327783423502283 60634560181991675135253425)
      ·
        refine ⟨45475920136493756351440069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60634560181991675135253425 45475920136493756351440069)
        ·
          refine ⟨8526735025592579315895013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45475920136493756351440069 8526735025592579315895013)
          ·
            refine ⟨1598762817298608621730315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8526735025592579315895013 1598762817298608621730315)
            ·
              refine ⟨2398144225947912932595473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598762817298608621730315 2398144225947912932595473)
              ·
                refine ⟨1798608169460934699446605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398144225947912932595473 1798608169460934699446605)
                ·
                  refine ⟨674478063547850512292477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1798608169460934699446605 674478063547850512292477)
                  ·
                    refine ⟨252929273830443942109679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674478063547850512292477 252929273830443942109679)
                    ·
                      rfl

theorem cell22_738867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 3].length) (baseStart_738867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738867 prefixEnd_738867 := by exact prefixLift 738867
  have htrace : WordTrace (prefixWord ++ tailWord_738867) baseStart_738867 baseEnd_738867 := by
    simpa [prefixWord, tailWord_738867, baseEnd_738867] using wordTrace_append hprefix tailTrace_738867
  have hstable : (prefixWord ++ tailWord_738867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738867).length < 2 ^ (prefixWord ++ tailWord_738867).sum := by decide
  have hdescent : baseEnd_738867 < baseStart_738867 := by decide
  rcases family_descends (prefixWord ++ tailWord_738867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738940 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_738940 : Nat := 118140960795 + 738940 * 2 ^ 59
def prefixEnd_738940 : Nat := 4983230072969 + 3 ^ 40 * 738940 * 2
def baseEnd_738940 : Nat := 252954263222296085034455

theorem tailTrace_738940 : CollatzResearch.WordTrace tailWord_738940 prefixEnd_738940 252954263222296085034455 := by
  unfold tailWord_738940
  simp only [CollatzResearch.WordTrace]
  refine ⟨13475677971477027874871137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17967570628636037166494849 13475677971477027874871137)
  ·
    refine ⟨10106758478607770906153353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13475677971477027874871137 10106758478607770906153353)
    ·
      refine ⟨7580068858955828179615015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10106758478607770906153353 7580068858955828179615015)
      ·
        refine ⟨11370103288433742269422523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7580068858955828179615015 11370103288433742269422523)
        ·
          refine ⟨17055154932650613404133785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11370103288433742269422523 17055154932650613404133785)
          ·
            refine ⟨12791366199487960053100339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17055154932650613404133785 12791366199487960053100339)
            ·
              refine ⟨19187049299231940079650509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12791366199487960053100339 19187049299231940079650509)
              ·
                refine ⟨7195143487211977529868941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19187049299231940079650509 7195143487211977529868941)
                ·
                  refine ⟨2698178807704491573700853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7195143487211977529868941 2698178807704491573700853)
                  ·
                    refine ⟨252954263222296085034455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2698178807704491573700853 252954263222296085034455)
                    ·
                      rfl

theorem cell22_738940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_738940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738940 prefixEnd_738940 := by exact prefixLift 738940
  have htrace : WordTrace (prefixWord ++ tailWord_738940) baseStart_738940 baseEnd_738940 := by
    simpa [prefixWord, tailWord_738940, baseEnd_738940] using wordTrace_append hprefix tailTrace_738940
  have hstable : (prefixWord ++ tailWord_738940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738940).length < 2 ^ (prefixWord ++ tailWord_738940).sum := by decide
  have hdescent : baseEnd_738940 < baseStart_738940 := by decide
  rcases family_descends (prefixWord ++ tailWord_738940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738978 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_738978 : Nat := 118140960795 + 738978 * 2 ^ 59
def prefixEnd_738978 : Nat := 4983230072969 + 3 ^ 40 * 738978 * 2
def baseEnd_738978 : Nat := 252967271398876652584339

theorem tailTrace_738978 : CollatzResearch.WordTrace tailWord_738978 prefixEnd_738978 252967271398876652584339 := by
  unfold tailWord_738978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738185479204097059906397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17968494611210925493083725 6738185479204097059906397)
  ·
    refine ⟨2526819554701536397464899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6738185479204097059906397 2526819554701536397464899)
    ·
      refine ⟨3790229332052304596197349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2526819554701536397464899 3790229332052304596197349)
      ·
        refine ⟨710667999759807111787003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3790229332052304596197349 710667999759807111787003)
        ·
          refine ⟨1066001999639710667680505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710667999759807111787003 1066001999639710667680505)
          ·
            refine ⟨799501499729783000760379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066001999639710667680505 799501499729783000760379)
            ·
              refine ⟨1199252249594674501140569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799501499729783000760379 1199252249594674501140569)
              ·
                refine ⟨899439187196005875855427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199252249594674501140569 899439187196005875855427)
                ·
                  refine ⟨1349158780794008813783141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899439187196005875855427 1349158780794008813783141)
                  ·
                    refine ⟨252967271398876652584339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1349158780794008813783141 252967271398876652584339)
                    ·
                      rfl

theorem cell22_738978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_738978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738978 prefixEnd_738978 := by exact prefixLift 738978
  have htrace : WordTrace (prefixWord ++ tailWord_738978) baseStart_738978 baseEnd_738978 := by
    simpa [prefixWord, tailWord_738978, baseEnd_738978] using wordTrace_append hprefix tailTrace_738978
  have hstable : (prefixWord ++ tailWord_738978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738978).length < 2 ^ (prefixWord ++ tailWord_738978).sum := by decide
  have hdescent : baseEnd_738978 < baseStart_738978 := by decide
  rcases family_descends (prefixWord ++ tailWord_738978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738989 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_738989 : Nat := 118140960795 + 738989 * 2 ^ 59
def prefixEnd_738989 : Nat := 4983230072969 + 3 ^ 40 * 738989 * 2
def baseEnd_738989 : Nat := 252971036923676290559305

theorem tailTrace_738989 : CollatzResearch.WordTrace tailWord_738989 prefixEnd_738989 252971036923676290559305 := by
  unfold tailWord_738989
  simp only [CollatzResearch.WordTrace]
  refine ⟨26953143119776537118276021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17968762079851024745517347 26953143119776537118276021)
  ·
    refine ⟨2526857167479050354838377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26953143119776537118276021 2526857167479050354838377)
    ·
      refine ⟨1895142875609287766128783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2526857167479050354838377 1895142875609287766128783)
      ·
        refine ⟨2842714313413931649193175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895142875609287766128783 2842714313413931649193175)
        ·
          refine ⟨4264071470120897473789763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842714313413931649193175 4264071470120897473789763)
          ·
            refine ⟨6396107205181346210684645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264071470120897473789763 6396107205181346210684645)
            ·
              refine ⟨1199270100971502414503371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6396107205181346210684645 1199270100971502414503371)
              ·
                refine ⟨1798905151457253621755057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199270100971502414503371 1798905151457253621755057)
                ·
                  refine ⟨1349178863592940216316293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1798905151457253621755057 1349178863592940216316293)
                  ·
                    refine ⟨252971036923676290559305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1349178863592940216316293 252971036923676290559305)
                    ·
                      rfl

theorem cell22_738989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_738989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_738989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_738989 prefixEnd_738989 := by exact prefixLift 738989
  have htrace : WordTrace (prefixWord ++ tailWord_738989) baseStart_738989 baseEnd_738989 := by
    simpa [prefixWord, tailWord_738989, baseEnd_738989] using wordTrace_append hprefix tailTrace_738989
  have hstable : (prefixWord ++ tailWord_738989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738989).length < 2 ^ (prefixWord ++ tailWord_738989).sum := by decide
  have hdescent : baseEnd_738989 < baseStart_738989 := by decide
  rcases family_descends (prefixWord ++ tailWord_738989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739000 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_739000 : Nat := 118140960795 + 739000 * 2 ^ 59
def prefixEnd_739000 : Nat := 4983230072969 + 3 ^ 40 * 739000 * 2
def baseEnd_739000 : Nat := 252974802448475928534271

theorem tailTrace_739000 : CollatzResearch.WordTrace tailWord_739000 prefixEnd_739000 252974802448475928534271 := by
  unfold tailWord_739000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13476772161368342998463227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17969029548491123997950969 13476772161368342998463227)
  ·
    refine ⟨20215158242052514497694841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13476772161368342998463227 20215158242052514497694841)
    ·
      refine ⟨15161368681539385873271131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20215158242052514497694841 15161368681539385873271131)
      ·
        refine ⟨22742053022309078809906697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15161368681539385873271131 22742053022309078809906697)
        ·
          refine ⟨17056539766731809107430023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22742053022309078809906697 17056539766731809107430023)
          ·
            refine ⟨25584809650097713661145035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17056539766731809107430023 25584809650097713661145035)
            ·
              refine ⟨38377214475146570491717553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25584809650097713661145035 38377214475146570491717553)
              ·
                refine ⟨28782910856359927868788165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38377214475146570491717553 28782910856359927868788165)
                ·
                  refine ⟨5396795785567486475397781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28782910856359927868788165 5396795785567486475397781)
                  ·
                    refine ⟨252974802448475928534271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5396795785567486475397781 252974802448475928534271)
                    ·
                      rfl

theorem cell22_739000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_739000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739000 prefixEnd_739000 := by exact prefixLift 739000
  have htrace : WordTrace (prefixWord ++ tailWord_739000) baseStart_739000 baseEnd_739000 := by
    simpa [prefixWord, tailWord_739000, baseEnd_739000] using wordTrace_append hprefix tailTrace_739000
  have hstable : (prefixWord ++ tailWord_739000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739000).length < 2 ^ (prefixWord ++ tailWord_739000).sum := by decide
  have hdescent : baseEnd_739000 < baseStart_739000 := by decide
  rcases family_descends (prefixWord ++ tailWord_739000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739010 : List Nat := [3, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_739010 : Nat := 118140960795 + 739010 * 2 ^ 59
def prefixEnd_739010 : Nat := 4983230072969 + 3 ^ 40 * 739010 * 2
def baseEnd_739010 : Nat := 84326075217613078594747

theorem tailTrace_739010 : CollatzResearch.WordTrace tailWord_739010 prefixEnd_739010 84326075217613078594747 := by
  unfold tailWord_739010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738477263175114426197621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17969272701800305136526989 6738477263175114426197621)
  ·
    refine ⟨631732243422666977456027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6738477263175114426197621 631732243422666977456027)
    ·
      refine ⟨947598365134000466184041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631732243422666977456027 947598365134000466184041)
      ·
        refine ⟨710698773850500349638031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 947598365134000466184041 710698773850500349638031)
        ·
          refine ⟨1066048160775750524457047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710698773850500349638031 1066048160775750524457047)
          ·
            refine ⟨1599072241163625786685571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066048160775750524457047 1599072241163625786685571)
            ·
              refine ⟨2398608361745438680028357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599072241163625786685571 2398608361745438680028357)
              ·
                refine ⟨449739067827269752505317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2398608361745438680028357 449739067827269752505317)
                ·
                  refine ⟨84326075217613078594747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449739067827269752505317 84326075217613078594747)
                  ·
                    rfl

theorem cell22_739010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_739010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739010 prefixEnd_739010 := by exact prefixLift 739010
  have htrace : WordTrace (prefixWord ++ tailWord_739010) baseStart_739010 baseEnd_739010 := by
    simpa [prefixWord, tailWord_739010, baseEnd_739010] using wordTrace_append hprefix tailTrace_739010
  have hstable : (prefixWord ++ tailWord_739010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739010).length < 2 ^ (prefixWord ++ tailWord_739010).sum := by decide
  have hdescent : baseEnd_739010 < baseStart_739010 := by decide
  rcases family_descends (prefixWord ++ tailWord_739010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739021 : List Nat := [1, 6, 2, 1, 1, 3, 1, 7]
def baseStart_739021 : Nat := 118140960795 + 739021 * 2 ^ 59
def prefixEnd_739021 : Nat := 4983230072969 + 3 ^ 40 * 739021 * 2
def baseEnd_739021 : Nat := 28109110130848763751023

theorem tailTrace_739021 : CollatzResearch.WordTrace tailWord_739021 prefixEnd_739021 28109110130848763751023 := by
  unfold tailWord_739021
  simp only [CollatzResearch.WordTrace]
  refine ⟨26954310255660606583440917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17969540170440404388960611 26954310255660606583440917)
  ·
    refine ⟨1263483293234090933598793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26954310255660606583440917 1263483293234090933598793)
    ·
      refine ⟨947612469925568200199095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1263483293234090933598793 947612469925568200199095)
      ·
        refine ⟨1421418704888352300298643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947612469925568200199095 1421418704888352300298643)
        ·
          refine ⟨2132128057332528450447965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421418704888352300298643 2132128057332528450447965)
          ·
            refine ⟨799548021499698168917987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2132128057332528450447965 799548021499698168917987)
            ·
              refine ⟨1199322032249547253376981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799548021499698168917987 1199322032249547253376981)
              ·
                refine ⟨28109110130848763751023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1199322032249547253376981 28109110130848763751023)
                ·
                  rfl

theorem cell22_739021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 7].length) (baseStart_739021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739021 prefixEnd_739021 := by exact prefixLift 739021
  have htrace : WordTrace (prefixWord ++ tailWord_739021) baseStart_739021 baseEnd_739021 := by
    simpa [prefixWord, tailWord_739021, baseEnd_739021] using wordTrace_append hprefix tailTrace_739021
  have hstable : (prefixWord ++ tailWord_739021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739021).length < 2 ^ (prefixWord ++ tailWord_739021).sum := by decide
  have hdescent : baseEnd_739021 < baseStart_739021 := by decide
  rcases family_descends (prefixWord ++ tailWord_739021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739032 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 5]
def baseStart_739032 : Nat := 118140960795 + 739032 * 2 ^ 59
def prefixEnd_739032 : Nat := 4983230072969 + 3 ^ 40 * 739032 * 2
def baseEnd_739032 : Nat := 84328585567479503911391

theorem tailTrace_739032 : CollatzResearch.WordTrace tailWord_739032 prefixEnd_739032 84328585567479503911391 := by
  unfold tailWord_739032
  simp only [CollatzResearch.WordTrace]
  refine ⟨13477355729310377731045675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17969807639080503641394233 13477355729310377731045675)
  ·
    refine ⟨20216033593965566596568513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13477355729310377731045675 20216033593965566596568513)
    ·
      refine ⟨15162025195474174947426385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20216033593965566596568513 15162025195474174947426385)
      ·
        refine ⟨11371518896605631210569789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15162025195474174947426385 11371518896605631210569789)
        ·
          refine ⟨4264319586227111703963671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11371518896605631210569789 4264319586227111703963671)
          ·
            refine ⟨6396479379340667555945507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264319586227111703963671 6396479379340667555945507)
            ·
              refine ⟨9594719069011001333918261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396479379340667555945507 9594719069011001333918261)
              ·
                refine ⟨899504912719781375054837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9594719069011001333918261 899504912719781375054837)
                ·
                  refine ⟨84328585567479503911391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 899504912719781375054837 84328585567479503911391)
                  ·
                    rfl

theorem cell22_739032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_739032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739032 prefixEnd_739032 := by exact prefixLift 739032
  have htrace : WordTrace (prefixWord ++ tailWord_739032) baseStart_739032 baseEnd_739032 := by
    simpa [prefixWord, tailWord_739032, baseEnd_739032] using wordTrace_append hprefix tailTrace_739032
  have hstable : (prefixWord ++ tailWord_739032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739032).length < 2 ^ (prefixWord ++ tailWord_739032).sum := by decide
  have hdescent : baseEnd_739032 < baseStart_739032 := by decide
  rcases family_descends (prefixWord ++ tailWord_739032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739053 : List Nat := [1, 5, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_739053 : Nat := 118140960795 + 739053 * 2 ^ 59
def prefixEnd_739053 : Nat := 4983230072969 + 3 ^ 40 * 739053 * 2
def baseEnd_739053 : Nat := 252992945431601456959109

theorem tailTrace_739053 : CollatzResearch.WordTrace tailWord_739053 prefixEnd_739053 252992945431601456959109 := by
  unfold tailWord_739053
  simp only [CollatzResearch.WordTrace]
  refine ⟨26955477391544676048605813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17970318261029784032403875 26955477391544676048605813)
  ·
    refine ⟨2527076005457313379556795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26955477391544676048605813 2527076005457313379556795)
    ·
      refine ⟨3790614008185970069335193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2527076005457313379556795 3790614008185970069335193)
      ·
        refine ⟨2842960506139477552001395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3790614008185970069335193 2842960506139477552001395)
        ·
          refine ⟨4264440759209216328002093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842960506139477552001395 4264440759209216328002093)
          ·
            refine ⟨1599165284703456123000785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4264440759209216328002093 1599165284703456123000785)
            ·
              refine ⟨1199373963527592092250589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599165284703456123000785 1199373963527592092250589)
              ·
                refine ⟨449765236322847034593971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1199373963527592092250589 449765236322847034593971)
                ·
                  refine ⟨674647854484270551890957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449765236322847034593971 674647854484270551890957)
                  ·
                    refine ⟨252992945431601456959109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674647854484270551890957 252992945431601456959109)
                    ·
                      rfl

theorem cell22_739053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_739053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739053 prefixEnd_739053 := by exact prefixLift 739053
  have htrace : WordTrace (prefixWord ++ tailWord_739053) baseStart_739053 baseEnd_739053 := by
    simpa [prefixWord, tailWord_739053, baseEnd_739053] using wordTrace_append hprefix tailTrace_739053
  have hstable : (prefixWord ++ tailWord_739053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739053).length < 2 ^ (prefixWord ++ tailWord_739053).sum := by decide
  have hdescent : baseEnd_739053 < baseStart_739053 := by decide
  rcases family_descends (prefixWord ++ tailWord_739053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739107 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 1, 6]
def baseStart_739107 : Nat := 118140960795 + 739107 * 2 ^ 59
def prefixEnd_739107 : Nat := 4983230072969 + 3 ^ 40 * 739107 * 2
def baseEnd_739107 : Nat := 253011430735163316108943

theorem tailTrace_739107 : CollatzResearch.WordTrace tailWord_739107 prefixEnd_739107 253011430735163316108943 := by
  unfold tailWord_739107
  simp only [CollatzResearch.WordTrace]
  refine ⟨26957446933349043271071575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17971631288899362180714383 26957446933349043271071575)
  ·
    refine ⟨40436170400023564906607363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26957446933349043271071575 40436170400023564906607363)
    ·
      refine ⟨60654255600035347359911045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40436170400023564906607363 60654255600035347359911045)
      ·
        refine ⟨11372672925006627629983321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60654255600035347359911045 11372672925006627629983321)
        ·
          refine ⟨8529504693754970722487491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11372672925006627629983321 8529504693754970722487491)
          ·
            refine ⟨12794257040632456083731237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8529504693754970722487491 12794257040632456083731237)
            ·
              refine ⟨2398923195118585515699607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12794257040632456083731237 2398923195118585515699607)
              ·
                refine ⟨3598384792677878273549411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398923195118585515699607 3598384792677878273549411)
                ·
                  refine ⟨5397577189016817410324117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598384792677878273549411 5397577189016817410324117)
                  ·
                    refine ⟨253011430735163316108943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5397577189016817410324117 253011430735163316108943)
                    ·
                      rfl

theorem cell22_739107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_739107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739107 prefixEnd_739107 := by exact prefixLift 739107
  have htrace : WordTrace (prefixWord ++ tailWord_739107) baseStart_739107 baseEnd_739107 := by
    simpa [prefixWord, tailWord_739107, baseEnd_739107] using wordTrace_append hprefix tailTrace_739107
  have hstable : (prefixWord ++ tailWord_739107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739107).length < 2 ^ (prefixWord ++ tailWord_739107).sum := by decide
  have hdescent : baseEnd_739107 < baseStart_739107 := by decide
  rcases family_descends (prefixWord ++ tailWord_739107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739109 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_739109 : Nat := 118140960795 + 739109 * 2 ^ 59
def prefixEnd_739109 : Nat := 4983230072969 + 3 ^ 40 * 739109 * 2
def baseEnd_739109 : Nat := 253012115376035977558937

theorem tailTrace_739109 : CollatzResearch.WordTrace tailWord_739109 prefixEnd_739109 253012115376035977558937 := by
  unfold tailWord_739109
  simp only [CollatzResearch.WordTrace]
  refine ⟨26957519879341797612644381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17971679919561198408429587 26957519879341797612644381)
  ·
    refine ⟨10109069954753174104741643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26957519879341797612644381 10109069954753174104741643)
    ·
      refine ⟨15163604932129761157112465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10109069954753174104741643 15163604932129761157112465)
      ·
        refine ⟨11372703699097320867834349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15163604932129761157112465 11372703699097320867834349)
        ·
          refine ⟨4264763887161495325437881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11372703699097320867834349 4264763887161495325437881)
          ·
            refine ⟨3198572915371121494078411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4264763887161495325437881 3198572915371121494078411)
            ·
              refine ⟨4797859373056682241117617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198572915371121494078411 4797859373056682241117617)
              ·
                refine ⟨3598394529792511680838213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4797859373056682241117617 3598394529792511680838213)
                ·
                  refine ⟨674698974336095940157165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3598394529792511680838213 674698974336095940157165)
                  ·
                    refine ⟨253012115376035977558937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674698974336095940157165 253012115376035977558937)
                    ·
                      rfl

theorem cell22_739109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_739109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739109 prefixEnd_739109 := by exact prefixLift 739109
  have htrace : WordTrace (prefixWord ++ tailWord_739109) baseStart_739109 baseEnd_739109 := by
    simpa [prefixWord, tailWord_739109, baseEnd_739109] using wordTrace_append hprefix tailTrace_739109
  have hstable : (prefixWord ++ tailWord_739109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739109).length < 2 ^ (prefixWord ++ tailWord_739109).sum := by decide
  have hdescent : baseEnd_739109 < baseStart_739109 := by decide
  rcases family_descends (prefixWord ++ tailWord_739109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739122 : List Nat := [3, 2, 1, 1, 3, 2, 10]
def baseStart_739122 : Nat := 118140960795 + 739122 * 2 ^ 59
def prefixEnd_739122 : Nat := 4983230072969 + 3 ^ 40 * 739122 * 2
def baseEnd_739122 : Nat := 9370983908952158406811

theorem tailTrace_739122 : CollatzResearch.WordTrace tailWord_739122 prefixEnd_739122 9370983908952158406811 := by
  unfold tailWord_739122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739498507073675208216905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17971996018863133888578413 6739498507073675208216905)
  ·
    refine ⟨5054623880305256406162679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6739498507073675208216905 5054623880305256406162679)
    ·
      refine ⟨7581935820457884609244019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054623880305256406162679 7581935820457884609244019)
      ·
        refine ⟨11372903730686826913866029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581935820457884609244019 11372903730686826913866029)
        ·
          refine ⟨4264838899007560092699761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11372903730686826913866029 4264838899007560092699761)
          ·
            refine ⟨3198629174255670069524821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4264838899007560092699761 3198629174255670069524821)
            ·
              refine ⟨9370983908952158406811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3198629174255670069524821 9370983908952158406811)
              ·
                rfl

theorem cell22_739122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 10].length) (baseStart_739122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739122 prefixEnd_739122 := by exact prefixLift 739122
  have htrace : WordTrace (prefixWord ++ tailWord_739122) baseStart_739122 baseEnd_739122 := by
    simpa [prefixWord, tailWord_739122, baseEnd_739122] using wordTrace_append hprefix tailTrace_739122
  have hstable : (prefixWord ++ tailWord_739122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739122).length < 2 ^ (prefixWord ++ tailWord_739122).sum := by decide
  have hdescent : baseEnd_739122 < baseStart_739122 := by decide
  rcases family_descends (prefixWord ++ tailWord_739122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739261 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_739261 : Nat := 118140960795 + 739261 * 2 ^ 59
def prefixEnd_739261 : Nat := 4983230072969 + 3 ^ 40 * 739261 * 2
def baseEnd_739261 : Nat := 253064148082358247758471

theorem tailTrace_739261 : CollatzResearch.WordTrace tailWord_739261 prefixEnd_739261 253064148082358247758471 := by
  unfold tailWord_739261
  simp only [CollatzResearch.WordTrace]
  refine ⟨26963063774791127572177637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17975375849860751714785091 26963063774791127572177637)
  ·
    refine ⟨5055574457773336419783307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26963063774791127572177637 5055574457773336419783307)
    ·
      refine ⟨7583361686660004629674961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5055574457773336419783307 7583361686660004629674961)
      ·
        refine ⟨5687521264995003472256221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7583361686660004629674961 5687521264995003472256221)
        ·
          refine ⟨2132820474373126302096083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5687521264995003472256221 2132820474373126302096083)
          ·
            refine ⟨3199230711559689453144125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132820474373126302096083 3199230711559689453144125)
            ·
              refine ⟨1199711516834883544929047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3199230711559689453144125 1199711516834883544929047)
              ·
                refine ⟨1799567275252325317393571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199711516834883544929047 1799567275252325317393571)
                ·
                  refine ⟨2699350912878487976090357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799567275252325317393571 2699350912878487976090357)
                  ·
                    refine ⟨253064148082358247758471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2699350912878487976090357 253064148082358247758471)
                    ·
                      rfl

theorem cell22_739261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_739261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739261 prefixEnd_739261 := by exact prefixLift 739261
  have htrace : WordTrace (prefixWord ++ tailWord_739261) baseStart_739261 baseEnd_739261 := by
    simpa [prefixWord, tailWord_739261, baseEnd_739261] using wordTrace_append hprefix tailTrace_739261
  have hstable : (prefixWord ++ tailWord_739261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739261).length < 2 ^ (prefixWord ++ tailWord_739261).sum := by decide
  have hdescent : baseEnd_739261 < baseStart_739261 := by decide
  rcases family_descends (prefixWord ++ tailWord_739261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739293 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_739293 : Nat := 118140960795 + 739293 * 2 ^ 59
def prefixEnd_739293 : Nat := 4983230072969 + 3 ^ 40 * 739293 * 2
def baseEnd_739293 : Nat := 253075102336320830958373

theorem tailTrace_739293 : CollatzResearch.WordTrace tailWord_739293 prefixEnd_739293 253075102336320830958373 := by
  unfold tailWord_739293
  simp only [CollatzResearch.WordTrace]
  refine ⟨26964230910675197037342533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17976153940450131358228355 26964230910675197037342533)
  ·
    refine ⟨5055793295751599444501725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26964230910675197037342533 5055793295751599444501725)
    ·
      refine ⟨1895922485906849791688147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5055793295751599444501725 1895922485906849791688147)
      ·
        refine ⟨2843883728860274687532221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895922485906849791688147 2843883728860274687532221)
        ·
          refine ⟨1066456398322603007824583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2843883728860274687532221 1066456398322603007824583)
          ·
            refine ⟨1599684597483904511736875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066456398322603007824583 1599684597483904511736875)
            ·
              refine ⟨2399526896225856767605313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599684597483904511736875 2399526896225856767605313)
              ·
                refine ⟨1799645172169392575703985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2399526896225856767605313 1799645172169392575703985)
                ·
                  refine ⟨1349733879127044431777989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1799645172169392575703985 1349733879127044431777989)
                  ·
                    refine ⟨253075102336320830958373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1349733879127044431777989 253075102336320830958373)
                    ·
                      rfl

theorem cell22_739293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_739293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739293 prefixEnd_739293 := by exact prefixLift 739293
  have htrace : WordTrace (prefixWord ++ tailWord_739293) baseStart_739293 baseEnd_739293 := by
    simpa [prefixWord, tailWord_739293, baseEnd_739293] using wordTrace_append hprefix tailTrace_739293
  have hstable : (prefixWord ++ tailWord_739293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739293).length < 2 ^ (prefixWord ++ tailWord_739293).sum := by decide
  have hdescent : baseEnd_739293 < baseStart_739293 := by decide
  rcases family_descends (prefixWord ++ tailWord_739293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739304 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_739304 : Nat := 118140960795 + 739304 * 2 ^ 59
def prefixEnd_739304 : Nat := 4983230072969 + 3 ^ 40 * 739304 * 2
def baseEnd_739304 : Nat := 253078867861120468933339

theorem tailTrace_739304 : CollatzResearch.WordTrace tailWord_739304 prefixEnd_739304 253078867861120468933339 := by
  unfold tailWord_739304
  simp only [CollatzResearch.WordTrace]
  refine ⟨13482316056817672957996483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17976421409090230610661977 13482316056817672957996483)
  ·
    refine ⟨20223474085226509436994725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13482316056817672957996483 20223474085226509436994725)
    ·
      refine ⟨3791901390979970519436511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20223474085226509436994725 3791901390979970519436511)
      ·
        refine ⟨5687852086469955779154767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791901390979970519436511 5687852086469955779154767)
        ·
          refine ⟨8531778129704933668732151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5687852086469955779154767 8531778129704933668732151)
          ·
            refine ⟨12797667194557400503098227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8531778129704933668732151 12797667194557400503098227)
            ·
              refine ⟨19196500791836100754647341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12797667194557400503098227 19196500791836100754647341)
              ·
                refine ⟨7198687796938537782992753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19196500791836100754647341 7198687796938537782992753)
                ·
                  refine ⟨5399015847703903337244565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7198687796938537782992753 5399015847703903337244565)
                  ·
                    refine ⟨253078867861120468933339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5399015847703903337244565 253078867861120468933339)
                    ·
                      rfl

theorem cell22_739304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_739304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739304 prefixEnd_739304 := by exact prefixLift 739304
  have htrace : WordTrace (prefixWord ++ tailWord_739304) baseStart_739304 baseEnd_739304 := by
    simpa [prefixWord, tailWord_739304, baseEnd_739304] using wordTrace_append hprefix tailTrace_739304
  have hstable : (prefixWord ++ tailWord_739304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739304).length < 2 ^ (prefixWord ++ tailWord_739304).sum := by decide
  have hdescent : baseEnd_739304 < baseStart_739304 := by decide
  rcases family_descends (prefixWord ++ tailWord_739304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739357 : List Nat := [1, 4, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_739357 : Nat := 118140960795 + 739357 * 2 ^ 59
def prefixEnd_739357 : Nat := 4983230072969 + 3 ^ 40 * 739357 * 2
def baseEnd_739357 : Nat := 253097010844245997358177

theorem tailTrace_739357 : CollatzResearch.WordTrace tailWord_739357 prefixEnd_739357 253097010844245997358177 := by
  unfold tailWord_739357
  simp only [CollatzResearch.WordTrace]
  refine ⟨26966565182443335967672325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17977710121628890645114883 26966565182443335967672325)
  ·
    refine ⟨5056230971708125493938561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26966565182443335967672325 5056230971708125493938561)
    ·
      refine ⟨3792173228781094120453921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5056230971708125493938561 3792173228781094120453921)
      ·
        refine ⟨2844129921585820590340441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3792173228781094120453921 2844129921585820590340441)
        ·
          refine ⟨2133097441189365442755331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844129921585820590340441 2133097441189365442755331)
          ·
            refine ⟨3199646161784048164132997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133097441189365442755331 3199646161784048164132997)
            ·
              refine ⟨599933655334509030774937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3199646161784048164132997 599933655334509030774937)
              ·
                refine ⟨449950241500881773081203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599933655334509030774937 449950241500881773081203)
                ·
                  refine ⟨674925362251322659621805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449950241500881773081203 674925362251322659621805)
                  ·
                    refine ⟨253097010844245997358177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674925362251322659621805 253097010844245997358177)
                    ·
                      rfl

theorem cell22_739357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_739357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739357 prefixEnd_739357 := by exact prefixLift 739357
  have htrace : WordTrace (prefixWord ++ tailWord_739357) baseStart_739357 baseEnd_739357 := by
    simpa [prefixWord, tailWord_739357, baseEnd_739357] using wordTrace_append hprefix tailTrace_739357
  have hstable : (prefixWord ++ tailWord_739357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739357).length < 2 ^ (prefixWord ++ tailWord_739357).sum := by decide
  have hdescent : baseEnd_739357 < baseStart_739357 := by decide
  rcases family_descends (prefixWord ++ tailWord_739357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739398 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_739398 : Nat := 118140960795 + 739398 * 2 ^ 59
def prefixEnd_739398 : Nat := 4983230072969 + 3 ^ 40 * 739398 * 2
def baseEnd_739398 : Nat := 84370348660711852361017

theorem tailTrace_739398 : CollatzResearch.WordTrace tailWord_739398 prefixEnd_739398 84370348660711852361017 := by
  unfold tailWord_739398
  simp only [CollatzResearch.WordTrace]
  refine ⟨842751892977962499059839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17978707050196533313276565 842751892977962499059839)
  ·
    refine ⟨1264127839466943748589759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 842751892977962499059839 1264127839466943748589759)
    ·
      refine ⟨1896191759200415622884639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264127839466943748589759 1896191759200415622884639)
      ·
        refine ⟨2844287638800623434326959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896191759200415622884639 2844287638800623434326959)
        ·
          refine ⟨4266431458200935151490439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844287638800623434326959 4266431458200935151490439)
          ·
            refine ⟨6399647187301402727235659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266431458200935151490439 6399647187301402727235659)
            ·
              refine ⟨9599470780952104090853489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6399647187301402727235659 9599470780952104090853489)
              ·
                refine ⟨7199603085714078068140117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599470780952104090853489 7199603085714078068140117)
                ·
                  refine ⟨84370348660711852361017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7199603085714078068140117 84370348660711852361017)
                  ·
                    rfl

theorem cell22_739398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_739398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739398 prefixEnd_739398 := by exact prefixLift 739398
  have htrace : WordTrace (prefixWord ++ tailWord_739398) baseStart_739398 baseEnd_739398 := by
    simpa [prefixWord, tailWord_739398, baseEnd_739398] using wordTrace_append hprefix tailTrace_739398
  have hstable : (prefixWord ++ tailWord_739398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739398).length < 2 ^ (prefixWord ++ tailWord_739398).sum := by decide
  have hdescent : baseEnd_739398 < baseStart_739398 := by decide
  rcases family_descends (prefixWord ++ tailWord_739398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739413 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_739413 : Nat := 118140960795 + 739413 * 2 ^ 59
def prefixEnd_739413 : Nat := 4983230072969 + 3 ^ 40 * 739413 * 2
def baseEnd_739413 : Nat := 253116180788680517958005

theorem tailTrace_739413 : CollatzResearch.WordTrace tailWord_739413 prefixEnd_739413 253116180788680517958005 := by
  unfold tailWord_739413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26968607670240457531710893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17979071780160305021140595 26968607670240457531710893)
  ·
    refine ⟨10113227876340171574391585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26968607670240457531710893 10113227876340171574391585)
    ·
      refine ⟨7584920907255128680793689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10113227876340171574391585 7584920907255128680793689)
      ·
        refine ⟨5688690680441346510595267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7584920907255128680793689 5688690680441346510595267)
        ·
          refine ⟨8533036020662019765892901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5688690680441346510595267 8533036020662019765892901)
          ·
            refine ⟨1599944253874128706104919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8533036020662019765892901 1599944253874128706104919)
            ·
              refine ⟨2399916380811193059157379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599944253874128706104919 2399916380811193059157379)
              ·
                refine ⟨3599874571216789588736069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2399916380811193059157379 3599874571216789588736069)
                ·
                  refine ⟨674976482103148047888013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3599874571216789588736069 674976482103148047888013)
                  ·
                    refine ⟨253116180788680517958005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674976482103148047888013 253116180788680517958005)
                    ·
                      rfl

theorem cell22_739413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_739413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739413 prefixEnd_739413 := by exact prefixLift 739413
  have htrace : WordTrace (prefixWord ++ tailWord_739413) baseStart_739413 baseEnd_739413 := by
    simpa [prefixWord, tailWord_739413, baseEnd_739413] using wordTrace_append hprefix tailTrace_739413
  have hstable : (prefixWord ++ tailWord_739413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739413).length < 2 ^ (prefixWord ++ tailWord_739413).sum := by decide
  have hdescent : baseEnd_739413 < baseStart_739413 := by decide
  rcases family_descends (prefixWord ++ tailWord_739413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739488 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 5]
def baseStart_739488 : Nat := 118140960795 + 739488 * 2 ^ 59
def prefixEnd_739488 : Nat := 4983230072969 + 3 ^ 40 * 739488 * 2
def baseEnd_739488 : Nat := 84380618273801774110925

theorem tailTrace_739488 : CollatzResearch.WordTrace tailWord_739488 prefixEnd_739488 84380618273801774110925 := by
  unfold tailWord_739488
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485671572484372670345559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17980895429979163560460745 13485671572484372670345559)
  ·
    refine ⟨20228507358726559005518339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13485671572484372670345559 20228507358726559005518339)
    ·
      refine ⟨30342761038089838508277509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20228507358726559005518339 30342761038089838508277509)
      ·
        refine ⟨5689267694641844720302033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30342761038089838508277509 5689267694641844720302033)
        ·
          refine ⟨4266950770981383540226525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5689267694641844720302033 4266950770981383540226525)
          ·
            refine ⟨1600106539118018827584947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4266950770981383540226525 1600106539118018827584947)
            ·
              refine ⟨2400159808677028241377421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600106539118018827584947 2400159808677028241377421)
              ·
                refine ⟨900059928253885590516533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2400159808677028241377421 900059928253885590516533)
                ·
                  refine ⟨84380618273801774110925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 900059928253885590516533 84380618273801774110925)
                  ·
                    rfl

theorem cell22_739488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_739488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739488 prefixEnd_739488 := by exact prefixLift 739488
  have htrace : WordTrace (prefixWord ++ tailWord_739488) baseStart_739488 baseEnd_739488 := by
    simpa [prefixWord, tailWord_739488, baseEnd_739488] using wordTrace_append hprefix tailTrace_739488
  have hstable : (prefixWord ++ tailWord_739488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739488).length < 2 ^ (prefixWord ++ tailWord_739488).sum := by decide
  have hdescent : baseEnd_739488 < baseStart_739488 := by decide
  rcases family_descends (prefixWord ++ tailWord_739488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739522 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_739522 : Nat := 118140960795 + 739522 * 2 ^ 59
def prefixEnd_739522 : Nat := 4983230072969 + 3 ^ 40 * 739522 * 2
def baseEnd_739522 : Nat := 84384497905413522327557

theorem tailTrace_739522 : CollatzResearch.WordTrace tailWord_739522 prefixEnd_739522 84384497905413522327557 := by
  unfold tailWord_739522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743145806711392286857205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17981722151230379431619213 6743145806711392286857205)
  ·
    refine ⟨632169919379193026892863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6743145806711392286857205 632169919379193026892863)
    ·
      refine ⟨948254879068789540339295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 632169919379193026892863 948254879068789540339295)
      ·
        refine ⟨1422382318603184310508943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948254879068789540339295 1422382318603184310508943)
        ·
          refine ⟨2133573477904776465763415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422382318603184310508943 2133573477904776465763415)
          ·
            refine ⟨3200360216857164698645123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133573477904776465763415 3200360216857164698645123)
            ·
              refine ⟨4800540325285747047967685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200360216857164698645123 4800540325285747047967685)
              ·
                refine ⟨900101310991077571493941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4800540325285747047967685 900101310991077571493941)
                ·
                  refine ⟨84384497905413522327557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 900101310991077571493941 84384497905413522327557)
                  ·
                    rfl

theorem cell22_739522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_739522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739522 prefixEnd_739522 := by exact prefixLift 739522
  have htrace : WordTrace (prefixWord ++ tailWord_739522) baseStart_739522 baseEnd_739522 := by
    simpa [prefixWord, tailWord_739522, baseEnd_739522] using wordTrace_append hprefix tailTrace_739522
  have hstable : (prefixWord ++ tailWord_739522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739522).length < 2 ^ (prefixWord ++ tailWord_739522).sum := by decide
  have hdescent : baseEnd_739522 < baseStart_739522 := by decide
  rcases family_descends (prefixWord ++ tailWord_739522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739531 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 3, 5]
def baseStart_739531 : Nat := 118140960795 + 739531 * 2 ^ 59
def prefixEnd_739531 : Nat := 4983230072969 + 3 ^ 40 * 739531 * 2
def baseEnd_739531 : Nat := 253156574600167543507643

theorem tailTrace_739531 : CollatzResearch.WordTrace tailWord_739531 prefixEnd_739531 253156574600167543507643 := by
  unfold tailWord_739531
  simp only [CollatzResearch.WordTrace]
  refine ⟨26972911483812963684506447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17981940989208642456337631 26972911483812963684506447)
  ·
    refine ⟨40459367225719445526759671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26972911483812963684506447 40459367225719445526759671)
    ·
      refine ⟨60689050838579168290139507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40459367225719445526759671 60689050838579168290139507)
      ·
        refine ⟨91033576257868752435209261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60689050838579168290139507 91033576257868752435209261)
        ·
          refine ⟨34137591096700782163203473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91033576257868752435209261 34137591096700782163203473)
          ·
            refine ⟨25603193322525586622402605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34137591096700782163203473 25603193322525586622402605)
            ·
              refine ⟨9601197495947094983400977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25603193322525586622402605 9601197495947094983400977)
              ·
                refine ⟨7200898121960321237550733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9601197495947094983400977 7200898121960321237550733)
                ·
                  refine ⟨2700336795735120464081525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7200898121960321237550733 2700336795735120464081525)
                  ·
                    refine ⟨253156574600167543507643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2700336795735120464081525 253156574600167543507643)
                    ·
                      rfl

theorem cell22_739531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_739531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739531 prefixEnd_739531 := by exact prefixLift 739531
  have htrace : WordTrace (prefixWord ++ tailWord_739531) baseStart_739531 baseEnd_739531 := by
    simpa [prefixWord, tailWord_739531, baseEnd_739531] using wordTrace_append hprefix tailTrace_739531
  have hstable : (prefixWord ++ tailWord_739531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739531).length < 2 ^ (prefixWord ++ tailWord_739531).sum := by decide
  have hdescent : baseEnd_739531 < baseStart_739531 := by decide
  rcases family_descends (prefixWord ++ tailWord_739531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739576 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_739576 : Nat := 118140960795 + 739576 * 2 ^ 59
def prefixEnd_739576 : Nat := 4983230072969 + 3 ^ 40 * 739576 * 2
def baseEnd_739576 : Nat := 253171979019802426132505

theorem tailTrace_739576 : CollatzResearch.WordTrace tailWord_739576 prefixEnd_739576 253171979019802426132505 := by
  unfold tailWord_739576
  simp only [CollatzResearch.WordTrace]
  refine ⟨13487276384324968184947291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17983035179099957579929721 13487276384324968184947291)
  ·
    refine ⟨20230914576487452277420937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13487276384324968184947291 20230914576487452277420937)
    ·
      refine ⟨15173185932365589208065703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20230914576487452277420937 15173185932365589208065703)
      ·
        refine ⟨22759778898548383812098555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15173185932365589208065703 22759778898548383812098555)
        ·
          refine ⟨34139668347822575718147833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22759778898548383812098555 34139668347822575718147833)
          ·
            refine ⟨25604751260866931788610875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34139668347822575718147833 25604751260866931788610875)
            ·
              refine ⟨38407126891300397682916313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25604751260866931788610875 38407126891300397682916313)
              ·
                refine ⟨28805345168475298262187235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38407126891300397682916313 28805345168475298262187235)
                ·
                  refine ⟨43208017752712947393280853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28805345168475298262187235 43208017752712947393280853)
                  ·
                    refine ⟨253171979019802426132505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43208017752712947393280853 253171979019802426132505)
                    ·
                      rfl

theorem cell22_739576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_739576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739576 prefixEnd_739576 := by exact prefixLift 739576
  have htrace : WordTrace (prefixWord ++ tailWord_739576) baseStart_739576 baseEnd_739576 := by
    simpa [prefixWord, tailWord_739576, baseEnd_739576] using wordTrace_append hprefix tailTrace_739576
  have hstable : (prefixWord ++ tailWord_739576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739576).length < 2 ^ (prefixWord ++ tailWord_739576).sum := by decide
  have hdescent : baseEnd_739576 < baseStart_739576 := by decide
  rcases family_descends (prefixWord ++ tailWord_739576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739644 : List Nat := [2, 2, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_739644 : Nat := 118140960795 + 739644 * 2 ^ 59
def prefixEnd_739644 : Nat := 4983230072969 + 3 ^ 40 * 739644 * 2
def baseEnd_739644 : Nat := 253195256809472915432297

theorem tailTrace_739644 : CollatzResearch.WordTrace tailWord_739644 prefixEnd_739644 253195256809472915432297 := by
  unfold tailWord_739644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488516466201791991684993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17984688621602389322246657 13488516466201791991684993)
  ·
    refine ⟨10116387349651343993763745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13488516466201791991684993 10116387349651343993763745)
    ·
      refine ⟨7587290512238507995322809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10116387349651343993763745 7587290512238507995322809)
      ·
        refine ⟨5690467884178880996492107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7587290512238507995322809 5690467884178880996492107)
        ·
          refine ⟨8535701826268321494738161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690467884178880996492107 8535701826268321494738161)
          ·
            refine ⟨6401776369701241121053621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8535701826268321494738161 6401776369701241121053621)
            ·
              refine ⟨600166534659491355098777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6401776369701241121053621 600166534659491355098777)
              ·
                refine ⟨450124900994618516324083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600166534659491355098777 450124900994618516324083)
                ·
                  refine ⟨675187351491927774486125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450124900994618516324083 675187351491927774486125)
                  ·
                    refine ⟨253195256809472915432297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675187351491927774486125 253195256809472915432297)
                    ·
                      rfl

theorem cell22_739644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_739644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739644 prefixEnd_739644 := by exact prefixLift 739644
  have htrace : WordTrace (prefixWord ++ tailWord_739644) baseStart_739644 baseEnd_739644 := by
    simpa [prefixWord, tailWord_739644, baseEnd_739644] using wordTrace_append hprefix tailTrace_739644
  have hstable : (prefixWord ++ tailWord_739644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739644).length < 2 ^ (prefixWord ++ tailWord_739644).sum := by decide
  have hdescent : baseEnd_739644 < baseStart_739644 := by decide
  rcases family_descends (prefixWord ++ tailWord_739644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739732 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_739732 : Nat := 118140960795 + 739732 * 2 ^ 59
def prefixEnd_739732 : Nat := 4983230072969 + 3 ^ 40 * 739732 * 2
def baseEnd_739732 : Nat := 253225381007870019232027

theorem tailTrace_739732 : CollatzResearch.WordTrace tailWord_739732 prefixEnd_739732 253225381007870019232027 := by
  unfold tailWord_739732
  simp only [CollatzResearch.WordTrace]
  refine ⟨13490121278042387506286725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17986828370723183341715633 13490121278042387506286725)
  ·
    refine ⟨2529397739632947657428761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13490121278042387506286725 2529397739632947657428761)
    ·
      refine ⟨1897048304724710743071571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2529397739632947657428761 1897048304724710743071571)
      ·
        refine ⟨2845572457087066114607357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897048304724710743071571 2845572457087066114607357)
        ·
          refine ⟨1067089671407649792977759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2845572457087066114607357 1067089671407649792977759)
          ·
            refine ⟨1600634507111474689466639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067089671407649792977759 1600634507111474689466639)
            ·
              refine ⟨2400951760667212034199959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600634507111474689466639 2400951760667212034199959)
              ·
                refine ⟨3601427641000818051299939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400951760667212034199959 3601427641000818051299939)
                ·
                  refine ⟨5402141461501227076949909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601427641000818051299939 5402141461501227076949909)
                  ·
                    refine ⟨253225381007870019232027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5402141461501227076949909 253225381007870019232027)
                    ·
                      rfl

theorem cell22_739732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_739732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739732 prefixEnd_739732 := by exact prefixLift 739732
  have htrace : WordTrace (prefixWord ++ tailWord_739732) baseStart_739732 baseEnd_739732 := by
    simpa [prefixWord, tailWord_739732, baseEnd_739732] using wordTrace_append hprefix tailTrace_739732
  have hstable : (prefixWord ++ tailWord_739732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739732).length < 2 ^ (prefixWord ++ tailWord_739732).sum := by decide
  have hdescent : baseEnd_739732 < baseStart_739732 := by decide
  rcases family_descends (prefixWord ++ tailWord_739732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739762 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_739762 : Nat := 118140960795 + 739762 * 2 ^ 59
def prefixEnd_739762 : Nat := 4983230072969 + 3 ^ 40 * 739762 * 2
def baseEnd_739762 : Nat := 253235650620959940981935

theorem tailTrace_739762 : CollatzResearch.WordTrace tailWord_739762 prefixEnd_739762 253235650620959940981935 := by
  unfold tailWord_739762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745334186494022534041385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17987557830650726757443693 6745334186494022534041385)
  ·
    refine ⟨5059000639870516900531039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6745334186494022534041385 5059000639870516900531039)
    ·
      refine ⟨7588500959805775350796559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5059000639870516900531039 7588500959805775350796559)
      ·
        refine ⟨11382751439708663026194839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7588500959805775350796559 11382751439708663026194839)
        ·
          refine ⟨17074127159562994539292259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11382751439708663026194839 17074127159562994539292259)
          ·
            refine ⟨25611190739344491808938389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17074127159562994539292259 25611190739344491808938389)
            ·
              refine ⟨1200524565906773053543987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25611190739344491808938389 1200524565906773053543987)
              ·
                refine ⟨1800786848860159580315981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200524565906773053543987 1800786848860159580315981)
                ·
                  refine ⟨675295068322559842618493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1800786848860159580315981 675295068322559842618493)
                  ·
                    refine ⟨253235650620959940981935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675295068322559842618493 253235650620959940981935)
                    ·
                      rfl

theorem cell22_739762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_739762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739762 prefixEnd_739762 := by exact prefixLift 739762
  have htrace : WordTrace (prefixWord ++ tailWord_739762) baseStart_739762 baseEnd_739762 := by
    simpa [prefixWord, tailWord_739762, baseEnd_739762] using wordTrace_append hprefix tailTrace_739762
  have hstable : (prefixWord ++ tailWord_739762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739762).length < 2 ^ (prefixWord ++ tailWord_739762).sum := by decide
  have hdescent : baseEnd_739762 < baseStart_739762 := by decide
  rcases family_descends (prefixWord ++ tailWord_739762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739796 : List Nat := [2, 4, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_739796 : Nat := 118140960795 + 739796 * 2 ^ 59
def prefixEnd_739796 : Nat := 4983230072969 + 3 ^ 40 * 739796 * 2
def baseEnd_739796 : Nat := 253247289515795185631831

theorem tailTrace_739796 : CollatzResearch.WordTrace tailWord_739796 prefixEnd_739796 253247289515795185631831 := by
  unfold tailWord_739796
  simp only [CollatzResearch.WordTrace]
  refine ⟨13491288413926456971451621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17988384551901942628602161 13491288413926456971451621)
  ·
    refine ⟨2529616577611210682147179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13491288413926456971451621 2529616577611210682147179)
    ·
      refine ⟨3794424866416816023220769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2529616577611210682147179 3794424866416816023220769)
      ·
        refine ⟨2845818649812612017415577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3794424866416816023220769 2845818649812612017415577)
        ·
          refine ⟨2134363987359459013061683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845818649812612017415577 2134363987359459013061683)
          ·
            refine ⟨3201545981039188519592525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134363987359459013061683 3201545981039188519592525)
            ·
              refine ⟨1200579742889695694847197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201545981039188519592525 1200579742889695694847197)
              ·
                refine ⟨450217403583635885567699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1200579742889695694847197 450217403583635885567699)
                ·
                  refine ⟨675326105375453828351549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450217403583635885567699 675326105375453828351549)
                  ·
                    refine ⟨253247289515795185631831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675326105375453828351549 253247289515795185631831)
                    ·
                      rfl

theorem cell22_739796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_739796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739796 prefixEnd_739796 := by exact prefixLift 739796
  have htrace : WordTrace (prefixWord ++ tailWord_739796) baseStart_739796 baseEnd_739796 := by
    simpa [prefixWord, tailWord_739796, baseEnd_739796] using wordTrace_append hprefix tailTrace_739796
  have hstable : (prefixWord ++ tailWord_739796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739796).length < 2 ^ (prefixWord ++ tailWord_739796).sum := by decide
  have hdescent : baseEnd_739796 < baseStart_739796 := by decide
  rcases family_descends (prefixWord ++ tailWord_739796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739813 : List Nat := [1, 3, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_739813 : Nat := 118140960795 + 739813 * 2 ^ 59
def prefixEnd_739813 : Nat := 4983230072969 + 3 ^ 40 * 739813 * 2
def baseEnd_739813 : Nat := 253253108963212807956779

theorem tailTrace_739813 : CollatzResearch.WordTrace tailWord_739813 prefixEnd_739813 253253108963212807956779 := by
  unfold tailWord_739813
  simp only [CollatzResearch.WordTrace]
  refine ⟨26983196868791325846272093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17988797912527550564181395 26983196868791325846272093)
  ·
    refine ⟨10118698825796747192352035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26983196868791325846272093 10118698825796747192352035)
    ·
      refine ⟨15178048238695120788528053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10118698825796747192352035 15178048238695120788528053)
      ·
        refine ⟨1422942022377667573924505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15178048238695120788528053 1422942022377667573924505)
        ·
          refine ⟨1067206516783250680443379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1422942022377667573924505 1067206516783250680443379)
          ·
            refine ⟨1600809775174876020665069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067206516783250680443379 1600809775174876020665069)
            ·
              refine ⟨600303665690578507749401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1600809775174876020665069 600303665690578507749401)
              ·
                refine ⟨450227749267933880812051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600303665690578507749401 450227749267933880812051)
                ·
                  refine ⟨675341623901900821218077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450227749267933880812051 675341623901900821218077)
                  ·
                    refine ⟨253253108963212807956779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675341623901900821218077 253253108963212807956779)
                    ·
                      rfl

theorem cell22_739813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_739813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739813 prefixEnd_739813 := by exact prefixLift 739813
  have htrace : WordTrace (prefixWord ++ tailWord_739813) baseStart_739813 baseEnd_739813 := by
    simpa [prefixWord, tailWord_739813, baseEnd_739813] using wordTrace_append hprefix tailTrace_739813
  have hstable : (prefixWord ++ tailWord_739813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739813).length < 2 ^ (prefixWord ++ tailWord_739813).sum := by decide
  have hdescent : baseEnd_739813 < baseStart_739813 := by decide
  rcases family_descends (prefixWord ++ tailWord_739813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739826 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_739826 : Nat := 118140960795 + 739826 * 2 ^ 59
def prefixEnd_739826 : Nat := 4983230072969 + 3 ^ 40 * 739826 * 2
def baseEnd_739826 : Nat := 84419186376295035793913

theorem tailTrace_739826 : CollatzResearch.WordTrace tailWord_739826 prefixEnd_739826 84419186376295035793913 := by
  unfold tailWord_739826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745917754436057266623833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17989114011829486044330221 6745917754436057266623833)
  ·
    refine ⟨5059438315827042949967875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6745917754436057266623833 5059438315827042949967875)
    ·
      refine ⟨7589157473740564424951813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5059438315827042949967875 7589157473740564424951813)
      ·
        refine ⟨1422967026326355829678465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7589157473740564424951813 1422967026326355829678465)
        ·
          refine ⟨1067225269744766872258849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1422967026326355829678465 1067225269744766872258849)
          ·
            refine ⟨800418952308575154194137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1067225269744766872258849 800418952308575154194137)
            ·
              refine ⟨600314214231431365645603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800418952308575154194137 600314214231431365645603)
              ·
                refine ⟨900471321347147048468405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600314214231431365645603 900471321347147048468405)
                ·
                  refine ⟨84419186376295035793913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 900471321347147048468405 84419186376295035793913)
                  ·
                    rfl

theorem cell22_739826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_739826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739826 prefixEnd_739826 := by exact prefixLift 739826
  have htrace : WordTrace (prefixWord ++ tailWord_739826) baseStart_739826 baseEnd_739826 := by
    simpa [prefixWord, tailWord_739826, baseEnd_739826] using wordTrace_append hprefix tailTrace_739826
  have hstable : (prefixWord ++ tailWord_739826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739826).length < 2 ^ (prefixWord ++ tailWord_739826).sum := by decide
  have hdescent : baseEnd_739826 < baseStart_739826 := by decide
  rcases family_descends (prefixWord ++ tailWord_739826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739852 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_739852 : Nat := 118140960795 + 739852 * 2 ^ 59
def prefixEnd_739852 : Nat := 4983230072969 + 3 ^ 40 * 739852 * 2
def baseEnd_739852 : Nat := 253266459460229706231659

theorem tailTrace_739852 : CollatzResearch.WordTrace tailWord_739852 prefixEnd_739852 253266459460229706231659 := by
  unfold tailWord_739852
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492309657825017753470905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17989746210433357004627873 13492309657825017753470905)
  ·
    refine ⟨10119232243368763315103179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13492309657825017753470905 10119232243368763315103179)
    ·
      refine ⟨15178848365053144972654769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10119232243368763315103179 15178848365053144972654769)
      ·
        refine ⟨11384136273789858729491077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15178848365053144972654769 11384136273789858729491077)
        ·
          refine ⟨2134525551335598511779577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11384136273789858729491077 2134525551335598511779577)
          ·
            refine ⟨1600894163501698883834683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134525551335598511779577 1600894163501698883834683)
            ·
              refine ⟨2401341245252548325752025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600894163501698883834683 2401341245252548325752025)
              ·
                refine ⟨1801005933939411244314019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401341245252548325752025 1801005933939411244314019)
                ·
                  refine ⟨2701508900909116866471029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801005933939411244314019 2701508900909116866471029)
                  ·
                    refine ⟨253266459460229706231659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2701508900909116866471029 253266459460229706231659)
                    ·
                      rfl

theorem cell22_739852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_739852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739852 prefixEnd_739852 := by exact prefixLift 739852
  have htrace : WordTrace (prefixWord ++ tailWord_739852) baseStart_739852 baseEnd_739852 := by
    simpa [prefixWord, tailWord_739852, baseEnd_739852] using wordTrace_append hprefix tailTrace_739852
  have hstable : (prefixWord ++ tailWord_739852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739852).length < 2 ^ (prefixWord ++ tailWord_739852).sum := by decide
  have hdescent : baseEnd_739852 < baseStart_739852 := by decide
  rcases family_descends (prefixWord ++ tailWord_739852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739869 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_739869 : Nat := 118140960795 + 739869 * 2 ^ 59
def prefixEnd_739869 : Nat := 4983230072969 + 3 ^ 40 * 739869 * 2
def baseEnd_739869 : Nat := 253272278907647328556607

theorem tailTrace_739869 : CollatzResearch.WordTrace tailWord_739869 prefixEnd_739869 253272278907647328556607 := by
  unfold tailWord_739869
  simp only [CollatzResearch.WordTrace]
  refine ⟨26985239356588447410310661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17990159571058964940207107 26985239356588447410310661)
  ·
    refine ⟨5059732379360333889433249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26985239356588447410310661 5059732379360333889433249)
    ·
      refine ⟨3794799284520250417074937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5059732379360333889433249 3794799284520250417074937)
      ·
        refine ⟨2846099463390187812806203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3794799284520250417074937 2846099463390187812806203)
        ·
          refine ⟨4269149195085281719209305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846099463390187812806203 4269149195085281719209305)
          ·
            refine ⟨3201861896313961289406979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4269149195085281719209305 3201861896313961289406979)
            ·
              refine ⟨4802792844470941934110469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201861896313961289406979 4802792844470941934110469)
              ·
                refine ⟨900523658338301612645713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4802792844470941934110469 900523658338301612645713)
                ·
                  refine ⟨675392743753726209484285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 900523658338301612645713 675392743753726209484285)
                  ·
                    refine ⟨253272278907647328556607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675392743753726209484285 253272278907647328556607)
                    ·
                      rfl

theorem cell22_739869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_739869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739869 prefixEnd_739869 := by exact prefixLift 739869
  have htrace : WordTrace (prefixWord ++ tailWord_739869) baseStart_739869 baseEnd_739869 := by
    simpa [prefixWord, tailWord_739869, baseEnd_739869] using wordTrace_append hprefix tailTrace_739869
  have hstable : (prefixWord ++ tailWord_739869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739869).length < 2 ^ (prefixWord ++ tailWord_739869).sum := by decide
  have hdescent : baseEnd_739869 < baseStart_739869 := by decide
  rcases family_descends (prefixWord ++ tailWord_739869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739882 : List Nat := [3, 1, 4, 1, 1, 2, 3, 7]
def baseStart_739882 : Nat := 118140960795 + 739882 * 2 ^ 59
def prefixEnd_739882 : Nat := 4983230072969 + 3 ^ 40 * 739882 * 2
def baseEnd_739882 : Nat := 28141858785924403109063

theorem tailTrace_739882 : CollatzResearch.WordTrace tailWord_739882 prefixEnd_739882 28141858785924403109063 := by
  unfold tailWord_739882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6746428376385337657633475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17990475670360900420355933 6746428376385337657633475)
  ·
    refine ⟨10119642564578006486450213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6746428376385337657633475 10119642564578006486450213)
    ·
      refine ⟨1897432980858376216209415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10119642564578006486450213 1897432980858376216209415)
      ·
        refine ⟨2846149471287564324314123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897432980858376216209415 2846149471287564324314123)
        ·
          refine ⟨4269224206931346486471185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846149471287564324314123 4269224206931346486471185)
          ·
            refine ⟨3201918155198509864853389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4269224206931346486471185 3201918155198509864853389)
            ·
              refine ⟨1200719308199441199320021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201918155198509864853389 1200719308199441199320021)
              ·
                refine ⟨28141858785924403109063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1200719308199441199320021 28141858785924403109063)
                ·
                  rfl

theorem cell22_739882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_739882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739882 prefixEnd_739882 := by exact prefixLift 739882
  have htrace : WordTrace (prefixWord ++ tailWord_739882) baseStart_739882 baseEnd_739882 := by
    simpa [prefixWord, tailWord_739882, baseEnd_739882] using wordTrace_append hprefix tailTrace_739882
  have hstable : (prefixWord ++ tailWord_739882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739882).length < 2 ^ (prefixWord ++ tailWord_739882).sum := by decide
  have hdescent : baseEnd_739882 < baseStart_739882 := by decide
  rcases family_descends (prefixWord ++ tailWord_739882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739895 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 2, 6]
def baseStart_739895 : Nat := 118140960795 + 739895 * 2 ^ 59
def prefixEnd_739895 : Nat := 4983230072969 + 3 ^ 40 * 739895 * 2
def baseEnd_739895 : Nat := 253281179238991927406527

theorem tailTrace_739895 : CollatzResearch.WordTrace tailWord_739895 prefixEnd_739895 253281179238991927406527 := by
  unfold tailWord_739895
  simp only [CollatzResearch.WordTrace]
  refine ⟨26986187654494253850757139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17990791769662835900504759 26986187654494253850757139)
  ·
    refine ⟨40479281481741380776135709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26986187654494253850757139 40479281481741380776135709)
    ·
      refine ⟨15179730555653017791050891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40479281481741380776135709 15179730555653017791050891)
      ·
        refine ⟨22769595833479526686576337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15179730555653017791050891 22769595833479526686576337)
        ·
          refine ⟨17077196875109645014932253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22769595833479526686576337 17077196875109645014932253)
          ·
            refine ⟨6403948828166116880599595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17077196875109645014932253 6403948828166116880599595)
            ·
              refine ⟨9605923242249175320899393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403948828166116880599595 9605923242249175320899393)
              ·
                refine ⟨7204442431686881490674545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605923242249175320899393 7204442431686881490674545)
                ·
                  refine ⟨5403331823765161118005909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7204442431686881490674545 5403331823765161118005909)
                  ·
                    refine ⟨253281179238991927406527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5403331823765161118005909 253281179238991927406527)
                    ·
                      rfl

theorem cell22_739895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_739895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739895 prefixEnd_739895 := by exact prefixLift 739895
  have htrace : WordTrace (prefixWord ++ tailWord_739895) baseStart_739895 baseEnd_739895 := by
    simpa [prefixWord, tailWord_739895, baseEnd_739895] using wordTrace_append hprefix tailTrace_739895
  have hstable : (prefixWord ++ tailWord_739895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739895).length < 2 ^ (prefixWord ++ tailWord_739895).sum := by decide
  have hdescent : baseEnd_739895 < baseStart_739895 := by decide
  rcases family_descends (prefixWord ++ tailWord_739895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739955 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 8]
def baseStart_739955 : Nat := 118140960795 + 739955 * 2 ^ 59
def prefixEnd_739955 : Nat := 4983230072969 + 3 ^ 40 * 739955 * 2
def baseEnd_739955 : Nat := 84433906155057256968781

theorem tailTrace_739955 : CollatzResearch.WordTrace tailWord_739955 prefixEnd_739955 84433906155057256968781 := by
  unfold tailWord_739955
  simp only [CollatzResearch.WordTrace]
  refine ⟨26988376034276884097941319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17992250689517922731960879 26988376034276884097941319)
  ·
    refine ⟨40482564051415326146911979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26988376034276884097941319 40482564051415326146911979)
    ·
      refine ⟨60723846077122989220367969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40482564051415326146911979 60723846077122989220367969)
      ·
        refine ⟨45542884557842241915275977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60723846077122989220367969 45542884557842241915275977)
        ·
          refine ⟨34157163418381681436456983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45542884557842241915275977 34157163418381681436456983)
          ·
            refine ⟨51235745127572522154685475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34157163418381681436456983 51235745127572522154685475)
            ·
              refine ⟨76853617691358783232028213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51235745127572522154685475 76853617691358783232028213)
              ·
                refine ⟨7205026658564885928002645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76853617691358783232028213 7205026658564885928002645)
                ·
                  refine ⟨84433906155057256968781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7205026658564885928002645 84433906155057256968781)
                  ·
                    rfl

theorem cell22_739955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_739955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739955 prefixEnd_739955 := by exact prefixLift 739955
  have htrace : WordTrace (prefixWord ++ tailWord_739955) baseStart_739955 baseEnd_739955 := by
    simpa [prefixWord, tailWord_739955, baseEnd_739955] using wordTrace_append hprefix tailTrace_739955
  have hstable : (prefixWord ++ tailWord_739955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739955).length < 2 ^ (prefixWord ++ tailWord_739955).sum := by decide
  have hdescent : baseEnd_739955 < baseStart_739955 := by decide
  rcases family_descends (prefixWord ++ tailWord_739955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739965 : List Nat := [1, 4, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_739965 : Nat := 118140960795 + 739965 * 2 ^ 59
def prefixEnd_739965 : Nat := 4983230072969 + 3 ^ 40 * 739965 * 2
def baseEnd_739965 : Nat := 253305141669535078156313

theorem tailTrace_739965 : CollatzResearch.WordTrace tailWord_739965 prefixEnd_739965 253305141669535078156313 := by
  unfold tailWord_739965
  simp only [CollatzResearch.WordTrace]
  refine ⟨26988740764240655805805349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17992493842827103870536899 26988740764240655805805349)
  ·
    refine ⟨5060388893295122963588503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26988740764240655805805349 5060388893295122963588503)
    ·
      refine ⟨7590583339942684445382755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5060388893295122963588503 7590583339942684445382755)
      ·
        refine ⟨11385875009914026668074133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590583339942684445382755 11385875009914026668074133)
        ·
          refine ⟨533712891089720000065975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11385875009914026668074133 533712891089720000065975)
          ·
            refine ⟨800569336634580000098963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533712891089720000065975 800569336634580000098963)
            ·
              refine ⟨1200854004951870000148445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800569336634580000098963 1200854004951870000148445)
              ·
                refine ⟨450320251856951250055667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1200854004951870000148445 450320251856951250055667)
                ·
                  refine ⟨675480377785426875083501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450320251856951250055667 675480377785426875083501)
                  ·
                    refine ⟨253305141669535078156313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675480377785426875083501 253305141669535078156313)
                    ·
                      rfl

theorem cell22_739965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_739965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_739965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_739965 prefixEnd_739965 := by exact prefixLift 739965
  have htrace : WordTrace (prefixWord ++ tailWord_739965) baseStart_739965 baseEnd_739965 := by
    simpa [prefixWord, tailWord_739965, baseEnd_739965] using wordTrace_append hprefix tailTrace_739965
  have hstable : (prefixWord ++ tailWord_739965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739965).length < 2 ^ (prefixWord ++ tailWord_739965).sum := by decide
  have hdescent : baseEnd_739965 < baseStart_739965 := by decide
  rcases family_descends (prefixWord ++ tailWord_739965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740019 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 2, 4]
def baseStart_740019 : Nat := 118140960795 + 740019 * 2 ^ 59
def prefixEnd_740019 : Nat := 4983230072969 + 3 ^ 40 * 740019 * 2
def baseEnd_740019 : Nat := 253323626973096937306147

theorem tailTrace_740019 : CollatzResearch.WordTrace tailWord_740019 prefixEnd_740019 253323626973096937306147 := by
  unfold tailWord_740019
  simp only [CollatzResearch.WordTrace]
  refine ⟨26990710306045023028271111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17993806870696682018847407 26990710306045023028271111)
  ·
    refine ⟨40486065459067534542406667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26990710306045023028271111 40486065459067534542406667)
    ·
      refine ⟨60729098188601301813610001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40486065459067534542406667 60729098188601301813610001)
      ·
        refine ⟨45546823641450976360207501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60729098188601301813610001 45546823641450976360207501)
        ·
          refine ⟨17080058865544116135077813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45546823641450976360207501 17080058865544116135077813)
          ·
            refine ⟨1601255518644760887663545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17080058865544116135077813 1601255518644760887663545)
            ·
              refine ⟨1200941638983570665747659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601255518644760887663545 1200941638983570665747659)
              ·
                refine ⟨1801412458475355998621489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200941638983570665747659 1801412458475355998621489)
                ·
                  refine ⟨1351059343856516998966117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1801412458475355998621489 1351059343856516998966117)
                  ·
                    refine ⟨253323626973096937306147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351059343856516998966117 253323626973096937306147)
                    ·
                      rfl

theorem cell22_740019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4].length) (baseStart_740019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740019 prefixEnd_740019 := by exact prefixLift 740019
  have htrace : WordTrace (prefixWord ++ tailWord_740019) baseStart_740019 baseEnd_740019 := by
    simpa [prefixWord, tailWord_740019, baseEnd_740019] using wordTrace_append hprefix tailTrace_740019
  have hstable : (prefixWord ++ tailWord_740019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740019).length < 2 ^ (prefixWord ++ tailWord_740019).sum := by decide
  have hdescent : baseEnd_740019 < baseStart_740019 := by decide
  rcases family_descends (prefixWord ++ tailWord_740019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740034 : List Nat := [3, 5, 1, 13]
def baseStart_740034 : Nat := 118140960795 + 740034 * 2 ^ 59
def prefixEnd_740034 : Nat := 4983230072969 + 3 ^ 40 * 740034 * 2
def baseEnd_740034 : Nat := 347501730836271465269

theorem tailTrace_740034 : CollatzResearch.WordTrace tailWord_740034 prefixEnd_740034 347501730836271465269 := by
  unfold tailWord_740034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747814350247670147516789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17994171600660453726711437 6747814350247670147516789)
  ·
    refine ⟨632607595335719076329699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6747814350247670147516789 632607595335719076329699)
    ·
      refine ⟨948911393003578614494549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 632607595335719076329699 948911393003578614494549)
      ·
        refine ⟨347501730836271465269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 948911393003578614494549 347501730836271465269)
        ·
          rfl

theorem cell22_740034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 13].length) (baseStart_740034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740034 prefixEnd_740034 := by exact prefixLift 740034
  have htrace : WordTrace (prefixWord ++ tailWord_740034) baseStart_740034 baseEnd_740034 := by
    simpa [prefixWord, tailWord_740034, baseEnd_740034] using wordTrace_append hprefix tailTrace_740034
  have hstable : (prefixWord ++ tailWord_740034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740034).length < 2 ^ (prefixWord ++ tailWord_740034).sum := by decide
  have hdescent : baseEnd_740034 < baseStart_740034 := by decide
  rcases family_descends (prefixWord ++ tailWord_740034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740049 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 3, 3]
def baseStart_740049 : Nat := 118140960795 + 740049 * 2 ^ 59
def prefixEnd_740049 : Nat := 4983230072969 + 3 ^ 40 * 740049 * 2
def baseEnd_740049 : Nat := 253333896586186859056055

theorem tailTrace_740049 : CollatzResearch.WordTrace tailWord_740049 prefixEnd_740049 253333896586186859056055 := by
  unfold tailWord_740049
  simp only [CollatzResearch.WordTrace]
  refine ⟨26991804495936338151863201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17994536330624225434575467 26991804495936338151863201)
  ·
    refine ⟨20243853371952253613897401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26991804495936338151863201 20243853371952253613897401)
    ·
      refine ⟨15182890028964190210423051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20243853371952253613897401 15182890028964190210423051)
      ·
        refine ⟨22774335043446285315634577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15182890028964190210423051 22774335043446285315634577)
        ·
          refine ⟨17080751282584713986725933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22774335043446285315634577 17080751282584713986725933)
          ·
            refine ⟨6405281730969267745022225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17080751282584713986725933 6405281730969267745022225)
            ·
              refine ⟨4803961298226950808766669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6405281730969267745022225 4803961298226950808766669)
              ·
                refine ⟨1801485486835106553287501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4803961298226950808766669 1801485486835106553287501)
                ·
                  refine ⟨675557057563164957482813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1801485486835106553287501 675557057563164957482813)
                  ·
                    refine ⟨253333896586186859056055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675557057563164957482813 253333896586186859056055)
                    ·
                      rfl

theorem cell22_740049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_740049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740049 prefixEnd_740049 := by exact prefixLift 740049
  have htrace : WordTrace (prefixWord ++ tailWord_740049) baseStart_740049 baseEnd_740049 := by
    simpa [prefixWord, tailWord_740049, baseEnd_740049] using wordTrace_append hprefix tailTrace_740049
  have hstable : (prefixWord ++ tailWord_740049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740049).length < 2 ^ (prefixWord ++ tailWord_740049).sum := by decide
  have hdescent : baseEnd_740049 < baseStart_740049 := by decide
  rcases family_descends (prefixWord ++ tailWord_740049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740124 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 6]
def baseStart_740124 : Nat := 118140960795 + 740124 * 2 ^ 59
def prefixEnd_740124 : Nat := 4983230072969 + 3 ^ 40 * 740124 * 2
def baseEnd_740124 : Nat := 84453190206303887810275

theorem tailTrace_740124 : CollatzResearch.WordTrace tailWord_740124 prefixEnd_740124 84453190206303887810275 := by
  unfold tailWord_740124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13497269985332312980421713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17996359980443083973895617 13497269985332312980421713)
  ·
    refine ⟨10122952488999234735316285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13497269985332312980421713 10122952488999234735316285)
    ·
      refine ⟨3796107183374713025743607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10122952488999234735316285 3796107183374713025743607)
      ·
        refine ⟨5694160775062069538615411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796107183374713025743607 5694160775062069538615411)
        ·
          refine ⟨8541241162593104307923117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694160775062069538615411 8541241162593104307923117)
          ·
            refine ⟨3202965435972414115471169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8541241162593104307923117 3202965435972414115471169)
            ·
              refine ⟨2402224076979310586603377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3202965435972414115471169 2402224076979310586603377)
              ·
                refine ⟨1801668057734482939952533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2402224076979310586603377 1801668057734482939952533)
                ·
                  refine ⟨84453190206303887810275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1801668057734482939952533 84453190206303887810275)
                  ·
                    rfl

theorem cell22_740124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_740124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740124 prefixEnd_740124 := by exact prefixLift 740124
  have htrace : WordTrace (prefixWord ++ tailWord_740124) baseStart_740124 baseEnd_740124 := by
    simpa [prefixWord, tailWord_740124, baseEnd_740124] using wordTrace_append hprefix tailTrace_740124
  have hstable : (prefixWord ++ tailWord_740124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740124).length < 2 ^ (prefixWord ++ tailWord_740124).sum := by decide
  have hdescent : baseEnd_740124 < baseStart_740124 := by decide
  rcases family_descends (prefixWord ++ tailWord_740124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740139 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 4, 3]
def baseStart_740139 : Nat := 118140960795 + 740139 * 2 ^ 59
def prefixEnd_740139 : Nat := 4983230072969 + 3 ^ 40 * 740139 * 2
def baseEnd_740139 : Nat := 253364705425456624305779

theorem tailTrace_740139 : CollatzResearch.WordTrace tailWord_740139 prefixEnd_740139 253364705425456624305779 := by
  unfold tailWord_740139
  simp only [CollatzResearch.WordTrace]
  refine ⟨26995087065610283522639471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17996724710406855681759647 26995087065610283522639471)
  ·
    refine ⟨40492630598415425283959207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26995087065610283522639471 40492630598415425283959207)
    ·
      refine ⟨60738945897623137925938811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40492630598415425283959207 60738945897623137925938811)
      ·
        refine ⟨91108418846434706888908217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60738945897623137925938811 91108418846434706888908217)
        ·
          refine ⟨68331314134826030166681163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91108418846434706888908217 68331314134826030166681163)
          ·
            refine ⟨102496971202239045250021745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68331314134826030166681163 102496971202239045250021745)
            ·
              refine ⟨76872728401679283937516309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102496971202239045250021745 76872728401679283937516309)
              ·
                refine ⟨3603409143828716434571077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76872728401679283937516309 3603409143828716434571077)
                ·
                  refine ⟨675639214467884331482077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3603409143828716434571077 675639214467884331482077)
                  ·
                    refine ⟨253364705425456624305779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675639214467884331482077 253364705425456624305779)
                    ·
                      rfl

theorem cell22_740139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 3].length) (baseStart_740139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740139 prefixEnd_740139 := by exact prefixLift 740139
  have htrace : WordTrace (prefixWord ++ tailWord_740139) baseStart_740139 baseEnd_740139 := by
    simpa [prefixWord, tailWord_740139, baseEnd_740139] using wordTrace_append hprefix tailTrace_740139
  have hstable : (prefixWord ++ tailWord_740139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740139).length < 2 ^ (prefixWord ++ tailWord_740139).sum := by decide
  have hdescent : baseEnd_740139 < baseStart_740139 := by decide
  rcases family_descends (prefixWord ++ tailWord_740139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740156 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_740156 : Nat := 118140960795 + 740156 * 2 ^ 59
def prefixEnd_740156 : Nat := 4983230072969 + 3 ^ 40 * 740156 * 2
def baseEnd_740156 : Nat := 253370524872874246630727

theorem tailTrace_740156 : CollatzResearch.WordTrace tailWord_740156 prefixEnd_740156 253370524872874246630727 := by
  unfold tailWord_740156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13497853553274347713004161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17997138071032463617338881 13497853553274347713004161)
  ·
    refine ⟨10123390164955760784753121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13497853553274347713004161 10123390164955760784753121)
    ·
      refine ⟨7592542623716820588564841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10123390164955760784753121 7592542623716820588564841)
      ·
        refine ⟨5694406967787615441423631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7592542623716820588564841 5694406967787615441423631)
        ·
          refine ⟨8541610451681423162135447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694406967787615441423631 8541610451681423162135447)
          ·
            refine ⟨12812415677522134743203171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8541610451681423162135447 12812415677522134743203171)
            ·
              refine ⟨19218623516283202114804757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12812415677522134743203171 19218623516283202114804757)
              ·
                refine ⟨900872977325775099131473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19218623516283202114804757 900872977325775099131473)
                ·
                  refine ⟨675654732994331324348605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 900872977325775099131473 675654732994331324348605)
                  ·
                    refine ⟨253370524872874246630727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675654732994331324348605 253370524872874246630727)
                    ·
                      rfl

theorem cell22_740156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_740156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740156 prefixEnd_740156 := by exact prefixLift 740156
  have htrace : WordTrace (prefixWord ++ tailWord_740156) baseStart_740156 baseEnd_740156 := by
    simpa [prefixWord, tailWord_740156, baseEnd_740156] using wordTrace_append hprefix tailTrace_740156
  have hstable : (prefixWord ++ tailWord_740156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740156).length < 2 ^ (prefixWord ++ tailWord_740156).sum := by decide
  have hdescent : baseEnd_740156 < baseStart_740156 := by decide
  rcases family_descends (prefixWord ++ tailWord_740156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740158 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_740158 : Nat := 118140960795 + 740158 * 2 ^ 59
def prefixEnd_740158 : Nat := 4983230072969 + 3 ^ 40 * 740158 * 2
def baseEnd_740158 : Nat := 84457069837915636026907

theorem tailTrace_740158 : CollatzResearch.WordTrace tailWord_740158 prefixEnd_740158 84457069837915636026907 := by
  unfold tailWord_740158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374472506567681220947641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17997186701694299845054085 3374472506567681220947641)
  ·
    refine ⟨2530854379925760915710731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3374472506567681220947641 2530854379925760915710731)
    ·
      refine ⟨3796281569888641373566097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530854379925760915710731 3796281569888641373566097)
      ·
        refine ⟨2847211177416481030174573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3796281569888641373566097 2847211177416481030174573)
        ·
          refine ⟨1067704191531180386315465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2847211177416481030174573 1067704191531180386315465)
          ·
            refine ⟨800778143648385289736599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1067704191531180386315465 800778143648385289736599)
            ·
              refine ⟨1201167215472577934604899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800778143648385289736599 1201167215472577934604899)
              ·
                refine ⟨1801750823208866901907349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201167215472577934604899 1801750823208866901907349)
                ·
                  refine ⟨84457069837915636026907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1801750823208866901907349 84457069837915636026907)
                  ·
                    rfl

theorem cell22_740158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_740158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740158 prefixEnd_740158 := by exact prefixLift 740158
  have htrace : WordTrace (prefixWord ++ tailWord_740158) baseStart_740158 baseEnd_740158 := by
    simpa [prefixWord, tailWord_740158, baseEnd_740158] using wordTrace_append hprefix tailTrace_740158
  have hstable : (prefixWord ++ tailWord_740158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740158).length < 2 ^ (prefixWord ++ tailWord_740158).sum := by decide
  have hdescent : baseEnd_740158 < baseStart_740158 := by decide
  rcases family_descends (prefixWord ++ tailWord_740158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740169 : List Nat := [1, 2, 1, 1, 2, 6, 2, 7]
def baseStart_740169 : Nat := 118140960795 + 740169 * 2 ^ 59
def prefixEnd_740169 : Nat := 4983230072969 + 3 ^ 40 * 740169 * 2
def baseEnd_740169 : Nat := 28152775004282949561743

theorem tailTrace_740169 : CollatzResearch.WordTrace tailWord_740169 prefixEnd_740169 28152775004282949561743 := by
  unfold tailWord_740169
  simp only [CollatzResearch.WordTrace]
  refine ⟨26996181255501598646231561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17997454170334399097487707 26996181255501598646231561)
  ·
    refine ⟨20247135941626198984673671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26996181255501598646231561 20247135941626198984673671)
    ·
      refine ⟨30370703912439298477010507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20247135941626198984673671 30370703912439298477010507)
      ·
        refine ⟨45556055868658947715515761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30370703912439298477010507 45556055868658947715515761)
        ·
          refine ⟨34167041901494210786636821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45556055868658947715515761 34167041901494210786636821)
          ·
            refine ⟨1601580089132541130623601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34167041901494210786636821 1601580089132541130623601)
            ·
              refine ⟨1201185066849405847967701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601580089132541130623601 1201185066849405847967701)
              ·
                refine ⟨28152775004282949561743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1201185066849405847967701 28152775004282949561743)
                ·
                  rfl

theorem cell22_740169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 7].length) (baseStart_740169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740169 prefixEnd_740169 := by exact prefixLift 740169
  have htrace : WordTrace (prefixWord ++ tailWord_740169) baseStart_740169 baseEnd_740169 := by
    simpa [prefixWord, tailWord_740169, baseEnd_740169] using wordTrace_append hprefix tailTrace_740169
  have hstable : (prefixWord ++ tailWord_740169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740169).length < 2 ^ (prefixWord ++ tailWord_740169).sum := by decide
  have hdescent : baseEnd_740169 < baseStart_740169 := by decide
  rcases family_descends (prefixWord ++ tailWord_740169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740188 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_740188 : Nat := 118140960795 + 740188 * 2 ^ 59
def prefixEnd_740188 : Nat := 4983230072969 + 3 ^ 40 * 740188 * 2
def baseEnd_740188 : Nat := 253381479126836829830629

theorem tailTrace_740188 : CollatzResearch.WordTrace tailWord_740188 prefixEnd_740188 253381479126836829830629 := by
  unfold tailWord_740188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13498437121216382445586609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17997916161621843260782145 13498437121216382445586609)
  ·
    refine ⟨10123827840912286834189957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13498437121216382445586609 10123827840912286834189957)
    ·
      refine ⟨1898217720171053781410617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10123827840912286834189957 1898217720171053781410617)
      ·
        refine ⟨1423663290128290336057963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1898217720171053781410617 1423663290128290336057963)
        ·
          refine ⟨2135494935192435504086945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423663290128290336057963 2135494935192435504086945)
          ·
            refine ⟨1601621201394326628065209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135494935192435504086945 1601621201394326628065209)
            ·
              refine ⟨1201215901045744971048907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601621201394326628065209 1201215901045744971048907)
              ·
                refine ⟨1801823851568617456573361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201215901045744971048907 1801823851568617456573361)
                ·
                  refine ⟨1351367888676463092430021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1801823851568617456573361 1351367888676463092430021)
                  ·
                    refine ⟨253381479126836829830629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351367888676463092430021 253381479126836829830629)
                    ·
                      rfl

theorem cell22_740188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_740188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740188 prefixEnd_740188 := by exact prefixLift 740188
  have htrace : WordTrace (prefixWord ++ tailWord_740188) baseStart_740188 baseEnd_740188 := by
    simpa [prefixWord, tailWord_740188, baseEnd_740188] using wordTrace_append hprefix tailTrace_740188
  have hstable : (prefixWord ++ tailWord_740188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740188).length < 2 ^ (prefixWord ++ tailWord_740188).sum := by decide
  have hdescent : baseEnd_740188 < baseStart_740188 := by decide
  rcases family_descends (prefixWord ++ tailWord_740188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740229 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_740229 : Nat := 118140960795 + 740229 * 2 ^ 59
def prefixEnd_740229 : Nat := 4983230072969 + 3 ^ 40 * 740229 * 2
def baseEnd_740229 : Nat := 253395514264726389555503

theorem tailTrace_740229 : CollatzResearch.WordTrace tailWord_740229 prefixEnd_740229 253395514264726389555503 := by
  unfold tailWord_740229
  simp only [CollatzResearch.WordTrace]
  refine ⟨26998369635284228893415741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17998913090189485928943827 26998369635284228893415741)
  ·
    refine ⟨10124388613231585835030903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26998369635284228893415741 10124388613231585835030903)
    ·
      refine ⟨15186582919847378752546355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10124388613231585835030903 15186582919847378752546355)
      ·
        refine ⟨22779874379771068128819533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15186582919847378752546355 22779874379771068128819533)
        ·
          refine ⟨8542452892414150548307325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22779874379771068128819533 8542452892414150548307325)
          ·
            refine ⟨3203419834655306455615247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8542452892414150548307325 3203419834655306455615247)
            ·
              refine ⟨4805129751982959683422871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203419834655306455615247 4805129751982959683422871)
              ·
                refine ⟨7207694627974439525134307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805129751982959683422871 7207694627974439525134307)
                ·
                  refine ⟨10811541941961659287701461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7207694627974439525134307 10811541941961659287701461)
                  ·
                    refine ⟨253395514264726389555503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10811541941961659287701461 253395514264726389555503)
                    ·
                      rfl

theorem cell22_740229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_740229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740229 prefixEnd_740229 := by exact prefixLift 740229
  have htrace : WordTrace (prefixWord ++ tailWord_740229) baseStart_740229 baseEnd_740229 := by
    simpa [prefixWord, tailWord_740229, baseEnd_740229] using wordTrace_append hprefix tailTrace_740229
  have hstable : (prefixWord ++ tailWord_740229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740229).length < 2 ^ (prefixWord ++ tailWord_740229).sum := by decide
  have hdescent : baseEnd_740229 < baseStart_740229 := by decide
  rcases family_descends (prefixWord ++ tailWord_740229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740231 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 5]
def baseStart_740231 : Nat := 118140960795 + 740231 * 2 ^ 59
def prefixEnd_740231 : Nat := 4983230072969 + 3 ^ 40 * 740231 * 2
def baseEnd_740231 : Nat := 84465399635199683668499

theorem tailTrace_740231 : CollatzResearch.WordTrace tailWord_740231 prefixEnd_740231 84465399635199683668499 := by
  unfold tailWord_740231
  simp only [CollatzResearch.WordTrace]
  refine ⟨26998442581276983234988547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17998961720851322156659031 26998442581276983234988547)
  ·
    refine ⟨40497663871915474852482821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26998442581276983234988547 40497663871915474852482821)
    ·
      refine ⟨7593311975984151534840529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40497663871915474852482821 7593311975984151534840529)
      ·
        refine ⟨5694983981988113651130397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7593311975984151534840529 5694983981988113651130397)
        ·
          refine ⟨2135618993245542619173899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5694983981988113651130397 2135618993245542619173899)
          ·
            refine ⟨3203428489868313928760849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135618993245542619173899 3203428489868313928760849)
            ·
              refine ⟨2402571367401235446570637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3203428489868313928760849 2402571367401235446570637)
              ·
                refine ⟨900964262775463292463989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2402571367401235446570637 900964262775463292463989)
                ·
                  refine ⟨84465399635199683668499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 900964262775463292463989 84465399635199683668499)
                  ·
                    rfl

theorem cell22_740231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 5].length) (baseStart_740231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740231 prefixEnd_740231 := by exact prefixLift 740231
  have htrace : WordTrace (prefixWord ++ tailWord_740231) baseStart_740231 baseEnd_740231 := by
    simpa [prefixWord, tailWord_740231, baseEnd_740231] using wordTrace_append hprefix tailTrace_740231
  have hstable : (prefixWord ++ tailWord_740231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740231).length < 2 ^ (prefixWord ++ tailWord_740231).sum := by decide
  have hdescent : baseEnd_740231 < baseStart_740231 := by decide
  rcases family_descends (prefixWord ++ tailWord_740231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740252 : List Nat := [2, 2, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_740252 : Nat := 118140960795 + 740252 * 2 ^ 59
def prefixEnd_740252 : Nat := 4983230072969 + 3 ^ 40 * 740252 * 2
def baseEnd_740252 : Nat := 253403387634761996230433

theorem tailTrace_740252 : CollatzResearch.WordTrace tailWord_740252 prefixEnd_740252 253403387634761996230433 := by
  unfold tailWord_740252
  simp only [CollatzResearch.WordTrace]
  refine ⟨13499604257100451910751505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17999472342800602547668673 13499604257100451910751505)
  ·
    refine ⟨10124703192825338933063629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13499604257100451910751505 10124703192825338933063629)
    ·
      refine ⟨3796763697309502099898861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10124703192825338933063629 3796763697309502099898861)
      ·
        refine ⟨1423786386491063287462073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3796763697309502099898861 1423786386491063287462073)
        ·
          refine ⟨1067839789868297465596555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423786386491063287462073 1067839789868297465596555)
          ·
            refine ⟨1601759684802446198394833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067839789868297465596555 1601759684802446198394833)
            ·
              refine ⟨1201319763601834648796125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601759684802446198394833 1201319763601834648796125)
              ·
                refine ⟨450494911350687993298547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201319763601834648796125 450494911350687993298547)
                ·
                  refine ⟨675742367026031989947821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450494911350687993298547 675742367026031989947821)
                  ·
                    refine ⟨253403387634761996230433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675742367026031989947821 253403387634761996230433)
                    ·
                      rfl

theorem cell22_740252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_740252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740252 prefixEnd_740252 := by exact prefixLift 740252
  have htrace : WordTrace (prefixWord ++ tailWord_740252) baseStart_740252 baseEnd_740252 := by
    simpa [prefixWord, tailWord_740252, baseEnd_740252] using wordTrace_append hprefix tailTrace_740252
  have hstable : (prefixWord ++ tailWord_740252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740252).length < 2 ^ (prefixWord ++ tailWord_740252).sum := by decide
  have hdescent : baseEnd_740252 < baseStart_740252 := by decide
  rcases family_descends (prefixWord ++ tailWord_740252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740274 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_740274 : Nat := 118140960795 + 740274 * 2 ^ 59
def prefixEnd_740274 : Nat := 4983230072969 + 3 ^ 40 * 740274 * 2
def baseEnd_740274 : Nat := 253410918684361272180365

theorem tailTrace_740274 : CollatzResearch.WordTrace tailWord_740274 prefixEnd_740274 253410918684361272180365 := by
  unfold tailWord_740274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6750002730030300394700969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18000007280080801052535917 6750002730030300394700969)
  ·
    refine ⟨5062502047522725296025727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6750002730030300394700969 5062502047522725296025727)
    ·
      refine ⟨7593753071284087944038591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062502047522725296025727 7593753071284087944038591)
      ·
        refine ⟨11390629606926131916057887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7593753071284087944038591 11390629606926131916057887)
        ·
          refine ⟨17085944410389197874086831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11390629606926131916057887 17085944410389197874086831)
          ·
            refine ⟨25628916615583796811130247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17085944410389197874086831 25628916615583796811130247)
            ·
              refine ⟨38443374923375695216695371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25628916615583796811130247 38443374923375695216695371)
              ·
                refine ⟨57665062385063542825043057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38443374923375695216695371 57665062385063542825043057)
                ·
                  refine ⟨43248796788797657118782293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57665062385063542825043057 43248796788797657118782293)
                  ·
                    refine ⟨253410918684361272180365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43248796788797657118782293 253410918684361272180365)
                    ·
                      rfl

theorem cell22_740274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_740274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740274 prefixEnd_740274 := by exact prefixLift 740274
  have htrace : WordTrace (prefixWord ++ tailWord_740274) baseStart_740274 baseEnd_740274 := by
    simpa [prefixWord, tailWord_740274, baseEnd_740274] using wordTrace_append hprefix tailTrace_740274
  have hstable : (prefixWord ++ tailWord_740274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740274).length < 2 ^ (prefixWord ++ tailWord_740274).sum := by decide
  have hdescent : baseEnd_740274 < baseStart_740274 := by decide
  rcases family_descends (prefixWord ++ tailWord_740274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740308 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_740308 : Nat := 118140960795 + 740308 * 2 ^ 59
def prefixEnd_740308 : Nat := 4983230072969 + 3 ^ 40 * 740308 * 2
def baseEnd_740308 : Nat := 253422557579196516830261

theorem tailTrace_740308 : CollatzResearch.WordTrace tailWord_740308 prefixEnd_740308 253422557579196516830261 := by
  unfold tailWord_740308
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500625500999012692770789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18000834001332016923694385 13500625500999012692770789)
  ·
    refine ⟨2531367281437314879894523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13500625500999012692770789 2531367281437314879894523)
    ·
      refine ⟨3797050922155972319841785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531367281437314879894523 3797050922155972319841785)
      ·
        refine ⟨2847788191616979239881339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3797050922155972319841785 2847788191616979239881339)
        ·
          refine ⟨4271682287425468859822009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847788191616979239881339 4271682287425468859822009)
          ·
            refine ⟨3203761715569101644866507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4271682287425468859822009 3203761715569101644866507)
            ·
              refine ⟨4805642573353652467299761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203761715569101644866507 4805642573353652467299761)
              ·
                refine ⟨3604231930015239350474821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4805642573353652467299761 3604231930015239350474821)
                ·
                  refine ⟨675793486877857378214029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3604231930015239350474821 675793486877857378214029)
                  ·
                    refine ⟨253422557579196516830261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675793486877857378214029 253422557579196516830261)
                    ·
                      rfl

theorem cell22_740308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_740308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740308 prefixEnd_740308 := by exact prefixLift 740308
  have htrace : WordTrace (prefixWord ++ tailWord_740308) baseStart_740308 baseEnd_740308 := by
    simpa [prefixWord, tailWord_740308, baseEnd_740308] using wordTrace_append hprefix tailTrace_740308
  have hstable : (prefixWord ++ tailWord_740308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740308).length < 2 ^ (prefixWord ++ tailWord_740308).sum := by decide
  have hdescent : baseEnd_740308 < baseStart_740308 := by decide
  rcases family_descends (prefixWord ++ tailWord_740308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740342 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_740342 : Nat := 118140960795 + 740342 * 2 ^ 59
def prefixEnd_740342 : Nat := 4983230072969 + 3 ^ 40 * 740342 * 2
def baseEnd_740342 : Nat := 253434196474031761480157

theorem tailTrace_740342 : CollatzResearch.WordTrace tailWord_740342 prefixEnd_740342 253434196474031761480157 := by
  unfold tailWord_740342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687655692742178074517455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18001660722583232794852853 1687655692742178074517455)
  ·
    refine ⟨2531483539113267111776183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687655692742178074517455 2531483539113267111776183)
    ·
      refine ⟨3797225308669900667664275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531483539113267111776183 3797225308669900667664275)
      ·
        refine ⟨5695837963004851001496413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797225308669900667664275 5695837963004851001496413)
        ·
          refine ⟨2135939236126819125561155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5695837963004851001496413 2135939236126819125561155)
          ·
            refine ⟨3203908854190228688341733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135939236126819125561155 3203908854190228688341733)
            ·
              refine ⟨600732910160667879064075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3203908854190228688341733 600732910160667879064075)
              ·
                refine ⟨901099365241001818596113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600732910160667879064075 901099365241001818596113)
                ·
                  refine ⟨675824523930751363947085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 901099365241001818596113 675824523930751363947085)
                  ·
                    refine ⟨253434196474031761480157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675824523930751363947085 253434196474031761480157)
                    ·
                      rfl

theorem cell22_740342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_740342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740342 prefixEnd_740342 := by exact prefixLift 740342
  have htrace : WordTrace (prefixWord ++ tailWord_740342) baseStart_740342 baseEnd_740342 := by
    simpa [prefixWord, tailWord_740342, baseEnd_740342] using wordTrace_append hprefix tailTrace_740342
  have hstable : (prefixWord ++ tailWord_740342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740342).length < 2 ^ (prefixWord ++ tailWord_740342).sum := by decide
  have hdescent : baseEnd_740342 < baseStart_740342 := by decide
  rcases family_descends (prefixWord ++ tailWord_740342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740383 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 5]
def baseStart_740383 : Nat := 118140960795 + 740383 * 2 ^ 59
def prefixEnd_740383 : Nat := 4983230072969 + 3 ^ 40 * 740383 * 2
def baseEnd_740383 : Nat := 84482743870640440401677

theorem tailTrace_740383 : CollatzResearch.WordTrace tailWord_740383 prefixEnd_740383 84482743870640440401677 := by
  unfold tailWord_740383
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003986476726313194521803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18002657651150875463014535 27003986476726313194521803)
  ·
    refine ⟨40505979715089469791782705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27003986476726313194521803 40505979715089469791782705)
    ·
      refine ⟨30379484786317102343837029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40505979715089469791782705 30379484786317102343837029)
      ·
        refine ⟨5696153397434456689469443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30379484786317102343837029 5696153397434456689469443)
        ·
          refine ⟨8544230096151685034204165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696153397434456689469443 8544230096151685034204165)
          ·
            refine ⟨1602043143028440943913281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8544230096151685034204165 1602043143028440943913281)
            ·
              refine ⟨1201532357271330707934961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602043143028440943913281 1201532357271330707934961)
              ·
                refine ⟨901149267953498030951221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201532357271330707934961 901149267953498030951221)
                ·
                  refine ⟨84482743870640440401677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 901149267953498030951221 84482743870640440401677)
                  ·
                    rfl

theorem cell22_740383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 5].length) (baseStart_740383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740383 prefixEnd_740383 := by exact prefixLift 740383
  have htrace : WordTrace (prefixWord ++ tailWord_740383) baseStart_740383 baseEnd_740383 := by
    simpa [prefixWord, tailWord_740383, baseEnd_740383] using wordTrace_append hprefix tailTrace_740383
  have hstable : (prefixWord ++ tailWord_740383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740383).length < 2 ^ (prefixWord ++ tailWord_740383).sum := by decide
  have hdescent : baseEnd_740383 < baseStart_740383 := by decide
  rcases family_descends (prefixWord ++ tailWord_740383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740387 : List Nat := [1, 1, 1, 4, 3, 2, 4, 2, 1, 3]
def baseStart_740387 : Nat := 118140960795 + 740387 * 2 ^ 59
def prefixEnd_740387 : Nat := 4983230072969 + 3 ^ 40 * 740387 * 2
def baseEnd_740387 : Nat := 253449600893666644105019

theorem tailTrace_740387 : CollatzResearch.WordTrace tailWord_740387 prefixEnd_740387 253449600893666644105019 := by
  unfold tailWord_740387
  simp only [CollatzResearch.WordTrace]
  refine ⟨27004132368711821877667415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18002754912474547918444943 27004132368711821877667415)
  ·
    refine ⟨40506198553067732816501123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27004132368711821877667415 40506198553067732816501123)
    ·
      refine ⟨60759297829601599224751685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40506198553067732816501123 60759297829601599224751685)
      ·
        refine ⟨11392368343050299854640941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60759297829601599224751685 11392368343050299854640941)
        ·
          refine ⟨4272138128643862445490353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11392368343050299854640941 4272138128643862445490353)
          ·
            refine ⟨3204103596482896834117765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272138128643862445490353 3204103596482896834117765)
            ·
              refine ⟨600769424340543156397081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3204103596482896834117765 600769424340543156397081)
              ·
                refine ⟨450577068255407367297811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600769424340543156397081 450577068255407367297811)
                ·
                  refine ⟨675865602383111050946717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450577068255407367297811 675865602383111050946717)
                  ·
                    refine ⟨253449600893666644105019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675865602383111050946717 253449600893666644105019)
                    ·
                      rfl

theorem cell22_740387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 3].length) (baseStart_740387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740387 prefixEnd_740387 := by exact prefixLift 740387
  have htrace : WordTrace (prefixWord ++ tailWord_740387) baseStart_740387 baseEnd_740387 := by
    simpa [prefixWord, tailWord_740387, baseEnd_740387] using wordTrace_append hprefix tailTrace_740387
  have hstable : (prefixWord ++ tailWord_740387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740387).length < 2 ^ (prefixWord ++ tailWord_740387).sum := by decide
  have hdescent : baseEnd_740387 < baseStart_740387 := by decide
  rcases family_descends (prefixWord ++ tailWord_740387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740396 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_740396 : Nat := 118140960795 + 740396 * 2 ^ 59
def prefixEnd_740396 : Nat := 4983230072969 + 3 ^ 40 * 740396 * 2
def baseEnd_740396 : Nat := 253452681777593620629991

theorem tailTrace_740396 : CollatzResearch.WordTrace tailWord_740396 prefixEnd_740396 253452681777593620629991 := by
  unfold tailWord_740396
  simp only [CollatzResearch.WordTrace]
  refine ⟨13502230312839608207372521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18002973750452810943163361 13502230312839608207372521)
  ·
    refine ⟨10126672734629706155529391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13502230312839608207372521 10126672734629706155529391)
    ·
      refine ⟨15190009101944559233294087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10126672734629706155529391 15190009101944559233294087)
      ·
        refine ⟨22785013652916838849941131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15190009101944559233294087 22785013652916838849941131)
        ·
          refine ⟨34177520479375258274911697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22785013652916838849941131 34177520479375258274911697)
          ·
            refine ⟨25633140359531443706183773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34177520479375258274911697 25633140359531443706183773)
            ·
              refine ⟨9612427634824291389818915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25633140359531443706183773 9612427634824291389818915)
              ·
                refine ⟨14418641452236437084728373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9612427634824291389818915 14418641452236437084728373)
                ·
                  refine ⟨1351747636147165976693285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14418641452236437084728373 1351747636147165976693285)
                  ·
                    refine ⟨253452681777593620629991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351747636147165976693285 253452681777593620629991)
                    ·
                      rfl

theorem cell22_740396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_740396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740396 prefixEnd_740396 := by exact prefixLift 740396
  have htrace : WordTrace (prefixWord ++ tailWord_740396) baseStart_740396 baseEnd_740396 := by
    simpa [prefixWord, tailWord_740396, baseEnd_740396] using wordTrace_append hprefix tailTrace_740396
  have hstable : (prefixWord ++ tailWord_740396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740396).length < 2 ^ (prefixWord ++ tailWord_740396).sum := by decide
  have hdescent : baseEnd_740396 < baseStart_740396 := by decide
  rcases family_descends (prefixWord ++ tailWord_740396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740398 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_740398 : Nat := 118140960795 + 740398 * 2 ^ 59
def prefixEnd_740398 : Nat := 4983230072969 + 3 ^ 40 * 740398 * 2
def baseEnd_740398 : Nat := 253453366418466282079985

theorem tailTrace_740398 : CollatzResearch.WordTrace tailWord_740398 prefixEnd_740398 253453366418466282079985 := by
  unfold tailWord_740398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375566696458996344539731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18003022381114647170878565 3375566696458996344539731)
  ·
    refine ⟨5063350044688494516809597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375566696458996344539731 5063350044688494516809597)
    ·
      refine ⟨1898756266758185443803599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5063350044688494516809597 1898756266758185443803599)
      ·
        refine ⟨2848134400137278165705399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898756266758185443803599 2848134400137278165705399)
        ·
          refine ⟨4272201600205917248558099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848134400137278165705399 4272201600205917248558099)
          ·
            refine ⟨6408302400308875872837149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272201600205917248558099 6408302400308875872837149)
            ·
              refine ⟨2403113400115828452313931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6408302400308875872837149 2403113400115828452313931)
              ·
                refine ⟨3604670100173742678470897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403113400115828452313931 3604670100173742678470897)
                ·
                  refine ⟨2703502575130307008853173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604670100173742678470897 2703502575130307008853173)
                  ·
                    refine ⟨253453366418466282079985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2703502575130307008853173 253453366418466282079985)
                    ·
                      rfl

theorem cell22_740398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_740398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740398 prefixEnd_740398 := by exact prefixLift 740398
  have htrace : WordTrace (prefixWord ++ tailWord_740398) baseStart_740398 baseEnd_740398 := by
    simpa [prefixWord, tailWord_740398, baseEnd_740398] using wordTrace_append hprefix tailTrace_740398
  have hstable : (prefixWord ++ tailWord_740398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740398).length < 2 ^ (prefixWord ++ tailWord_740398).sum := by decide
  have hdescent : baseEnd_740398 < baseStart_740398 := by decide
  rcases family_descends (prefixWord ++ tailWord_740398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740413 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_740413 : Nat := 118140960795 + 740413 * 2 ^ 59
def prefixEnd_740413 : Nat := 4983230072969 + 3 ^ 40 * 740413 * 2
def baseEnd_740413 : Nat := 253458501225011242954939

theorem tailTrace_740413 : CollatzResearch.WordTrace tailWord_740413 prefixEnd_740413 253458501225011242954939 := by
  unfold tailWord_740413
  simp only [CollatzResearch.WordTrace]
  refine ⟨27005080666617628318113893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18003387111078418878742595 27005080666617628318113893)
  ·
    refine ⟨5063452624990805309646355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27005080666617628318113893 5063452624990805309646355)
    ·
      refine ⟨7595178937486207964469533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063452624990805309646355 7595178937486207964469533)
      ·
        refine ⟨2848192101557327986676075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7595178937486207964469533 2848192101557327986676075)
        ·
          refine ⟨4272288152335991980014113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848192101557327986676075 4272288152335991980014113)
          ·
            refine ⟨3204216114251993985010585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272288152335991980014113 3204216114251993985010585)
            ·
              refine ⟨2403162085688995488757939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204216114251993985010585 2403162085688995488757939)
              ·
                refine ⟨3604743128533493233136909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403162085688995488757939 3604743128533493233136909)
                ·
                  refine ⟨1351778673200059962426341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3604743128533493233136909 1351778673200059962426341)
                  ·
                    refine ⟨253458501225011242954939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351778673200059962426341 253458501225011242954939)
                    ·
                      rfl

theorem cell22_740413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_740413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740413 prefixEnd_740413 := by exact prefixLift 740413
  have htrace : WordTrace (prefixWord ++ tailWord_740413) baseStart_740413 baseEnd_740413 := by
    simpa [prefixWord, tailWord_740413, baseEnd_740413] using wordTrace_append hprefix tailTrace_740413
  have hstable : (prefixWord ++ tailWord_740413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740413).length < 2 ^ (prefixWord ++ tailWord_740413).sum := by decide
  have hdescent : baseEnd_740413 < baseStart_740413 := by decide
  rcases family_descends (prefixWord ++ tailWord_740413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740458 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_740458 : Nat := 118140960795 + 740458 * 2 ^ 59
def prefixEnd_740458 : Nat := 4983230072969 + 3 ^ 40 * 740458 * 2
def baseEnd_740458 : Nat := 253473905644646125579801

theorem tailTrace_740458 : CollatzResearch.WordTrace tailWord_740458 prefixEnd_740458 253473905644646125579801 := by
  unfold tailWord_740458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751680487863650250875507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18004481300969734002334685 6751680487863650250875507)
  ·
    refine ⟨10127520731795475376313261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6751680487863650250875507 10127520731795475376313261)
    ·
      refine ⟨3797820274423303266117473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10127520731795475376313261 3797820274423303266117473)
      ·
        refine ⟨2848365205817477449588105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3797820274423303266117473 2848365205817477449588105)
        ·
          refine ⟨2136273904363108087191079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848365205817477449588105 2136273904363108087191079)
          ·
            refine ⟨3204410856544662130786619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136273904363108087191079 3204410856544662130786619)
            ·
              refine ⟨4806616284816993196179929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204410856544662130786619 4806616284816993196179929)
              ·
                refine ⟨3604962213612744897134947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806616284816993196179929 3604962213612744897134947)
                ·
                  refine ⟨5407443320419117345702421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604962213612744897134947 5407443320419117345702421)
                  ·
                    refine ⟨253473905644646125579801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5407443320419117345702421 253473905644646125579801)
                    ·
                      rfl

theorem cell22_740458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_740458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740458 prefixEnd_740458 := by exact prefixLift 740458
  have htrace : WordTrace (prefixWord ++ tailWord_740458) baseStart_740458 baseEnd_740458 := by
    simpa [prefixWord, tailWord_740458, baseEnd_740458] using wordTrace_append hprefix tailTrace_740458
  have hstable : (prefixWord ++ tailWord_740458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740458).length < 2 ^ (prefixWord ++ tailWord_740458).sum := by decide
  have hdescent : baseEnd_740458 < baseStart_740458 := by decide
  rcases family_descends (prefixWord ++ tailWord_740458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740471 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 2, 7]
def baseStart_740471 : Nat := 118140960795 + 740471 * 2 ^ 59
def prefixEnd_740471 : Nat := 4983230072969 + 3 ^ 40 * 740471 * 2
def baseEnd_740471 : Nat := 253478355810318425004761

theorem tailTrace_740471 : CollatzResearch.WordTrace tailWord_740471 prefixEnd_740471 253478355810318425004761 := by
  unfold tailWord_740471
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007196100407504223725267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18004797400271669482483511 27007196100407504223725267)
  ·
    refine ⟨40510794150611256335587901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27007196100407504223725267 40510794150611256335587901)
    ·
      refine ⟨15191547806479221125845463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40510794150611256335587901 15191547806479221125845463)
      ·
        refine ⟨22787321709718831688768195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191547806479221125845463 22787321709718831688768195)
        ·
          refine ⟨34180982564578247533152293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22787321709718831688768195 34180982564578247533152293)
          ·
            refine ⟨6408934230858421412466055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34180982564578247533152293 6408934230858421412466055)
            ·
              refine ⟨9613401346287632118699083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408934230858421412466055 9613401346287632118699083)
              ·
                refine ⟨14420102019431448178048625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9613401346287632118699083 14420102019431448178048625)
                ·
                  refine ⟨10815076514573586133536469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14420102019431448178048625 10815076514573586133536469)
                  ·
                    refine ⟨253478355810318425004761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10815076514573586133536469 253478355810318425004761)
                    ·
                      rfl

theorem cell22_740471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_740471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740471 prefixEnd_740471 := by exact prefixLift 740471
  have htrace : WordTrace (prefixWord ++ tailWord_740471) baseStart_740471 baseEnd_740471 := by
    simpa [prefixWord, tailWord_740471, baseEnd_740471] using wordTrace_append hprefix tailTrace_740471
  have hstable : (prefixWord ++ tailWord_740471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740471).length < 2 ^ (prefixWord ++ tailWord_740471).sum := by decide
  have hdescent : baseEnd_740471 < baseStart_740471 := by decide
  rcases family_descends (prefixWord ++ tailWord_740471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740473 : List Nat := [1, 2, 1, 3, 5, 1, 1, 8]
def baseStart_740473 : Nat := 118140960795 + 740473 * 2 ^ 59
def prefixEnd_740473 : Nat := 4983230072969 + 3 ^ 40 * 740473 * 2
def baseEnd_740473 : Nat := 28164337827910120717195

theorem tailTrace_740473 : CollatzResearch.WordTrace tailWord_740473 prefixEnd_740473 28164337827910120717195 := by
  unfold tailWord_740473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007269046400258565298073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18004846030933505710198715 27007269046400258565298073)
  ·
    refine ⟨20255451784800193923973555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27007269046400258565298073 20255451784800193923973555)
    ·
      refine ⟨30383177677200290885960333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20255451784800193923973555 30383177677200290885960333)
      ·
        refine ⟨11393691628950109082235125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30383177677200290885960333 11393691628950109082235125)
        ·
          refine ⟨1068158590214072726459543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11393691628950109082235125 1068158590214072726459543)
          ·
            refine ⟨1602237885321109089689315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068158590214072726459543 1602237885321109089689315)
            ·
              refine ⟨2403356827981663634533973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602237885321109089689315 2403356827981663634533973)
              ·
                refine ⟨28164337827910120717195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2403356827981663634533973 28164337827910120717195)
                ·
                  rfl

theorem cell22_740473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 8].length) (baseStart_740473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740473 prefixEnd_740473 := by exact prefixLift 740473
  have htrace : WordTrace (prefixWord ++ tailWord_740473) baseStart_740473 baseEnd_740473 := by
    simpa [prefixWord, tailWord_740473, baseEnd_740473] using wordTrace_append hprefix tailTrace_740473
  have hstable : (prefixWord ++ tailWord_740473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740473).length < 2 ^ (prefixWord ++ tailWord_740473).sum := by decide
  have hdescent : baseEnd_740473 < baseStart_740473 := by decide
  rcases family_descends (prefixWord ++ tailWord_740473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740511 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 2, 3]
def baseStart_740511 : Nat := 118140960795 + 740511 * 2 ^ 59
def prefixEnd_740511 : Nat := 4983230072969 + 3 ^ 40 * 740511 * 2
def baseEnd_740511 : Nat := 253492048627771654004639

theorem tailTrace_740511 : CollatzResearch.WordTrace tailWord_740511 prefixEnd_740511 253492048627771654004639 := by
  unfold tailWord_740511
  simp only [CollatzResearch.WordTrace]
  refine ⟨27008655020262591055181387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18005770013508394036787591 27008655020262591055181387)
  ·
    refine ⟨40512982530393886582772081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27008655020262591055181387 40512982530393886582772081)
    ·
      refine ⟨30384736897795414937079061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40512982530393886582772081 30384736897795414937079061)
      ·
        refine ⟨1424284542084160075175581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30384736897795414937079061 1424284542084160075175581)
        ·
          refine ⟨534106703281560028190843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1424284542084160075175581 534106703281560028190843)
          ·
            refine ⟨801160054922340042286265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534106703281560028190843 801160054922340042286265)
            ·
              refine ⟨600870041191755031714699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801160054922340042286265 600870041191755031714699)
              ·
                refine ⟨901305061787632547572049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600870041191755031714699 901305061787632547572049)
                ·
                  refine ⟨675978796340724410679037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 901305061787632547572049 675978796340724410679037)
                  ·
                    refine ⟨253492048627771654004639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 675978796340724410679037 253492048627771654004639)
                    ·
                      rfl

theorem cell22_740511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_740511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740511 prefixEnd_740511 := by exact prefixLift 740511
  have htrace : WordTrace (prefixWord ++ tailWord_740511) baseStart_740511 baseEnd_740511 := by
    simpa [prefixWord, tailWord_740511, baseEnd_740511] using wordTrace_append hprefix tailTrace_740511
  have hstable : (prefixWord ++ tailWord_740511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740511).length < 2 ^ (prefixWord ++ tailWord_740511).sum := by decide
  have hdescent : baseEnd_740511 < baseStart_740511 := by decide
  rcases family_descends (prefixWord ++ tailWord_740511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740565 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_740565 : Nat := 118140960795 + 740565 * 2 ^ 59
def prefixEnd_740565 : Nat := 4983230072969 + 3 ^ 40 * 740565 * 2
def baseEnd_740565 : Nat := 253510533931333513154473

theorem tailTrace_740565 : CollatzResearch.WordTrace tailWord_740565 prefixEnd_740565 253510533931333513154473 := by
  unfold tailWord_740565
  simp only [CollatzResearch.WordTrace]
  refine ⟨27010624562066958277647149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18007083041377972185098099 27010624562066958277647149)
  ·
    refine ⟨10128984210775109354117681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27010624562066958277647149 10128984210775109354117681)
    ·
      refine ⟨7596738158081332015588261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10128984210775109354117681 7596738158081332015588261)
      ·
        refine ⟨1424388404640249752922799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7596738158081332015588261 1424388404640249752922799)
        ·
          refine ⟨2136582606960374629384199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424388404640249752922799 2136582606960374629384199)
          ·
            refine ⟨3204873910440561944076299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136582606960374629384199 3204873910440561944076299)
            ·
              refine ⟨4807310865660842916114449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204873910440561944076299 4807310865660842916114449)
              ·
                refine ⟨3605483149245632187085837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807310865660842916114449 3605483149245632187085837)
                ·
                  refine ⟨1352056180967112070157189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605483149245632187085837 1352056180967112070157189)
                  ·
                    refine ⟨253510533931333513154473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352056180967112070157189 253510533931333513154473)
                    ·
                      rfl

theorem cell22_740565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_740565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740565 prefixEnd_740565 := by exact prefixLift 740565
  have htrace : WordTrace (prefixWord ++ tailWord_740565) baseStart_740565 baseEnd_740565 := by
    simpa [prefixWord, tailWord_740565, baseEnd_740565] using wordTrace_append hprefix tailTrace_740565
  have hstable : (prefixWord ++ tailWord_740565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740565).length < 2 ^ (prefixWord ++ tailWord_740565).sum := by decide
  have hdescent : baseEnd_740565 < baseStart_740565 := by decide
  rcases family_descends (prefixWord ++ tailWord_740565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740612 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_740612 : Nat := 118140960795 + 740612 * 2 ^ 59
def prefixEnd_740612 : Nat := 4983230072969 + 3 ^ 40 * 740612 * 2
def baseEnd_740612 : Nat := 253526622991841057229329

theorem tailTrace_740612 : CollatzResearch.WordTrace tailWord_740612 prefixEnd_740612 253526622991841057229329 := by
  unfold tailWord_740612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506169396448342652304045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18008225861931123536405393 13506169396448342652304045)
  ·
    refine ⟨5064813523668128494614017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13506169396448342652304045 5064813523668128494614017)
    ·
      refine ⟨3798610142751096370960513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5064813523668128494614017 3798610142751096370960513)
      ·
        refine ⟨2848957607063322278220385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3798610142751096370960513 2848957607063322278220385)
        ·
          refine ⟨2136718205297491708665289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848957607063322278220385 2136718205297491708665289)
          ·
            refine ⟨1602538653973118781498967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2136718205297491708665289 1602538653973118781498967)
            ·
              refine ⟨2403807980959678172248451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602538653973118781498967 2403807980959678172248451)
              ·
                refine ⟨3605711971439517258372677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403807980959678172248451 3605711971439517258372677)
                ·
                  refine ⟨676070994644909485944877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3605711971439517258372677 676070994644909485944877)
                  ·
                    refine ⟨253526622991841057229329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676070994644909485944877 253526622991841057229329)
                    ·
                      rfl

theorem cell22_740612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_740612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740612 prefixEnd_740612 := by exact prefixLift 740612
  have htrace : WordTrace (prefixWord ++ tailWord_740612) baseStart_740612 baseEnd_740612 := by
    simpa [prefixWord, tailWord_740612, baseEnd_740612] using wordTrace_append hprefix tailTrace_740612
  have hstable : (prefixWord ++ tailWord_740612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740612).length < 2 ^ (prefixWord ++ tailWord_740612).sum := by decide
  have hdescent : baseEnd_740612 < baseStart_740612 := by decide
  rcases family_descends (prefixWord ++ tailWord_740612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740670 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_740670 : Nat := 118140960795 + 740670 * 2 ^ 59
def prefixEnd_740670 : Nat := 4983230072969 + 3 ^ 40 * 740670 * 2
def baseEnd_740670 : Nat := 84515492525716079759717

theorem tailTrace_740670 : CollatzResearch.WordTrace tailWord_740670 prefixEnd_740670 84515492525716079759717 := by
  unfold tailWord_740670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376806778335820151277433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18009636151124374140146309 3376806778335820151277433)
  ·
    refine ⟨2532605083751865113458075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3376806778335820151277433 2532605083751865113458075)
    ·
      refine ⟨3798907625627797670187113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532605083751865113458075 3798907625627797670187113)
      ·
        refine ⟨2849180719220848252640335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3798907625627797670187113 2849180719220848252640335)
        ·
          refine ⟨4273771078831272378960503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849180719220848252640335 4273771078831272378960503)
          ·
            refine ⟨6410656618246908568440755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273771078831272378960503 6410656618246908568440755)
            ·
              refine ⟨9615984927370362852661133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410656618246908568440755 9615984927370362852661133)
              ·
                refine ⟨3605994347763886069747925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9615984927370362852661133 3605994347763886069747925)
                ·
                  refine ⟨84515492525716079759717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3605994347763886069747925 84515492525716079759717)
                  ·
                    rfl

theorem cell22_740670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_740670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740670 prefixEnd_740670 := by exact prefixLift 740670
  have htrace : WordTrace (prefixWord ++ tailWord_740670) baseStart_740670 baseEnd_740670 := by
    simpa [prefixWord, tailWord_740670, baseEnd_740670] using wordTrace_append hprefix tailTrace_740670
  have hstable : (prefixWord ++ tailWord_740670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740670).length < 2 ^ (prefixWord ++ tailWord_740670).sum := by decide
  have hdescent : baseEnd_740670 < baseStart_740670 := by decide
  rcases family_descends (prefixWord ++ tailWord_740670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740725 : List Nat := [1, 3, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_740725 : Nat := 118140960795 + 740725 * 2 ^ 59
def prefixEnd_740725 : Nat := 4983230072969 + 3 ^ 40 * 740725 * 2
def baseEnd_740725 : Nat := 253565305201146429153983

theorem tailTrace_740725 : CollatzResearch.WordTrace tailWord_740725 prefixEnd_740725 253565305201146429153983 := by
  unfold tailWord_740725
  simp only [CollatzResearch.WordTrace]
  refine ⟨27016460241487305603471629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18010973494324870402314419 27016460241487305603471629)
  ·
    refine ⟨10131172590557739601301861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27016460241487305603471629 10131172590557739601301861)
    ·
      refine ⟨1899594860729576175244099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10131172590557739601301861 1899594860729576175244099)
      ·
        refine ⟨2849392291094364262866149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899594860729576175244099 2849392291094364262866149)
        ·
          refine ⟨534261054580193299287403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2849392291094364262866149 534261054580193299287403)
          ·
            refine ⟨801391581870289948931105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534261054580193299287403 801391581870289948931105)
            ·
              refine ⟨601043686402717461698329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801391581870289948931105 601043686402717461698329)
              ·
                refine ⟨450782764802038096273747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601043686402717461698329 450782764802038096273747)
                ·
                  refine ⟨676174147203057144410621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450782764802038096273747 676174147203057144410621)
                  ·
                    refine ⟨253565305201146429153983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676174147203057144410621 253565305201146429153983)
                    ·
                      rfl

theorem cell22_740725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_740725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740725 prefixEnd_740725 := by exact prefixLift 740725
  have htrace : WordTrace (prefixWord ++ tailWord_740725) baseStart_740725 baseEnd_740725 := by
    simpa [prefixWord, tailWord_740725, baseEnd_740725] using wordTrace_append hprefix tailTrace_740725
  have hstable : (prefixWord ++ tailWord_740725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740725).length < 2 ^ (prefixWord ++ tailWord_740725).sum := by decide
  have hdescent : baseEnd_740725 < baseStart_740725 := by decide
  rcases family_descends (prefixWord ++ tailWord_740725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740732 : List Nat := [2, 2, 2, 1, 1, 1, 5, 4, 4]
def baseStart_740732 : Nat := 118140960795 + 740732 * 2 ^ 59
def prefixEnd_740732 : Nat := 4983230072969 + 3 ^ 40 * 740732 * 2
def baseEnd_740732 : Nat := 84522567148066914742987

theorem tailTrace_740732 : CollatzResearch.WordTrace tailWord_740732 prefixEnd_740732 84522567148066914742987 := by
  unfold tailWord_740732
  simp only [CollatzResearch.WordTrace]
  refine ⟨13508357776230972899488225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18011143701641297199317633 13508357776230972899488225)
  ·
    refine ⟨10131268332173229674616169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13508357776230972899488225 10131268332173229674616169)
    ·
      refine ⟨7598451249129922255962127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10131268332173229674616169 7598451249129922255962127)
      ·
        refine ⟨11397676873694883383943191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7598451249129922255962127 11397676873694883383943191)
        ·
          refine ⟨17096515310542325075914787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11397676873694883383943191 17096515310542325075914787)
          ·
            refine ⟨25644772965813487613872181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17096515310542325075914787 25644772965813487613872181)
            ·
              refine ⟨2404197465545014463800517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25644772965813487613872181 2404197465545014463800517)
              ·
                refine ⟨450787024789690211962597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2404197465545014463800517 450787024789690211962597)
                ·
                  refine ⟨84522567148066914742987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 450787024789690211962597 84522567148066914742987)
                  ·
                    rfl

theorem cell22_740732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_740732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740732 prefixEnd_740732 := by exact prefixLift 740732
  have htrace : WordTrace (prefixWord ++ tailWord_740732) baseStart_740732 baseEnd_740732 := by
    simpa [prefixWord, tailWord_740732, baseEnd_740732] using wordTrace_append hprefix tailTrace_740732
  have hstable : (prefixWord ++ tailWord_740732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740732).length < 2 ^ (prefixWord ++ tailWord_740732).sum := by decide
  have hdescent : baseEnd_740732 < baseStart_740732 := by decide
  rcases family_descends (prefixWord ++ tailWord_740732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740747 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 2, 3]
def baseStart_740747 : Nat := 118140960795 + 740747 * 2 ^ 59
def prefixEnd_740747 : Nat := 4983230072969 + 3 ^ 40 * 740747 * 2
def baseEnd_740747 : Nat := 253572836250745705103915

theorem tailTrace_740747 : CollatzResearch.WordTrace tailWord_740747 prefixEnd_740747 253572836250745705103915 := by
  unfold tailWord_740747
  simp only [CollatzResearch.WordTrace]
  refine ⟨27017262647407603360772495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18011508431605068907181663 27017262647407603360772495)
  ·
    refine ⟨40525893971111405041158743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27017262647407603360772495 40525893971111405041158743)
    ·
      refine ⟨60788840956667107561738115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40525893971111405041158743 60788840956667107561738115)
      ·
        refine ⟨91183261435000661342607173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60788840956667107561738115 91183261435000661342607173)
        ·
          refine ⟨17096861519062624001738845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91183261435000661342607173 17096861519062624001738845)
          ·
            refine ⟨6411323069648484000652067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17096861519062624001738845 6411323069648484000652067)
            ·
              refine ⟨9616984604472726000978101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6411323069648484000652067 9616984604472726000978101)
              ·
                refine ⟨901592306669318062591697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9616984604472726000978101 901592306669318062591697)
                ·
                  refine ⟨676194230001988546943773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 901592306669318062591697 676194230001988546943773)
                  ·
                    refine ⟨253572836250745705103915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676194230001988546943773 253572836250745705103915)
                    ·
                      rfl

theorem cell22_740747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 3].length) (baseStart_740747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740747 prefixEnd_740747 := by exact prefixLift 740747
  have htrace : WordTrace (prefixWord ++ tailWord_740747) baseStart_740747 baseEnd_740747 := by
    simpa [prefixWord, tailWord_740747, baseEnd_740747] using wordTrace_append hprefix tailTrace_740747
  have hstable : (prefixWord ++ tailWord_740747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740747).length < 2 ^ (prefixWord ++ tailWord_740747).sum := by decide
  have hdescent : baseEnd_740747 < baseStart_740747 := by decide
  rcases family_descends (prefixWord ++ tailWord_740747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740781 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_740781 : Nat := 118140960795 + 740781 * 2 ^ 59
def prefixEnd_740781 : Nat := 4983230072969 + 3 ^ 40 * 740781 * 2
def baseEnd_740781 : Nat := 253584475145580949753811

theorem tailTrace_740781 : CollatzResearch.WordTrace tailWord_740781 prefixEnd_740781 253584475145580949753811 := by
  unfold tailWord_740781
  simp only [CollatzResearch.WordTrace]
  refine ⟨27018502729284427167510197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18012335152856284778340131 27018502729284427167510197)
  ·
    refine ⟨2532984630870415046954081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27018502729284427167510197 2532984630870415046954081)
    ·
      refine ⟨1899738473152811285215561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2532984630870415046954081 1899738473152811285215561)
      ·
        refine ⟨1424803854864608463911671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1899738473152811285215561 1424803854864608463911671)
        ·
          refine ⟨2137205782296912695867507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424803854864608463911671 2137205782296912695867507)
          ·
            refine ⟨3205808673445369043801261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137205782296912695867507 3205808673445369043801261)
            ·
              refine ⟨1202178252542013391425473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3205808673445369043801261 1202178252542013391425473)
              ·
                refine ⟨901633689406510043569105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202178252542013391425473 901633689406510043569105)
                ·
                  refine ⟨676225267054882532676829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 901633689406510043569105 676225267054882532676829)
                  ·
                    refine ⟨253584475145580949753811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676225267054882532676829 253584475145580949753811)
                    ·
                      rfl

theorem cell22_740781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_740781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740781 prefixEnd_740781 := by exact prefixLift 740781
  have htrace : WordTrace (prefixWord ++ tailWord_740781) baseStart_740781 baseEnd_740781 := by
    simpa [prefixWord, tailWord_740781, baseEnd_740781] using wordTrace_append hprefix tailTrace_740781
  have hstable : (prefixWord ++ tailWord_740781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740781).length < 2 ^ (prefixWord ++ tailWord_740781).sum := by decide
  have hdescent : baseEnd_740781 < baseStart_740781 := by decide
  rcases family_descends (prefixWord ++ tailWord_740781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740792 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 3, 3]
def baseStart_740792 : Nat := 118140960795 + 740792 * 2 ^ 59
def prefixEnd_740792 : Nat := 4983230072969 + 3 ^ 40 * 740792 * 2
def baseEnd_740792 : Nat := 253588240670380587728777

theorem tailTrace_740792 : CollatzResearch.WordTrace tailWord_740792 prefixEnd_740792 253588240670380587728777 := by
  unfold tailWord_740792
  simp only [CollatzResearch.WordTrace]
  refine ⟨13509451966122288023080315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18012602621496384030773753 13509451966122288023080315)
  ·
    refine ⟨20264177949183432034620473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13509451966122288023080315 20264177949183432034620473)
    ·
      refine ⟨15198133461887574025965355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20264177949183432034620473 15198133461887574025965355)
      ·
        refine ⟨22797200192831361038948033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15198133461887574025965355 22797200192831361038948033)
        ·
          refine ⟨17097900144623520779211025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22797200192831361038948033 17097900144623520779211025)
          ·
            refine ⟨12823425108467640584408269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17097900144623520779211025 12823425108467640584408269)
            ·
              refine ⟨4808784415675365219153101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12823425108467640584408269 4808784415675365219153101)
              ·
                refine ⟨1803294155878261957182413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4808784415675365219153101 1803294155878261957182413)
                ·
                  refine ⟨676235308454348233943405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1803294155878261957182413 676235308454348233943405)
                  ·
                    refine ⟨253588240670380587728777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676235308454348233943405 253588240670380587728777)
                    ·
                      rfl

theorem cell22_740792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_740792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740792 prefixEnd_740792 := by exact prefixLift 740792
  have htrace : WordTrace (prefixWord ++ tailWord_740792) baseStart_740792 baseEnd_740792 := by
    simpa [prefixWord, tailWord_740792, baseEnd_740792] using wordTrace_append hprefix tailTrace_740792
  have hstable : (prefixWord ++ tailWord_740792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740792).length < 2 ^ (prefixWord ++ tailWord_740792).sum := by decide
  have hdescent : baseEnd_740792 < baseStart_740792 := by decide
  rcases family_descends (prefixWord ++ tailWord_740792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740826 : List Nat := [3, 1, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_740826 : Nat := 118140960795 + 740826 * 2 ^ 59
def prefixEnd_740826 : Nat := 4983230072969 + 3 ^ 40 * 740826 * 2
def baseEnd_740826 : Nat := 253599879565215832378673

theorem tailTrace_740826 : CollatzResearch.WordTrace tailWord_740826 prefixEnd_740826 253599879565215832378673 := by
  unfold tailWord_740826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6755036003530349963224583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18013429342747599901932221 6755036003530349963224583)
  ·
    refine ⟨10132554005295524944836875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6755036003530349963224583 10132554005295524944836875)
    ·
      refine ⟨15198831007943287417255313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10132554005295524944836875 15198831007943287417255313)
      ·
        refine ⟨11399123255957465562941485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15198831007943287417255313 11399123255957465562941485)
        ·
          refine ⟨4274671220984049586103057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11399123255957465562941485 4274671220984049586103057)
          ·
            refine ⟨3206003415738037189577293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274671220984049586103057 3206003415738037189577293)
            ·
              refine ⟨1202251280901763946091485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3206003415738037189577293 1202251280901763946091485)
              ·
                refine ⟨450844230338161479784307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1202251280901763946091485 450844230338161479784307)
                ·
                  refine ⟨676266345507242219676461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450844230338161479784307 676266345507242219676461)
                  ·
                    refine ⟨253599879565215832378673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676266345507242219676461 253599879565215832378673)
                    ·
                      rfl

theorem cell22_740826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_740826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740826 prefixEnd_740826 := by exact prefixLift 740826
  have htrace : WordTrace (prefixWord ++ tailWord_740826) baseStart_740826 baseEnd_740826 := by
    simpa [prefixWord, tailWord_740826, baseEnd_740826] using wordTrace_append hprefix tailTrace_740826
  have hstable : (prefixWord ++ tailWord_740826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740826).length < 2 ^ (prefixWord ++ tailWord_740826).sum := by decide
  have hdescent : baseEnd_740826 < baseStart_740826 := by decide
  rcases family_descends (prefixWord ++ tailWord_740826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740929 : List Nat := [1, 2, 5, 1, 1, 1, 5, 6]
def baseStart_740929 : Nat := 118140960795 + 740929 * 2 ^ 59
def prefixEnd_740929 : Nat := 4983230072969 + 3 ^ 40 * 740929 * 2
def baseEnd_740929 : Nat := 28181682063350877450373

theorem tailTrace_740929 : CollatzResearch.WordTrace tailWord_740929 prefixEnd_740929 28181682063350877450373 := by
  unfold tailWord_740929
  simp only [CollatzResearch.WordTrace]
  refine ⟨27023900732748248443897841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18015933821832165629265227 27023900732748248443897841)
  ·
    refine ⟨20267925549561186332923381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27023900732748248443897841 20267925549561186332923381)
    ·
      refine ⟨1900118020271361218711567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20267925549561186332923381 1900118020271361218711567)
      ·
        refine ⟨2850177030407041828067351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900118020271361218711567 2850177030407041828067351)
        ·
          refine ⟨4275265545610562742101027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850177030407041828067351 4275265545610562742101027)
          ·
            refine ⟨6412898318415844113151541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275265545610562742101027 6412898318415844113151541)
            ·
              refine ⟨601209217351485385607957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6412898318415844113151541 601209217351485385607957)
              ·
                refine ⟨28181682063350877450373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 601209217351485385607957 28181682063350877450373)
                ·
                  rfl

theorem cell22_740929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 6].length) (baseStart_740929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740929 prefixEnd_740929 := by exact prefixLift 740929
  have htrace : WordTrace (prefixWord ++ tailWord_740929) baseStart_740929 baseEnd_740929 := by
    simpa [prefixWord, tailWord_740929, baseEnd_740929] using wordTrace_append hprefix tailTrace_740929
  have hstable : (prefixWord ++ tailWord_740929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740929).length < 2 ^ (prefixWord ++ tailWord_740929).sum := by decide
  have hdescent : baseEnd_740929 < baseStart_740929 := by decide
  rcases family_descends (prefixWord ++ tailWord_740929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740950 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_740950 : Nat := 118140960795 + 740950 * 2 ^ 59
def prefixEnd_740950 : Nat := 4983230072969 + 3 ^ 40 * 740950 * 2
def baseEnd_740950 : Nat := 253642327299320842278293

theorem tailTrace_740950 : CollatzResearch.WordTrace tailWord_740950 prefixEnd_740950 253642327299320842278293 := by
  unfold tailWord_740950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689041666604510564400769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18016444443781446020274869 1689041666604510564400769)
  ·
    refine ⟨1266781249953382923300577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1689041666604510564400769 1266781249953382923300577)
    ·
      refine ⟨950085937465037192475433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1266781249953382923300577 950085937465037192475433)
      ·
        refine ⟨712564453098777894356575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950085937465037192475433 712564453098777894356575)
        ·
          refine ⟨1068846679648166841534863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712564453098777894356575 1068846679648166841534863)
          ·
            refine ⟨1603270019472250262302295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068846679648166841534863 1603270019472250262302295)
            ·
              refine ⟨2404905029208375393453443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603270019472250262302295 2404905029208375393453443)
              ·
                refine ⟨3607357543812563090180165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404905029208375393453443 3607357543812563090180165)
                ·
                  refine ⟨676379539464855579408781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3607357543812563090180165 676379539464855579408781)
                  ·
                    refine ⟨253642327299320842278293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676379539464855579408781 253642327299320842278293)
                    ·
                      rfl

theorem cell22_740950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_740950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740950 prefixEnd_740950 := by exact prefixLift 740950
  have htrace : WordTrace (prefixWord ++ tailWord_740950) baseStart_740950 baseEnd_740950 := by
    simpa [prefixWord, tailWord_740950, baseEnd_740950] using wordTrace_append hprefix tailTrace_740950
  have hstable : (prefixWord ++ tailWord_740950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740950).length < 2 ^ (prefixWord ++ tailWord_740950).sum := by decide
  have hdescent : baseEnd_740950 < baseStart_740950 := by decide
  rcases family_descends (prefixWord ++ tailWord_740950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740961 : List Nat := [1, 2, 3, 1, 1, 3, 1, 6, 1, 3]
def baseStart_740961 : Nat := 118140960795 + 740961 * 2 ^ 59
def prefixEnd_740961 : Nat := 4983230072969 + 3 ^ 40 * 740961 * 2
def baseEnd_740961 : Nat := 253646092824120480253259

theorem tailTrace_740961 : CollatzResearch.WordTrace tailWord_740961 prefixEnd_740961 253646092824120480253259 := by
  unfold tailWord_740961
  simp only [CollatzResearch.WordTrace]
  refine ⟨27025067868632317909062737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18016711912421545272708491 27025067868632317909062737)
  ·
    refine ⟨20268800901474238431797053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27025067868632317909062737 20268800901474238431797053)
    ·
      refine ⟨7600800338052839411923895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20268800901474238431797053 7600800338052839411923895)
      ·
        refine ⟨11401200507079259117885843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7600800338052839411923895 11401200507079259117885843)
        ·
          refine ⟨17101800760618888676828765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11401200507079259117885843 17101800760618888676828765)
          ·
            refine ⟨6413175285232083253810787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17101800760618888676828765 6413175285232083253810787)
            ·
              refine ⟨9619762927848124880716181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413175285232083253810787 9619762927848124880716181)
              ·
                refine ⟨450926387242880853783571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9619762927848124880716181 450926387242880853783571)
                ·
                  refine ⟨676389580864321280675357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450926387242880853783571 676389580864321280675357)
                  ·
                    refine ⟨253646092824120480253259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676389580864321280675357 253646092824120480253259)
                    ·
                      rfl

theorem cell22_740961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_740961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_740961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_740961 prefixEnd_740961 := by exact prefixLift 740961
  have htrace : WordTrace (prefixWord ++ tailWord_740961) baseStart_740961 baseEnd_740961 := by
    simpa [prefixWord, tailWord_740961, baseEnd_740961] using wordTrace_append hprefix tailTrace_740961
  have hstable : (prefixWord ++ tailWord_740961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740961).length < 2 ^ (prefixWord ++ tailWord_740961).sum := by decide
  have hdescent : baseEnd_740961 < baseStart_740961 := by decide
  rcases family_descends (prefixWord ++ tailWord_740961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741004 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_741004 : Nat := 118140960795 + 741004 * 2 ^ 59
def prefixEnd_741004 : Nat := 4983230072969 + 3 ^ 40 * 741004 * 2
def baseEnd_741004 : Nat := 253660812602882701428127

theorem tailTrace_741004 : CollatzResearch.WordTrace tailWord_741004 prefixEnd_741004 253660812602882701428127 := by
  unfold tailWord_741004
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513318103738268126439033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18017757471651024168585377 13513318103738268126439033)
  ·
    refine ⟨10134988577803701094829275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13513318103738268126439033 10134988577803701094829275)
    ·
      refine ⟨15202482866705551642243913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10134988577803701094829275 15202482866705551642243913)
      ·
        refine ⟨11401862150029163731682935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15202482866705551642243913 11401862150029163731682935)
        ·
          refine ⟨17102793225043745597524403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11401862150029163731682935 17102793225043745597524403)
          ·
            refine ⟨25654189837565618396286605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17102793225043745597524403 25654189837565618396286605)
            ·
              refine ⟨9620321189087106898607477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25654189837565618396286605 9620321189087106898607477)
              ·
                refine ⟨901905111476916271744451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9620321189087106898607477 901905111476916271744451)
                ·
                  refine ⟨1352857667215374407616677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901905111476916271744451 1352857667215374407616677)
                  ·
                    refine ⟨253660812602882701428127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352857667215374407616677 253660812602882701428127)
                    ·
                      rfl

theorem cell22_741004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_741004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741004 prefixEnd_741004 := by exact prefixLift 741004
  have htrace : WordTrace (prefixWord ++ tailWord_741004) baseStart_741004 baseEnd_741004 := by
    simpa [prefixWord, tailWord_741004, baseEnd_741004] using wordTrace_append hprefix tailTrace_741004
  have hstable : (prefixWord ++ tailWord_741004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741004).length < 2 ^ (prefixWord ++ tailWord_741004).sum := by decide
  have hdescent : baseEnd_741004 < baseStart_741004 := by decide
  rcases family_descends (prefixWord ++ tailWord_741004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741012 : List Nat := [2, 4, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_741012 : Nat := 118140960795 + 741012 * 2 ^ 59
def prefixEnd_741012 : Nat := 4983230072969 + 3 ^ 40 * 741012 * 2
def baseEnd_741012 : Nat := 253663551166373347228103

theorem tailTrace_741012 : CollatzResearch.WordTrace tailWord_741012 prefixEnd_741012 253663551166373347228103 := by
  unfold tailWord_741012
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513463995723776809584645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18017951994298369079446193 13513463995723776809584645)
  ·
    refine ⟨2533774499198208151797121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13513463995723776809584645 2533774499198208151797121)
    ·
      refine ⟨1900330874398656113847841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2533774499198208151797121 1900330874398656113847841)
      ·
        refine ⟨1425248155798992085385881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1900330874398656113847841 1425248155798992085385881)
        ·
          refine ⟨1068936116849244064039411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425248155798992085385881 1068936116849244064039411)
          ·
            refine ⟨1603404175273866096059117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068936116849244064039411 1603404175273866096059117)
            ·
              refine ⟨601276565727699786022169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1603404175273866096059117 601276565727699786022169)
              ·
                refine ⟨450957424295774839516627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601276565727699786022169 450957424295774839516627)
                ·
                  refine ⟨676436136443662259274941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450957424295774839516627 676436136443662259274941)
                  ·
                    refine ⟨253663551166373347228103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676436136443662259274941 253663551166373347228103)
                    ·
                      rfl

theorem cell22_741012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_741012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741012 prefixEnd_741012 := by exact prefixLift 741012
  have htrace : WordTrace (prefixWord ++ tailWord_741012) baseStart_741012 baseEnd_741012 := by
    simpa [prefixWord, tailWord_741012, baseEnd_741012] using wordTrace_append hprefix tailTrace_741012
  have hstable : (prefixWord ++ tailWord_741012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741012).length < 2 ^ (prefixWord ++ tailWord_741012).sum := by decide
  have hdescent : baseEnd_741012 < baseStart_741012 := by decide
  rcases family_descends (prefixWord ++ tailWord_741012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741017 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_741017 : Nat := 118140960795 + 741017 * 2 ^ 59
def prefixEnd_741017 : Nat := 4983230072969 + 3 ^ 40 * 741017 * 2
def baseEnd_741017 : Nat := 253665262768555000853087

theorem tailTrace_741017 : CollatzResearch.WordTrace tailWord_741017 prefixEnd_741017 253665262768555000853087 := by
  unfold tailWord_741017
  simp only [CollatzResearch.WordTrace]
  refine ⟨27027110356429439473101305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18018073570952959648734203 27027110356429439473101305)
  ·
    refine ⟨20270332767322079604825979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27027110356429439473101305 20270332767322079604825979)
    ·
      refine ⟨30405499150983119407238969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20270332767322079604825979 30405499150983119407238969)
      ·
        refine ⟨22804124363237339555429227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30405499150983119407238969 22804124363237339555429227)
        ·
          refine ⟨34206186544856009333143841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22804124363237339555429227 34206186544856009333143841)
          ·
            refine ⟨25654639908642006999857881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34206186544856009333143841 25654639908642006999857881)
            ·
              refine ⟨19240979931481505249893411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25654639908642006999857881 19240979931481505249893411)
              ·
                refine ⟨28861469897222257874840117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19240979931481505249893411 28861469897222257874840117)
                ·
                  refine ⟨2705762802864586675766261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28861469897222257874840117 2705762802864586675766261)
                  ·
                    refine ⟨253665262768555000853087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2705762802864586675766261 253665262768555000853087)
                    ·
                      rfl

theorem cell22_741017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_741017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741017 prefixEnd_741017 := by exact prefixLift 741017
  have htrace : WordTrace (prefixWord ++ tailWord_741017) baseStart_741017 baseEnd_741017 := by
    simpa [prefixWord, tailWord_741017, baseEnd_741017] using wordTrace_append hprefix tailTrace_741017
  have hstable : (prefixWord ++ tailWord_741017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741017).length < 2 ^ (prefixWord ++ tailWord_741017).sum := by decide
  have hdescent : baseEnd_741017 < baseStart_741017 := by decide
  rcases family_descends (prefixWord ++ tailWord_741017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741038 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_741038 : Nat := 118140960795 + 741038 * 2 ^ 59
def prefixEnd_741038 : Nat := 4983230072969 + 3 ^ 40 * 741038 * 2
def baseEnd_741038 : Nat := 253672451497717946078023

theorem tailTrace_741038 : CollatzResearch.WordTrace tailWord_741038 prefixEnd_741038 253672451497717946078023 := by
  unfold tailWord_741038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378484536169170007451971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18018584192902240039743845 3378484536169170007451971)
  ·
    refine ⟨5067726804253755011177957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3378484536169170007451971 5067726804253755011177957)
    ·
      refine ⟨950198775797579064595867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5067726804253755011177957 950198775797579064595867)
      ·
        refine ⟨1425298163696368596893801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950198775797579064595867 1425298163696368596893801)
        ·
          refine ⟨1068973622772276447670351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425298163696368596893801 1068973622772276447670351)
          ·
            refine ⟨1603460434158414671505527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068973622772276447670351 1603460434158414671505527)
            ·
              refine ⟨2405190651237622007258291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603460434158414671505527 2405190651237622007258291)
              ·
                refine ⟨3607785976856433010887437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405190651237622007258291 3607785976856433010887437)
                ·
                  refine ⟨1352919741321162379082789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3607785976856433010887437 1352919741321162379082789)
                  ·
                    refine ⟨253672451497717946078023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352919741321162379082789 253672451497717946078023)
                    ·
                      rfl

theorem cell22_741038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_741038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741038 prefixEnd_741038 := by exact prefixLift 741038
  have htrace : WordTrace (prefixWord ++ tailWord_741038) baseStart_741038 baseEnd_741038 := by
    simpa [prefixWord, tailWord_741038, baseEnd_741038] using wordTrace_append hprefix tailTrace_741038
  have hstable : (prefixWord ++ tailWord_741038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741038).length < 2 ^ (prefixWord ++ tailWord_741038).sum := by decide
  have hdescent : baseEnd_741038 < baseStart_741038 := by decide
  rcases family_descends (prefixWord ++ tailWord_741038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741049 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_741049 : Nat := 118140960795 + 741049 * 2 ^ 59
def prefixEnd_741049 : Nat := 4983230072969 + 3 ^ 40 * 741049 * 2
def baseEnd_741049 : Nat := 253676217022517584052989

theorem tailTrace_741049 : CollatzResearch.WordTrace tailWord_741049 prefixEnd_741049 253676217022517584052989 := by
  unfold tailWord_741049
  simp only [CollatzResearch.WordTrace]
  refine ⟨27028277492313508938266201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18018851661542339292177467 27028277492313508938266201)
  ·
    refine ⟨20271208119235131703699651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27028277492313508938266201 20271208119235131703699651)
    ·
      refine ⟨30406812178852697555549477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20271208119235131703699651 30406812178852697555549477)
      ·
        refine ⟨5701277283534880791665527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30406812178852697555549477 5701277283534880791665527)
        ·
          refine ⟨8551915925302321187498291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701277283534880791665527 8551915925302321187498291)
          ·
            refine ⟨12827873887953481781247437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551915925302321187498291 12827873887953481781247437)
            ·
              refine ⟨4810452707982555667967789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12827873887953481781247437 4810452707982555667967789)
              ·
                refine ⟨1803919765493458375487921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4810452707982555667967789 1803919765493458375487921)
                ·
                  refine ⟨1352939824120093781615941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803919765493458375487921 1352939824120093781615941)
                  ·
                    refine ⟨253676217022517584052989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1352939824120093781615941 253676217022517584052989)
                    ·
                      rfl

theorem cell22_741049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_741049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741049 prefixEnd_741049 := by exact prefixLift 741049
  have htrace : WordTrace (prefixWord ++ tailWord_741049) baseStart_741049 baseEnd_741049 := by
    simpa [prefixWord, tailWord_741049, baseEnd_741049] using wordTrace_append hprefix tailTrace_741049
  have hstable : (prefixWord ++ tailWord_741049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741049).length < 2 ^ (prefixWord ++ tailWord_741049).sum := by decide
  have hdescent : baseEnd_741049 < baseStart_741049 := by decide
  rcases family_descends (prefixWord ++ tailWord_741049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741096 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 5, 3]
def baseStart_741096 : Nat := 118140960795 + 741096 * 2 ^ 59
def prefixEnd_741096 : Nat := 4983230072969 + 3 ^ 40 * 741096 * 2
def baseEnd_741096 : Nat := 253692306083025128127845

theorem tailTrace_741096 : CollatzResearch.WordTrace tailWord_741096 prefixEnd_741096 253692306083025128127845 := by
  unfold tailWord_741096
  simp only [CollatzResearch.WordTrace]
  refine ⟨13514995861571617982613571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18019994482095490643484761 13514995861571617982613571)
  ·
    refine ⟨20272493792357426973920357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13514995861571617982613571 20272493792357426973920357)
    ·
      refine ⟨3801092586067017557610067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20272493792357426973920357 3801092586067017557610067)
      ·
        refine ⟨5701638879100526336415101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801092586067017557610067 5701638879100526336415101)
        ·
          refine ⟨2138114579662697376155663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5701638879100526336415101 2138114579662697376155663)
          ·
            refine ⟨3207171869494046064233495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138114579662697376155663 3207171869494046064233495)
            ·
              refine ⟨4810757804241069096350243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207171869494046064233495 4810757804241069096350243)
              ·
                refine ⟨7216136706361603644525365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810757804241069096350243 7216136706361603644525365)
                ·
                  refine ⟨676512816221400341674253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7216136706361603644525365 676512816221400341674253)
                  ·
                    refine ⟨253692306083025128127845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676512816221400341674253 253692306083025128127845)
                    ·
                      rfl

theorem cell22_741096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_741096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741096 prefixEnd_741096 := by exact prefixLift 741096
  have htrace : WordTrace (prefixWord ++ tailWord_741096) baseStart_741096 baseEnd_741096 := by
    simpa [prefixWord, tailWord_741096, baseEnd_741096] using wordTrace_append hprefix tailTrace_741096
  have hstable : (prefixWord ++ tailWord_741096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741096).length < 2 ^ (prefixWord ++ tailWord_741096).sum := by decide
  have hdescent : baseEnd_741096 < baseStart_741096 := by decide
  rcases family_descends (prefixWord ++ tailWord_741096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741139 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 3, 4]
def baseStart_741139 : Nat := 118140960795 + 741139 * 2 ^ 59
def prefixEnd_741139 : Nat := 4983230072969 + 3 ^ 40 * 741139 * 2
def baseEnd_741139 : Nat := 253707025861787349302713

theorem tailTrace_741139 : CollatzResearch.WordTrace tailWord_741139 prefixEnd_741139 253707025861787349302713 := by
  unfold tailWord_741139
  simp only [CollatzResearch.WordTrace]
  refine ⟨27031560061987454309042471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18021040041324969539361647 27031560061987454309042471)
  ·
    refine ⟨40547340092981181463563707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27031560061987454309042471 40547340092981181463563707)
    ·
      refine ⟨60821010139471772195345561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40547340092981181463563707 60821010139471772195345561)
      ·
        refine ⟨45615757604603829146509171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60821010139471772195345561 45615757604603829146509171)
        ·
          refine ⟨68423636406905743719763757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45615757604603829146509171 68423636406905743719763757)
          ·
            refine ⟨25658863652589653894911409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68423636406905743719763757 25658863652589653894911409)
            ·
              refine ⟨19244147739442240421183557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25658863652589653894911409 19244147739442240421183557)
              ·
                refine ⟨3608277701145420078971917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19244147739442240421183557 3608277701145420078971917)
                ·
                  refine ⟨1353104137929532529614469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3608277701145420078971917 1353104137929532529614469)
                  ·
                    refine ⟨253707025861787349302713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1353104137929532529614469 253707025861787349302713)
                    ·
                      rfl

theorem cell22_741139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_741139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741139 prefixEnd_741139 := by exact prefixLift 741139
  have htrace : WordTrace (prefixWord ++ tailWord_741139) baseStart_741139 baseEnd_741139 := by
    simpa [prefixWord, tailWord_741139, baseEnd_741139] using wordTrace_append hprefix tailTrace_741139
  have hstable : (prefixWord ++ tailWord_741139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741139).length < 2 ^ (prefixWord ++ tailWord_741139).sum := by decide
  have hdescent : baseEnd_741139 < baseStart_741139 := by decide
  rcases family_descends (prefixWord ++ tailWord_741139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741143 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 5]
def baseStart_741143 : Nat := 118140960795 + 741143 * 2 ^ 59
def prefixEnd_741143 : Nat := 4983230072969 + 3 ^ 40 * 741143 * 2
def baseEnd_741143 : Nat := 84569465047844224067567

theorem tailTrace_741143 : CollatzResearch.WordTrace tailWord_741143 prefixEnd_741143 84569465047844224067567 := by
  unfold tailWord_741143
  simp only [CollatzResearch.WordTrace]
  refine ⟨27031705953972962992188083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18021137302648641994792055 27031705953972962992188083)
  ·
    refine ⟨40547558930959444488282125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27031705953972962992188083 40547558930959444488282125)
    ·
      refine ⟨15205334599109791683105797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40547558930959444488282125 15205334599109791683105797)
      ·
        refine ⟨2851000237333085940582337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15205334599109791683105797 2851000237333085940582337)
        ·
          refine ⟨2138250177999814455436753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851000237333085940582337 2138250177999814455436753)
          ·
            refine ⟨1603687633499860841577565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2138250177999814455436753 1603687633499860841577565)
            ·
              refine ⟨601382862562447815591587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1603687633499860841577565 601382862562447815591587)
              ·
                refine ⟨902074293843671723387381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601382862562447815591587 902074293843671723387381)
                ·
                  refine ⟨84569465047844224067567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 902074293843671723387381 84569465047844224067567)
                  ·
                    rfl

theorem cell22_741143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 5].length) (baseStart_741143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741143 prefixEnd_741143 := by exact prefixLift 741143
  have htrace : WordTrace (prefixWord ++ tailWord_741143) baseStart_741143 baseEnd_741143 := by
    simpa [prefixWord, tailWord_741143, baseEnd_741143] using wordTrace_append hprefix tailTrace_741143
  have hstable : (prefixWord ++ tailWord_741143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741143).length < 2 ^ (prefixWord ++ tailWord_741143).sum := by decide
  have hdescent : baseEnd_741143 < baseStart_741143 := by decide
  rcases family_descends (prefixWord ++ tailWord_741143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741218 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_741218 : Nat := 118140960795 + 741218 * 2 ^ 59
def prefixEnd_741218 : Nat := 4983230072969 + 3 ^ 40 * 741218 * 2
def baseEnd_741218 : Nat := 253734069176257476577471

theorem tailTrace_741218 : CollatzResearch.WordTrace tailWord_741218 prefixEnd_741218 253734069176257476577471 := by
  unfold tailWord_741218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758610357175312700292077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18022960952467500534112205 6758610357175312700292077)
  ·
    refine ⟨2534478883940742262609529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6758610357175312700292077 2534478883940742262609529)
    ·
      refine ⟨1900859162955556696957147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2534478883940742262609529 1900859162955556696957147)
      ·
        refine ⟨2851288744433335045435721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900859162955556696957147 2851288744433335045435721)
        ·
          refine ⟨2138466558325001284076791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851288744433335045435721 2138466558325001284076791)
          ·
            refine ⟨3207699837487501926115187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138466558325001284076791 3207699837487501926115187)
            ·
              refine ⟨4811549756231252889172781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207699837487501926115187 4811549756231252889172781)
              ·
                refine ⟨1804331158586719833439793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4811549756231252889172781 1804331158586719833439793)
                ·
                  refine ⟨1353248368940039875079845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1804331158586719833439793 1353248368940039875079845)
                  ·
                    refine ⟨253734069176257476577471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1353248368940039875079845 253734069176257476577471)
                    ·
                      rfl

theorem cell22_741218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_741218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741218 prefixEnd_741218 := by exact prefixLift 741218
  have htrace : WordTrace (prefixWord ++ tailWord_741218) baseStart_741218 baseEnd_741218 := by
    simpa [prefixWord, tailWord_741218, baseEnd_741218] using wordTrace_append hprefix tailTrace_741218
  have hstable : (prefixWord ++ tailWord_741218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741218).length < 2 ^ (prefixWord ++ tailWord_741218).sum := by decide
  have hdescent : baseEnd_741218 < baseStart_741218 := by decide
  rcases family_descends (prefixWord ++ tailWord_741218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741336 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_741336 : Nat := 118140960795 + 741336 * 2 ^ 59
def prefixEnd_741336 : Nat := 4983230072969 + 3 ^ 40 * 741336 * 2
def baseEnd_741336 : Nat := 253774462987744502127109

theorem tailTrace_741336 : CollatzResearch.WordTrace tailWord_741336 prefixEnd_741336 253774462987744502127109 := by
  unfold tailWord_741336
  simp only [CollatzResearch.WordTrace]
  refine ⟨13519372621136878476981931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18025830161515837969309241 13519372621136878476981931)
  ·
    refine ⟨20279058931705317715472897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13519372621136878476981931 20279058931705317715472897)
    ·
      refine ⟨15209294198778988286604673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20279058931705317715472897 15209294198778988286604673)
      ·
        refine ⟨11406970649084241214953505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15209294198778988286604673 11406970649084241214953505)
        ·
          refine ⟨8555227986813180911215129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11406970649084241214953505 8555227986813180911215129)
          ·
            refine ⟨6416420990109885683411347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8555227986813180911215129 6416420990109885683411347)
            ·
              refine ⟨9624631485164828525117021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416420990109885683411347 9624631485164828525117021)
              ·
                refine ⟨3609236806936810696918883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9624631485164828525117021 3609236806936810696918883)
                ·
                  refine ⟨5413855210405216045378325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609236806936810696918883 5413855210405216045378325)
                  ·
                    refine ⟨253774462987744502127109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5413855210405216045378325 253774462987744502127109)
                    ·
                      rfl

theorem cell22_741336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_741336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741336 prefixEnd_741336 := by exact prefixLift 741336
  have htrace : WordTrace (prefixWord ++ tailWord_741336) baseStart_741336 baseEnd_741336 := by
    simpa [prefixWord, tailWord_741336, baseEnd_741336] using wordTrace_append hprefix tailTrace_741336
  have hstable : (prefixWord ++ tailWord_741336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741336).length < 2 ^ (prefixWord ++ tailWord_741336).sum := by decide
  have hdescent : baseEnd_741336 < baseStart_741336 := by decide
  rcases family_descends (prefixWord ++ tailWord_741336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741357 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 6]
def baseStart_741357 : Nat := 118140960795 + 741357 * 2 ^ 59
def prefixEnd_741357 : Nat := 4983230072969 + 3 ^ 40 * 741357 * 2
def baseEnd_741357 : Nat := 84593883905635815784015

theorem tailTrace_741357 : CollatzResearch.WordTrace tailWord_741357 prefixEnd_741357 84593883905635815784015 := by
  unfold tailWord_741357
  simp only [CollatzResearch.WordTrace]
  refine ⟨27039511175197677540478325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18026340783465118360318883 27039511175197677540478325)
  ·
    refine ⟨2534954172674782269419843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27039511175197677540478325 2534954172674782269419843)
    ·
      refine ⟨3802431259012173404129765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534954172674782269419843 3802431259012173404129765)
      ·
        refine ⟨712955861064782513274331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3802431259012173404129765 712955861064782513274331)
        ·
          refine ⟨1069433791597173769911497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712955861064782513274331 1069433791597173769911497)
          ·
            refine ⟨802075343697880327433623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069433791597173769911497 802075343697880327433623)
            ·
              refine ⟨1203113015546820491150435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802075343697880327433623 1203113015546820491150435)
              ·
                refine ⟨1804669523320230736725653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203113015546820491150435 1804669523320230736725653)
                ·
                  refine ⟨84593883905635815784015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1804669523320230736725653 84593883905635815784015)
                  ·
                    rfl

theorem cell22_741357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_741357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741357 prefixEnd_741357 := by exact prefixLift 741357
  have htrace : WordTrace (prefixWord ++ tailWord_741357) baseStart_741357 baseEnd_741357 := by
    simpa [prefixWord, tailWord_741357, baseEnd_741357] using wordTrace_append hprefix tailTrace_741357
  have hstable : (prefixWord ++ tailWord_741357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741357).length < 2 ^ (prefixWord ++ tailWord_741357).sum := by decide
  have hdescent : baseEnd_741357 < baseStart_741357 := by decide
  rcases family_descends (prefixWord ++ tailWord_741357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741389 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_741389 : Nat := 118140960795 + 741389 * 2 ^ 59
def prefixEnd_741389 : Nat := 4983230072969 + 3 ^ 40 * 741389 * 2
def baseEnd_741389 : Nat := 253792605970870030551947

theorem tailTrace_741389 : CollatzResearch.WordTrace tailWord_741389 prefixEnd_741389 253792605970870030551947 := by
  unfold tailWord_741389
  simp only [CollatzResearch.WordTrace]
  refine ⟨27040678311081747005643221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18027118874054498003762147 27040678311081747005643221)
  ·
    refine ⟨633765897915978445444763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27040678311081747005643221 633765897915978445444763)
    ·
      refine ⟨950648846873967668167145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633765897915978445444763 950648846873967668167145)
      ·
        refine ⟨712986635155475751125359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950648846873967668167145 712986635155475751125359)
        ·
          refine ⟨1069479952733213626688039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712986635155475751125359 1069479952733213626688039)
          ·
            refine ⟨1604219929099820440032059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069479952733213626688039 1604219929099820440032059)
            ·
              refine ⟨2406329893649730660048089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604219929099820440032059 2406329893649730660048089)
              ·
                refine ⟨1804747420237297995036067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406329893649730660048089 1804747420237297995036067)
                ·
                  refine ⟨2707121130355946992554101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804747420237297995036067 2707121130355946992554101)
                  ·
                    refine ⟨253792605970870030551947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2707121130355946992554101 253792605970870030551947)
                    ·
                      rfl

theorem cell22_741389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_741389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741389 prefixEnd_741389 := by exact prefixLift 741389
  have htrace : WordTrace (prefixWord ++ tailWord_741389) baseStart_741389 baseEnd_741389 := by
    simpa [prefixWord, tailWord_741389, baseEnd_741389] using wordTrace_append hprefix tailTrace_741389
  have hstable : (prefixWord ++ tailWord_741389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741389).length < 2 ^ (prefixWord ++ tailWord_741389).sum := by decide
  have hdescent : baseEnd_741389 < baseStart_741389 := by decide
  rcases family_descends (prefixWord ++ tailWord_741389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741413 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 5]
def baseStart_741413 : Nat := 118140960795 + 741413 * 2 ^ 59
def prefixEnd_741413 : Nat := 4983230072969 + 3 ^ 40 * 741413 * 2
def baseEnd_741413 : Nat := 84600273887113989317291

theorem tailTrace_741413 : CollatzResearch.WordTrace tailWord_741413 prefixEnd_741413 84600273887113989317291 := by
  unfold tailWord_741413
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041553662994799104516893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18027702441996532736344595 27041553662994799104516893)
  ·
    refine ⟨10140582623623049664193835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27041553662994799104516893 10140582623623049664193835)
    ·
      refine ⟨15210873935434574496290753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10140582623623049664193835 15210873935434574496290753)
      ·
        refine ⟨11408155451575930872218065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15210873935434574496290753 11408155451575930872218065)
        ·
          refine ⟨8556116588681948154163549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11408155451575930872218065 8556116588681948154163549)
          ·
            refine ⟨3208543720755730557811331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8556116588681948154163549 3208543720755730557811331)
            ·
              refine ⟨4812815581133595836716997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208543720755730557811331 4812815581133595836716997)
              ·
                refine ⟨902402921462549219384437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4812815581133595836716997 902402921462549219384437)
                ·
                  refine ⟨84600273887113989317291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 902402921462549219384437 84600273887113989317291)
                  ·
                    rfl

theorem cell22_741413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_741413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741413 prefixEnd_741413 := by exact prefixLift 741413
  have htrace : WordTrace (prefixWord ++ tailWord_741413) baseStart_741413 baseEnd_741413 := by
    simpa [prefixWord, tailWord_741413, baseEnd_741413] using wordTrace_append hprefix tailTrace_741413
  have hstable : (prefixWord ++ tailWord_741413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741413).length < 2 ^ (prefixWord ++ tailWord_741413).sum := by decide
  have hdescent : baseEnd_741413 < baseStart_741413 := by decide
  rcases family_descends (prefixWord ++ tailWord_741413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741430 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_741430 : Nat := 118140960795 + 741430 * 2 ^ 59
def prefixEnd_741430 : Nat := 4983230072969 + 3 ^ 40 * 741430 * 2
def baseEnd_741430 : Nat := 84602213702919863425607

theorem tailTrace_741430 : CollatzResearch.WordTrace tailWord_741430 prefixEnd_741430 84602213702919863425607 := by
  unfold tailWord_741430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690135856495825687992859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18028115802622140671923829 1690135856495825687992859)
  ·
    refine ⟨2535203784743738531989289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1690135856495825687992859 2535203784743738531989289)
    ·
      refine ⟨1901402838557803898991967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2535203784743738531989289 1901402838557803898991967)
      ·
        refine ⟨2852104257836705848487951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901402838557803898991967 2852104257836705848487951)
        ·
          refine ⟨4278156386755058772731927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852104257836705848487951 4278156386755058772731927)
          ·
            refine ⟨6417234580132588159097891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278156386755058772731927 6417234580132588159097891)
            ·
              refine ⟨9625851870198882238646837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417234580132588159097891 9625851870198882238646837)
              ·
                refine ⟨902423612831145209873141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9625851870198882238646837 902423612831145209873141)
                ·
                  refine ⟨84602213702919863425607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 902423612831145209873141 84602213702919863425607)
                  ·
                    rfl

theorem cell22_741430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_741430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741430 prefixEnd_741430 := by exact prefixLift 741430
  have htrace : WordTrace (prefixWord ++ tailWord_741430) baseStart_741430 baseEnd_741430 := by
    simpa [prefixWord, tailWord_741430, baseEnd_741430] using wordTrace_append hprefix tailTrace_741430
  have hstable : (prefixWord ++ tailWord_741430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741430).length < 2 ^ (prefixWord ++ tailWord_741430).sum := by decide
  have hdescent : baseEnd_741430 < baseStart_741430 := by decide
  rcases family_descends (prefixWord ++ tailWord_741430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741462 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_741462 : Nat := 118140960795 + 741462 * 2 ^ 59
def prefixEnd_741462 : Nat := 4983230072969 + 3 ^ 40 * 741462 * 2
def baseEnd_741462 : Nat := 253817595362722173476723

theorem tailTrace_741462 : CollatzResearch.WordTrace tailWord_741462 prefixEnd_741462 253817595362722173476723 := by
  unfold tailWord_741462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690208802488580029565665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18028893893211520315367093 1690208802488580029565665)
  ·
    refine ⟨1267656601866435022174249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1690208802488580029565665 1267656601866435022174249)
    ·
      refine ⟨950742451399826266630687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1267656601866435022174249 950742451399826266630687)
      ·
        refine ⟨1426113677099739399946031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950742451399826266630687 1426113677099739399946031)
        ·
          refine ⟨2139170515649609099919047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426113677099739399946031 2139170515649609099919047)
          ·
            refine ⟨3208755773474413649878571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139170515649609099919047 3208755773474413649878571)
            ·
              refine ⟨4813133660211620474817857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208755773474413649878571 4813133660211620474817857)
              ·
                refine ⟨3609850245158715356113393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813133660211620474817857 3609850245158715356113393)
                ·
                  refine ⟨2707387683869036517085045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3609850245158715356113393 2707387683869036517085045)
                  ·
                    refine ⟨253817595362722173476723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2707387683869036517085045 253817595362722173476723)
                    ·
                      rfl

theorem cell22_741462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_741462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741462 prefixEnd_741462 := by exact prefixLift 741462
  have htrace : WordTrace (prefixWord ++ tailWord_741462) baseStart_741462 baseEnd_741462 := by
    simpa [prefixWord, tailWord_741462, baseEnd_741462] using wordTrace_append hprefix tailTrace_741462
  have hstable : (prefixWord ++ tailWord_741462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741462).length < 2 ^ (prefixWord ++ tailWord_741462).sum := by decide
  have hdescent : baseEnd_741462 < baseStart_741462 := by decide
  rcases family_descends (prefixWord ++ tailWord_741462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741475 : List Nat := [1, 1, 1, 5, 1, 1, 4, 4, 4]
def baseStart_741475 : Nat := 118140960795 + 741475 * 2 ^ 59
def prefixEnd_741475 : Nat := 4983230072969 + 3 ^ 40 * 741475 * 2
def baseEnd_741475 : Nat := 84607348509464824300561

theorem tailTrace_741475 : CollatzResearch.WordTrace tailWord_741475 prefixEnd_741475 84607348509464824300561 := by
  unfold tailWord_741475
  simp only [CollatzResearch.WordTrace]
  refine ⟨27043814988770183693273879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18029209992513455795515919 27043814988770183693273879)
  ·
    refine ⟨40565722483155275539910819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27043814988770183693273879 40565722483155275539910819)
    ·
      refine ⟨60848583724732913309866229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40565722483155275539910819 60848583724732913309866229)
      ·
        refine ⟨5704554724193710622799959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60848583724732913309866229 5704554724193710622799959)
        ·
          refine ⟨8556832086290565934199939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5704554724193710622799959 8556832086290565934199939)
          ·
            refine ⟨12835248129435848901299909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556832086290565934199939 12835248129435848901299909)
            ·
              refine ⟨2406609024269221668993733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12835248129435848901299909 2406609024269221668993733)
              ·
                refine ⟨451239192050479062936325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2406609024269221668993733 451239192050479062936325)
                ·
                  refine ⟨84607348509464824300561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451239192050479062936325 84607348509464824300561)
                  ·
                    rfl

theorem cell22_741475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 4].length) (baseStart_741475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741475 prefixEnd_741475 := by exact prefixLift 741475
  have htrace : WordTrace (prefixWord ++ tailWord_741475) baseStart_741475 baseEnd_741475 := by
    simpa [prefixWord, tailWord_741475, baseEnd_741475] using wordTrace_append hprefix tailTrace_741475
  have hstable : (prefixWord ++ tailWord_741475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741475).length < 2 ^ (prefixWord ++ tailWord_741475).sum := by decide
  have hdescent : baseEnd_741475 < baseStart_741475 := by decide
  rcases family_descends (prefixWord ++ tailWord_741475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741488 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_741488 : Nat := 118140960795 + 741488 * 2 ^ 59
def prefixEnd_741488 : Nat := 4983230072969 + 3 ^ 40 * 741488 * 2
def baseEnd_741488 : Nat := 253826495694066772326643

theorem tailTrace_741488 : CollatzResearch.WordTrace tailWord_741488 prefixEnd_741488 253826495694066772326643 := by
  unfold tailWord_741488
  simp only [CollatzResearch.WordTrace]
  refine ⟨13522144568861543456748559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18029526091815391275664745 13522144568861543456748559)
  ·
    refine ⟨20283216853292315185122839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13522144568861543456748559 20283216853292315185122839)
    ·
      refine ⟨30424825279938472777684259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20283216853292315185122839 30424825279938472777684259)
      ·
        refine ⟨45637237919907709166526389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30424825279938472777684259 45637237919907709166526389)
        ·
          refine ⟨4278491054991347734361849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45637237919907709166526389 4278491054991347734361849)
          ·
            refine ⟨3208868291243510800771387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278491054991347734361849 3208868291243510800771387)
            ·
              refine ⟨4813302436865266201157081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208868291243510800771387 4813302436865266201157081)
              ·
                refine ⟨3609976827648949650867811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813302436865266201157081 3609976827648949650867811)
                ·
                  refine ⟨5414965241473424476301717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609976827648949650867811 5414965241473424476301717)
                  ·
                    refine ⟨253826495694066772326643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5414965241473424476301717 253826495694066772326643)
                    ·
                      rfl

theorem cell22_741488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_741488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741488 prefixEnd_741488 := by exact prefixLift 741488
  have htrace : WordTrace (prefixWord ++ tailWord_741488) baseStart_741488 baseEnd_741488 := by
    simpa [prefixWord, tailWord_741488, baseEnd_741488] using wordTrace_append hprefix tailTrace_741488
  have hstable : (prefixWord ++ tailWord_741488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741488).length < 2 ^ (prefixWord ++ tailWord_741488).sum := by decide
  have hdescent : baseEnd_741488 < baseStart_741488 := by decide
  rcases family_descends (prefixWord ++ tailWord_741488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741490 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_741490 : Nat := 118140960795 + 741490 * 2 ^ 59
def prefixEnd_741490 : Nat := 4983230072969 + 3 ^ 40 * 741490 * 2
def baseEnd_741490 : Nat := 253827180334939433776637

theorem tailTrace_741490 : CollatzResearch.WordTrace tailWord_741490 prefixEnd_741490 253827180334939433776637 := by
  unfold tailWord_741490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761090520928960313767481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18029574722477227503379949 6761090520928960313767481)
  ·
    refine ⟨5070817890696720235325611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6761090520928960313767481 5070817890696720235325611)
    ·
      refine ⟨7606226836045080352988417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070817890696720235325611 7606226836045080352988417)
      ·
        refine ⟨5704670127033810264741313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7606226836045080352988417 5704670127033810264741313)
        ·
          refine ⟨4278502595275357698555985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5704670127033810264741313 4278502595275357698555985)
          ·
            refine ⟨3208876946456518273916989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278502595275357698555985 3208876946456518273916989)
            ·
              refine ⟨1203328854921194352718871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3208876946456518273916989 1203328854921194352718871)
              ·
                refine ⟨1804993282381791529078307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203328854921194352718871 1804993282381791529078307)
                ·
                  refine ⟨2707489923572687293617461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804993282381791529078307 2707489923572687293617461)
                  ·
                    refine ⟨253827180334939433776637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2707489923572687293617461 253827180334939433776637)
                    ·
                      rfl

theorem cell22_741490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_741490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741490 prefixEnd_741490 := by exact prefixLift 741490
  have htrace : WordTrace (prefixWord ++ tailWord_741490) baseStart_741490 baseEnd_741490 := by
    simpa [prefixWord, tailWord_741490, baseEnd_741490] using wordTrace_append hprefix tailTrace_741490
  have hstable : (prefixWord ++ tailWord_741490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741490).length < 2 ^ (prefixWord ++ tailWord_741490).sum := by decide
  have hdescent : baseEnd_741490 < baseStart_741490 := by decide
  rcases family_descends (prefixWord ++ tailWord_741490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741582 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_741582 : Nat := 118140960795 + 741582 * 2 ^ 59
def prefixEnd_741582 : Nat := 4983230072969 + 3 ^ 40 * 741582 * 2
def baseEnd_741582 : Nat := 84619557938360620158785

theorem tailTrace_741582 : CollatzResearch.WordTrace tailWord_741582 prefixEnd_741582 84619557938360620158785 := by
  unfold tailWord_741582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380964699922817620927375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18031811732921693978279333 3380964699922817620927375)
  ·
    refine ⟨5071447049884226431391063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3380964699922817620927375 5071447049884226431391063)
    ·
      refine ⟨7607170574826339647086595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5071447049884226431391063 7607170574826339647086595)
      ·
        refine ⟨11410755862239509470629893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7607170574826339647086595 11410755862239509470629893)
        ·
          refine ⟨2139516724169908025743105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11410755862239509470629893 2139516724169908025743105)
          ·
            refine ⟨1604637543127431019307329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2139516724169908025743105 1604637543127431019307329)
            ·
              refine ⟨1203478157345573264480497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604637543127431019307329 1203478157345573264480497)
              ·
                refine ⟨902608618009179948360373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203478157345573264480497 902608618009179948360373)
                ·
                  refine ⟨84619557938360620158785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 902608618009179948360373 84619557938360620158785)
                  ·
                    rfl

theorem cell22_741582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_741582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741582 prefixEnd_741582 := by exact prefixLift 741582
  have htrace : WordTrace (prefixWord ++ tailWord_741582) baseStart_741582 baseEnd_741582 := by
    simpa [prefixWord, tailWord_741582, baseEnd_741582] using wordTrace_append hprefix tailTrace_741582
  have hstable : (prefixWord ++ tailWord_741582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741582).length < 2 ^ (prefixWord ++ tailWord_741582).sum := by decide
  have hdescent : baseEnd_741582 < baseStart_741582 := by decide
  rcases family_descends (prefixWord ++ tailWord_741582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741586 : List Nat := [3, 2, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_741586 : Nat := 118140960795 + 741586 * 2 ^ 59
def prefixEnd_741586 : Nat := 4983230072969 + 3 ^ 40 * 741586 * 2
def baseEnd_741586 : Nat := 253860043096827183376343

theorem tailTrace_741586 : CollatzResearch.WordTrace tailWord_741586 prefixEnd_741586 253860043096827183376343 := by
  unfold tailWord_741586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761965872842012412641153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18031908994245366433709741 6761965872842012412641153)
  ·
    refine ⟨5071474404631509309480865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6761965872842012412641153 5071474404631509309480865)
    ·
      refine ⟨3803605803473631982110649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5071474404631509309480865 3803605803473631982110649)
      ·
        refine ⟨2852704352605223986582987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3803605803473631982110649 2852704352605223986582987)
        ·
          refine ⟨4279056528907835979874481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852704352605223986582987 4279056528907835979874481)
          ·
            refine ⟨3209292396680876984905861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4279056528907835979874481 3209292396680876984905861)
            ·
              refine ⟨601742324377664434669849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3209292396680876984905861 601742324377664434669849)
              ·
                refine ⟨451306743283248326002387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601742324377664434669849 451306743283248326002387)
                ·
                  refine ⟨676960114924872489003581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451306743283248326002387 676960114924872489003581)
                  ·
                    refine ⟨253860043096827183376343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676960114924872489003581 253860043096827183376343)
                    ·
                      rfl

theorem cell22_741586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_741586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741586 prefixEnd_741586 := by exact prefixLift 741586
  have htrace : WordTrace (prefixWord ++ tailWord_741586) baseStart_741586 baseEnd_741586 := by
    simpa [prefixWord, tailWord_741586, baseEnd_741586] using wordTrace_append hprefix tailTrace_741586
  have hstable : (prefixWord ++ tailWord_741586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741586).length < 2 ^ (prefixWord ++ tailWord_741586).sum := by decide
  have hdescent : baseEnd_741586 < baseStart_741586 := by decide
  rcases family_descends (prefixWord ++ tailWord_741586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741597 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_741597 : Nat := 118140960795 + 741597 * 2 ^ 59
def prefixEnd_741597 : Nat := 4983230072969 + 3 ^ 40 * 741597 * 2
def baseEnd_741597 : Nat := 253863808621626821351309

theorem tailTrace_741597 : CollatzResearch.WordTrace tailWord_741597 prefixEnd_741597 253863808621626821351309 := by
  unfold tailWord_741597
  simp only [CollatzResearch.WordTrace]
  refine ⟨27048264694328198529215045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18032176462885465686143363 27048264694328198529215045)
  ·
    refine ⟨5071549630186537224227821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27048264694328198529215045 5071549630186537224227821)
    ·
      refine ⟨1901831111319951459085433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5071549630186537224227821 1901831111319951459085433)
      ·
        refine ⟨1426373333489963594314075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1901831111319951459085433 1426373333489963594314075)
        ·
          refine ⟨2139560000234945391471113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426373333489963594314075 2139560000234945391471113)
          ·
            refine ⟨1604670000176209043603335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2139560000234945391471113 1604670000176209043603335)
            ·
              refine ⟨2407005000264313565405003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604670000176209043603335 2407005000264313565405003)
              ·
                refine ⟨3610507500396470348107505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407005000264313565405003 3610507500396470348107505)
                ·
                  refine ⟨2707880625297352761080629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3610507500396470348107505 2707880625297352761080629)
                  ·
                    refine ⟨253863808621626821351309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2707880625297352761080629 253863808621626821351309)
                    ·
                      rfl

theorem cell22_741597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_741597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741597 prefixEnd_741597 := by exact prefixLift 741597
  have htrace : WordTrace (prefixWord ++ tailWord_741597) baseStart_741597 baseEnd_741597 := by
    simpa [prefixWord, tailWord_741597, baseEnd_741597] using wordTrace_append hprefix tailTrace_741597
  have hstable : (prefixWord ++ tailWord_741597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741597).length < 2 ^ (prefixWord ++ tailWord_741597).sum := by decide
  have hdescent : baseEnd_741597 < baseStart_741597 := by decide
  rcases family_descends (prefixWord ++ tailWord_741597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741610 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_741610 : Nat := 118140960795 + 741610 * 2 ^ 59
def prefixEnd_741610 : Nat := 4983230072969 + 3 ^ 40 * 741610 * 2
def baseEnd_741610 : Nat := 84622752929099706925423

theorem tailTrace_741610 : CollatzResearch.WordTrace tailWord_741610 prefixEnd_741610 84622752929099706925423 := by
  unfold tailWord_741610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762184710820275437359571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18032492562187401166292189 6762184710820275437359571)
  ·
    refine ⟨10143277066230413156039357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6762184710820275437359571 10143277066230413156039357)
    ·
      refine ⟨3803728899836404933514759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10143277066230413156039357 3803728899836404933514759)
      ·
        refine ⟨5705593349754607400272139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3803728899836404933514759 5705593349754607400272139)
        ·
          refine ⟨8558390024631911100408209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705593349754607400272139 8558390024631911100408209)
          ·
            refine ⟨6418792518473933325306157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8558390024631911100408209 6418792518473933325306157)
            ·
              refine ⟨2407047194427724996989809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6418792518473933325306157 2407047194427724996989809)
              ·
                refine ⟨1805285395820793747742357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407047194427724996989809 1805285395820793747742357)
                ·
                  refine ⟨84622752929099706925423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1805285395820793747742357 84622752929099706925423)
                  ·
                    rfl

theorem cell22_741610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_741610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741610 prefixEnd_741610 := by exact prefixLift 741610
  have htrace : WordTrace (prefixWord ++ tailWord_741610) baseStart_741610 baseEnd_741610 := by
    simpa [prefixWord, tailWord_741610, baseEnd_741610] using wordTrace_append hprefix tailTrace_741610
  have hstable : (prefixWord ++ tailWord_741610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741610).length < 2 ^ (prefixWord ++ tailWord_741610).sum := by decide
  have hdescent : baseEnd_741610 < baseStart_741610 := by decide
  rcases family_descends (prefixWord ++ tailWord_741610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741672 : List Nat := [2, 1, 5, 1, 3, 1, 1, 8]
def baseStart_741672 : Nat := 118140960795 + 741672 * 2 ^ 59
def prefixEnd_741672 : Nat := 4983230072969 + 3 ^ 40 * 741672 * 2
def baseEnd_741672 : Nat := 28209942517150180636231

theorem tailTrace_741672 : CollatzResearch.WordTrace tailWord_741672 prefixEnd_741672 28209942517150180636231 := by
  unfold tailWord_741672
  simp only [CollatzResearch.WordTrace]
  refine ⟨13525500084528243169097635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18034000112704324225463513 13525500084528243169097635)
  ·
    refine ⟨20288250126792364753646453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13525500084528243169097635 20288250126792364753646453)
    ·
      refine ⟨1902023449386784195654355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20288250126792364753646453 1902023449386784195654355)
      ·
        refine ⟨2853035174080176293481533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902023449386784195654355 2853035174080176293481533)
        ·
          refine ⟨1069888190280066110055575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2853035174080176293481533 1069888190280066110055575)
          ·
            refine ⟨1604832285420099165083363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069888190280066110055575 1604832285420099165083363)
            ·
              refine ⟨2407248428130148747625045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604832285420099165083363 2407248428130148747625045)
              ·
                refine ⟨28209942517150180636231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2407248428130148747625045 28209942517150180636231)
                ·
                  rfl

theorem cell22_741672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_741672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741672 prefixEnd_741672 := by exact prefixLift 741672
  have htrace : WordTrace (prefixWord ++ tailWord_741672) baseStart_741672 baseEnd_741672 := by
    simpa [prefixWord, tailWord_741672, baseEnd_741672] using wordTrace_append hprefix tailTrace_741672
  have hstable : (prefixWord ++ tailWord_741672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741672).length < 2 ^ (prefixWord ++ tailWord_741672).sum := by decide
  have hdescent : baseEnd_741672 < baseStart_741672 := by decide
  rcases family_descends (prefixWord ++ tailWord_741672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741678 : List Nat := [4, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_741678 : Nat := 118140960795 + 741678 * 2 ^ 59
def prefixEnd_741678 : Nat := 4983230072969 + 3 ^ 40 * 741678 * 2
def baseEnd_741678 : Nat := 84630512192323203358687

theorem tailTrace_741678 : CollatzResearch.WordTrace tailWord_741678 prefixEnd_741678 84630512192323203358687 := by
  unfold tailWord_741678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381402375879343670364211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18034146004689832908609125 3381402375879343670364211)
  ·
    refine ⟨5072103563819015505546317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3381402375879343670364211 5072103563819015505546317)
    ·
      refine ⟨1902038836432130814579869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5072103563819015505546317 1902038836432130814579869)
      ·
        refine ⟨713264563662049055467451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1902038836432130814579869 713264563662049055467451)
        ·
          refine ⟨1069896845493073583201177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713264563662049055467451 1069896845493073583201177)
          ·
            refine ⟨802422634119805187400883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069896845493073583201177 802422634119805187400883)
            ·
              refine ⟨1203633951179707781101325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802422634119805187400883 1203633951179707781101325)
              ·
                refine ⟨451362731692390417912997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1203633951179707781101325 451362731692390417912997)
                ·
                  refine ⟨84630512192323203358687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451362731692390417912997 84630512192323203358687)
                  ·
                    rfl

theorem cell22_741678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_741678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741678 prefixEnd_741678 := by exact prefixLift 741678
  have htrace : WordTrace (prefixWord ++ tailWord_741678) baseStart_741678 baseEnd_741678 := by
    simpa [prefixWord, tailWord_741678, baseEnd_741678] using wordTrace_append hprefix tailTrace_741678
  have hstable : (prefixWord ++ tailWord_741678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741678).length < 2 ^ (prefixWord ++ tailWord_741678).sum := by decide
  have hdescent : baseEnd_741678 < baseStart_741678 := by decide
  rcases family_descends (prefixWord ++ tailWord_741678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741704 : List Nat := [2, 1, 3, 1, 1, 2, 2, 6, 1, 3]
def baseStart_741704 : Nat := 118140960795 + 741704 * 2 ^ 59
def prefixEnd_741704 : Nat := 4983230072969 + 3 ^ 40 * 741704 * 2
def baseEnd_741704 : Nat := 253900436908314208925981

theorem tailTrace_741704 : CollatzResearch.WordTrace tailWord_741704 prefixEnd_741704 253900436908314208925981 := by
  unfold tailWord_741704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13526083652470277901680083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18034778203293703868906777 13526083652470277901680083)
  ·
    refine ⟨20289125478705416852520125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13526083652470277901680083 20289125478705416852520125)
    ·
      refine ⟨7608422054514531319695047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20289125478705416852520125 7608422054514531319695047)
      ·
        refine ⟨11412633081771796979542571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7608422054514531319695047 11412633081771796979542571)
        ·
          refine ⟨17118949622657695469313857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11412633081771796979542571 17118949622657695469313857)
          ·
            refine ⟨12839212216993271601985393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17118949622657695469313857 12839212216993271601985393)
            ·
              refine ⟨9629409162744953701489045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12839212216993271601985393 9629409162744953701489045)
              ·
                refine ⟨451378554503669704757299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9629409162744953701489045 451378554503669704757299)
                ·
                  refine ⟨677067831755504557135949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451378554503669704757299 677067831755504557135949)
                  ·
                    refine ⟨253900436908314208925981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677067831755504557135949 253900436908314208925981)
                    ·
                      rfl

theorem cell22_741704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_741704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741704 prefixEnd_741704 := by exact prefixLift 741704
  have htrace : WordTrace (prefixWord ++ tailWord_741704) baseStart_741704 baseEnd_741704 := by
    simpa [prefixWord, tailWord_741704, baseEnd_741704] using wordTrace_append hprefix tailTrace_741704
  have hstable : (prefixWord ++ tailWord_741704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741704).length < 2 ^ (prefixWord ++ tailWord_741704).sum := by decide
  have hdescent : baseEnd_741704 < baseStart_741704 := by decide
  rcases family_descends (prefixWord ++ tailWord_741704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741792 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_741792 : Nat := 118140960795 + 741792 * 2 ^ 59
def prefixEnd_741792 : Nat := 4983230072969 + 3 ^ 40 * 741792 * 2
def baseEnd_741792 : Nat := 253930561106711312725711

theorem tailTrace_741792 : CollatzResearch.WordTrace tailWord_741792 prefixEnd_741792 253930561106711312725711 := by
  unfold tailWord_741792
  simp only [CollatzResearch.WordTrace]
  refine ⟨13527688464310873416281815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18036917952414497888375753 13527688464310873416281815)
  ·
    refine ⟨20291532696466310124422723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13527688464310873416281815 20291532696466310124422723)
    ·
      refine ⟨30437299044699465186634085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20291532696466310124422723 30437299044699465186634085)
      ·
        refine ⟨5706993570881149722493891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30437299044699465186634085 5706993570881149722493891)
        ·
          refine ⟨8560490356321724583740837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5706993570881149722493891 8560490356321724583740837)
          ·
            refine ⟨1605091941810323359451407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8560490356321724583740837 1605091941810323359451407)
            ·
              refine ⟨2407637912715485039177111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605091941810323359451407 2407637912715485039177111)
              ·
                refine ⟨3611456869073227558765667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407637912715485039177111 3611456869073227558765667)
                ·
                  refine ⟨5417185303609841338148501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611456869073227558765667 5417185303609841338148501)
                  ·
                    refine ⟨253930561106711312725711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5417185303609841338148501 253930561106711312725711)
                    ·
                      rfl

theorem cell22_741792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_741792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741792 prefixEnd_741792 := by exact prefixLift 741792
  have htrace : WordTrace (prefixWord ++ tailWord_741792) baseStart_741792 baseEnd_741792 := by
    simpa [prefixWord, tailWord_741792, baseEnd_741792] using wordTrace_append hprefix tailTrace_741792
  have hstable : (prefixWord ++ tailWord_741792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741792).length < 2 ^ (prefixWord ++ tailWord_741792).sum := by decide
  have hdescent : baseEnd_741792 < baseStart_741792 := by decide
  rcases family_descends (prefixWord ++ tailWord_741792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741794 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_741794 : Nat := 118140960795 + 741794 * 2 ^ 59
def prefixEnd_741794 : Nat := 4983230072969 + 3 ^ 40 * 741794 * 2
def baseEnd_741794 : Nat := 253931245747583974175705

theorem tailTrace_741794 : CollatzResearch.WordTrace tailWord_741794 prefixEnd_741794 253931245747583974175705 := by
  unfold tailWord_741794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6763862468653625293534109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18036966583076334116090957 6763862468653625293534109)
  ·
    refine ⟨2536448425745109485075291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6763862468653625293534109 2536448425745109485075291)
    ·
      refine ⟨3804672638617664227612937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536448425745109485075291 3804672638617664227612937)
      ·
        refine ⟨2853504478963248170709703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3804672638617664227612937 2853504478963248170709703)
        ·
          refine ⟨4280256718444872256064555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853504478963248170709703 4280256718444872256064555)
          ·
            refine ⟨6420385077667308384096833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280256718444872256064555 6420385077667308384096833)
            ·
              refine ⟨4815288808250481288072625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420385077667308384096833 4815288808250481288072625)
              ·
                refine ⟨3611466606187860966054469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4815288808250481288072625 3611466606187860966054469)
                ·
                  refine ⟨677149988660223931135213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3611466606187860966054469 677149988660223931135213)
                  ·
                    refine ⟨253931245747583974175705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677149988660223931135213 253931245747583974175705)
                    ·
                      rfl

theorem cell22_741794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_741794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741794 prefixEnd_741794 := by exact prefixLift 741794
  have htrace : WordTrace (prefixWord ++ tailWord_741794) baseStart_741794 baseEnd_741794 := by
    simpa [prefixWord, tailWord_741794, baseEnd_741794] using wordTrace_append hprefix tailTrace_741794
  have hstable : (prefixWord ++ tailWord_741794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741794).length < 2 ^ (prefixWord ++ tailWord_741794).sum := by decide
  have hdescent : baseEnd_741794 < baseStart_741794 := by decide
  rcases family_descends (prefixWord ++ tailWord_741794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741828 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_741828 : Nat := 118140960795 + 741828 * 2 ^ 59
def prefixEnd_741828 : Nat := 4983230072969 + 3 ^ 40 * 741828 * 2
def baseEnd_741828 : Nat := 253942884642419218825601

theorem tailTrace_741828 : CollatzResearch.WordTrace tailWord_741828 prefixEnd_741828 253942884642419218825601 := by
  unfold tailWord_741828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13528344978245662490437069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18037793304327549987249425 13528344978245662490437069)
  ·
    refine ⟨5073129366842123433913901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13528344978245662490437069 5073129366842123433913901)
    ·
      refine ⟨1902423512565796287717713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5073129366842123433913901 1902423512565796287717713)
      ·
        refine ⟨1426817634424347215788285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1902423512565796287717713 1426817634424347215788285)
        ·
          refine ⟨535056612909130205920607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1426817634424347215788285 535056612909130205920607)
          ·
            refine ⟨802584919363695308880911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535056612909130205920607 802584919363695308880911)
            ·
              refine ⟨1203877379045542963321367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802584919363695308880911 1203877379045542963321367)
              ·
                refine ⟨1805816068568314444982051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203877379045542963321367 1805816068568314444982051)
                ·
                  refine ⟨2708724102852471667473077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805816068568314444982051 2708724102852471667473077)
                  ·
                    refine ⟨253942884642419218825601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2708724102852471667473077 253942884642419218825601)
                    ·
                      rfl

theorem cell22_741828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_741828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741828 prefixEnd_741828 := by exact prefixLift 741828
  have htrace : WordTrace (prefixWord ++ tailWord_741828) baseStart_741828 baseEnd_741828 := by
    simpa [prefixWord, tailWord_741828, baseEnd_741828] using wordTrace_append hprefix tailTrace_741828
  have hstable : (prefixWord ++ tailWord_741828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741828).length < 2 ^ (prefixWord ++ tailWord_741828).sum := by decide
  have hdescent : baseEnd_741828 < baseStart_741828 := by decide
  rcases family_descends (prefixWord ++ tailWord_741828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741858 : List Nat := [3, 3, 3, 2, 2, 1, 8]
def baseStart_741858 : Nat := 118140960795 + 741858 * 2 ^ 59
def prefixEnd_741858 : Nat := 4983230072969 + 3 ^ 40 * 741858 * 2
def baseEnd_741858 : Nat := 9405672379833671873167

theorem tailTrace_741858 : CollatzResearch.WordTrace tailWord_741858 prefixEnd_741858 9405672379833671873167 := by
  unfold tailWord_741858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764446036595660026116557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18038522764255093402977485 6764446036595660026116557)
  ·
    refine ⟨2536667263723372509793709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6764446036595660026116557 2536667263723372509793709)
    ·
      refine ⟨951250223896264691172641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2536667263723372509793709 951250223896264691172641)
      ·
        refine ⟨713437667922198518379481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951250223896264691172641 713437667922198518379481)
        ·
          refine ⟨535078250941648888784611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713437667922198518379481 535078250941648888784611)
          ·
            refine ⟨802617376412473333176917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535078250941648888784611 802617376412473333176917)
            ·
              refine ⟨9405672379833671873167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 802617376412473333176917 9405672379833671873167)
              ·
                rfl

theorem cell22_741858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 8].length) (baseStart_741858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741858 prefixEnd_741858 := by exact prefixLift 741858
  have htrace : WordTrace (prefixWord ++ tailWord_741858) baseStart_741858 baseEnd_741858 := by
    simpa [prefixWord, tailWord_741858, baseEnd_741858] using wordTrace_append hprefix tailTrace_741858
  have hstable : (prefixWord ++ tailWord_741858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741858).length < 2 ^ (prefixWord ++ tailWord_741858).sum := by decide
  have hdescent : baseEnd_741858 < baseStart_741858 := by decide
  rcases family_descends (prefixWord ++ tailWord_741858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741869 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 7]
def baseStart_741869 : Nat := 118140960795 + 741869 * 2 ^ 59
def prefixEnd_741869 : Nat := 4983230072969 + 3 ^ 40 * 741869 * 2
def baseEnd_741869 : Nat := 84652306593436259516825

theorem tailTrace_741869 : CollatzResearch.WordTrace tailWord_741869 prefixEnd_741869 84652306593436259516825 := by
  unfold tailWord_741869
  simp only [CollatzResearch.WordTrace]
  refine ⟨27058185349342788983116661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18038790232895192655411107 27058185349342788983116661)
  ·
    refine ⟨2536704876500886467167187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27058185349342788983116661 2536704876500886467167187)
    ·
      refine ⟨3805057314751329700750781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536704876500886467167187 3805057314751329700750781)
      ·
        refine ⟨1426896493031748637781543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3805057314751329700750781 1426896493031748637781543)
        ·
          refine ⟨2140344739547622956672315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426896493031748637781543 2140344739547622956672315)
          ·
            refine ⟨3210517109321434435008473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140344739547622956672315 3210517109321434435008473)
            ·
              refine ⟨2407887831991075826256355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210517109321434435008473 2407887831991075826256355)
              ·
                refine ⟨3611831747986613739384533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407887831991075826256355 3611831747986613739384533)
                ·
                  refine ⟨84652306593436259516825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3611831747986613739384533 84652306593436259516825)
                  ·
                    rfl

theorem cell22_741869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_741869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741869 prefixEnd_741869 := by exact prefixLift 741869
  have htrace : WordTrace (prefixWord ++ tailWord_741869) baseStart_741869 baseEnd_741869 := by
    simpa [prefixWord, tailWord_741869, baseEnd_741869] using wordTrace_append hprefix tailTrace_741869
  have hstable : (prefixWord ++ tailWord_741869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741869).length < 2 ^ (prefixWord ++ tailWord_741869).sum := by decide
  have hdescent : baseEnd_741869 < baseStart_741869 := by decide
  rcases family_descends (prefixWord ++ tailWord_741869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741873 : List Nat := [1, 2, 2, 2, 3, 1, 5, 2, 1, 3]
def baseStart_741873 : Nat := 118140960795 + 741873 * 2 ^ 59
def prefixEnd_741873 : Nat := 4983230072969 + 3 ^ 40 * 741873 * 2
def baseEnd_741873 : Nat := 253958289062054101450463

theorem tailTrace_741873 : CollatzResearch.WordTrace tailWord_741873 prefixEnd_741873 253958289062054101450463 := by
  unfold tailWord_741873
  simp only [CollatzResearch.WordTrace]
  refine ⟨27058331241328297666262273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18038887494218865110841515 27058331241328297666262273)
  ·
    refine ⟨20293748430996223249696705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27058331241328297666262273 20293748430996223249696705)
    ·
      refine ⟨15220311323247167437272529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20293748430996223249696705 15220311323247167437272529)
      ·
        refine ⟨11415233492435375577954397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15220311323247167437272529 11415233492435375577954397)
        ·
          refine ⟨4280712559663265841732899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11415233492435375577954397 4280712559663265841732899)
          ·
            refine ⟨6421068839494898762599349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280712559663265841732899 6421068839494898762599349)
            ·
              refine ⟨601975203702646758993689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6421068839494898762599349 601975203702646758993689)
              ·
                refine ⟨451481402776985069245267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601975203702646758993689 451481402776985069245267)
                ·
                  refine ⟨677222104165477603867901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451481402776985069245267 677222104165477603867901)
                  ·
                    refine ⟨253958289062054101450463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677222104165477603867901 253958289062054101450463)
                    ·
                      rfl

theorem cell22_741873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_741873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741873 prefixEnd_741873 := by exact prefixLift 741873
  have htrace : WordTrace (prefixWord ++ tailWord_741873) baseStart_741873 baseEnd_741873 := by
    simpa [prefixWord, tailWord_741873, baseEnd_741873] using wordTrace_append hprefix tailTrace_741873
  have hstable : (prefixWord ++ tailWord_741873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741873).length < 2 ^ (prefixWord ++ tailWord_741873).sum := by decide
  have hdescent : baseEnd_741873 < baseStart_741873 := by decide
  rcases family_descends (prefixWord ++ tailWord_741873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741899 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 3, 4]
def baseStart_741899 : Nat := 118140960795 + 741899 * 2 ^ 59
def prefixEnd_741899 : Nat := 4983230072969 + 3 ^ 40 * 741899 * 2
def baseEnd_741899 : Nat := 253967189393398700300383

theorem tailTrace_741899 : CollatzResearch.WordTrace tailWord_741899 prefixEnd_741899 253967189393398700300383 := by
  unfold tailWord_741899
  simp only [CollatzResearch.WordTrace]
  refine ⟨27059279539234104106708751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18039519692822736071139167 27059279539234104106708751)
  ·
    refine ⟨40588919308851156160063127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27059279539234104106708751 40588919308851156160063127)
    ·
      refine ⟨60883378963276734240094691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40588919308851156160063127 60883378963276734240094691)
      ·
        refine ⟨91325068444915101360142037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60883378963276734240094691 91325068444915101360142037)
        ·
          refine ⟨2140431291677697688128329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91325068444915101360142037 2140431291677697688128329)
          ·
            refine ⟨1605323468758273266096247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2140431291677697688128329 1605323468758273266096247)
            ·
              refine ⟨2407985203137409899144371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605323468758273266096247 2407985203137409899144371)
              ·
                refine ⟨3611977804706114848716557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407985203137409899144371 3611977804706114848716557)
                ·
                  refine ⟨1354491676764793068268709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3611977804706114848716557 1354491676764793068268709)
                  ·
                    refine ⟨253967189393398700300383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354491676764793068268709 253967189393398700300383)
                    ·
                      rfl

theorem cell22_741899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_741899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741899 prefixEnd_741899 := by exact prefixLift 741899
  have htrace : WordTrace (prefixWord ++ tailWord_741899) baseStart_741899 baseEnd_741899 := by
    simpa [prefixWord, tailWord_741899, baseEnd_741899] using wordTrace_append hprefix tailTrace_741899
  have hstable : (prefixWord ++ tailWord_741899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741899).length < 2 ^ (prefixWord ++ tailWord_741899).sum := by decide
  have hdescent : baseEnd_741899 < baseStart_741899 := by decide
  rcases family_descends (prefixWord ++ tailWord_741899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741924 : List Nat := [2, 3, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_741924 : Nat := 118140960795 + 741924 * 2 ^ 59
def prefixEnd_741924 : Nat := 4983230072969 + 3 ^ 40 * 741924 * 2
def baseEnd_741924 : Nat := 253975747404306968425307

theorem tailTrace_741924 : CollatzResearch.WordTrace tailWord_741924 prefixEnd_741924 253975747404306968425307 := by
  unfold tailWord_741924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13530095682071766688184413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18040127576095688917579217 13530095682071766688184413)
  ·
    refine ⟨5073785880776912508069155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13530095682071766688184413 5073785880776912508069155)
    ·
      refine ⟨7610678821165368762103733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073785880776912508069155 7610678821165368762103733)
      ·
        refine ⟨713501139484253321447225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7610678821165368762103733 713501139484253321447225)
        ·
          refine ⟨535125854613189991085419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713501139484253321447225 535125854613189991085419)
          ·
            refine ⟨802688781919784986628129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535125854613189991085419 802688781919784986628129)
            ·
              refine ⟨602016586439838739971097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802688781919784986628129 602016586439838739971097)
              ·
                refine ⟨451512439829879054978323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602016586439838739971097 451512439829879054978323)
                ·
                  refine ⟨677268659744818582467485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451512439829879054978323 677268659744818582467485)
                  ·
                    refine ⟨253975747404306968425307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677268659744818582467485 253975747404306968425307)
                    ·
                      rfl

theorem cell22_741924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_741924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741924 prefixEnd_741924 := by exact prefixLift 741924
  have htrace : WordTrace (prefixWord ++ tailWord_741924) baseStart_741924 baseEnd_741924 := by
    simpa [prefixWord, tailWord_741924, baseEnd_741924] using wordTrace_append hprefix tailTrace_741924
  have hstable : (prefixWord ++ tailWord_741924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741924).length < 2 ^ (prefixWord ++ tailWord_741924).sum := by decide
  have hdescent : baseEnd_741924 < baseStart_741924 := by decide
  rcases family_descends (prefixWord ++ tailWord_741924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741946 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_741946 : Nat := 118140960795 + 741946 * 2 ^ 59
def prefixEnd_741946 : Nat := 4983230072969 + 3 ^ 40 * 741946 * 2
def baseEnd_741946 : Nat := 253983278453906244375239

theorem tailTrace_741946 : CollatzResearch.WordTrace tailWord_741946 prefixEnd_741946 253983278453906244375239 := by
  unfold tailWord_741946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765248442515957783417423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18040662513375887422446461 6765248442515957783417423)
  ·
    refine ⟨10147872663773936675126135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6765248442515957783417423 10147872663773936675126135)
    ·
      refine ⟨15221808995660905012689203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10147872663773936675126135 15221808995660905012689203)
      ·
        refine ⟨22832713493491357519033805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15221808995660905012689203 22832713493491357519033805)
        ·
          refine ⟨8562267560059259069637677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22832713493491357519033805 8562267560059259069637677)
          ·
            refine ⟨3210850335022222151114129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8562267560059259069637677 3210850335022222151114129)
            ·
              refine ⟨2408137751266666613335597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210850335022222151114129 2408137751266666613335597)
              ·
                refine ⟨903051656724999980000849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2408137751266666613335597 903051656724999980000849)
                ·
                  refine ⟨677288742543749985000637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 903051656724999980000849 677288742543749985000637)
                  ·
                    refine ⟨253983278453906244375239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677288742543749985000637 253983278453906244375239)
                    ·
                      rfl

theorem cell22_741946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_741946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741946 prefixEnd_741946 := by exact prefixLift 741946
  have htrace : WordTrace (prefixWord ++ tailWord_741946) baseStart_741946 baseEnd_741946 := by
    simpa [prefixWord, tailWord_741946, baseEnd_741946] using wordTrace_append hprefix tailTrace_741946
  have hstable : (prefixWord ++ tailWord_741946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741946).length < 2 ^ (prefixWord ++ tailWord_741946).sum := by decide
  have hdescent : baseEnd_741946 < baseStart_741946 := by decide
  rcases family_descends (prefixWord ++ tailWord_741946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741980 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_741980 : Nat := 118140960795 + 741980 * 2 ^ 59
def prefixEnd_741980 : Nat := 4983230072969 + 3 ^ 40 * 741980 * 2
def baseEnd_741980 : Nat := 253994917348741489025135

theorem tailTrace_741980 : CollatzResearch.WordTrace tailWord_741980 prefixEnd_741980 253994917348741489025135 := by
  unfold tailWord_741980
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531116925970327470203697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18041489234627103293604929 13531116925970327470203697)
  ·
    refine ⟨10148337694477745602652773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13531116925970327470203697 10148337694477745602652773)
    ·
      refine ⟨1902813317714577300497395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10148337694477745602652773 1902813317714577300497395)
      ·
        refine ⟨2854219976571865950746093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902813317714577300497395 2854219976571865950746093)
        ·
          refine ⟨1070332491214449731529785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2854219976571865950746093 1070332491214449731529785)
          ·
            refine ⟨802749368410837298647339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070332491214449731529785 802749368410837298647339)
            ·
              refine ⟨1204124052616255947971009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802749368410837298647339 1204124052616255947971009)
              ·
                refine ⟨903093039462191960978257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204124052616255947971009 903093039462191960978257)
                ·
                  refine ⟨677319779596643970733693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 903093039462191960978257 677319779596643970733693)
                  ·
                    refine ⟨253994917348741489025135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677319779596643970733693 253994917348741489025135)
                    ·
                      rfl

theorem cell22_741980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_741980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_741980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_741980 prefixEnd_741980 := by exact prefixLift 741980
  have htrace : WordTrace (prefixWord ++ tailWord_741980) baseStart_741980 baseEnd_741980 := by
    simpa [prefixWord, tailWord_741980, baseEnd_741980] using wordTrace_append hprefix tailTrace_741980
  have hstable : (prefixWord ++ tailWord_741980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741980).length < 2 ^ (prefixWord ++ tailWord_741980).sum := by decide
  have hdescent : baseEnd_741980 < baseStart_741980 := by decide
  rcases family_descends (prefixWord ++ tailWord_741980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742042 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_742042 : Nat := 118140960795 + 742042 * 2 ^ 59
def prefixEnd_742042 : Nat := 4983230072969 + 3 ^ 40 * 742042 * 2
def baseEnd_742042 : Nat := 254016141215793993974945

theorem tailTrace_742042 : CollatzResearch.WordTrace tailWord_742042 prefixEnd_742042 254016141215793993974945 := by
  unfold tailWord_742042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766123794429009882291095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18042996785144026352776253 6766123794429009882291095)
  ·
    refine ⟨10149185691643514823436643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6766123794429009882291095 10149185691643514823436643)
    ·
      refine ⟨15223778537465272235154965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10149185691643514823436643 15223778537465272235154965)
      ·
        refine ⟨713614618943684636022889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15223778537465272235154965 713614618943684636022889)
        ·
          refine ⟨535210964207763477017167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713614618943684636022889 535210964207763477017167)
          ·
            refine ⟨802816446311645215525751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535210964207763477017167 802816446311645215525751)
            ·
              refine ⟨1204224669467467823288627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802816446311645215525751 1204224669467467823288627)
              ·
                refine ⟨1806337004201201734932941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204224669467467823288627 1806337004201201734932941)
                ·
                  refine ⟨677376376575450650599853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1806337004201201734932941 677376376575450650599853)
                  ·
                    refine ⟨254016141215793993974945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677376376575450650599853 254016141215793993974945)
                    ·
                      rfl

theorem cell22_742042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_742042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742042 prefixEnd_742042 := by exact prefixLift 742042
  have htrace : WordTrace (prefixWord ++ tailWord_742042) baseStart_742042 baseEnd_742042 := by
    simpa [prefixWord, tailWord_742042, baseEnd_742042] using wordTrace_append hprefix tailTrace_742042
  have hstable : (prefixWord ++ tailWord_742042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742042).length < 2 ^ (prefixWord ++ tailWord_742042).sum := by decide
  have hdescent : baseEnd_742042 < baseStart_742042 := by decide
  rcases family_descends (prefixWord ++ tailWord_742042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742064 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_742064 : Nat := 118140960795 + 742064 * 2 ^ 59
def prefixEnd_742064 : Nat := 4983230072969 + 3 ^ 40 * 742064 * 2
def baseEnd_742064 : Nat := 254023672265393269924877

theorem tailTrace_742064 : CollatzResearch.WordTrace tailWord_742064 prefixEnd_742064 254023672265393269924877 := by
  unfold tailWord_742064
  simp only [CollatzResearch.WordTrace]
  refine ⟨13532648791818168643232623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18043531722424224857643497 13532648791818168643232623)
  ·
    refine ⟨20298973187727252964848935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13532648791818168643232623 20298973187727252964848935)
    ·
      refine ⟨30448459781590879447273403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20298973187727252964848935 30448459781590879447273403)
      ·
        refine ⟨45672689672386319170910105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30448459781590879447273403 45672689672386319170910105)
        ·
          refine ⟨34254517254289739378182579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45672689672386319170910105 34254517254289739378182579)
          ·
            refine ⟨51381775881434609067273869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34254517254289739378182579 51381775881434609067273869)
            ·
              refine ⟨19268165955537978400227701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51381775881434609067273869 19268165955537978400227701)
              ·
                refine ⟨1806390558331685475021347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19268165955537978400227701 1806390558331685475021347)
                ·
                  refine ⟨2709585837497528212532021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806390558331685475021347 2709585837497528212532021)
                  ·
                    refine ⟨254023672265393269924877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2709585837497528212532021 254023672265393269924877)
                    ·
                      rfl

theorem cell22_742064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_742064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742064 prefixEnd_742064 := by exact prefixLift 742064
  have htrace : WordTrace (prefixWord ++ tailWord_742064) baseStart_742064 baseEnd_742064 := by
    simpa [prefixWord, tailWord_742064, baseEnd_742064] using wordTrace_append hprefix tailTrace_742064
  have hstable : (prefixWord ++ tailWord_742064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742064).length < 2 ^ (prefixWord ++ tailWord_742064).sum := by decide
  have hdescent : baseEnd_742064 < baseStart_742064 := by decide
  rcases family_descends (prefixWord ++ tailWord_742064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742094 : List Nat := [4, 1, 1, 1, 3, 12]
def baseStart_742094 : Nat := 118140960795 + 742094 * 2 ^ 59
def prefixEnd_742094 : Nat := 4983230072969 + 3 ^ 40 * 742094 * 2
def baseEnd_742094 : Nat := 3136221504672631995985

theorem tailTrace_742094 : CollatzResearch.WordTrace tailWord_742094 prefixEnd_742094 3136221504672631995985 := by
  unfold tailWord_742094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383298971690956551257167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18044261182351768273371557 3383298971690956551257167)
  ·
    refine ⟨5074948457536434826885751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3383298971690956551257167 5074948457536434826885751)
    ·
      refine ⟨7612422686304652240328627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074948457536434826885751 7612422686304652240328627)
      ·
        refine ⟨11418634029456978360492941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7612422686304652240328627 11418634029456978360492941)
        ·
          refine ⟨4281987761046366885184853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11418634029456978360492941 4281987761046366885184853)
          ·
            refine ⟨3136221504672631995985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4281987761046366885184853 3136221504672631995985)
            ·
              rfl

theorem cell22_742094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 12].length) (baseStart_742094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742094 prefixEnd_742094 := by exact prefixLift 742094
  have htrace : WordTrace (prefixWord ++ tailWord_742094) baseStart_742094 baseEnd_742094 := by
    simpa [prefixWord, tailWord_742094, baseEnd_742094] using wordTrace_append hprefix tailTrace_742094
  have hstable : (prefixWord ++ tailWord_742094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742094).length < 2 ^ (prefixWord ++ tailWord_742094).sum := by decide
  have hdescent : baseEnd_742094 < baseStart_742094 := by decide
  rcases family_descends (prefixWord ++ tailWord_742094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742100 : List Nat := [2, 4, 1, 3, 2, 1, 1, 4, 4]
def baseStart_742100 : Nat := 118140960795 + 742100 * 2 ^ 59
def prefixEnd_742100 : Nat := 4983230072969 + 3 ^ 40 * 742100 * 2
def baseEnd_742100 : Nat := 84678665267033725341589

theorem tailTrace_742100 : CollatzResearch.WordTrace tailWord_742100 prefixEnd_742100 84678665267033725341589 := by
  unfold tailWord_742100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13533305305752957717387877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18044407074337276956517169 13533305305752957717387877)
  ·
    refine ⟨2537494744828679572010227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13533305305752957717387877 2537494744828679572010227)
    ·
      refine ⟨3806242117243019358015341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2537494744828679572010227 3806242117243019358015341)
      ·
        refine ⟨1427340793966132259255753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3806242117243019358015341 1427340793966132259255753)
        ·
          refine ⟨1070505595474599194441815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1427340793966132259255753 1070505595474599194441815)
          ·
            refine ⟨1605758393211898791662723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070505595474599194441815 1605758393211898791662723)
            ·
              refine ⟨2408637589817848187494085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605758393211898791662723 2408637589817848187494085)
              ·
                refine ⟨451619548090846535155141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2408637589817848187494085 451619548090846535155141)
                ·
                  refine ⟨84678665267033725341589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451619548090846535155141 84678665267033725341589)
                  ·
                    rfl

theorem cell22_742100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_742100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742100 prefixEnd_742100 := by exact prefixLift 742100
  have htrace : WordTrace (prefixWord ++ tailWord_742100) baseStart_742100 baseEnd_742100 := by
    simpa [prefixWord, tailWord_742100, baseEnd_742100] using wordTrace_append hprefix tailTrace_742100
  have hstable : (prefixWord ++ tailWord_742100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742100).length < 2 ^ (prefixWord ++ tailWord_742100).sum := by decide
  have hdescent : baseEnd_742100 < baseStart_742100 := by decide
  rcases family_descends (prefixWord ++ tailWord_742100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742111 : List Nat := [1, 1, 2, 3, 2, 5, 1, 7]
def baseStart_742111 : Nat := 118140960795 + 742111 * 2 ^ 59
def prefixEnd_742111 : Nat := 4983230072969 + 3 ^ 40 * 742111 * 2
def baseEnd_742111 : Nat := 28226640147322312666637

theorem tailTrace_742111 : CollatzResearch.WordTrace tailWord_742111 prefixEnd_742111 28226640147322312666637 := by
  unfold tailWord_742111
  simp only [CollatzResearch.WordTrace]
  refine ⟨27067011814466064313426187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18044674542977376208950791 27067011814466064313426187)
  ·
    refine ⟨40600517721699096470139281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27067011814466064313426187 40600517721699096470139281)
    ·
      refine ⟨30450388291274322352604461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40600517721699096470139281 30450388291274322352604461)
      ·
        refine ⟨11418895609227870882226673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30450388291274322352604461 11418895609227870882226673)
        ·
          refine ⟨8564171706920903161670005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11418895609227870882226673 8564171706920903161670005)
          ·
            refine ⟨802891097523834671406563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8564171706920903161670005 802891097523834671406563)
            ·
              refine ⟨1204336646285752007109845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802891097523834671406563 1204336646285752007109845)
              ·
                refine ⟨28226640147322312666637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1204336646285752007109845 28226640147322312666637)
                ·
                  rfl

theorem cell22_742111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 7].length) (baseStart_742111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742111 prefixEnd_742111 := by exact prefixLift 742111
  have htrace : WordTrace (prefixWord ++ tailWord_742111) baseStart_742111 baseEnd_742111 := by
    simpa [prefixWord, tailWord_742111, baseEnd_742111] using wordTrace_append hprefix tailTrace_742111
  have hstable : (prefixWord ++ tailWord_742111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742111).length < 2 ^ (prefixWord ++ tailWord_742111).sum := by decide
  have hdescent : baseEnd_742111 < baseStart_742111 := by decide
  rcases family_descends (prefixWord ++ tailWord_742111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742124 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_742124 : Nat := 118140960795 + 742124 * 2 ^ 59
def prefixEnd_742124 : Nat := 4983230072969 + 3 ^ 40 * 742124 * 2
def baseEnd_742124 : Nat := 254044211491573113424693

theorem tailTrace_742124 : CollatzResearch.WordTrace tailWord_742124 prefixEnd_742124 254044211491573113424693 := by
  unfold tailWord_742124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13533742981709483766824713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18044990642279311689099617 13533742981709483766824713)
  ·
    refine ⟨10150307236282112825118535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13533742981709483766824713 10150307236282112825118535)
    ·
      refine ⟨15225460854423169237677803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150307236282112825118535 15225460854423169237677803)
      ·
        refine ⟨22838191281634753856516705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15225460854423169237677803 22838191281634753856516705)
        ·
          refine ⟨17128643461226065392387529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22838191281634753856516705 17128643461226065392387529)
          ·
            refine ⟨12846482595919549044290647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17128643461226065392387529 12846482595919549044290647)
            ·
              refine ⟨19269723893879323566435971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12846482595919549044290647 19269723893879323566435971)
              ·
                refine ⟨28904585840818985349653957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19269723893879323566435971 28904585840818985349653957)
                ·
                  refine ⟨5419609845153559753060117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28904585840818985349653957 5419609845153559753060117)
                  ·
                    refine ⟨254044211491573113424693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5419609845153559753060117 254044211491573113424693)
                    ·
                      rfl

theorem cell22_742124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_742124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742124 prefixEnd_742124 := by exact prefixLift 742124
  have htrace : WordTrace (prefixWord ++ tailWord_742124) baseStart_742124 baseEnd_742124 := by
    simpa [prefixWord, tailWord_742124, baseEnd_742124] using wordTrace_append hprefix tailTrace_742124
  have hstable : (prefixWord ++ tailWord_742124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742124).length < 2 ^ (prefixWord ++ tailWord_742124).sum := by decide
  have hdescent : baseEnd_742124 < baseStart_742124 := by decide
  rcases family_descends (prefixWord ++ tailWord_742124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742169 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_742169 : Nat := 118140960795 + 742169 * 2 ^ 59
def prefixEnd_742169 : Nat := 4983230072969 + 3 ^ 40 * 742169 * 2
def baseEnd_742169 : Nat := 254059615911207996049555

theorem tailTrace_742169 : CollatzResearch.WordTrace tailWord_742169 prefixEnd_742169 254059615911207996049555 := by
  unfold tailWord_742169
  simp only [CollatzResearch.WordTrace]
  refine ⟨27069127248255940219037561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18046084832170626812691707 27069127248255940219037561)
  ·
    refine ⟨20301845436191955164278171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27069127248255940219037561 20301845436191955164278171)
    ·
      refine ⟨30452768154287932746417257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20301845436191955164278171 30452768154287932746417257)
      ·
        refine ⟨22839576115715949559812943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30452768154287932746417257 22839576115715949559812943)
        ·
          refine ⟨34259364173573924339719415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22839576115715949559812943 34259364173573924339719415)
          ·
            refine ⟨51389046260360886509579123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34259364173573924339719415 51389046260360886509579123)
            ·
              refine ⟨77083569390541329764368685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51389046260360886509579123 77083569390541329764368685)
              ·
                refine ⟨28906338521452998661638257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77083569390541329764368685 28906338521452998661638257)
                ·
                  refine ⟨21679753891089748996228693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28906338521452998661638257 21679753891089748996228693)
                  ·
                    refine ⟨254059615911207996049555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21679753891089748996228693 254059615911207996049555)
                    ·
                      rfl

theorem cell22_742169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_742169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742169 prefixEnd_742169 := by exact prefixLift 742169
  have htrace : WordTrace (prefixWord ++ tailWord_742169) baseStart_742169 baseEnd_742169 := by
    simpa [prefixWord, tailWord_742169, baseEnd_742169] using wordTrace_append hprefix tailTrace_742169
  have hstable : (prefixWord ++ tailWord_742169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742169).length < 2 ^ (prefixWord ++ tailWord_742169).sum := by decide
  have hdescent : baseEnd_742169 < baseStart_742169 := by decide
  rcases family_descends (prefixWord ++ tailWord_742169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742248 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_742248 : Nat := 118140960795 + 742248 * 2 ^ 59
def prefixEnd_742248 : Nat := 4983230072969 + 3 ^ 40 * 742248 * 2
def baseEnd_742248 : Nat := 254086659225678123324313

theorem tailTrace_742248 : CollatzResearch.WordTrace tailWord_742248 prefixEnd_742248 254086659225678123324313 := by
  unfold tailWord_742248
  simp only [CollatzResearch.WordTrace]
  refine ⟨13536004307484868355581699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18048005743313157807442265 13536004307484868355581699)
  ·
    refine ⟨20304006461227302533372549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13536004307484868355581699 20304006461227302533372549)
    ·
      refine ⟨3807001211480119225007353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20304006461227302533372549 3807001211480119225007353)
      ·
        refine ⟨2855250908610089418755515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807001211480119225007353 2855250908610089418755515)
        ·
          refine ⟨4282876362915134128133273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855250908610089418755515 4282876362915134128133273)
          ·
            refine ⟨3212157272186350596099955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282876362915134128133273 3212157272186350596099955)
            ·
              refine ⟨4818235908279525894149933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212157272186350596099955 4818235908279525894149933)
              ·
                refine ⟨1806838465604822210306225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4818235908279525894149933 1806838465604822210306225)
                ·
                  refine ⟨1355128849203616657729669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806838465604822210306225 1355128849203616657729669)
                  ·
                    refine ⟨254086659225678123324313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1355128849203616657729669 254086659225678123324313)
                    ·
                      rfl

theorem cell22_742248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_742248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742248 prefixEnd_742248 := by exact prefixLift 742248
  have htrace : WordTrace (prefixWord ++ tailWord_742248) baseStart_742248 baseEnd_742248 := by
    simpa [prefixWord, tailWord_742248, baseEnd_742248] using wordTrace_append hprefix tailTrace_742248
  have hstable : (prefixWord ++ tailWord_742248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742248).length < 2 ^ (prefixWord ++ tailWord_742248).sum := by decide
  have hdescent : baseEnd_742248 < baseStart_742248 := by decide
  rcases family_descends (prefixWord ++ tailWord_742248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742383 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 4, 4]
def baseStart_742383 : Nat := 118140960795 + 742383 * 2 ^ 59
def prefixEnd_742383 : Nat := 4983230072969 + 3 ^ 40 * 742383 * 2
def baseEnd_742383 : Nat := 254132872484582771198899

theorem tailTrace_742383 : CollatzResearch.WordTrace tailWord_742383 prefixEnd_742383 254132872484582771198899 := by
  unfold tailWord_742383
  simp only [CollatzResearch.WordTrace]
  refine ⟨27076932469480654767327803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18051288312987103178218535 27076932469480654767327803)
  ·
    refine ⟨40615398704220982150991705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27076932469480654767327803 40615398704220982150991705)
    ·
      refine ⟨30461549028165736613243779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40615398704220982150991705 30461549028165736613243779)
      ·
        refine ⟨45692323542248604919865669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30461549028165736613243779 45692323542248604919865669)
        ·
          refine ⟨8567310664171613422474813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45692323542248604919865669 8567310664171613422474813)
          ·
            refine ⟨3212741499064355033428055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8567310664171613422474813 3212741499064355033428055)
            ·
              refine ⟨4819112248596532550142083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212741499064355033428055 4819112248596532550142083)
              ·
                refine ⟨7228668372894798825213125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819112248596532550142083 7228668372894798825213125)
                ·
                  refine ⟨1355375319917774779727461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7228668372894798825213125 1355375319917774779727461)
                  ·
                    refine ⟨254132872484582771198899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1355375319917774779727461 254132872484582771198899)
                    ·
                      rfl

theorem cell22_742383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_742383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742383 prefixEnd_742383 := by exact prefixLift 742383
  have htrace : WordTrace (prefixWord ++ tailWord_742383) baseStart_742383 baseEnd_742383 := by
    simpa [prefixWord, tailWord_742383, baseEnd_742383] using wordTrace_append hprefix tailTrace_742383
  have hstable : (prefixWord ++ tailWord_742383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742383).length < 2 ^ (prefixWord ++ tailWord_742383).sum := by decide
  have hdescent : baseEnd_742383 < baseStart_742383 := by decide
  rcases family_descends (prefixWord ++ tailWord_742383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742385 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 4, 3]
def baseStart_742385 : Nat := 118140960795 + 742385 * 2 ^ 59
def prefixEnd_742385 : Nat := 4983230072969 + 3 ^ 40 * 742385 * 2
def baseEnd_742385 : Nat := 254133557125455432648893

theorem tailTrace_742385 : CollatzResearch.WordTrace tailWord_742385 prefixEnd_742385 254133557125455432648893 := by
  unfold tailWord_742385
  simp only [CollatzResearch.WordTrace]
  refine ⟨27077005415473409108900609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18051336943648939405933739 27077005415473409108900609)
  ·
    refine ⟨20307754061605056831675457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27077005415473409108900609 20307754061605056831675457)
    ·
      refine ⟨15230815546203792623756593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20307754061605056831675457 15230815546203792623756593)
      ·
        refine ⟨11423111659652844467817445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15230815546203792623756593 11423111659652844467817445)
        ·
          refine ⟨2141833436184908337715771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11423111659652844467817445 2141833436184908337715771)
          ·
            refine ⟨3212750154277362506573657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141833436184908337715771 3212750154277362506573657)
            ·
              refine ⟨2409562615708021879930243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3212750154277362506573657 2409562615708021879930243)
              ·
                refine ⟨3614343923562032819895365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409562615708021879930243 3614343923562032819895365)
                ·
                  refine ⟨677689485667881153730381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3614343923562032819895365 677689485667881153730381)
                  ·
                    refine ⟨254133557125455432648893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677689485667881153730381 254133557125455432648893)
                    ·
                      rfl

theorem cell22_742385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_742385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742385 prefixEnd_742385 := by exact prefixLift 742385
  have htrace : WordTrace (prefixWord ++ tailWord_742385) baseStart_742385 baseEnd_742385 := by
    simpa [prefixWord, tailWord_742385, baseEnd_742385] using wordTrace_append hprefix tailTrace_742385
  have hstable : (prefixWord ++ tailWord_742385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742385).length < 2 ^ (prefixWord ++ tailWord_742385).sum := by decide
  have hdescent : baseEnd_742385 < baseStart_742385 := by decide
  rcases family_descends (prefixWord ++ tailWord_742385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742458 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_742458 : Nat := 118140960795 + 742458 * 2 ^ 59
def prefixEnd_742458 : Nat := 4983230072969 + 3 ^ 40 * 742458 * 2
def baseEnd_742458 : Nat := 254158546517307575573669

theorem tailTrace_742458 : CollatzResearch.WordTrace tailWord_742458 prefixEnd_742458 254158546517307575573669 := by
  unfold tailWord_742458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769916986052235644077007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18053111962805961717538685 6769916986052235644077007)
  ·
    refine ⟨10154875479078353466115511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6769916986052235644077007 10154875479078353466115511)
    ·
      refine ⟨15232313218617530199173267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10154875479078353466115511 15232313218617530199173267)
      ·
        refine ⟨22848469827926295298759901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15232313218617530199173267 22848469827926295298759901)
        ·
          refine ⟨8568176185472360737034963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22848469827926295298759901 8568176185472360737034963)
          ·
            refine ⟨12852264278208541105552445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568176185472360737034963 12852264278208541105552445)
            ·
              refine ⟨4819599104328202914582167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12852264278208541105552445 4819599104328202914582167)
              ·
                refine ⟨7229398656492304371873251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819599104328202914582167 7229398656492304371873251)
                ·
                  refine ⟨10844097984738456557809877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7229398656492304371873251 10844097984738456557809877)
                  ·
                    refine ⟨254158546517307575573669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10844097984738456557809877 254158546517307575573669)
                    ·
                      rfl

theorem cell22_742458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_742458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742458 prefixEnd_742458 := by exact prefixLift 742458
  have htrace : WordTrace (prefixWord ++ tailWord_742458) baseStart_742458 baseEnd_742458 := by
    simpa [prefixWord, tailWord_742458, baseEnd_742458] using wordTrace_append hprefix tailTrace_742458
  have hstable : (prefixWord ++ tailWord_742458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742458).length < 2 ^ (prefixWord ++ tailWord_742458).sum := by decide
  have hdescent : baseEnd_742458 < baseStart_742458 := by decide
  rcases family_descends (prefixWord ++ tailWord_742458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742460 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 5]
def baseStart_742460 : Nat := 118140960795 + 742460 * 2 ^ 59
def prefixEnd_742460 : Nat := 4983230072969 + 3 ^ 40 * 742460 * 2
def baseEnd_742460 : Nat := 84719743719393412341221

theorem tailTrace_742460 : CollatzResearch.WordTrace tailWord_742460 prefixEnd_742460 84719743719393412341221 := by
  unfold tailWord_742460
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539870445100848458940417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18053160593467797945253889 13539870445100848458940417)
  ·
    refine ⟨10154902833825636344205313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13539870445100848458940417 10154902833825636344205313)
    ·
      refine ⟨7616177125369227258153985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10154902833825636344205313 7616177125369227258153985)
      ·
        refine ⟨5712132844026920443615489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7616177125369227258153985 5712132844026920443615489)
        ·
          refine ⟨4284099633020190332711617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5712132844026920443615489 4284099633020190332711617)
          ·
            refine ⟨3213074724765142749533713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284099633020190332711617 3213074724765142749533713)
            ·
              refine ⟨2409806043573857062150285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3213074724765142749533713 2409806043573857062150285)
              ·
                refine ⟨903677266340196398306357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2409806043573857062150285 903677266340196398306357)
                ·
                  refine ⟨84719743719393412341221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 903677266340196398306357 84719743719393412341221)
                  ·
                    rfl

theorem cell22_742460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_742460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742460 prefixEnd_742460 := by exact prefixLift 742460
  have htrace : WordTrace (prefixWord ++ tailWord_742460) baseStart_742460 baseEnd_742460 := by
    simpa [prefixWord, tailWord_742460, baseEnd_742460] using wordTrace_append hprefix tailTrace_742460
  have hstable : (prefixWord ++ tailWord_742460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742460).length < 2 ^ (prefixWord ++ tailWord_742460).sum := by decide
  have hdescent : baseEnd_742460 < baseStart_742460 := by decide
  rcases family_descends (prefixWord ++ tailWord_742460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742488 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 8]
def baseStart_742488 : Nat := 118140960795 + 742488 * 2 ^ 59
def prefixEnd_742488 : Nat := 4983230072969 + 3 ^ 40 * 742488 * 2
def baseEnd_742488 : Nat := 84722938710132499107859

theorem tailTrace_742488 : CollatzResearch.WordTrace tailWord_742488 prefixEnd_742488 84722938710132499107859 := by
  unfold tailWord_742488
  simp only [CollatzResearch.WordTrace]
  refine ⟨13540381067050128849950059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18053841422733505133266745 13540381067050128849950059)
  ·
    refine ⟨20310571600575193274925089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13540381067050128849950059 20310571600575193274925089)
    ·
      refine ⟨15232928700431394956193817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20310571600575193274925089 15232928700431394956193817)
      ·
        refine ⟨11424696525323546217145363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15232928700431394956193817 11424696525323546217145363)
        ·
          refine ⟨17137044787985319325718045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11424696525323546217145363 17137044787985319325718045)
          ·
            refine ⟨6426391795494494747144267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17137044787985319325718045 6426391795494494747144267)
            ·
              refine ⟨9639587693241742120716401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6426391795494494747144267 9639587693241742120716401)
              ·
                refine ⟨7229690769931306590537301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9639587693241742120716401 7229690769931306590537301)
                ·
                  refine ⟨84722938710132499107859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7229690769931306590537301 84722938710132499107859)
                  ·
                    rfl

theorem cell22_742488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_742488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742488 prefixEnd_742488 := by exact prefixLift 742488
  have htrace : WordTrace (prefixWord ++ tailWord_742488) baseStart_742488 baseEnd_742488 := by
    simpa [prefixWord, tailWord_742488, baseEnd_742488] using wordTrace_append hprefix tailTrace_742488
  have hstable : (prefixWord ++ tailWord_742488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742488).length < 2 ^ (prefixWord ++ tailWord_742488).sum := by decide
  have hdescent : baseEnd_742488 < baseStart_742488 := by decide
  rcases family_descends (prefixWord ++ tailWord_742488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742494 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_742494 : Nat := 118140960795 + 742494 * 2 ^ 59
def prefixEnd_742494 : Nat := 4983230072969 + 3 ^ 40 * 742494 * 2
def baseEnd_742494 : Nat := 84723623351005160557853

theorem tailTrace_742494 : CollatzResearch.WordTrace tailWord_742494 prefixEnd_742494 84723623351005160557853 := by
  unfold tailWord_742494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385122621509815090577317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18053987314719013816412357 3385122621509815090577317)
  ·
    refine ⟨634710491533090329483247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3385122621509815090577317 634710491533090329483247)
    ·
      refine ⟨952065737299635494224871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634710491533090329483247 952065737299635494224871)
      ·
        refine ⟨1428098605949453241337307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952065737299635494224871 1428098605949453241337307)
        ·
          refine ⟨2142147908924179862005961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428098605949453241337307 2142147908924179862005961)
          ·
            refine ⟨1606610931693134896504471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142147908924179862005961 1606610931693134896504471)
            ·
              refine ⟨2409916397539702344756707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606610931693134896504471 2409916397539702344756707)
              ·
                refine ⟨3614874596309553517135061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409916397539702344756707 3614874596309553517135061)
                ·
                  refine ⟨84723623351005160557853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3614874596309553517135061 84723623351005160557853)
                  ·
                    rfl

theorem cell22_742494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_742494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742494 prefixEnd_742494 := by exact prefixLift 742494
  have htrace : WordTrace (prefixWord ++ tailWord_742494) baseStart_742494 baseEnd_742494 := by
    simpa [prefixWord, tailWord_742494, baseEnd_742494] using wordTrace_append hprefix tailTrace_742494
  have hstable : (prefixWord ++ tailWord_742494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742494).length < 2 ^ (prefixWord ++ tailWord_742494).sum := by decide
  have hdescent : baseEnd_742494 < baseStart_742494 := by decide
  rcases family_descends (prefixWord ++ tailWord_742494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742505 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 6]
def baseStart_742505 : Nat := 118140960795 + 742505 * 2 ^ 59
def prefixEnd_742505 : Nat := 4983230072969 + 3 ^ 40 * 742505 * 2
def baseEnd_742505 : Nat := 84724878525938373216175

theorem tailTrace_742505 : CollatzResearch.WordTrace tailWord_742505 prefixEnd_742505 84724878525938373216175 := by
  unfold tailWord_742505
  simp only [CollatzResearch.WordTrace]
  refine ⟨27081382175038669603268969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18054254783359113068845979 27081382175038669603268969)
  ·
    refine ⟨20311036631279002202451727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27081382175038669603268969 20311036631279002202451727)
    ·
      refine ⟨30466554946918503303677591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20311036631279002202451727 30466554946918503303677591)
      ·
        refine ⟨45699832420377754955516387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30466554946918503303677591 45699832420377754955516387)
        ·
          refine ⟨68549748630566632433274581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45699832420377754955516387 68549748630566632433274581)
          ·
            refine ⟨1606634733528905447654873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 68549748630566632433274581 1606634733528905447654873)
            ·
              refine ⟨1204976050146679085741155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606634733528905447654873 1204976050146679085741155)
              ·
                refine ⟨1807464075220018628611733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204976050146679085741155 1807464075220018628611733)
                ·
                  refine ⟨84724878525938373216175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1807464075220018628611733 84724878525938373216175)
                  ·
                    rfl

theorem cell22_742505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_742505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742505 prefixEnd_742505 := by exact prefixLift 742505
  have htrace : WordTrace (prefixWord ++ tailWord_742505) baseStart_742505 baseEnd_742505 := by
    simpa [prefixWord, tailWord_742505, baseEnd_742505] using wordTrace_append hprefix tailTrace_742505
  have hstable : (prefixWord ++ tailWord_742505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742505).length < 2 ^ (prefixWord ++ tailWord_742505).sum := by decide
  have hdescent : baseEnd_742505 < baseStart_742505 := by decide
  rcases family_descends (prefixWord ++ tailWord_742505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742520 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_742520 : Nat := 118140960795 + 742520 * 2 ^ 59
def prefixEnd_742520 : Nat := 4983230072969 + 3 ^ 40 * 742520 * 2
def baseEnd_742520 : Nat := 254179770384360080523479

theorem tailTrace_742520 : CollatzResearch.WordTrace tailWord_742520 prefixEnd_742520 254179770384360080523479 := by
  unfold tailWord_742520
  simp only [CollatzResearch.WordTrace]
  refine ⟨13540964634992163582532507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18054619513322884776710009 13540964634992163582532507)
  ·
    refine ⟨20311446952488245373798761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13540964634992163582532507 20311446952488245373798761)
    ·
      refine ⟨15233585214366184030349071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20311446952488245373798761 15233585214366184030349071)
      ·
        refine ⟨22850377821549276045523607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15233585214366184030349071 22850377821549276045523607)
        ·
          refine ⟨34275566732323914068285411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22850377821549276045523607 34275566732323914068285411)
          ·
            refine ⟨51413350098485871102428117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34275566732323914068285411 51413350098485871102428117)
            ·
              refine ⟨1205000392933262603963159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51413350098485871102428117 1205000392933262603963159)
              ·
                refine ⟨1807500589399893905944739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205000392933262603963159 1807500589399893905944739)
                ·
                  refine ⟨2711250884099840858917109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807500589399893905944739 2711250884099840858917109)
                  ·
                    refine ⟨254179770384360080523479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2711250884099840858917109 254179770384360080523479)
                    ·
                      rfl

theorem cell22_742520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_742520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742520 prefixEnd_742520 := by exact prefixLift 742520
  have htrace : WordTrace (prefixWord ++ tailWord_742520) baseStart_742520 baseEnd_742520 := by
    simpa [prefixWord, tailWord_742520, baseEnd_742520] using wordTrace_append hprefix tailTrace_742520
  have hstable : (prefixWord ++ tailWord_742520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742520).length < 2 ^ (prefixWord ++ tailWord_742520).sum := by decide
  have hdescent : baseEnd_742520 < baseStart_742520 := by decide
  rcases family_descends (prefixWord ++ tailWord_742520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742535 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 2, 4]
def baseStart_742535 : Nat := 118140960795 + 742535 * 2 ^ 59
def prefixEnd_742535 : Nat := 4983230072969 + 3 ^ 40 * 742535 * 2
def baseEnd_742535 : Nat := 254184905190905041398433

theorem tailTrace_742535 : CollatzResearch.WordTrace tailWord_742535 prefixEnd_742535 254184905190905041398433 := by
  unfold tailWord_742535
  simp only [CollatzResearch.WordTrace]
  refine ⟨27082476364929984726861059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18054984243286656484574039 27082476364929984726861059)
  ·
    refine ⟨40623714547394977090291589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27082476364929984726861059 40623714547394977090291589)
    ·
      refine ⟨7616946477636558204429673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40623714547394977090291589 7616946477636558204429673)
      ·
        refine ⟨5712709858227418653322255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7616946477636558204429673 5712709858227418653322255)
        ·
          refine ⟨8569064787341127979983383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712709858227418653322255 8569064787341127979983383)
          ·
            refine ⟨12853597181011691969975075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8569064787341127979983383 12853597181011691969975075)
            ·
              refine ⟨19280395771517537954962613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12853597181011691969975075 19280395771517537954962613)
              ·
                refine ⟨1807537103579769183277745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19280395771517537954962613 1807537103579769183277745)
                ·
                  refine ⟨1355652827684826887458309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807537103579769183277745 1355652827684826887458309)
                  ·
                    refine ⟨254184905190905041398433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1355652827684826887458309 254184905190905041398433)
                    ·
                      rfl

theorem cell22_742535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_742535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742535 prefixEnd_742535 := by exact prefixLift 742535
  have htrace : WordTrace (prefixWord ++ tailWord_742535) baseStart_742535 baseEnd_742535 := by
    simpa [prefixWord, tailWord_742535, baseEnd_742535] using wordTrace_append hprefix tailTrace_742535
  have hstable : (prefixWord ++ tailWord_742535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742535).length < 2 ^ (prefixWord ++ tailWord_742535).sum := by decide
  have hdescent : baseEnd_742535 < baseStart_742535 := by decide
  rcases family_descends (prefixWord ++ tailWord_742535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742552 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_742552 : Nat := 118140960795 + 742552 * 2 ^ 59
def prefixEnd_742552 : Nat := 4983230072969 + 3 ^ 40 * 742552 * 2
def baseEnd_742552 : Nat := 254190724638322663723381

theorem tailTrace_742552 : CollatzResearch.WordTrace tailWord_742552 prefixEnd_742552 254190724638322663723381 := by
  unfold tailWord_742552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13541548202934198315114955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18055397603912264420153273 13541548202934198315114955)
  ·
    refine ⟨20312322304401297472672433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13541548202934198315114955 20312322304401297472672433)
    ·
      refine ⟨15234241728300973104504325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20312322304401297472672433 15234241728300973104504325)
      ·
        refine ⟨2856420324056432457094561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15234241728300973104504325 2856420324056432457094561)
        ·
          refine ⟨2142315243042324342820921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856420324056432457094561 2142315243042324342820921)
          ·
            refine ⟨1606736432281743257115691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142315243042324342820921 1606736432281743257115691)
            ·
              refine ⟨2410104648422614885673537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606736432281743257115691 2410104648422614885673537)
              ·
                refine ⟨1807578486316961164255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410104648422614885673537 1807578486316961164255153)
                ·
                  refine ⟨1355683864737720873191365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807578486316961164255153 1355683864737720873191365)
                  ·
                    refine ⟨254190724638322663723381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1355683864737720873191365 254190724638322663723381)
                    ·
                      rfl

theorem cell22_742552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_742552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742552 prefixEnd_742552 := by exact prefixLift 742552
  have htrace : WordTrace (prefixWord ++ tailWord_742552) baseStart_742552 baseEnd_742552 := by
    simpa [prefixWord, tailWord_742552, baseEnd_742552] using wordTrace_append hprefix tailTrace_742552
  have hstable : (prefixWord ++ tailWord_742552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742552).length < 2 ^ (prefixWord ++ tailWord_742552).sum := by decide
  have hdescent : baseEnd_742552 < baseStart_742552 := by decide
  rcases family_descends (prefixWord ++ tailWord_742552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742567 : List Nat := [1, 1, 6, 2, 1, 2, 2, 7]
def baseStart_742567 : Nat := 118140960795 + 742567 * 2 ^ 59
def prefixEnd_742567 : Nat := 4983230072969 + 3 ^ 40 * 742567 * 2
def baseEnd_742567 : Nat := 28243984382763069399815

theorem tailTrace_742567 : CollatzResearch.WordTrace tailWord_742567 prefixEnd_742567 28243984382763069399815 := by
  unfold tailWord_742567
  simp only [CollatzResearch.WordTrace]
  refine ⟨27083643500814054192025955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18055762333876036128017303 27083643500814054192025955)
  ·
    refine ⟨40625465251221081288038933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27083643500814054192025955 40625465251221081288038933)
    ·
      refine ⟨1904318683650988185376825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40625465251221081288038933 1904318683650988185376825)
      ·
        refine ⟨1428239012738241139032619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1904318683650988185376825 1428239012738241139032619)
        ·
          refine ⟨2142358519107361708548929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428239012738241139032619 2142358519107361708548929)
          ·
            refine ⟨1606768889330521281411697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142358519107361708548929 1606768889330521281411697)
            ·
              refine ⟨1205076666997890961058773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606768889330521281411697 1205076666997890961058773)
              ·
                refine ⟨28243984382763069399815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1205076666997890961058773 28243984382763069399815)
                ·
                  rfl

theorem cell22_742567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 7].length) (baseStart_742567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742567 prefixEnd_742567 := by exact prefixLift 742567
  have htrace : WordTrace (prefixWord ++ tailWord_742567) baseStart_742567 baseEnd_742567 := by
    simpa [prefixWord, tailWord_742567, baseEnd_742567] using wordTrace_append hprefix tailTrace_742567
  have hstable : (prefixWord ++ tailWord_742567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742567).length < 2 ^ (prefixWord ++ tailWord_742567).sum := by decide
  have hdescent : baseEnd_742567 < baseStart_742567 := by decide
  rcases family_descends (prefixWord ++ tailWord_742567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742616 : List Nat := [2, 1, 2, 2, 5, 1, 1, 4, 1, 3]
def baseStart_742616 : Nat := 118140960795 + 742616 * 2 ^ 59
def prefixEnd_742616 : Nat := 4983230072969 + 3 ^ 40 * 742616 * 2
def baseEnd_742616 : Nat := 254212633146247830123185

theorem tailTrace_742616 : CollatzResearch.WordTrace tailWord_742616 prefixEnd_742616 254212633146247830123185 := by
  unfold tailWord_742616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542715338818267780279851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18056953785091023707039801 13542715338818267780279851)
  ·
    refine ⟨20314073008227401670419777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13542715338818267780279851 20314073008227401670419777)
    ·
      refine ⟨15235554756170551252814833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20314073008227401670419777 15235554756170551252814833)
      ·
        refine ⟨11426666067127913439611125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15235554756170551252814833 11426666067127913439611125)
        ·
          refine ⟨1071249943793241884963543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11426666067127913439611125 1071249943793241884963543)
          ·
            refine ⟨1606874915689862827445315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071249943793241884963543 1606874915689862827445315)
            ·
              refine ⟨2410312373534794241167973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606874915689862827445315 2410312373534794241167973)
              ·
                refine ⟨451933570037773920218995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2410312373534794241167973 451933570037773920218995)
                ·
                  refine ⟨677900355056660880328493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451933570037773920218995 677900355056660880328493)
                  ·
                    refine ⟨254212633146247830123185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677900355056660880328493 254212633146247830123185)
                    ·
                      rfl

theorem cell22_742616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_742616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742616 prefixEnd_742616 := by exact prefixLift 742616
  have htrace : WordTrace (prefixWord ++ tailWord_742616) baseStart_742616 baseEnd_742616 := by
    simpa [prefixWord, tailWord_742616, baseEnd_742616] using wordTrace_append hprefix tailTrace_742616
  have hstable : (prefixWord ++ tailWord_742616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742616).length < 2 ^ (prefixWord ++ tailWord_742616).sum := by decide
  have hdescent : baseEnd_742616 < baseStart_742616 := by decide
  rcases family_descends (prefixWord ++ tailWord_742616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742659 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 1, 4]
def baseStart_742659 : Nat := 118140960795 + 742659 * 2 ^ 59
def prefixEnd_742659 : Nat := 4983230072969 + 3 ^ 40 * 742659 * 2
def baseEnd_742659 : Nat := 254227352925010051298053

theorem tailTrace_742659 : CollatzResearch.WordTrace tailWord_742659 prefixEnd_742659 254227352925010051298053 := by
  unfold tailWord_742659
  simp only [CollatzResearch.WordTrace]
  refine ⟨27086999016480753904375031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18057999344320502602916687 27086999016480753904375031)
  ·
    refine ⟨40630498524721130856562547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27086999016480753904375031 40630498524721130856562547)
    ·
      refine ⟨60945747787081696284843821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40630498524721130856562547 60945747787081696284843821)
      ·
        refine ⟨22854655420155636106816433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60945747787081696284843821 22854655420155636106816433)
        ·
          refine ⟨17140991565116727080112325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22854655420155636106816433 17140991565116727080112325)
          ·
            refine ⟨3213935918459386327521061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17140991565116727080112325 3213935918459386327521061)
            ·
              refine ⟨602612984711134936410199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3213935918459386327521061 602612984711134936410199)
              ·
                refine ⟨903919477066702404615299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602612984711134936410199 903919477066702404615299)
                ·
                  refine ⟨1355879215600053606922949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903919477066702404615299 1355879215600053606922949)
                  ·
                    refine ⟨254227352925010051298053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1355879215600053606922949 254227352925010051298053)
                    ·
                      rfl

theorem cell22_742659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 4].length) (baseStart_742659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742659 prefixEnd_742659 := by exact prefixLift 742659
  have htrace : WordTrace (prefixWord ++ tailWord_742659) baseStart_742659 baseEnd_742659 := by
    simpa [prefixWord, tailWord_742659, baseEnd_742659] using wordTrace_append hprefix tailTrace_742659
  have hstable : (prefixWord ++ tailWord_742659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742659).length < 2 ^ (prefixWord ++ tailWord_742659).sum := by decide
  have hdescent : baseEnd_742659 < baseStart_742659 := by decide
  rcases family_descends (prefixWord ++ tailWord_742659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742700 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_742700 : Nat := 118140960795 + 742700 * 2 ^ 59
def prefixEnd_742700 : Nat := 4983230072969 + 3 ^ 40 * 742700 * 2
def baseEnd_742700 : Nat := 254241388062899611022927

theorem tailTrace_742700 : CollatzResearch.WordTrace tailWord_742700 prefixEnd_742700 254241388062899611022927 := by
  unfold tailWord_742700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13544247204666108953308777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18058996272888145271078369 13544247204666108953308777)
  ·
    refine ⟨10158185403499581714981583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13544247204666108953308777 10158185403499581714981583)
    ·
      refine ⟨15237278105249372572472375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10158185403499581714981583 15237278105249372572472375)
      ·
        refine ⟨22855917157874058858708563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15237278105249372572472375 22855917157874058858708563)
        ·
          refine ⟨34283875736811088288062845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22855917157874058858708563 34283875736811088288062845)
          ·
            refine ⟨12856453401304158108023567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34283875736811088288062845 12856453401304158108023567)
            ·
              refine ⟨19284680101956237162035351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12856453401304158108023567 19284680101956237162035351)
              ·
                refine ⟨28927020152934355743053027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19284680101956237162035351 28927020152934355743053027)
                ·
                  refine ⟨43390530229401533614579541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28927020152934355743053027 43390530229401533614579541)
                  ·
                    refine ⟨254241388062899611022927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 43390530229401533614579541 254241388062899611022927)
                    ·
                      rfl

theorem cell22_742700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_742700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742700 prefixEnd_742700 := by exact prefixLift 742700
  have htrace : WordTrace (prefixWord ++ tailWord_742700) baseStart_742700 baseEnd_742700 := by
    simpa [prefixWord, tailWord_742700, baseEnd_742700] using wordTrace_append hprefix tailTrace_742700
  have hstable : (prefixWord ++ tailWord_742700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742700).length < 2 ^ (prefixWord ++ tailWord_742700).sum := by decide
  have hdescent : baseEnd_742700 < baseStart_742700 := by decide
  rcases family_descends (prefixWord ++ tailWord_742700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742841 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 4, 3]
def baseStart_742841 : Nat := 118140960795 + 742841 * 2 ^ 59
def prefixEnd_742841 : Nat := 4983230072969 + 3 ^ 40 * 742841 * 2
def baseEnd_742841 : Nat := 254289655244422243247495

theorem tailTrace_742841 : CollatzResearch.WordTrace tailWord_742841 prefixEnd_742841 254289655244422243247495 := by
  unfold tailWord_742841
  simp only [CollatzResearch.WordTrace]
  refine ⟨27093637101821398987500377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18062424734547599325000251 27093637101821398987500377)
  ·
    refine ⟨20320227826366049240625283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27093637101821398987500377 20320227826366049240625283)
    ·
      refine ⟨30480341739549073860937925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20320227826366049240625283 30480341739549073860937925)
      ·
        refine ⟨5715064076165451348925861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30480341739549073860937925 5715064076165451348925861)
        ·
          refine ⟨1071574514281022127923599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5715064076165451348925861 1071574514281022127923599)
          ·
            refine ⟨1607361771421533191885399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071574514281022127923599 1607361771421533191885399)
            ·
              refine ⟨2411042657132299787828099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607361771421533191885399 2411042657132299787828099)
              ·
                refine ⟨3616563985698449681742149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411042657132299787828099 3616563985698449681742149)
                ·
                  refine ⟨678105747318459315326653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3616563985698449681742149 678105747318459315326653)
                  ·
                    refine ⟨254289655244422243247495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678105747318459315326653 254289655244422243247495)
                    ·
                      rfl

theorem cell22_742841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_742841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742841 prefixEnd_742841 := by exact prefixLift 742841
  have htrace : WordTrace (prefixWord ++ tailWord_742841) baseStart_742841 baseEnd_742841 := by
    simpa [prefixWord, tailWord_742841, baseEnd_742841] using wordTrace_append hprefix tailTrace_742841
  have hstable : (prefixWord ++ tailWord_742841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742841).length < 2 ^ (prefixWord ++ tailWord_742841).sum := by decide
  have hdescent : baseEnd_742841 < baseStart_742841 := by decide
  rcases family_descends (prefixWord ++ tailWord_742841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742858 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_742858 : Nat := 118140960795 + 742858 * 2 ^ 59
def prefixEnd_742858 : Nat := 4983230072969 + 3 ^ 40 * 742858 * 2
def baseEnd_742858 : Nat := 254295474691839865572443

theorem tailTrace_742858 : CollatzResearch.WordTrace tailWord_742858 prefixEnd_742858 254295474691839865572443 := by
  unfold tailWord_742858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6773564285689952722717307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18062838095173207260579485 6773564285689952722717307)
  ·
    refine ⟨10160346428534929084075961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6773564285689952722717307 10160346428534929084075961)
    ·
      refine ⟨7620259821401196813056971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10160346428534929084075961 7620259821401196813056971)
      ·
        refine ⟨11430389732101795219585457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7620259821401196813056971 11430389732101795219585457)
        ·
          refine ⟨8572792299076346414689093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11430389732101795219585457 8572792299076346414689093)
          ·
            refine ⟨1607398556076814952754205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8572792299076346414689093 1607398556076814952754205)
            ·
              refine ⟨602774458528805607282827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1607398556076814952754205 602774458528805607282827)
              ·
                refine ⟨904161687793208410924241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602774458528805607282827 904161687793208410924241)
                ·
                  refine ⟨678121265844906308193181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 904161687793208410924241 678121265844906308193181)
                  ·
                    refine ⟨254295474691839865572443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678121265844906308193181 254295474691839865572443)
                    ·
                      rfl

theorem cell22_742858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_742858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742858 prefixEnd_742858 := by exact prefixLift 742858
  have htrace : WordTrace (prefixWord ++ tailWord_742858) baseStart_742858 baseEnd_742858 := by
    simpa [prefixWord, tailWord_742858, baseEnd_742858] using wordTrace_append hprefix tailTrace_742858
  have hstable : (prefixWord ++ tailWord_742858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742858).length < 2 ^ (prefixWord ++ tailWord_742858).sum := by decide
  have hdescent : baseEnd_742858 < baseStart_742858 := by decide
  rcases family_descends (prefixWord ++ tailWord_742858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742929 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_742929 : Nat := 118140960795 + 742929 * 2 ^ 59
def prefixEnd_742929 : Nat := 4983230072969 + 3 ^ 40 * 742929 * 2
def baseEnd_742929 : Nat := 254319779442819347047225

theorem tailTrace_742929 : CollatzResearch.WordTrace tailWord_742929 prefixEnd_742929 254319779442819347047225 := by
  unfold tailWord_742929
  simp only [CollatzResearch.WordTrace]
  refine ⟨27096846725502590016703841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18064564483668393344469227 27096846725502590016703841)
  ·
    refine ⟨20322635044126942512527881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27096846725502590016703841 20322635044126942512527881)
    ·
      refine ⟨15241976283095206884395911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20322635044126942512527881 15241976283095206884395911)
      ·
        refine ⟨22862964424642810326593867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15241976283095206884395911 22862964424642810326593867)
        ·
          refine ⟨34294446636964215489890801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22862964424642810326593867 34294446636964215489890801)
          ·
            refine ⟨25720834977723161617418101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34294446636964215489890801 25720834977723161617418101)
            ·
              refine ⟨2411328279161546401632947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25720834977723161617418101 2411328279161546401632947)
              ·
                refine ⟨3616992418742319602449421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411328279161546401632947 3616992418742319602449421)
                ·
                  refine ⟨1356372157028369850918533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3616992418742319602449421 1356372157028369850918533)
                  ·
                    refine ⟨254319779442819347047225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1356372157028369850918533 254319779442819347047225)
                    ·
                      rfl

theorem cell22_742929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_742929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742929 prefixEnd_742929 := by exact prefixLift 742929
  have htrace : WordTrace (prefixWord ++ tailWord_742929) baseStart_742929 baseEnd_742929 := by
    simpa [prefixWord, tailWord_742929, baseEnd_742929] using wordTrace_append hprefix tailTrace_742929
  have hstable : (prefixWord ++ tailWord_742929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742929).length < 2 ^ (prefixWord ++ tailWord_742929).sum := by decide
  have hdescent : baseEnd_742929 < baseStart_742929 := by decide
  rcases family_descends (prefixWord ++ tailWord_742929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742946 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_742946 : Nat := 118140960795 + 742946 * 2 ^ 59
def prefixEnd_742946 : Nat := 4983230072969 + 3 ^ 40 * 742946 * 2
def baseEnd_742946 : Nat := 254325598890236969372173

theorem tailTrace_742946 : CollatzResearch.WordTrace tailWord_742946 prefixEnd_742946 254325598890236969372173 := by
  unfold tailWord_742946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774366691610250480018173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18064977844294001280048461 6774366691610250480018173)
  ·
    refine ⟨2540387509353843930006815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6774366691610250480018173 2540387509353843930006815)
    ·
      refine ⟨3810581264030765895010223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2540387509353843930006815 3810581264030765895010223)
      ·
        refine ⟨5715871896046148842515335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810581264030765895010223 5715871896046148842515335)
        ·
          refine ⟨8573807844069223263773003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715871896046148842515335 8573807844069223263773003)
          ·
            refine ⟨12860711766103834895659505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8573807844069223263773003 12860711766103834895659505)
            ·
              refine ⟨9645533824577876171744629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12860711766103834895659505 9645533824577876171744629)
              ·
                refine ⟨904268796054175891101059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9645533824577876171744629 904268796054175891101059)
                ·
                  refine ⟨1356403194081263836651589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904268796054175891101059 1356403194081263836651589)
                  ·
                    refine ⟨254325598890236969372173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1356403194081263836651589 254325598890236969372173)
                    ·
                      rfl

theorem cell22_742946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_742946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_742946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_742946 prefixEnd_742946 := by exact prefixLift 742946
  have htrace : WordTrace (prefixWord ++ tailWord_742946) baseStart_742946 baseEnd_742946 := by
    simpa [prefixWord, tailWord_742946, baseEnd_742946] using wordTrace_append hprefix tailTrace_742946
  have hstable : (prefixWord ++ tailWord_742946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742946).length < 2 ^ (prefixWord ++ tailWord_742946).sum := by decide
  have hdescent : baseEnd_742946 < baseStart_742946 := by decide
  rcases family_descends (prefixWord ++ tailWord_742946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743049 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_743049 : Nat := 118140960795 + 743049 * 2 ^ 59
def prefixEnd_743049 : Nat := 4983230072969 + 3 ^ 40 * 743049 * 2
def baseEnd_743049 : Nat := 254360857895179034046857

theorem tailTrace_743049 : CollatzResearch.WordTrace tailWord_743049 prefixEnd_743049 254360857895179034046857 := by
  unfold tailWord_743049
  simp only [CollatzResearch.WordTrace]
  refine ⟨27101223485067850511072201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18067482323378567007381467 27101223485067850511072201)
  ·
    refine ⟨20325917613800887883304151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27101223485067850511072201 20325917613800887883304151)
    ·
      refine ⟨30488876420701331824956227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20325917613800887883304151 30488876420701331824956227)
      ·
        refine ⟨45733314631051997737434341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30488876420701331824956227 45733314631051997737434341)
        ·
          refine ⟨8574996493322249575768939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45733314631051997737434341 8574996493322249575768939)
          ·
            refine ⟨12862494739983374363653409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8574996493322249575768939 12862494739983374363653409)
            ·
              refine ⟨9646871054987530772740057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12862494739983374363653409 9646871054987530772740057)
              ·
                refine ⟨7235153291240648079555043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9646871054987530772740057 7235153291240648079555043)
                ·
                  refine ⟨10852729936860972119332565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7235153291240648079555043 10852729936860972119332565)
                  ·
                    refine ⟨254360857895179034046857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10852729936860972119332565 254360857895179034046857)
                    ·
                      rfl

theorem cell22_743049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_743049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743049 prefixEnd_743049 := by exact prefixLift 743049
  have htrace : WordTrace (prefixWord ++ tailWord_743049) baseStart_743049 baseEnd_743049 := by
    simpa [prefixWord, tailWord_743049, baseEnd_743049] using wordTrace_append hprefix tailTrace_743049
  have hstable : (prefixWord ++ tailWord_743049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743049).length < 2 ^ (prefixWord ++ tailWord_743049).sum := by decide
  have hdescent : baseEnd_743049 < baseStart_743049 := by decide
  rcases family_descends (prefixWord ++ tailWord_743049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743072 : List Nat := [2, 1, 1, 4, 3, 2, 3, 2, 1, 3]
def baseStart_743072 : Nat := 118140960795 + 743072 * 2 ^ 59
def prefixEnd_743072 : Nat := 4983230072969 + 3 ^ 40 * 743072 * 2
def baseEnd_743072 : Nat := 254368731265214640721787

theorem tailTrace_743072 : CollatzResearch.WordTrace tailWord_743072 prefixEnd_743072 254368731265214640721787 := by
  unfold tailWord_743072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13551031181992262719579735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18068041575989683626106313 13551031181992262719579735)
  ·
    refine ⟨20326546772988394079369603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13551031181992262719579735 20326546772988394079369603)
    ·
      refine ⟨30489820159482591119054405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20326546772988394079369603 30489820159482591119054405)
      ·
        refine ⟨5716841279902985834822701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30489820159482591119054405 5716841279902985834822701)
        ·
          refine ⟨2143815479963619688058513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5716841279902985834822701 2143815479963619688058513)
          ·
            refine ⟨1607861609972714766043885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2143815479963619688058513 1607861609972714766043885)
            ·
              refine ⟨602948103739768037266457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1607861609972714766043885 602948103739768037266457)
              ·
                refine ⟨452211077804826027949843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602948103739768037266457 452211077804826027949843)
                ·
                  refine ⟨678316616707239041924765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452211077804826027949843 678316616707239041924765)
                  ·
                    refine ⟨254368731265214640721787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678316616707239041924765 254368731265214640721787)
                    ·
                      rfl

theorem cell22_743072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 3].length) (baseStart_743072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743072 prefixEnd_743072 := by exact prefixLift 743072
  have htrace : WordTrace (prefixWord ++ tailWord_743072) baseStart_743072 baseEnd_743072 := by
    simpa [prefixWord, tailWord_743072, baseEnd_743072] using wordTrace_append hprefix tailTrace_743072
  have hstable : (prefixWord ++ tailWord_743072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743072).length < 2 ^ (prefixWord ++ tailWord_743072).sum := by decide
  have hdescent : baseEnd_743072 < baseStart_743072 := by decide
  rcases family_descends (prefixWord ++ tailWord_743072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743098 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_743098 : Nat := 118140960795 + 743098 * 2 ^ 59
def prefixEnd_743098 : Nat := 4983230072969 + 3 ^ 40 * 743098 * 2
def baseEnd_743098 : Nat := 254377631596559239571707

theorem tailTrace_743098 : CollatzResearch.WordTrace tailWord_743098 prefixEnd_743098 254377631596559239571707 := by
  unfold tailWord_743098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775752665472582969901487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18068673774593554586403965 6775752665472582969901487)
  ·
    refine ⟨10163628998208874454852231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6775752665472582969901487 10163628998208874454852231)
    ·
      refine ⟨15245443497313311682278347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10163628998208874454852231 15245443497313311682278347)
      ·
        refine ⟨22868165245969967523417521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15245443497313311682278347 22868165245969967523417521)
        ·
          refine ⟨17151123934477475642563141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22868165245969967523417521 17151123934477475642563141)
          ·
            refine ⟨3215835737714526682980589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17151123934477475642563141 3215835737714526682980589)
            ·
              refine ⟨1205938401642947506117721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3215835737714526682980589 1205938401642947506117721)
              ·
                refine ⟨904453801232210629588291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205938401642947506117721 904453801232210629588291)
                ·
                  refine ⟨1356680701848315944382437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904453801232210629588291 1356680701848315944382437)
                  ·
                    refine ⟨254377631596559239571707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1356680701848315944382437 254377631596559239571707)
                    ·
                      rfl

theorem cell22_743098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_743098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743098 prefixEnd_743098 := by exact prefixLift 743098
  have htrace : WordTrace (prefixWord ++ tailWord_743098) baseStart_743098 baseEnd_743098 := by
    simpa [prefixWord, tailWord_743098, baseEnd_743098] using wordTrace_append hprefix tailTrace_743098
  have hstable : (prefixWord ++ tailWord_743098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743098).length < 2 ^ (prefixWord ++ tailWord_743098).sum := by decide
  have hdescent : baseEnd_743098 < baseStart_743098 := by decide
  rcases family_descends (prefixWord ++ tailWord_743098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743111 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 1, 5]
def baseStart_743111 : Nat := 118140960795 + 743111 * 2 ^ 59
def prefixEnd_743111 : Nat := 4983230072969 + 3 ^ 40 * 743111 * 2
def baseEnd_743111 : Nat := 254382081762231538996667

theorem tailTrace_743111 : CollatzResearch.WordTrace tailWord_743111 prefixEnd_743111 254382081762231538996667 := by
  unfold tailWord_743111
  simp only [CollatzResearch.WordTrace]
  refine ⟨27103484810843235099829187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18068989873895490066552791 27103484810843235099829187)
  ·
    refine ⟨40655227216264852649743781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27103484810843235099829187 40655227216264852649743781)
    ·
      refine ⟨7622855103049659871826959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40655227216264852649743781 7622855103049659871826959)
      ·
        refine ⟨11434282654574489807740439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7622855103049659871826959 11434282654574489807740439)
        ·
          refine ⟨17151423981861734711610659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11434282654574489807740439 17151423981861734711610659)
          ·
            refine ⟨25727135972792602067415989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17151423981861734711610659 25727135972792602067415989)
            ·
              refine ⟨2411918997449306443820249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25727135972792602067415989 2411918997449306443820249)
              ·
                refine ⟨1808939248086979832865187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411918997449306443820249 1808939248086979832865187)
                ·
                  refine ⟨2713408872130469749297781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808939248086979832865187 2713408872130469749297781)
                  ·
                    refine ⟨254382081762231538996667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2713408872130469749297781 254382081762231538996667)
                    ·
                      rfl

theorem cell22_743111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_743111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743111 prefixEnd_743111 := by exact prefixLift 743111
  have htrace : WordTrace (prefixWord ++ tailWord_743111) baseStart_743111 baseEnd_743111 := by
    simpa [prefixWord, tailWord_743111, baseEnd_743111] using wordTrace_append hprefix tailTrace_743111
  have hstable : (prefixWord ++ tailWord_743111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743111).length < 2 ^ (prefixWord ++ tailWord_743111).sum := by decide
  have hdescent : baseEnd_743111 < baseStart_743111 := by decide
  rcases family_descends (prefixWord ++ tailWord_743111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743130 : List Nat := [3, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_743130 : Nat := 118140960795 + 743130 * 2 ^ 59
def prefixEnd_743130 : Nat := 4983230072969 + 3 ^ 40 * 743130 * 2
def baseEnd_743130 : Nat := 84796195283507274257203

theorem tailTrace_743130 : CollatzResearch.WordTrace tailWord_743130 prefixEnd_743130 84796195283507274257203 := by
  unfold tailWord_743130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6776044449443600336192711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18069451865182934229847229 6776044449443600336192711)
  ·
    refine ⟨10164066674165400504289067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6776044449443600336192711 10164066674165400504289067)
    ·
      refine ⟨15246100011248100756433601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10164066674165400504289067 15246100011248100756433601)
      ·
        refine ⟨11434575008436075567325201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15246100011248100756433601 11434575008436075567325201)
        ·
          refine ⟨8575931256327056675493901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11434575008436075567325201 8575931256327056675493901)
          ·
            refine ⟨3215974221122646253310213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8575931256327056675493901 3215974221122646253310213)
            ·
              refine ⟨602995166460496172495665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3215974221122646253310213 602995166460496172495665)
              ·
                refine ⟨452246374845372129371749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602995166460496172495665 452246374845372129371749)
                ·
                  refine ⟨84796195283507274257203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452246374845372129371749 84796195283507274257203)
                  ·
                    rfl

theorem cell22_743130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_743130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743130 prefixEnd_743130 := by exact prefixLift 743130
  have htrace : WordTrace (prefixWord ++ tailWord_743130) baseStart_743130 baseEnd_743130 := by
    simpa [prefixWord, tailWord_743130, baseEnd_743130] using wordTrace_append hprefix tailTrace_743130
  have hstable : (prefixWord ++ tailWord_743130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743130).length < 2 ^ (prefixWord ++ tailWord_743130).sum := by decide
  have hdescent : baseEnd_743130 < baseStart_743130 := by decide
  rcases family_descends (prefixWord ++ tailWord_743130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743267 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 1, 4]
def baseStart_743267 : Nat := 118140960795 + 743267 * 2 ^ 59
def prefixEnd_743267 : Nat := 4983230072969 + 3 ^ 40 * 743267 * 2
def baseEnd_743267 : Nat := 254435483750299132096189

theorem tailTrace_743267 : CollatzResearch.WordTrace tailWord_743267 prefixEnd_743267 254435483750299132096189 := by
  unfold tailWord_743267
  simp only [CollatzResearch.WordTrace]
  refine ⟨27109174598278073742508055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18072783065518715828338703 27109174598278073742508055)
  ·
    refine ⟨40663761897417110613762083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27109174598278073742508055 40663761897417110613762083)
    ·
      refine ⟨60995642846125665920643125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40663761897417110613762083 60995642846125665920643125)
      ·
        refine ⟨5718341516824281180060293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60995642846125665920643125 5718341516824281180060293)
        ·
          refine ⟨1072189034404552721261305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5718341516824281180060293 1072189034404552721261305)
          ·
            refine ⟨804141775803414540945979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072189034404552721261305 804141775803414540945979)
            ·
              refine ⟨1206212663705121811418969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804141775803414540945979 1206212663705121811418969)
              ·
                refine ⟨904659497778841358564227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206212663705121811418969 904659497778841358564227)
                ·
                  refine ⟨1356989246668262037846341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904659497778841358564227 1356989246668262037846341)
                  ·
                    refine ⟨254435483750299132096189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1356989246668262037846341 254435483750299132096189)
                    ·
                      rfl

theorem cell22_743267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 4].length) (baseStart_743267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743267 prefixEnd_743267 := by exact prefixLift 743267
  have htrace : WordTrace (prefixWord ++ tailWord_743267) baseStart_743267 baseEnd_743267 := by
    simpa [prefixWord, tailWord_743267, baseEnd_743267] using wordTrace_append hprefix tailTrace_743267
  have hstable : (prefixWord ++ tailWord_743267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743267).length < 2 ^ (prefixWord ++ tailWord_743267).sum := by decide
  have hdescent : baseEnd_743267 < baseStart_743267 := by decide
  rcases family_descends (prefixWord ++ tailWord_743267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743325 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_743325 : Nat := 118140960795 + 743325 * 2 ^ 59
def prefixEnd_743325 : Nat := 4983230072969 + 3 ^ 40 * 743325 * 2
def baseEnd_743325 : Nat := 254455338335606314146011

theorem tailTrace_743325 : CollatzResearch.WordTrace tailWord_743325 prefixEnd_743325 254455338335606314146011 := by
  unfold tailWord_743325
  simp only [CollatzResearch.WordTrace]
  refine ⟨27111290032067949648119429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18074193354711966432079619 27111290032067949648119429)
  ·
    refine ⟨5083366881012740559022393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27111290032067949648119429 5083366881012740559022393)
    ·
      refine ⟨3812525160759555419266795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5083366881012740559022393 3812525160759555419266795)
      ·
        refine ⟨5718787741139333128900193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812525160759555419266795 5718787741139333128900193)
        ·
          refine ⟨4289090805854499846675145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5718787741139333128900193 4289090805854499846675145)
          ·
            refine ⟨3216818104390874885006359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4289090805854499846675145 3216818104390874885006359)
            ·
              refine ⟨4825227156586312327509539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216818104390874885006359 4825227156586312327509539)
              ·
                refine ⟨7237840734879468491264309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825227156586312327509539 7237840734879468491264309)
                ·
                  refine ⟨678547568894950171056029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7237840734879468491264309 678547568894950171056029)
                  ·
                    refine ⟨254455338335606314146011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678547568894950171056029 254455338335606314146011)
                    ·
                      rfl

theorem cell22_743325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_743325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743325 prefixEnd_743325 := by exact prefixLift 743325
  have htrace : WordTrace (prefixWord ++ tailWord_743325) baseStart_743325 baseEnd_743325 := by
    simpa [prefixWord, tailWord_743325, baseEnd_743325] using wordTrace_append hprefix tailTrace_743325
  have hstable : (prefixWord ++ tailWord_743325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743325).length < 2 ^ (prefixWord ++ tailWord_743325).sum := by decide
  have hdescent : baseEnd_743325 < baseStart_743325 := by decide
  rcases family_descends (prefixWord ++ tailWord_743325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743329 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 2, 4]
def baseStart_743329 : Nat := 118140960795 + 743329 * 2 ^ 59
def prefixEnd_743329 : Nat := 4983230072969 + 3 ^ 40 * 743329 * 2
def baseEnd_743329 : Nat := 254456707617351637045999

theorem tailTrace_743329 : CollatzResearch.WordTrace tailWord_743329 prefixEnd_743329 254456707617351637045999 := by
  unfold tailWord_743329
  simp only [CollatzResearch.WordTrace]
  refine ⟨27111435924053458331265041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18074290616035638887510027 27111435924053458331265041)
  ·
    refine ⟨20333576943040093748448781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27111435924053458331265041 20333576943040093748448781)
    ·
      refine ⟨7625091353640035155668293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20333576943040093748448781 7625091353640035155668293)
      ·
        refine ⟨1429704628807506591687805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7625091353640035155668293 1429704628807506591687805)
        ·
          refine ⟨536139235802814971882927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1429704628807506591687805 536139235802814971882927)
          ·
            refine ⟨804208853704222457824391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536139235802814971882927 804208853704222457824391)
            ·
              refine ⟨1206313280556333686736587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804208853704222457824391 1206313280556333686736587)
              ·
                refine ⟨1809469920834500530104881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206313280556333686736587 1809469920834500530104881)
                ·
                  refine ⟨1357102440625875397578661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1809469920834500530104881 1357102440625875397578661)
                  ·
                    refine ⟨254456707617351637045999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1357102440625875397578661 254456707617351637045999)
                    ·
                      rfl

theorem cell22_743329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_743329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743329 prefixEnd_743329 := by exact prefixLift 743329
  have htrace : WordTrace (prefixWord ++ tailWord_743329) baseStart_743329 baseEnd_743329 := by
    simpa [prefixWord, tailWord_743329, baseEnd_743329] using wordTrace_append hprefix tailTrace_743329
  have hstable : (prefixWord ++ tailWord_743329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743329).length < 2 ^ (prefixWord ++ tailWord_743329).sum := by decide
  have hdescent : baseEnd_743329 < baseStart_743329 := by decide
  rcases family_descends (prefixWord ++ tailWord_743329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743348 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_743348 : Nat := 118140960795 + 743348 * 2 ^ 59
def prefixEnd_743348 : Nat := 4983230072969 + 3 ^ 40 * 743348 * 2
def baseEnd_743348 : Nat := 254463211705641920820941

theorem tailTrace_743348 : CollatzResearch.WordTrace tailWord_743348 prefixEnd_743348 254463211705641920820941 := by
  unfold tailWord_743348
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556064455492312288103349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18074752607323083050804465 13556064455492312288103349)
  ·
    refine ⟨1270881042702404277009689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13556064455492312288103349 1270881042702404277009689)
    ·
      refine ⟨953160782026803207757267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1270881042702404277009689 953160782026803207757267)
      ·
        refine ⟨1429741173040204811635901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953160782026803207757267 1429741173040204811635901)
        ·
          refine ⟨536152939890076804363463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1429741173040204811635901 536152939890076804363463)
          ·
            refine ⟨804229409835115206545195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536152939890076804363463 804229409835115206545195)
            ·
              refine ⟨1206344114752672809817793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804229409835115206545195 1206344114752672809817793)
              ·
                refine ⟨904758086064504607363345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206344114752672809817793 904758086064504607363345)
                ·
                  refine ⟨678568564548378455522509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 904758086064504607363345 678568564548378455522509)
                  ·
                    refine ⟨254463211705641920820941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678568564548378455522509 254463211705641920820941)
                    ·
                      rfl

theorem cell22_743348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_743348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743348 prefixEnd_743348 := by exact prefixLift 743348
  have htrace : WordTrace (prefixWord ++ tailWord_743348) baseStart_743348 baseEnd_743348 := by
    simpa [prefixWord, tailWord_743348, baseEnd_743348] using wordTrace_append hprefix tailTrace_743348
  have hstable : (prefixWord ++ tailWord_743348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743348).length < 2 ^ (prefixWord ++ tailWord_743348).sum := by decide
  have hdescent : baseEnd_743348 < baseStart_743348 := by decide
  rcases family_descends (prefixWord ++ tailWord_743348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743353 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_743353 : Nat := 118140960795 + 743353 * 2 ^ 59
def prefixEnd_743353 : Nat := 4983230072969 + 3 ^ 40 * 743353 * 2
def baseEnd_743353 : Nat := 254464923307823574445925

theorem tailTrace_743353 : CollatzResearch.WordTrace tailWord_743353 prefixEnd_743353 254464923307823574445925 := by
  unfold tailWord_743353
  simp only [CollatzResearch.WordTrace]
  refine ⟨27112311275966510430138713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18074874183977673620092475 27112311275966510430138713)
  ·
    refine ⟨20334233456974882822604035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27112311275966510430138713 20334233456974882822604035)
    ·
      refine ⟨30501350185462324233906053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20334233456974882822604035 30501350185462324233906053)
      ·
        refine ⟨5719003159774185793857385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30501350185462324233906053 5719003159774185793857385)
        ·
          refine ⟨4289252369830639345393039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5719003159774185793857385 4289252369830639345393039)
          ·
            refine ⟨6433878554745959018089559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4289252369830639345393039 6433878554745959018089559)
            ·
              refine ⟨9650817832118938527134339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6433878554745959018089559 9650817832118938527134339)
              ·
                refine ⟨14476226748178407790701509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9650817832118938527134339 14476226748178407790701509)
                ·
                  refine ⟨2714292515283451460756533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14476226748178407790701509 2714292515283451460756533)
                  ·
                    refine ⟨254464923307823574445925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2714292515283451460756533 254464923307823574445925)
                    ·
                      rfl

theorem cell22_743353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_743353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743353 prefixEnd_743353 := by exact prefixLift 743353
  have htrace : WordTrace (prefixWord ++ tailWord_743353) baseStart_743353 baseEnd_743353 := by
    simpa [prefixWord, tailWord_743353, baseEnd_743353] using wordTrace_append hprefix tailTrace_743353
  have hstable : (prefixWord ++ tailWord_743353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743353).length < 2 ^ (prefixWord ++ tailWord_743353).sum := by decide
  have hdescent : baseEnd_743353 < baseStart_743353 := by decide
  rcases family_descends (prefixWord ++ tailWord_743353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743372 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 5]
def baseStart_743372 : Nat := 118140960795 + 743372 * 2 ^ 59
def prefixEnd_743372 : Nat := 4983230072969 + 3 ^ 40 * 743372 * 2
def baseEnd_743372 : Nat := 84823809132037952740289

theorem tailTrace_743372 : CollatzResearch.WordTrace tailWord_743372 prefixEnd_743372 84823809132037952740289 := by
  unfold tailWord_743372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556502131448838337540185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18075336175265117783386913 13556502131448838337540185)
  ·
    refine ⟨10167376598586628753155139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13556502131448838337540185 10167376598586628753155139)
    ·
      refine ⟨15251064897879943129732709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10167376598586628753155139 15251064897879943129732709)
      ·
        refine ⟨2859574668352489336824883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15251064897879943129732709 2859574668352489336824883)
        ·
          refine ⟨4289362002528734005237325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859574668352489336824883 4289362002528734005237325)
          ·
            refine ⟨1608510750948275251963997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4289362002528734005237325 1608510750948275251963997)
            ·
              refine ⟨603191531605603219486499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1608510750948275251963997 603191531605603219486499)
              ·
                refine ⟨904787297408404829229749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603191531605603219486499 904787297408404829229749)
                ·
                  refine ⟨84823809132037952740289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 904787297408404829229749 84823809132037952740289)
                  ·
                    rfl

theorem cell22_743372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_743372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743372 prefixEnd_743372 := by exact prefixLift 743372
  have htrace : WordTrace (prefixWord ++ tailWord_743372) baseStart_743372 baseEnd_743372 := by
    simpa [prefixWord, tailWord_743372, baseEnd_743372] using wordTrace_append hprefix tailTrace_743372
  have hstable : (prefixWord ++ tailWord_743372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743372).length < 2 ^ (prefixWord ++ tailWord_743372).sum := by decide
  have hdescent : baseEnd_743372 < baseStart_743372 := by decide
  rcases family_descends (prefixWord ++ tailWord_743372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743383 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 6]
def baseStart_743383 : Nat := 118140960795 + 743383 * 2 ^ 59
def prefixEnd_743383 : Nat := 4983230072969 + 3 ^ 40 * 743383 * 2
def baseEnd_743383 : Nat := 84825064306971165398611

theorem tailTrace_743383 : CollatzResearch.WordTrace tailWord_743383 prefixEnd_743383 84825064306971165398611 := by
  unfold tailWord_743383
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113405465857825553730803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18075603643905217035820535 27113405465857825553730803)
  ·
    refine ⟨40670108198786738330596205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27113405465857825553730803 40670108198786738330596205)
    ·
      refine ⟨15251290574545026873973577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40670108198786738330596205 15251290574545026873973577)
      ·
        refine ⟨11438467930908770155480183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15251290574545026873973577 11438467930908770155480183)
        ·
          refine ⟨17157701896363155233220275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11438467930908770155480183 17157701896363155233220275)
          ·
            refine ⟨25736552844544732849830413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17157701896363155233220275 25736552844544732849830413)
            ·
              refine ⟨9651207316704274818686405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25736552844544732849830413 9651207316704274818686405)
              ·
                refine ⟨1809601371882051528503701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9651207316704274818686405 1809601371882051528503701)
                ·
                  refine ⟨84825064306971165398611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1809601371882051528503701 84825064306971165398611)
                  ·
                    rfl

theorem cell22_743383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 6].length) (baseStart_743383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743383 prefixEnd_743383 := by exact prefixLift 743383
  have htrace : WordTrace (prefixWord ++ tailWord_743383) baseStart_743383 baseEnd_743383 := by
    simpa [prefixWord, tailWord_743383, baseEnd_743383] using wordTrace_append hprefix tailTrace_743383
  have hstable : (prefixWord ++ tailWord_743383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743383).length < 2 ^ (prefixWord ++ tailWord_743383).sum := by decide
  have hdescent : baseEnd_743383 < baseStart_743383 := by decide
  rcases family_descends (prefixWord ++ tailWord_743383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743432 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 2, 3]
def baseStart_743432 : Nat := 118140960795 + 743432 * 2 ^ 59
def prefixEnd_743432 : Nat := 4983230072969 + 3 ^ 40 * 743432 * 2
def baseEnd_743432 : Nat := 254491966622293701720683

theorem tailTrace_743432 : CollatzResearch.WordTrace tailWord_743432 prefixEnd_743432 254491966622293701720683 := by
  unfold tailWord_743432
  simp only [CollatzResearch.WordTrace]
  refine ⟨13557596321340153461132275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18076795095120204614843033 13557596321340153461132275)
  ·
    refine ⟨20336394482010230191698413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13557596321340153461132275 20336394482010230191698413)
    ·
      refine ⟨7626147930753836321886905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20336394482010230191698413 7626147930753836321886905)
      ·
        refine ⟨5719610948065377241415179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7626147930753836321886905 5719610948065377241415179)
        ·
          refine ⟨8579416422098065862122769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719610948065377241415179 8579416422098065862122769)
          ·
            refine ⟨6434562316573549396592077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8579416422098065862122769 6434562316573549396592077)
            ·
              refine ⟨2412960868715081023722029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6434562316573549396592077 2412960868715081023722029)
              ·
                refine ⟨904860325768155383895761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2412960868715081023722029 904860325768155383895761)
                ·
                  refine ⟨678645244326116537921821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 904860325768155383895761 678645244326116537921821)
                  ·
                    refine ⟨254491966622293701720683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678645244326116537921821 254491966622293701720683)
                    ·
                      rfl

theorem cell22_743432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_743432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743432 prefixEnd_743432 := by exact prefixLift 743432
  have htrace : WordTrace (prefixWord ++ tailWord_743432) baseStart_743432 baseEnd_743432 := by
    simpa [prefixWord, tailWord_743432, baseEnd_743432] using wordTrace_append hprefix tailTrace_743432
  have hstable : (prefixWord ++ tailWord_743432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743432).length < 2 ^ (prefixWord ++ tailWord_743432).sum := by decide
  have hdescent : baseEnd_743432 < baseStart_743432 := by decide
  rcases family_descends (prefixWord ++ tailWord_743432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743443 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 2, 7]
def baseStart_743443 : Nat := 118140960795 + 743443 * 2 ^ 59
def prefixEnd_743443 : Nat := 4983230072969 + 3 ^ 40 * 743443 * 2
def baseEnd_743443 : Nat := 254495732147093339695649

theorem tailTrace_743443 : CollatzResearch.WordTrace tailWord_743443 prefixEnd_743443 254495732147093339695649 := by
  unfold tailWord_743443
  simp only [CollatzResearch.WordTrace]
  refine ⟨27115593845640455800914983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18077062563760303867276655 27115593845640455800914983)
  ·
    refine ⟨40673390768460683701372475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27115593845640455800914983 40673390768460683701372475)
    ·
      refine ⟨61010086152691025552058713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40673390768460683701372475 61010086152691025552058713)
      ·
        refine ⟨45757564614518269164044035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61010086152691025552058713 45757564614518269164044035)
        ·
          refine ⟨68636346921777403746066053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45757564614518269164044035 68636346921777403746066053)
          ·
            refine ⟨12869315047833263202387385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68636346921777403746066053 12869315047833263202387385)
            ·
              refine ⟨9651986285874947401790539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12869315047833263202387385 9651986285874947401790539)
              ·
                refine ⟨14477979428812421102685809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9651986285874947401790539 14477979428812421102685809)
                ·
                  refine ⟨10858484571609315827014357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14477979428812421102685809 10858484571609315827014357)
                  ·
                    refine ⟨254495732147093339695649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10858484571609315827014357 254495732147093339695649)
                    ·
                      rfl

theorem cell22_743443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_743443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743443 prefixEnd_743443 := by exact prefixLift 743443
  have htrace : WordTrace (prefixWord ++ tailWord_743443) baseStart_743443 baseEnd_743443 := by
    simpa [prefixWord, tailWord_743443, baseEnd_743443] using wordTrace_append hprefix tailTrace_743443
  have hstable : (prefixWord ++ tailWord_743443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743443).length < 2 ^ (prefixWord ++ tailWord_743443).sum := by decide
  have hdescent : baseEnd_743443 < baseStart_743443 := by decide
  rcases family_descends (prefixWord ++ tailWord_743443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743535 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 6]
def baseStart_743535 : Nat := 118140960795 + 743535 * 2 ^ 59
def prefixEnd_743535 : Nat := 4983230072969 + 3 ^ 40 * 743535 * 2
def baseEnd_743535 : Nat := 84842408542411922131789

theorem tailTrace_743535 : CollatzResearch.WordTrace tailWord_743535 prefixEnd_743535 84842408542411922131789 := by
  unfold tailWord_743535
  simp only [CollatzResearch.WordTrace]
  refine ⟨27118949361307155513264059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18079299574204770342176039 27118949361307155513264059)
  ·
    refine ⟨40678424041960733269896089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27118949361307155513264059 40678424041960733269896089)
    ·
      refine ⟨30508818031470549952422067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40678424041960733269896089 30508818031470549952422067)
      ·
        refine ⟨45763227047205824928633101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30508818031470549952422067 45763227047205824928633101)
        ·
          refine ⟨17161210142702184348237413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45763227047205824928633101 17161210142702184348237413)
          ·
            refine ⟨3217726901756659565294515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17161210142702184348237413 3217726901756659565294515)
            ·
              refine ⟨4826590352634989347941773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217726901756659565294515 4826590352634989347941773)
              ·
                refine ⟨1809971382238121005478165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4826590352634989347941773 1809971382238121005478165)
                ·
                  refine ⟨84842408542411922131789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1809971382238121005478165 84842408542411922131789)
                  ·
                    rfl

theorem cell22_743535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 6].length) (baseStart_743535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743535 prefixEnd_743535 := by exact prefixLift 743535
  have htrace : WordTrace (prefixWord ++ tailWord_743535) baseStart_743535 baseEnd_743535 := by
    simpa [prefixWord, tailWord_743535, baseEnd_743535] using wordTrace_append hprefix tailTrace_743535
  have hstable : (prefixWord ++ tailWord_743535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743535).length < 2 ^ (prefixWord ++ tailWord_743535).sum := by decide
  have hdescent : baseEnd_743535 < baseStart_743535 := by decide
  rcases family_descends (prefixWord ++ tailWord_743535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743597 : List Nat := [1, 5, 2, 1, 2, 1, 1, 9]
def baseStart_743597 : Nat := 118140960795 + 743597 * 2 ^ 59
def prefixEnd_743597 : Nat := 4983230072969 + 3 ^ 40 * 743597 * 2
def baseEnd_743597 : Nat := 28283161054920919038353

theorem tailTrace_743597 : CollatzResearch.WordTrace tailWord_743597 prefixEnd_743597 28283161054920919038353 := by
  unfold tailWord_743597
  simp only [CollatzResearch.WordTrace]
  refine ⟨27121210687082540102021045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18080807124721693401347363 27121210687082540102021045)
  ·
    refine ⟨2542613501913988134564473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27121210687082540102021045 2542613501913988134564473)
    ·
      refine ⟨1906960126435491100923355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2542613501913988134564473 1906960126435491100923355)
      ·
        refine ⟨2860440189653236651385033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906960126435491100923355 2860440189653236651385033)
        ·
          refine ⟨2145330142239927488538775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2860440189653236651385033 2145330142239927488538775)
          ·
            refine ⟨3217995213359891232808163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145330142239927488538775 3217995213359891232808163)
            ·
              refine ⟨4826992820039836849212245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217995213359891232808163 4826992820039836849212245)
              ·
                refine ⟨28283161054920919038353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4826992820039836849212245 28283161054920919038353)
                ·
                  rfl

theorem cell22_743597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 9].length) (baseStart_743597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743597 prefixEnd_743597 := by exact prefixLift 743597
  have htrace : WordTrace (prefixWord ++ tailWord_743597) baseStart_743597 baseEnd_743597 := by
    simpa [prefixWord, tailWord_743597, baseEnd_743597] using wordTrace_append hprefix tailTrace_743597
  have hstable : (prefixWord ++ tailWord_743597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743597).length < 2 ^ (prefixWord ++ tailWord_743597).sum := by decide
  have hdescent : baseEnd_743597 < baseStart_743597 := by decide
  rcases family_descends (prefixWord ++ tailWord_743597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743601 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 2, 3]
def baseStart_743601 : Nat := 118140960795 + 743601 * 2 ^ 59
def prefixEnd_743601 : Nat := 4983230072969 + 3 ^ 40 * 743601 * 2
def baseEnd_743601 : Nat := 254549818776033594245165

theorem tailTrace_743601 : CollatzResearch.WordTrace tailWord_743601 prefixEnd_743601 254549818776033594245165 := by
  unfold tailWord_743601
  simp only [CollatzResearch.WordTrace]
  refine ⟨27121356579068048785166657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18080904386045365856777771 27121356579068048785166657)
  ·
    refine ⟨20341017434301036588874993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27121356579068048785166657 20341017434301036588874993)
    ·
      refine ⟨15255763075725777441656245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20341017434301036588874993 15255763075725777441656245)
      ·
        refine ⟨1430227788349291635155273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15255763075725777441656245 1430227788349291635155273)
        ·
          refine ⟨1072670841261968726366455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430227788349291635155273 1072670841261968726366455)
          ·
            refine ⟨1609006261892953089549683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072670841261968726366455 1609006261892953089549683)
            ·
              refine ⟨2413509392839429634324525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609006261892953089549683 2413509392839429634324525)
              ·
                refine ⟨905066022314786112871697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413509392839429634324525 905066022314786112871697)
                ·
                  refine ⟨678799516736089584653773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905066022314786112871697 678799516736089584653773)
                  ·
                    refine ⟨254549818776033594245165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678799516736089584653773 254549818776033594245165)
                    ·
                      rfl

theorem cell22_743601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_743601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743601 prefixEnd_743601 := by exact prefixLift 743601
  have htrace : WordTrace (prefixWord ++ tailWord_743601) baseStart_743601 baseEnd_743601 := by
    simpa [prefixWord, tailWord_743601, baseEnd_743601] using wordTrace_append hprefix tailTrace_743601
  have hstable : (prefixWord ++ tailWord_743601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743601).length < 2 ^ (prefixWord ++ tailWord_743601).sum := by decide
  have hdescent : baseEnd_743601 < baseStart_743601 := by decide
  rcases family_descends (prefixWord ++ tailWord_743601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743625 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 7]
def baseStart_743625 : Nat := 118140960795 + 743625 * 2 ^ 59
def prefixEnd_743625 : Nat := 4983230072969 + 3 ^ 40 * 743625 * 2
def baseEnd_743625 : Nat := 84852678155501843881697

theorem tailTrace_743625 : CollatzResearch.WordTrace tailWord_743625 prefixEnd_743625 84852678155501843881697 := by
  unfold tailWord_743625
  simp only [CollatzResearch.WordTrace]
  refine ⟨27122231930981100884040329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18081487953987400589360219 27122231930981100884040329)
  ·
    refine ⟨20341673948235825663030247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27122231930981100884040329 20341673948235825663030247)
    ·
      refine ⟨30512510922353738494545371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20341673948235825663030247 30512510922353738494545371)
      ·
        refine ⟨45768766383530607741818057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30512510922353738494545371 45768766383530607741818057)
        ·
          refine ⟨34326574787647955806363543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45768766383530607741818057 34326574787647955806363543)
          ·
            refine ⟨51489862181471933709545315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34326574787647955806363543 51489862181471933709545315)
            ·
              refine ⟨77234793272207900564317973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51489862181471933709545315 77234793272207900564317973)
              ·
                refine ⟨3620380934634745338952405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77234793272207900564317973 3620380934634745338952405)
                ·
                  refine ⟨84852678155501843881697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3620380934634745338952405 84852678155501843881697)
                  ·
                    rfl

theorem cell22_743625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_743625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743625 prefixEnd_743625 := by exact prefixLift 743625
  have htrace : WordTrace (prefixWord ++ tailWord_743625) baseStart_743625 baseEnd_743625 := by
    simpa [prefixWord, tailWord_743625, baseEnd_743625] using wordTrace_append hprefix tailTrace_743625
  have hstable : (prefixWord ++ tailWord_743625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743625).length < 2 ^ (prefixWord ++ tailWord_743625).sum := by decide
  have hdescent : baseEnd_743625 < baseStart_743625 := by decide
  rcases family_descends (prefixWord ++ tailWord_743625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743642 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_743642 : Nat := 118140960795 + 743642 * 2 ^ 59
def prefixEnd_743642 : Nat := 4983230072969 + 3 ^ 40 * 743642 * 2
def baseEnd_743642 : Nat := 84854617971307717990013

theorem tailTrace_743642 : CollatzResearch.WordTrace tailWord_743642 prefixEnd_743642 84854617971307717990013 := by
  unfold tailWord_743642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780712992979878196852295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18081901314613008524939453 6780712992979878196852295)
  ·
    refine ⟨10171069489469817295278443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6780712992979878196852295 10171069489469817295278443)
    ·
      refine ⟨15256604234204725942917665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10171069489469817295278443 15256604234204725942917665)
      ·
        refine ⟨11442453175653544457188249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15256604234204725942917665 11442453175653544457188249)
        ·
          refine ⟨8581839881740158342891187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11442453175653544457188249 8581839881740158342891187)
          ·
            refine ⟨12872759822610237514336781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8581839881740158342891187 12872759822610237514336781)
            ·
              refine ⟨4827284933478839067876293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12872759822610237514336781 4827284933478839067876293)
              ·
                refine ⟨905115925027282325226805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4827284933478839067876293 905115925027282325226805)
                ·
                  refine ⟨84854617971307717990013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905115925027282325226805 84854617971307717990013)
                  ·
                    rfl

theorem cell22_743642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_743642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743642 prefixEnd_743642 := by exact prefixLift 743642
  have htrace : WordTrace (prefixWord ++ tailWord_743642) baseStart_743642 baseEnd_743642 := by
    simpa [prefixWord, tailWord_743642, baseEnd_743642] using wordTrace_append hprefix tailTrace_743642
  have hstable : (prefixWord ++ tailWord_743642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743642).length < 2 ^ (prefixWord ++ tailWord_743642).sum := by decide
  have hdescent : baseEnd_743642 < baseStart_743642 := by decide
  rcases family_descends (prefixWord ++ tailWord_743642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743689 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_743689 : Nat := 118140960795 + 743689 * 2 ^ 59
def prefixEnd_743689 : Nat := 4983230072969 + 3 ^ 40 * 743689 * 2
def baseEnd_743689 : Nat := 254579942974430698044895

theorem tailTrace_743689 : CollatzResearch.WordTrace tailWord_743689 prefixEnd_743689 254579942974430698044895 := by
  unfold tailWord_743689
  simp only [CollatzResearch.WordTrace]
  refine ⟨27124566202749239814370121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18083044135166159876246747 27124566202749239814370121)
  ·
    refine ⟨20343424652061929860777591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27124566202749239814370121 20343424652061929860777591)
    ·
      refine ⟨30515136978092894791166387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20343424652061929860777591 30515136978092894791166387)
      ·
        refine ⟨45772705467139342186749581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30515136978092894791166387 45772705467139342186749581)
        ·
          refine ⟨17164764550177253320031093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45772705467139342186749581 17164764550177253320031093)
          ·
            refine ⟨1609196676579117498752915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17164764550177253320031093 1609196676579117498752915)
            ·
              refine ⟨2413795014868676248129373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609196676579117498752915 2413795014868676248129373)
              ·
                refine ⟨905173130575753593048515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413795014868676248129373 905173130575753593048515)
                ·
                  refine ⟨1357759695863630389572773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905173130575753593048515 1357759695863630389572773)
                  ·
                    refine ⟨254579942974430698044895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1357759695863630389572773 254579942974430698044895)
                    ·
                      rfl

theorem cell22_743689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_743689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743689 prefixEnd_743689 := by exact prefixLift 743689
  have htrace : WordTrace (prefixWord ++ tailWord_743689) baseStart_743689 baseEnd_743689 := by
    simpa [prefixWord, tailWord_743689, baseEnd_743689] using wordTrace_append hprefix tailTrace_743689
  have hstable : (prefixWord ++ tailWord_743689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743689).length < 2 ^ (prefixWord ++ tailWord_743689).sum := by decide
  have hdescent : baseEnd_743689 < baseStart_743689 := by decide
  rcases family_descends (prefixWord ++ tailWord_743689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743704 : List Nat := [2, 1, 2, 3, 1, 2, 1, 6, 4]
def baseStart_743704 : Nat := 118140960795 + 743704 * 2 ^ 59
def prefixEnd_743704 : Nat := 4983230072969 + 3 ^ 40 * 743704 * 2
def baseEnd_743704 : Nat := 84861692593658552973283

theorem tailTrace_743704 : CollatzResearch.WordTrace tailWord_743704 prefixEnd_743704 84861692593658552973283 := by
  unfold tailWord_743704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13562556648847448688083083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18083408865129931584110777 13562556648847448688083083)
  ·
    refine ⟨20343834973271173032124625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13562556648847448688083083 20343834973271173032124625)
    ·
      refine ⟨15257876229953379774093469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20343834973271173032124625 15257876229953379774093469)
      ·
        refine ⟨5721703586232517415285051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15257876229953379774093469 5721703586232517415285051)
        ·
          refine ⟨8582555379348776122927577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721703586232517415285051 8582555379348776122927577)
          ·
            refine ⟨6436916534511582092195683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8582555379348776122927577 6436916534511582092195683)
            ·
              refine ⟨9655374801767373138293525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6436916534511582092195683 9655374801767373138293525)
              ·
                refine ⟨452595693832845615857509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9655374801767373138293525 452595693832845615857509)
                ·
                  refine ⟨84861692593658552973283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452595693832845615857509 84861692593658552973283)
                  ·
                    rfl

theorem cell22_743704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_743704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743704 prefixEnd_743704 := by exact prefixLift 743704
  have htrace : WordTrace (prefixWord ++ tailWord_743704) baseStart_743704 baseEnd_743704 := by
    simpa [prefixWord, tailWord_743704, baseEnd_743704] using wordTrace_append hprefix tailTrace_743704
  have hstable : (prefixWord ++ tailWord_743704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743704).length < 2 ^ (prefixWord ++ tailWord_743704).sum := by decide
  have hdescent : baseEnd_743704 < baseStart_743704 := by decide
  rcases family_descends (prefixWord ++ tailWord_743704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743774 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_743774 : Nat := 118140960795 + 743774 * 2 ^ 59
def prefixEnd_743774 : Nat := 4983230072969 + 3 ^ 40 * 743774 * 2
def baseEnd_743774 : Nat := 254609040211518809669635

theorem tailTrace_743774 : CollatzResearch.WordTrace tailWord_743774 prefixEnd_743774 254609040211518809669635 := by
  unfold tailWord_743774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390958300930162416401797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18085110938294199554142917 3390958300930162416401797)
  ·
    refine ⟨635804681424405453075337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3390958300930162416401797 635804681424405453075337)
    ·
      refine ⟨476853511068304089806503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 635804681424405453075337 476853511068304089806503)
      ·
        refine ⟨715280266602456134709755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476853511068304089806503 715280266602456134709755)
        ·
          refine ⟨1072920399903684202064633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715280266602456134709755 1072920399903684202064633)
          ·
            refine ⟨804690299927763151548475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072920399903684202064633 804690299927763151548475)
            ·
              refine ⟨1207035449891644727322713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804690299927763151548475 1207035449891644727322713)
              ·
                refine ⟨905276587418733545492035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207035449891644727322713 905276587418733545492035)
                ·
                  refine ⟨1357914881128100318238053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905276587418733545492035 1357914881128100318238053)
                  ·
                    refine ⟨254609040211518809669635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1357914881128100318238053 254609040211518809669635)
                    ·
                      rfl

theorem cell22_743774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_743774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743774 prefixEnd_743774 := by exact prefixLift 743774
  have htrace : WordTrace (prefixWord ++ tailWord_743774) baseStart_743774 baseEnd_743774 := by
    simpa [prefixWord, tailWord_743774, baseEnd_743774] using wordTrace_append hprefix tailTrace_743774
  have hstable : (prefixWord ++ tailWord_743774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743774).length < 2 ^ (prefixWord ++ tailWord_743774).sum := by decide
  have hdescent : baseEnd_743774 < baseStart_743774 := by decide
  rcases family_descends (prefixWord ++ tailWord_743774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743811 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 5]
def baseStart_743811 : Nat := 118140960795 + 743811 * 2 ^ 59
def prefixEnd_743811 : Nat := 4983230072969 + 3 ^ 40 * 743811 * 2
def baseEnd_743811 : Nat := 84873902022554348831507

theorem tailTrace_743811 : CollatzResearch.WordTrace tailWord_743811 prefixEnd_743811 84873902022554348831507 := by
  unfold tailWord_743811
  simp only [CollatzResearch.WordTrace]
  refine ⟨27129015908307254650311287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18086010605538169766874191 27129015908307254650311287)
  ·
    refine ⟨40693523862460881975466931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27129015908307254650311287 40693523862460881975466931)
    ·
      refine ⟨61040285793691322963200397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40693523862460881975466931 61040285793691322963200397)
      ·
        refine ⟨22890107172634246111200149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61040285793691322963200397 22890107172634246111200149)
        ·
          refine ⟨1072973773717230286462507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22890107172634246111200149 1072973773717230286462507)
          ·
            refine ⟨1609460660575845429693761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072973773717230286462507 1609460660575845429693761)
            ·
              refine ⟨1207095495431884072270321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609460660575845429693761 1207095495431884072270321)
              ·
                refine ⟨905321621573913054202741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207095495431884072270321 905321621573913054202741)
                ·
                  refine ⟨84873902022554348831507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905321621573913054202741 84873902022554348831507)
                  ·
                    rfl

theorem cell22_743811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 5].length) (baseStart_743811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743811 prefixEnd_743811 := by exact prefixLift 743811
  have htrace : WordTrace (prefixWord ++ tailWord_743811) baseStart_743811 baseEnd_743811 := by
    simpa [prefixWord, tailWord_743811, baseEnd_743811] using wordTrace_append hprefix tailTrace_743811
  have hstable : (prefixWord ++ tailWord_743811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743811).length < 2 ^ (prefixWord ++ tailWord_743811).sum := by decide
  have hdescent : baseEnd_743811 < baseStart_743811 := by decide
  rcases family_descends (prefixWord ++ tailWord_743811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743839 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 6]
def baseStart_743839 : Nat := 118140960795 + 743839 * 2 ^ 59
def prefixEnd_743839 : Nat := 4983230072969 + 3 ^ 40 * 743839 * 2
def baseEnd_743839 : Nat := 84877097013293435598145

theorem tailTrace_743839 : CollatzResearch.WordTrace tailWord_743839 prefixEnd_743839 84877097013293435598145 := by
  unfold tailWord_743839
  simp only [CollatzResearch.WordTrace]
  refine ⟨27130037152205815432330571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18086691434803876954887047 27130037152205815432330571)
  ·
    refine ⟨40695055728308723148495857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27130037152205815432330571 40695055728308723148495857)
    ·
      refine ⟨30521291796231542361371893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40695055728308723148495857 30521291796231542361371893)
      ·
        refine ⟨2861371105896707096378615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30521291796231542361371893 2861371105896707096378615)
        ·
          refine ⟨4292056658845060644567923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861371105896707096378615 4292056658845060644567923)
          ·
            refine ⟨6438084988267590966851885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292056658845060644567923 6438084988267590966851885)
            ·
              refine ⟨2414281870600346612569457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6438084988267590966851885 2414281870600346612569457)
              ·
                refine ⟨1810711402950259959427093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414281870600346612569457 1810711402950259959427093)
                ·
                  refine ⟨84877097013293435598145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1810711402950259959427093 84877097013293435598145)
                  ·
                    rfl

theorem cell22_743839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 6].length) (baseStart_743839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743839 prefixEnd_743839 := by exact prefixLift 743839
  have htrace : WordTrace (prefixWord ++ tailWord_743839) baseStart_743839 baseEnd_743839 := by
    simpa [prefixWord, tailWord_743839, baseEnd_743839] using wordTrace_append hprefix tailTrace_743839
  have hstable : (prefixWord ++ tailWord_743839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743839).length < 2 ^ (prefixWord ++ tailWord_743839).sum := by decide
  have hdescent : baseEnd_743839 < baseStart_743839 := by decide
  rcases family_descends (prefixWord ++ tailWord_743839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743929 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 7]
def baseStart_743929 : Nat := 118140960795 + 743929 * 2 ^ 59
def prefixEnd_743929 : Nat := 4983230072969 + 3 ^ 40 * 743929 * 2
def baseEnd_743929 : Nat := 84887366626383357348053

theorem tailTrace_743929 : CollatzResearch.WordTrace tailWord_743929 prefixEnd_743929 84887366626383357348053 := by
  unfold tailWord_743929
  simp only [CollatzResearch.WordTrace]
  refine ⟨27133319721879760803106841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18088879814586507202071227 27133319721879760803106841)
  ·
    refine ⟨20349989791409820602330131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27133319721879760803106841 20349989791409820602330131)
    ·
      refine ⟨30524984687114730903495197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20349989791409820602330131 30524984687114730903495197)
      ·
        refine ⟨11446869257668024088810699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30524984687114730903495197 11446869257668024088810699)
        ·
          refine ⟨17170303886502036133216049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11446869257668024088810699 17170303886502036133216049)
          ·
            refine ⟨12877727914876527099912037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17170303886502036133216049 12877727914876527099912037)
            ·
              refine ⟨2414573984039348831233507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12877727914876527099912037 2414573984039348831233507)
              ·
                refine ⟨3621860976059023246850261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414573984039348831233507 3621860976059023246850261)
                ·
                  refine ⟨84887366626383357348053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3621860976059023246850261 84887366626383357348053)
                  ·
                    rfl

theorem cell22_743929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_743929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743929 prefixEnd_743929 := by exact prefixLift 743929
  have htrace : WordTrace (prefixWord ++ tailWord_743929) baseStart_743929 baseEnd_743929 := by
    simpa [prefixWord, tailWord_743929, baseEnd_743929] using wordTrace_append hprefix tailTrace_743929
  have hstable : (prefixWord ++ tailWord_743929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743929).length < 2 ^ (prefixWord ++ tailWord_743929).sum := by decide
  have hdescent : baseEnd_743929 < baseStart_743929 := by decide
  rcases family_descends (prefixWord ++ tailWord_743929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743944 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_743944 : Nat := 118140960795 + 743944 * 2 ^ 59
def prefixEnd_743944 : Nat := 4983230072969 + 3 ^ 40 * 743944 * 2
def baseEnd_743944 : Nat := 254667234685695032919113

theorem tailTrace_743944 : CollatzResearch.WordTrace tailWord_743944 prefixEnd_743944 254667234685695032919113 := by
  unfold tailWord_743944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13566933408412709182451443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18089244544550278909935257 13566933408412709182451443)
  ·
    refine ⟨20350400112619063773677165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13566933408412709182451443 20350400112619063773677165)
    ·
      refine ⟨7631400042232148915128937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20350400112619063773677165 7631400042232148915128937)
      ·
        refine ⟨5723550031674111686346703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7631400042232148915128937 5723550031674111686346703)
        ·
          refine ⟨8585325047511167529520055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723550031674111686346703 8585325047511167529520055)
          ·
            refine ⟨12877987571266751294280083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8585325047511167529520055 12877987571266751294280083)
            ·
              refine ⟨19316981356900126941420125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12877987571266751294280083 19316981356900126941420125)
              ·
                refine ⟨7243868008837547603032547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19316981356900126941420125 7243868008837547603032547)
                ·
                  refine ⟨10865802013256321404548821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7243868008837547603032547 10865802013256321404548821)
                  ·
                    refine ⟨254667234685695032919113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10865802013256321404548821 254667234685695032919113)
                    ·
                      rfl

theorem cell22_743944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_743944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743944 prefixEnd_743944 := by exact prefixLift 743944
  have htrace : WordTrace (prefixWord ++ tailWord_743944) baseStart_743944 baseEnd_743944 := by
    simpa [prefixWord, tailWord_743944, baseEnd_743944] using wordTrace_append hprefix tailTrace_743944
  have hstable : (prefixWord ++ tailWord_743944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743944).length < 2 ^ (prefixWord ++ tailWord_743944).sum := by decide
  have hdescent : baseEnd_743944 < baseStart_743944 := by decide
  rcases family_descends (prefixWord ++ tailWord_743944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743946 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_743946 : Nat := 118140960795 + 743946 * 2 ^ 59
def prefixEnd_743946 : Nat := 4983230072969 + 3 ^ 40 * 743946 * 2
def baseEnd_743946 : Nat := 84889306442189231456369

theorem tailTrace_743946 : CollatzResearch.WordTrace tailWord_743946 prefixEnd_743946 84889306442189231456369 := by
  unfold tailWord_743946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6783484940704543176618923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18089293175212115137650461 6783484940704543176618923)
  ·
    refine ⟨10175227411056814764928385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6783484940704543176618923 10175227411056814764928385)
    ·
      refine ⟨7631420558292611073696289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10175227411056814764928385 7631420558292611073696289)
      ·
        refine ⟨5723565418719458305272217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7631420558292611073696289 5723565418719458305272217)
        ·
          refine ⟨4292674064039593728954163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5723565418719458305272217 4292674064039593728954163)
          ·
            refine ⟨6439011096059390593431245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292674064039593728954163 6439011096059390593431245)
            ·
              refine ⟨2414629161022271472536717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6439011096059390593431245 2414629161022271472536717)
              ·
                refine ⟨905485935383351802201269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2414629161022271472536717 905485935383351802201269)
                ·
                  refine ⟨84889306442189231456369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905485935383351802201269 84889306442189231456369)
                  ·
                    rfl

theorem cell22_743946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_743946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_743946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_743946 prefixEnd_743946 := by exact prefixLift 743946
  have htrace : WordTrace (prefixWord ++ tailWord_743946) baseStart_743946 baseEnd_743946 := by
    simpa [prefixWord, tailWord_743946, baseEnd_743946] using wordTrace_append hprefix tailTrace_743946
  have hstable : (prefixWord ++ tailWord_743946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743946).length < 2 ^ (prefixWord ++ tailWord_743946).sum := by decide
  have hdescent : baseEnd_743946 < baseStart_743946 := by decide
  rcases family_descends (prefixWord ++ tailWord_743946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744040 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 4, 3]
def baseStart_744040 : Nat := 118140960795 + 744040 * 2 ^ 59
def prefixEnd_744040 : Nat := 4983230072969 + 3 ^ 40 * 744040 * 2
def baseEnd_744040 : Nat := 254700097447582782518819

theorem tailTrace_744040 : CollatzResearch.WordTrace tailWord_744040 prefixEnd_744040 254700097447582782518819 := by
  unfold tailWord_744040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13568684112238813380198787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18091578816318417840265049 13568684112238813380198787)
  ·
    refine ⟨20353026168358220070298181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13568684112238813380198787 20353026168358220070298181)
    ·
      refine ⟨3816192406567166263180909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20353026168358220070298181 3816192406567166263180909)
      ·
        refine ⟨1431072152462687348692841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3816192406567166263180909 1431072152462687348692841)
        ·
          refine ⟨1073304114347015511519631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1431072152462687348692841 1073304114347015511519631)
          ·
            refine ⟨1609956171520523267279447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073304114347015511519631 1609956171520523267279447)
            ·
              refine ⟨2414934257280784900919171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609956171520523267279447 2414934257280784900919171)
              ·
                refine ⟨3622401385921177351378757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414934257280784900919171 3622401385921177351378757)
                ·
                  refine ⟨679200259860220753383517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3622401385921177351378757 679200259860220753383517)
                  ·
                    refine ⟨254700097447582782518819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679200259860220753383517 254700097447582782518819)
                    ·
                      rfl

theorem cell22_744040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_744040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744040 prefixEnd_744040 := by exact prefixLift 744040
  have htrace : WordTrace (prefixWord ++ tailWord_744040) baseStart_744040 baseEnd_744040 := by
    simpa [prefixWord, tailWord_744040, baseEnd_744040] using wordTrace_append hprefix tailTrace_744040
  have hstable : (prefixWord ++ tailWord_744040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744040).length < 2 ^ (prefixWord ++ tailWord_744040).sum := by decide
  have hdescent : baseEnd_744040 < baseStart_744040 := by decide
  rcases family_descends (prefixWord ++ tailWord_744040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744115 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 5]
def baseStart_744115 : Nat := 118140960795 + 744115 * 2 ^ 59
def prefixEnd_744115 : Nat := 4983230072969 + 3 ^ 40 * 744115 * 2
def baseEnd_744115 : Nat := 84908590493435862297863

theorem tailTrace_744115 : CollatzResearch.WordTrace tailWord_744115 prefixEnd_744115 84908590493435862297863 := by
  unfold tailWord_744115
  simp only [CollatzResearch.WordTrace]
  refine ⟨27140103699205914569377799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18093402466137276379585199 27140103699205914569377799)
  ·
    refine ⟨40710155548808871854066699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27140103699205914569377799 40710155548808871854066699)
    ·
      refine ⟨61065233323213307781100049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40710155548808871854066699 61065233323213307781100049)
      ·
        refine ⟨45798924992409980835825037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61065233323213307781100049 45798924992409980835825037)
        ·
          refine ⟨17174596872153742813434389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45798924992409980835825037 17174596872153742813434389)
          ·
            refine ⟨805059228382206694379737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17174596872153742813434389 805059228382206694379737)
            ·
              refine ⟨603794421286655020784803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805059228382206694379737 603794421286655020784803)
              ·
                refine ⟨905691631929982531177205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603794421286655020784803 905691631929982531177205)
                ·
                  refine ⟨84908590493435862297863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905691631929982531177205 84908590493435862297863)
                  ·
                    rfl

theorem cell22_744115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 5].length) (baseStart_744115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744115 prefixEnd_744115 := by exact prefixLift 744115
  have htrace : WordTrace (prefixWord ++ tailWord_744115) baseStart_744115 baseEnd_744115 := by
    simpa [prefixWord, tailWord_744115, baseEnd_744115] using wordTrace_append hprefix tailTrace_744115
  have hstable : (prefixWord ++ tailWord_744115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744115).length < 2 ^ (prefixWord ++ tailWord_744115).sum := by decide
  have hdescent : baseEnd_744115 < baseStart_744115 := by decide
  rcases family_descends (prefixWord ++ tailWord_744115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744128 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_744128 : Nat := 118140960795 + 744128 * 2 ^ 59
def prefixEnd_744128 : Nat := 4983230072969 + 3 ^ 40 * 744128 * 2
def baseEnd_744128 : Nat := 254730221645979886318549

theorem tailTrace_744128 : CollatzResearch.WordTrace tailWord_744128 prefixEnd_744128 254730221645979886318549 := by
  unfold tailWord_744128
  simp only [CollatzResearch.WordTrace]
  refine ⟨13570288924079408894800519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18093718565439211859734025 13570288924079408894800519)
  ·
    refine ⟨20355433386119113342200779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13570288924079408894800519 20355433386119113342200779)
    ·
      refine ⟨30533150079178670013301169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20355433386119113342200779 30533150079178670013301169)
      ·
        refine ⟨22899862559384002509975877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30533150079178670013301169 22899862559384002509975877)
        ·
          refine ⟨4293724229884500470620477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22899862559384002509975877 4293724229884500470620477)
          ·
            refine ⟨1610146586206687676482679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4293724229884500470620477 1610146586206687676482679)
            ·
              refine ⟨2415219879310031514724019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610146586206687676482679 2415219879310031514724019)
              ·
                refine ⟨3622829818965047272086029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415219879310031514724019 3622829818965047272086029)
                ·
                  refine ⟨1358561182111892727032261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3622829818965047272086029 1358561182111892727032261)
                  ·
                    refine ⟨254730221645979886318549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358561182111892727032261 254730221645979886318549)
                    ·
                      rfl

theorem cell22_744128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_744128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744128 prefixEnd_744128 := by exact prefixLift 744128
  have htrace : WordTrace (prefixWord ++ tailWord_744128) baseStart_744128 baseEnd_744128 := by
    simpa [prefixWord, tailWord_744128, baseEnd_744128] using wordTrace_append hprefix tailTrace_744128
  have hstable : (prefixWord ++ tailWord_744128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744128).length < 2 ^ (prefixWord ++ tailWord_744128).sum := by decide
  have hdescent : baseEnd_744128 < baseStart_744128 := by decide
  rcases family_descends (prefixWord ++ tailWord_744128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744145 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 1, 4]
def baseStart_744145 : Nat := 118140960795 + 744145 * 2 ^ 59
def prefixEnd_744145 : Nat := 4983230072969 + 3 ^ 40 * 744145 * 2
def baseEnd_744145 : Nat := 254736041093397508643497

theorem tailTrace_744145 : CollatzResearch.WordTrace tailWord_744145 prefixEnd_744145 254736041093397508643497 := by
  unfold tailWord_744145
  simp only [CollatzResearch.WordTrace]
  refine ⟨27141197889097229692969889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18094131926064819795313259 27141197889097229692969889)
  ·
    refine ⟨20355898416822922269727417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27141197889097229692969889 20355898416822922269727417)
    ·
      refine ⟨15266923812617191702295563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20355898416822922269727417 15266923812617191702295563)
      ·
        refine ⟨22900385718925787553443345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15266923812617191702295563 22900385718925787553443345)
        ·
          refine ⟨17175289289194340665082509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22900385718925787553443345 17175289289194340665082509)
          ·
            refine ⟨6440733483447877749405941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17175289289194340665082509 6440733483447877749405941)
            ·
              refine ⟨603818764073238539006807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6440733483447877749405941 603818764073238539006807)
              ·
                refine ⟨905728146109857808510211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603818764073238539006807 905728146109857808510211)
                ·
                  refine ⟨1358592219164786712765317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905728146109857808510211 1358592219164786712765317)
                  ·
                    refine ⟨254736041093397508643497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358592219164786712765317 254736041093397508643497)
                    ·
                      rfl

theorem cell22_744145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_744145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744145 prefixEnd_744145 := by exact prefixLift 744145
  have htrace : WordTrace (prefixWord ++ tailWord_744145) baseStart_744145 baseEnd_744145 := by
    simpa [prefixWord, tailWord_744145, baseEnd_744145] using wordTrace_append hprefix tailTrace_744145
  have hstable : (prefixWord ++ tailWord_744145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744145).length < 2 ^ (prefixWord ++ tailWord_744145).sum := by decide
  have hdescent : baseEnd_744145 < baseStart_744145 := by decide
  rcases family_descends (prefixWord ++ tailWord_744145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744173 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_744173 : Nat := 118140960795 + 744173 * 2 ^ 59
def prefixEnd_744173 : Nat := 4983230072969 + 3 ^ 40 * 744173 * 2
def baseEnd_744173 : Nat := 254745626065614768943411

theorem tailTrace_744173 : CollatzResearch.WordTrace tailWord_744173 prefixEnd_744173 254745626065614768943411 := by
  unfold tailWord_744173
  simp only [CollatzResearch.WordTrace]
  refine ⟨27142219132995790474989173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18094812755330526983326115 27142219132995790474989173)
  ·
    refine ⟨2544583043718355357030235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27142219132995790474989173 2544583043718355357030235)
    ·
      refine ⟨3816874565577533035545353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2544583043718355357030235 3816874565577533035545353)
      ·
        refine ⟨2862655924183149776659015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3816874565577533035545353 2862655924183149776659015)
        ·
          refine ⟨4293983886274724664988523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862655924183149776659015 4293983886274724664988523)
          ·
            refine ⟨6440975829412086997482785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293983886274724664988523 6440975829412086997482785)
            ·
              refine ⟨4830731872059065248112089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6440975829412086997482785 4830731872059065248112089)
              ·
                refine ⟨3623048904044298936084067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830731872059065248112089 3623048904044298936084067)
                ·
                  refine ⟨5434573356066448404126101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623048904044298936084067 5434573356066448404126101)
                  ·
                    refine ⟨254745626065614768943411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5434573356066448404126101 254745626065614768943411)
                    ·
                      rfl

theorem cell22_744173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_744173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744173 prefixEnd_744173 := by exact prefixLift 744173
  have htrace : WordTrace (prefixWord ++ tailWord_744173) baseStart_744173 baseEnd_744173 := by
    simpa [prefixWord, tailWord_744173, baseEnd_744173] using wordTrace_append hprefix tailTrace_744173
  have hstable : (prefixWord ++ tailWord_744173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744173).length < 2 ^ (prefixWord ++ tailWord_744173).sum := by decide
  have hdescent : baseEnd_744173 < baseStart_744173 := by decide
  rcases family_descends (prefixWord ++ tailWord_744173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744175 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 2, 3]
def baseStart_744175 : Nat := 118140960795 + 744175 * 2 ^ 59
def prefixEnd_744175 : Nat := 4983230072969 + 3 ^ 40 * 744175 * 2
def baseEnd_744175 : Nat := 254746310706487430393405

theorem tailTrace_744175 : CollatzResearch.WordTrace tailWord_744175 prefixEnd_744175 254746310706487430393405 := by
  unfold tailWord_744175
  simp only [CollatzResearch.WordTrace]
  refine ⟨27142292078988544816561979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18094861385992363211041319 27142292078988544816561979)
  ·
    refine ⟨40713438118482817224842969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27142292078988544816561979 40713438118482817224842969)
    ·
      refine ⟨30535078588862112918632227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40713438118482817224842969 30535078588862112918632227)
      ·
        refine ⟨45802617883293169377948341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30535078588862112918632227 45802617883293169377948341)
        ·
          refine ⟨4293995426558734629182657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45802617883293169377948341 4293995426558734629182657)
          ·
            refine ⟨3220496569919050971886993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4293995426558734629182657 3220496569919050971886993)
            ·
              refine ⟨2415372427439288228915245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3220496569919050971886993 2415372427439288228915245)
              ·
                refine ⟨905764660289733085843217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2415372427439288228915245 905764660289733085843217)
                ·
                  refine ⟨679323495217299814382413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905764660289733085843217 679323495217299814382413)
                  ·
                    refine ⟨254746310706487430393405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679323495217299814382413 254746310706487430393405)
                    ·
                      rfl

theorem cell22_744175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_744175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744175 prefixEnd_744175 := by exact prefixLift 744175
  have htrace : WordTrace (prefixWord ++ tailWord_744175) baseStart_744175 baseEnd_744175 := by
    simpa [prefixWord, tailWord_744175, baseEnd_744175] using wordTrace_append hprefix tailTrace_744175
  have hstable : (prefixWord ++ tailWord_744175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744175).length < 2 ^ (prefixWord ++ tailWord_744175).sum := by decide
  have hdescent : baseEnd_744175 < baseStart_744175 := by decide
  rcases family_descends (prefixWord ++ tailWord_744175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744190 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_744190 : Nat := 118140960795 + 744190 * 2 ^ 59
def prefixEnd_744190 : Nat := 4983230072969 + 3 ^ 40 * 744190 * 2
def baseEnd_744190 : Nat := 254751445513032391268359

theorem tailTrace_744190 : CollatzResearch.WordTrace tailWord_744190 prefixEnd_744190 254751445513032391268359 := by
  unfold tailWord_744190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392854896741775297294753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18095226115956134918905349 3392854896741775297294753)
  ·
    refine ⟨2544641172556331472971065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3392854896741775297294753 2544641172556331472971065)
    ·
      refine ⟨1908480879417248604728299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2544641172556331472971065 1908480879417248604728299)
      ·
        refine ⟨2862721319125872907092449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908480879417248604728299 2862721319125872907092449)
        ·
          refine ⟨2147040989344404680319337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862721319125872907092449 2147040989344404680319337)
          ·
            refine ⟨1610280742008303510239503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147040989344404680319337 1610280742008303510239503)
            ·
              refine ⟨2415421113012455265359255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610280742008303510239503 2415421113012455265359255)
              ·
                refine ⟨3623131669518682898038883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415421113012455265359255 3623131669518682898038883)
                ·
                  refine ⟨5434697504278024347058325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623131669518682898038883 5434697504278024347058325)
                  ·
                    refine ⟨254751445513032391268359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5434697504278024347058325 254751445513032391268359)
                    ·
                      rfl

theorem cell22_744190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_744190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744190 prefixEnd_744190 := by exact prefixLift 744190
  have htrace : WordTrace (prefixWord ++ tailWord_744190) baseStart_744190 baseEnd_744190 := by
    simpa [prefixWord, tailWord_744190, baseEnd_744190] using wordTrace_append hprefix tailTrace_744190
  have hstable : (prefixWord ++ tailWord_744190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744190).length < 2 ^ (prefixWord ++ tailWord_744190).sum := by decide
  have hdescent : baseEnd_744190 < baseStart_744190 := by decide
  rcases family_descends (prefixWord ++ tailWord_744190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744203 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 7, 3]
def baseStart_744203 : Nat := 118140960795 + 744203 * 2 ^ 59
def prefixEnd_744203 : Nat := 4983230072969 + 3 ^ 40 * 744203 * 2
def baseEnd_744203 : Nat := 254755895678704690693319

theorem tailTrace_744203 : CollatzResearch.WordTrace tailWord_744203 prefixEnd_744203 254755895678704690693319 := by
  unfold tailWord_744203
  simp only [CollatzResearch.WordTrace]
  refine ⟨27143313322887105598581263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18095542215258070399054175 27143313322887105598581263)
  ·
    refine ⟨40714969984330658397871895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27143313322887105598581263 40714969984330658397871895)
    ·
      refine ⟨61072454976495987596807843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40714969984330658397871895 61072454976495987596807843)
      ·
        refine ⟨91608682464743981395211765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61072454976495987596807843 91608682464743981395211765)
        ·
          refine ⟨8588313981069748255801103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91608682464743981395211765 8588313981069748255801103)
          ·
            refine ⟨12882470971604622383701655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8588313981069748255801103 12882470971604622383701655)
            ·
              refine ⟨19323706457406933575552483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12882470971604622383701655 19323706457406933575552483)
              ·
                refine ⟨28985559686110400363328725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19323706457406933575552483 28985559686110400363328725)
                ·
                  refine ⟨679349055143212508515517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 28985559686110400363328725 679349055143212508515517)
                  ·
                    refine ⟨254755895678704690693319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679349055143212508515517 254755895678704690693319)
                    ·
                      rfl

theorem cell22_744203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 3].length) (baseStart_744203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744203 prefixEnd_744203 := by exact prefixLift 744203
  have htrace : WordTrace (prefixWord ++ tailWord_744203) baseStart_744203 baseEnd_744203 := by
    simpa [prefixWord, tailWord_744203, baseEnd_744203] using wordTrace_append hprefix tailTrace_744203
  have hstable : (prefixWord ++ tailWord_744203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744203).length < 2 ^ (prefixWord ++ tailWord_744203).sum := by decide
  have hdescent : baseEnd_744203 < baseStart_744203 := by decide
  rcases family_descends (prefixWord ++ tailWord_744203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744220 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_744220 : Nat := 118140960795 + 744220 * 2 ^ 59
def prefixEnd_744220 : Nat := 4983230072969 + 3 ^ 40 * 744220 * 2
def baseEnd_744220 : Nat := 254761715126122313018267

theorem tailTrace_744220 : CollatzResearch.WordTrace tailWord_744220 prefixEnd_744220 254761715126122313018267 := by
  unfold tailWord_744220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571966681912758750975057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18095955575883678334633409 13571966681912758750975057)
  ·
    refine ⟨10178975011434569063231293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13571966681912758750975057 10178975011434569063231293)
    ·
      refine ⟨3817115629287963398711735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10178975011434569063231293 3817115629287963398711735)
      ·
        refine ⟨5725673443931945098067603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817115629287963398711735 5725673443931945098067603)
        ·
          refine ⟨8588510165897917647101405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5725673443931945098067603 8588510165897917647101405)
          ·
            refine ⟨3220691312211719117663027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8588510165897917647101405 3220691312211719117663027)
            ·
              refine ⟨4831036968317578676494541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220691312211719117663027 4831036968317578676494541)
              ·
                refine ⟨1811638863119092003685453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4831036968317578676494541 1811638863119092003685453)
                ·
                  refine ⟨679364573669659501382045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1811638863119092003685453 679364573669659501382045)
                  ·
                    refine ⟨254761715126122313018267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679364573669659501382045 254761715126122313018267)
                    ·
                      rfl

theorem cell22_744220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_744220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744220 prefixEnd_744220 := by exact prefixLift 744220
  have htrace : WordTrace (prefixWord ++ tailWord_744220) baseStart_744220 baseEnd_744220 := by
    simpa [prefixWord, tailWord_744220, baseEnd_744220] using wordTrace_append hprefix tailTrace_744220
  have hstable : (prefixWord ++ tailWord_744220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744220).length < 2 ^ (prefixWord ++ tailWord_744220).sum := by decide
  have hdescent : baseEnd_744220 < baseStart_744220 := by decide
  rcases family_descends (prefixWord ++ tailWord_744220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744263 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 5, 4]
def baseStart_744263 : Nat := 118140960795 + 744263 * 2 ^ 59
def prefixEnd_744263 : Nat := 4983230072969 + 3 ^ 40 * 744263 * 2
def baseEnd_744263 : Nat := 254776434904884534193135

theorem tailTrace_744263 : CollatzResearch.WordTrace tailWord_744263 prefixEnd_744263 254776434904884534193135 := by
  unfold tailWord_744263
  simp only [CollatzResearch.WordTrace]
  refine ⟨27145501702669735845765443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18097001135113157230510295 27145501702669735845765443)
  ·
    refine ⟨40718252554004603768648165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27145501702669735845765443 40718252554004603768648165)
    ·
      refine ⟨7634672353875863206621531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40718252554004603768648165 7634672353875863206621531)
      ·
        refine ⟨11452008530813794809932297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7634672353875863206621531 11452008530813794809932297)
        ·
          refine ⟨8589006398110346107449223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11452008530813794809932297 8589006398110346107449223)
          ·
            refine ⟨12883509597165519161173835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8589006398110346107449223 12883509597165519161173835)
            ·
              refine ⟨19325264395748278741760753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12883509597165519161173835 19325264395748278741760753)
              ·
                refine ⟨14493948296811209056320565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19325264395748278741760753 14493948296811209056320565)
                ·
                  refine ⟨1358807652826050849030053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14493948296811209056320565 1358807652826050849030053)
                  ·
                    refine ⟨254776434904884534193135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358807652826050849030053 254776434904884534193135)
                    ·
                      rfl

theorem cell22_744263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_744263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744263 prefixEnd_744263 := by exact prefixLift 744263
  have htrace : WordTrace (prefixWord ++ tailWord_744263) baseStart_744263 baseEnd_744263 := by
    simpa [prefixWord, tailWord_744263, baseEnd_744263] using wordTrace_append hprefix tailTrace_744263
  have hstable : (prefixWord ++ tailWord_744263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744263).length < 2 ^ (prefixWord ++ tailWord_744263).sum := by decide
  have hdescent : baseEnd_744263 < baseStart_744263 := by decide
  rcases family_descends (prefixWord ++ tailWord_744263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744284 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 5]
def baseStart_744284 : Nat := 118140960795 + 744284 * 2 ^ 59
def prefixEnd_744284 : Nat := 4983230072969 + 3 ^ 40 * 744284 * 2
def baseEnd_744284 : Nat := 84927874544682493139357

theorem tailTrace_744284 : CollatzResearch.WordTrace tailWord_744284 prefixEnd_744284 84927874544682493139357 := by
  unfold tailWord_744284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13573133817796828216139953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18097511757062437621519937 13573133817796828216139953)
  ·
    refine ⟨10179850363347621162104965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13573133817796828216139953 10179850363347621162104965)
    ·
      refine ⟨1908721943127678967894681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10179850363347621162104965 1908721943127678967894681)
      ·
        refine ⟨1431541457345759225921011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1908721943127678967894681 1431541457345759225921011)
        ·
          refine ⟨2147312186018638838881517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431541457345759225921011 2147312186018638838881517)
          ·
            refine ⟨805242069756989564580569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2147312186018638838881517 805242069756989564580569)
            ·
              refine ⟨603931552317742173435427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805242069756989564580569 603931552317742173435427)
              ·
                refine ⟨905897328476613260153141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603931552317742173435427 905897328476613260153141)
                ·
                  refine ⟨84927874544682493139357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905897328476613260153141 84927874544682493139357)
                  ·
                    rfl

theorem cell22_744284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_744284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744284 prefixEnd_744284 := by exact prefixLift 744284
  have htrace : WordTrace (prefixWord ++ tailWord_744284) baseStart_744284 baseEnd_744284 := by
    simpa [prefixWord, tailWord_744284, baseEnd_744284] using wordTrace_append hprefix tailTrace_744284
  have hstable : (prefixWord ++ tailWord_744284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744284).length < 2 ^ (prefixWord ++ tailWord_744284).sum := by decide
  have hdescent : baseEnd_744284 < baseStart_744284 := by decide
  rcases family_descends (prefixWord ++ tailWord_744284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744322 : List Nat := [3, 4, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_744322 : Nat := 118140960795 + 744322 * 2 ^ 59
def prefixEnd_744322 : Nat := 4983230072969 + 3 ^ 40 * 744322 * 2
def baseEnd_744322 : Nat := 254796631810628046967955

theorem tailTrace_744322 : CollatzResearch.WordTrace tailWord_744322 prefixEnd_744322 254796631810628046967955 := by
  unfold tailWord_744322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786913402363997230540805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18098435739637325948108813 6786913402363997230540805)
  ·
    refine ⟨1272546262943249480726401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6786913402363997230540805 1272546262943249480726401)
    ·
      refine ⟨954409697207437110544801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1272546262943249480726401 954409697207437110544801)
      ·
        refine ⟨715807272905577832908601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954409697207437110544801 715807272905577832908601)
        ·
          refine ⟨536855454679183374681451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715807272905577832908601 536855454679183374681451)
          ·
            refine ⟨805283182018775062022177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536855454679183374681451 805283182018775062022177)
            ·
              refine ⟨603962386514081296516633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805283182018775062022177 603962386514081296516633)
              ·
                refine ⟨452971789885560972387475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603962386514081296516633 452971789885560972387475)
                ·
                  refine ⟨679457684828341458581213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452971789885560972387475 679457684828341458581213)
                  ·
                    refine ⟨254796631810628046967955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679457684828341458581213 254796631810628046967955)
                    ·
                      rfl

theorem cell22_744322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_744322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744322 prefixEnd_744322 := by exact prefixLift 744322
  have htrace : WordTrace (prefixWord ++ tailWord_744322) baseStart_744322 baseEnd_744322 := by
    simpa [prefixWord, tailWord_744322, baseEnd_744322] using wordTrace_append hprefix tailTrace_744322
  have hstable : (prefixWord ++ tailWord_744322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744322).length < 2 ^ (prefixWord ++ tailWord_744322).sum := by decide
  have hdescent : baseEnd_744322 < baseStart_744322 := by decide
  rcases family_descends (prefixWord ++ tailWord_744322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744325 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_744325 : Nat := 118140960795 + 744325 * 2 ^ 59
def prefixEnd_744325 : Nat := 4983230072969 + 3 ^ 40 * 744325 * 2
def baseEnd_744325 : Nat := 254797658771937039142945

theorem tailTrace_744325 : CollatzResearch.WordTrace tailWord_744325 prefixEnd_744325 254797658771937039142945 := by
  unfold tailWord_744325
  simp only [CollatzResearch.WordTrace]
  refine ⟨27147763028445120434522429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18098508685630080289681619 27147763028445120434522429)
  ·
    refine ⟨10180411135666920162945911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27147763028445120434522429 10180411135666920162945911)
    ·
      refine ⟨15270616703500380244418867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10180411135666920162945911 15270616703500380244418867)
      ·
        refine ⟨22905925055250570366628301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15270616703500380244418867 22905925055250570366628301)
        ·
          refine ⟨8589721895718963887485613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22905925055250570366628301 8589721895718963887485613)
          ·
            refine ⟨3221145710894611457807105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8589721895718963887485613 3221145710894611457807105)
            ·
              refine ⟨2415859283170958593355329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3221145710894611457807105 2415859283170958593355329)
              ·
                refine ⟨1811894462378218945016497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415859283170958593355329 1811894462378218945016497)
                ·
                  refine ⟨1358920846783664208762373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1811894462378218945016497 1358920846783664208762373)
                  ·
                    refine ⟨254797658771937039142945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358920846783664208762373 254797658771937039142945)
                    ·
                      rfl

theorem cell22_744325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_744325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744325 prefixEnd_744325 := by exact prefixLift 744325
  have htrace : WordTrace (prefixWord ++ tailWord_744325) baseStart_744325 baseEnd_744325 := by
    simpa [prefixWord, tailWord_744325, baseEnd_744325] using wordTrace_append hprefix tailTrace_744325
  have hstable : (prefixWord ++ tailWord_744325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744325).length < 2 ^ (prefixWord ++ tailWord_744325).sum := by decide
  have hdescent : baseEnd_744325 < baseStart_744325 := by decide
  rcases family_descends (prefixWord ++ tailWord_744325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744327 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 2, 3]
def baseStart_744327 : Nat := 118140960795 + 744327 * 2 ^ 59
def prefixEnd_744327 : Nat := 4983230072969 + 3 ^ 40 * 744327 * 2
def baseEnd_744327 : Nat := 254798343412809700592939

theorem tailTrace_744327 : CollatzResearch.WordTrace tailWord_744327 prefixEnd_744327 254798343412809700592939 := by
  unfold tailWord_744327
  simp only [CollatzResearch.WordTrace]
  refine ⟨27147835974437874776095235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18098557316291916517396823 27147835974437874776095235)
  ·
    refine ⟨40721753961656812164142853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27147835974437874776095235 40721753961656812164142853)
    ·
      refine ⟨7635328867810652280776785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40721753961656812164142853 7635328867810652280776785)
      ·
        refine ⟨5726496650857989210582589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7635328867810652280776785 5726496650857989210582589)
        ·
          refine ⟨2147436244071745953968471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5726496650857989210582589 2147436244071745953968471)
          ·
            refine ⟨3221154366107618930952707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147436244071745953968471 3221154366107618930952707)
            ·
              refine ⟨4831731549161428396429061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221154366107618930952707 4831731549161428396429061)
              ·
                refine ⟨905949665467767824330449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4831731549161428396429061 905949665467767824330449)
                ·
                  refine ⟨679462249100825868247837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905949665467767824330449 679462249100825868247837)
                  ·
                    refine ⟨254798343412809700592939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679462249100825868247837 254798343412809700592939)
                    ·
                      rfl

theorem cell22_744327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_744327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744327 prefixEnd_744327 := by exact prefixLift 744327
  have htrace : WordTrace (prefixWord ++ tailWord_744327) baseStart_744327 baseEnd_744327 := by
    simpa [prefixWord, tailWord_744327, baseEnd_744327] using wordTrace_append hprefix tailTrace_744327
  have hstable : (prefixWord ++ tailWord_744327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744327).length < 2 ^ (prefixWord ++ tailWord_744327).sum := by decide
  have hdescent : baseEnd_744327 < baseStart_744327 := by decide
  rcases family_descends (prefixWord ++ tailWord_744327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744329 : List Nat := [1, 2, 1, 1, 5, 4, 2, 2, 4]
def baseStart_744329 : Nat := 118140960795 + 744329 * 2 ^ 59
def prefixEnd_744329 : Nat := 4983230072969 + 3 ^ 40 * 744329 * 2
def baseEnd_744329 : Nat := 84933009351227454014311

theorem tailTrace_744329 : CollatzResearch.WordTrace tailWord_744329 prefixEnd_744329 84933009351227454014311 := by
  unfold tailWord_744329
  simp only [CollatzResearch.WordTrace]
  refine ⟨27147908920430629117668041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18098605946953752745112027 27147908920430629117668041)
  ·
    refine ⟨20360931690322971838251031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27147908920430629117668041 20360931690322971838251031)
    ·
      refine ⟨30541397535484457757376547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20360931690322971838251031 30541397535484457757376547)
      ·
        refine ⟨45812096303226686636064821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30541397535484457757376547 45812096303226686636064821)
        ·
          refine ⟨4294884028427501872131077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45812096303226686636064821 4294884028427501872131077)
          ·
            refine ⟨805290755330156601024577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4294884028427501872131077 805290755330156601024577)
            ·
              refine ⟨603968066497617450768433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805290755330156601024577 603968066497617450768433)
              ·
                refine ⟨452976049873213088076325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603968066497617450768433 452976049873213088076325)
                ·
                  refine ⟨84933009351227454014311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452976049873213088076325 84933009351227454014311)
                  ·
                    rfl

theorem cell22_744329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_744329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744329 prefixEnd_744329 := by exact prefixLift 744329
  have htrace : WordTrace (prefixWord ++ tailWord_744329) baseStart_744329 baseEnd_744329 := by
    simpa [prefixWord, tailWord_744329, baseEnd_744329] using wordTrace_append hprefix tailTrace_744329
  have hstable : (prefixWord ++ tailWord_744329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744329).length < 2 ^ (prefixWord ++ tailWord_744329).sum := by decide
  have hdescent : baseEnd_744329 < baseStart_744329 := by decide
  rcases family_descends (prefixWord ++ tailWord_744329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744355 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 5, 3]
def baseStart_744355 : Nat := 118140960795 + 744355 * 2 ^ 59
def prefixEnd_744355 : Nat := 4983230072969 + 3 ^ 40 * 744355 * 2
def baseEnd_744355 : Nat := 254807928385026960892853

theorem tailTrace_744355 : CollatzResearch.WordTrace tailWord_744355 prefixEnd_744355 254807928385026960892853 := by
  unfold tailWord_744355
  simp only [CollatzResearch.WordTrace]
  refine ⟨27148857218336435558114519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18099238145557623705409679 27148857218336435558114519)
  ·
    refine ⟨40723285827504653337171779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27148857218336435558114519 40723285827504653337171779)
    ·
      refine ⟨61084928741256980005757669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40723285827504653337171779 61084928741256980005757669)
      ·
        refine ⟨11453424138985683751079563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61084928741256980005757669 11453424138985683751079563)
        ·
          refine ⟨17180136208478525626619345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11453424138985683751079563 17180136208478525626619345)
          ·
            refine ⟨12885102156358894219964509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17180136208478525626619345 12885102156358894219964509)
            ·
              refine ⟨4831913308634585332486691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12885102156358894219964509 4831913308634585332486691)
              ·
                refine ⟨7247869962951877998730037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831913308634585332486691 7247869962951877998730037)
                ·
                  refine ⟨679487809026738562380941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7247869962951877998730037 679487809026738562380941)
                  ·
                    refine ⟨254807928385026960892853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679487809026738562380941 254807928385026960892853)
                    ·
                      rfl

theorem cell22_744355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 3].length) (baseStart_744355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744355 prefixEnd_744355 := by exact prefixLift 744355
  have htrace : WordTrace (prefixWord ++ tailWord_744355) baseStart_744355 baseEnd_744355 := by
    simpa [prefixWord, tailWord_744355, baseEnd_744355] using wordTrace_append hprefix tailTrace_744355
  have hstable : (prefixWord ++ tailWord_744355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744355).length < 2 ^ (prefixWord ++ tailWord_744355).sum := by decide
  have hdescent : baseEnd_744355 < baseStart_744355 := by decide
  rcases family_descends (prefixWord ++ tailWord_744355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744359 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 2, 4]
def baseStart_744359 : Nat := 118140960795 + 744359 * 2 ^ 59
def prefixEnd_744359 : Nat := 4983230072969 + 3 ^ 40 * 744359 * 2
def baseEnd_744359 : Nat := 254809297666772283792841

theorem tailTrace_744359 : CollatzResearch.WordTrace tailWord_744359 prefixEnd_744359 254809297666772283792841 := by
  unfold tailWord_744359
  simp only [CollatzResearch.WordTrace]
  refine ⟨27149003110321944241260131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18099335406881296160840087 27149003110321944241260131)
  ·
    refine ⟨40723504665482916361890197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27149003110321944241260131 40723504665482916361890197)
    ·
      refine ⟨1908914281194511704463603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40723504665482916361890197 1908914281194511704463603)
      ·
        refine ⟨2863371421791767556695405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908914281194511704463603 2863371421791767556695405)
        ·
          refine ⟨1073764283171912833760777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2863371421791767556695405 1073764283171912833760777)
          ·
            refine ⟨805323212378934625320583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073764283171912833760777 805323212378934625320583)
            ·
              refine ⟨1207984818568401937980875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805323212378934625320583 1207984818568401937980875)
              ·
                refine ⟨1811977227852602906971313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207984818568401937980875 1811977227852602906971313)
                ·
                  refine ⟨1358982920889452180228485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1811977227852602906971313 1358982920889452180228485)
                  ·
                    refine ⟨254809297666772283792841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358982920889452180228485 254809297666772283792841)
                    ·
                      rfl

theorem cell22_744359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_744359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744359 prefixEnd_744359 := by exact prefixLift 744359
  have htrace : WordTrace (prefixWord ++ tailWord_744359) baseStart_744359 baseEnd_744359 := by
    simpa [prefixWord, tailWord_744359, baseEnd_744359] using wordTrace_append hprefix tailTrace_744359
  have hstable : (prefixWord ++ tailWord_744359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744359).length < 2 ^ (prefixWord ++ tailWord_744359).sum := by decide
  have hdescent : baseEnd_744359 < baseStart_744359 := by decide
  rcases family_descends (prefixWord ++ tailWord_744359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744535 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 3, 7]
def baseStart_744535 : Nat := 118140960795 + 744535 * 2 ^ 59
def prefixEnd_744535 : Nat := 4983230072969 + 3 ^ 40 * 744535 * 2
def baseEnd_744535 : Nat := 254869546063566491392301

theorem tailTrace_744535 : CollatzResearch.WordTrace tailWord_744535 prefixEnd_744535 254869546063566491392301 := by
  unfold tailWord_744535
  simp only [CollatzResearch.WordTrace]
  refine ⟨27155422357684326299667059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18103614905122884199778039 27155422357684326299667059)
  ·
    refine ⟨40733133536526489449500589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27155422357684326299667059 40733133536526489449500589)
    ·
      refine ⟨15274925076197433543562721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40733133536526489449500589 15274925076197433543562721)
      ·
        refine ⟨11456193807148075157672041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15274925076197433543562721 11456193807148075157672041)
        ·
          refine ⟨8592145355361056368254031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11456193807148075157672041 8592145355361056368254031)
          ·
            refine ⟨12888218033041584552381047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592145355361056368254031 12888218033041584552381047)
            ·
              refine ⟨19332327049562376828571571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12888218033041584552381047 19332327049562376828571571)
              ·
                refine ⟨28998490574343565242857357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19332327049562376828571571 28998490574343565242857357)
                ·
                  refine ⟨10874433965378836966071509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28998490574343565242857357 10874433965378836966071509)
                  ·
                    refine ⟨254869546063566491392301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10874433965378836966071509 254869546063566491392301)
                    ·
                      rfl

theorem cell22_744535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_744535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744535 prefixEnd_744535 := by exact prefixLift 744535
  have htrace : WordTrace (prefixWord ++ tailWord_744535) baseStart_744535 baseEnd_744535 := by
    simpa [prefixWord, tailWord_744535, baseEnd_744535] using wordTrace_append hprefix tailTrace_744535
  have hstable : (prefixWord ++ tailWord_744535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744535).length < 2 ^ (prefixWord ++ tailWord_744535).sum := by decide
  have hdescent : baseEnd_744535 < baseStart_744535 := by decide
  rcases family_descends (prefixWord ++ tailWord_744535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744554 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_744554 : Nat := 118140960795 + 744554 * 2 ^ 59
def prefixEnd_744554 : Nat := 4983230072969 + 3 ^ 40 * 744554 * 2
def baseEnd_744554 : Nat := 84958683383952258389081

theorem tailTrace_744554 : CollatzResearch.WordTrace tailWord_744554 prefixEnd_744554 84958683383952258389081 := by
  unfold tailWord_744554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6789028836153873136152179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18104076896410328363072477 6789028836153873136152179)
  ·
    refine ⟨10183543254230809704228269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6789028836153873136152179 10183543254230809704228269)
    ·
      refine ⟨3818828720336553639085601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10183543254230809704228269 3818828720336553639085601)
      ·
        refine ⟨2864121540252415229314201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3818828720336553639085601 2864121540252415229314201)
        ·
          refine ⟨2148091155189311421985651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2864121540252415229314201 2148091155189311421985651)
          ·
            refine ⟨3222136732783967132978477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148091155189311421985651 3222136732783967132978477)
            ·
              refine ⟨1208301274793987674866929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3222136732783967132978477 1208301274793987674866929)
              ·
                refine ⟨906225956095490756150197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208301274793987674866929 906225956095490756150197)
                ·
                  refine ⟨84958683383952258389081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 906225956095490756150197 84958683383952258389081)
                  ·
                    rfl

theorem cell22_744554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_744554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744554 prefixEnd_744554 := by exact prefixLift 744554
  have htrace : WordTrace (prefixWord ++ tailWord_744554) baseStart_744554 baseEnd_744554 := by
    simpa [prefixWord, tailWord_744554, baseEnd_744554] using wordTrace_append hprefix tailTrace_744554
  have hstable : (prefixWord ++ tailWord_744554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744554).length < 2 ^ (prefixWord ++ tailWord_744554).sum := by decide
  have hdescent : baseEnd_744554 < baseStart_744554 := by decide
  rcases family_descends (prefixWord ++ tailWord_744554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744764 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_744764 : Nat := 118140960795 + 744764 * 2 ^ 59
def prefixEnd_744764 : Nat := 4983230072969 + 3 ^ 40 * 744764 * 2
def baseEnd_744764 : Nat := 254947937443486227416599

theorem tailTrace_744764 : CollatzResearch.WordTrace tailWord_744764 prefixEnd_744764 254947937443486227416599 := by
  unfold tailWord_744764
  simp only [CollatzResearch.WordTrace]
  refine ⟨13581887336927349204876673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18109183115903132273168897 13581887336927349204876673)
  ·
    refine ⟨10186415502695511903657505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13581887336927349204876673 10186415502695511903657505)
    ·
      refine ⟨7639811627021633927743129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10186415502695511903657505 7639811627021633927743129)
      ·
        refine ⟨5729858720266225445807347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7639811627021633927743129 5729858720266225445807347)
        ·
          refine ⟨8594788080399338168711021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729858720266225445807347 8594788080399338168711021)
          ·
            refine ⟨3223045530149751813266633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8594788080399338168711021 3223045530149751813266633)
            ·
              refine ⟨2417284147612313859949975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3223045530149751813266633 2417284147612313859949975)
              ·
                refine ⟨3625926221418470789924963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417284147612313859949975 3625926221418470789924963)
                ·
                  refine ⟨5438889332127706184887445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625926221418470789924963 5438889332127706184887445)
                  ·
                    refine ⟨254947937443486227416599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5438889332127706184887445 254947937443486227416599)
                    ·
                      rfl

theorem cell22_744764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_744764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744764 prefixEnd_744764 := by exact prefixLift 744764
  have htrace : WordTrace (prefixWord ++ tailWord_744764) baseStart_744764 baseEnd_744764 := by
    simpa [prefixWord, tailWord_744764, baseEnd_744764] using wordTrace_append hprefix tailTrace_744764
  have hstable : (prefixWord ++ tailWord_744764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744764).length < 2 ^ (prefixWord ++ tailWord_744764).sum := by decide
  have hdescent : baseEnd_744764 < baseStart_744764 := by decide
  rcases family_descends (prefixWord ++ tailWord_744764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744766 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_744766 : Nat := 118140960795 + 744766 * 2 ^ 59
def prefixEnd_744766 : Nat := 4983230072969 + 3 ^ 40 * 744766 * 2
def baseEnd_744766 : Nat := 254948622084358888866593

theorem tailTrace_744766 : CollatzResearch.WordTrace tailWord_744766 prefixEnd_744766 254948622084358888866593 := by
  unfold tailWord_744766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395480952480931593915769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18109231746564968500884101 3395480952480931593915769)
  ·
    refine ⟨2546610714360698695436827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3395480952480931593915769 2546610714360698695436827)
    ·
      refine ⟨3819916071541048043155241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2546610714360698695436827 3819916071541048043155241)
      ·
        refine ⟨2864937053655786032366431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3819916071541048043155241 2864937053655786032366431)
        ·
          refine ⟨4297405580483679048549647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2864937053655786032366431 4297405580483679048549647)
          ·
            refine ⟨6446108370725518572824471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297405580483679048549647 6446108370725518572824471)
            ·
              refine ⟨9669162556088277859236707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6446108370725518572824471 9669162556088277859236707)
              ·
                refine ⟨14503743834132416788855061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9669162556088277859236707 14503743834132416788855061)
                ·
                  refine ⟨679862992224957036977581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14503743834132416788855061 679862992224957036977581)
                  ·
                    refine ⟨254948622084358888866593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679862992224957036977581 254948622084358888866593)
                    ·
                      rfl

theorem cell22_744766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_744766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744766 prefixEnd_744766 := by exact prefixLift 744766
  have htrace : WordTrace (prefixWord ++ tailWord_744766) baseStart_744766 baseEnd_744766 := by
    simpa [prefixWord, tailWord_744766, baseEnd_744766] using wordTrace_append hprefix tailTrace_744766
  have hstable : (prefixWord ++ tailWord_744766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744766).length < 2 ^ (prefixWord ++ tailWord_744766).sum := by decide
  have hdescent : baseEnd_744766 < baseStart_744766 := by decide
  rcases family_descends (prefixWord ++ tailWord_744766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744800 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 2, 3]
def baseStart_744800 : Nat := 118140960795 + 744800 * 2 ^ 59
def prefixEnd_744800 : Nat := 4983230072969 + 3 ^ 40 * 744800 * 2
def baseEnd_744800 : Nat := 254960260979194133516489

theorem tailTrace_744800 : CollatzResearch.WordTrace tailWord_744800 prefixEnd_744800 254960260979194133516489 := by
  unfold tailWord_744800
  simp only [CollatzResearch.WordTrace]
  refine ⟨13582543850862138279031927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18110058467816184372042569 13582543850862138279031927)
  ·
    refine ⟨20373815776293207418547891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13582543850862138279031927 20373815776293207418547891)
    ·
      refine ⟨30560723664439811127821837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20373815776293207418547891 30560723664439811127821837)
      ·
        refine ⟨11460271374164929172933189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30560723664439811127821837 11460271374164929172933189)
        ·
          refine ⟨2148800882655924219924973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11460271374164929172933189 2148800882655924219924973)
          ·
            refine ⟨805800330995971582471865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2148800882655924219924973 805800330995971582471865)
            ·
              refine ⟨604350248246978686853899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805800330995971582471865 604350248246978686853899)
              ·
                refine ⟨906525372370468030280849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604350248246978686853899 906525372370468030280849)
                ·
                  refine ⟨679894029277851022710637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 906525372370468030280849 679894029277851022710637)
                  ·
                    refine ⟨254960260979194133516489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679894029277851022710637 254960260979194133516489)
                    ·
                      rfl

theorem cell22_744800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_744800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744800 prefixEnd_744800 := by exact prefixLift 744800
  have htrace : WordTrace (prefixWord ++ tailWord_744800) baseStart_744800 baseEnd_744800 := by
    simpa [prefixWord, tailWord_744800, baseEnd_744800] using wordTrace_append hprefix tailTrace_744800
  have hstable : (prefixWord ++ tailWord_744800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744800).length < 2 ^ (prefixWord ++ tailWord_744800).sum := by decide
  have hdescent : baseEnd_744800 < baseStart_744800 := by decide
  rcases family_descends (prefixWord ++ tailWord_744800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744828 : List Nat := [2, 2, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_744828 : Nat := 118140960795 + 744828 * 2 ^ 59
def prefixEnd_744828 : Nat := 4983230072969 + 3 ^ 40 * 744828 * 2
def baseEnd_744828 : Nat := 254969845951411393816403

theorem tailTrace_744828 : CollatzResearch.WordTrace tailWord_744828 prefixEnd_744828 254969845951411393816403 := by
  unfold tailWord_744828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13583054472811418670041569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18110739297081891560055425 13583054472811418670041569)
  ·
    refine ⟨10187290854608564002531177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13583054472811418670041569 10187290854608564002531177)
    ·
      refine ⟨7640468140956423001898383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10187290854608564002531177 7640468140956423001898383)
      ·
        refine ⟨11460702211434634502847575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7640468140956423001898383 11460702211434634502847575)
        ·
          refine ⟨17191053317151951754271363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11460702211434634502847575 17191053317151951754271363)
          ·
            refine ⟨25786579975727927631407045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17191053317151951754271363 25786579975727927631407045)
            ·
              refine ⟨4834983745448986430888821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25786579975727927631407045 4834983745448986430888821)
              ·
                refine ⟨453279726135842477895827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4834983745448986430888821 453279726135842477895827)
                ·
                  refine ⟨679919589203763716843741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453279726135842477895827 679919589203763716843741)
                  ·
                    refine ⟨254969845951411393816403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 679919589203763716843741 254969845951411393816403)
                    ·
                      rfl

theorem cell22_744828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_744828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744828 prefixEnd_744828 := by exact prefixLift 744828
  have htrace : WordTrace (prefixWord ++ tailWord_744828) baseStart_744828 baseEnd_744828 := by
    simpa [prefixWord, tailWord_744828, baseEnd_744828] using wordTrace_append hprefix tailTrace_744828
  have hstable : (prefixWord ++ tailWord_744828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744828).length < 2 ^ (prefixWord ++ tailWord_744828).sum := by decide
  have hdescent : baseEnd_744828 < baseStart_744828 := by decide
  rcases family_descends (prefixWord ++ tailWord_744828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744871 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 3, 4]
def baseStart_744871 : Nat := 118140960795 + 744871 * 2 ^ 59
def prefixEnd_744871 : Nat := 4983230072969 + 3 ^ 40 * 744871 * 2
def baseEnd_744871 : Nat := 254984565730173614991271

theorem tailTrace_744871 : CollatzResearch.WordTrace tailWord_744871 prefixEnd_744871 254984565730173614991271 := by
  unfold tailWord_744871
  simp only [CollatzResearch.WordTrace]
  refine ⟨27167677284467055683898467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18111784856311370455932311 27167677284467055683898467)
  ·
    refine ⟨40751515926700583525847701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27167677284467055683898467 40751515926700583525847701)
    ·
      refine ⟨1910227309064089852774111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40751515926700583525847701 1910227309064089852774111)
      ·
        refine ⟨2865340963596134779161167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910227309064089852774111 2865340963596134779161167)
        ·
          refine ⟨4298011445394202168741751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865340963596134779161167 4298011445394202168741751)
          ·
            refine ⟨6447017168091303253112627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298011445394202168741751 6447017168091303253112627)
            ·
              refine ⟨9670525752136954879668941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447017168091303253112627 9670525752136954879668941)
              ·
                refine ⟨3626447157051358079875853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9670525752136954879668941 3626447157051358079875853)
                ·
                  refine ⟨1359917683894259279953445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3626447157051358079875853 1359917683894259279953445)
                  ·
                    refine ⟨254984565730173614991271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1359917683894259279953445 254984565730173614991271)
                    ·
                      rfl

theorem cell22_744871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_744871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744871 prefixEnd_744871 := by exact prefixLift 744871
  have htrace : WordTrace (prefixWord ++ tailWord_744871) baseStart_744871 baseEnd_744871 := by
    simpa [prefixWord, tailWord_744871, baseEnd_744871] using wordTrace_append hprefix tailTrace_744871
  have hstable : (prefixWord ++ tailWord_744871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744871).length < 2 ^ (prefixWord ++ tailWord_744871).sum := by decide
  have hdescent : baseEnd_744871 < baseStart_744871 := by decide
  rcases family_descends (prefixWord ++ tailWord_744871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744888 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 1, 4]
def baseStart_744888 : Nat := 118140960795 + 744888 * 2 ^ 59
def prefixEnd_744888 : Nat := 4983230072969 + 3 ^ 40 * 744888 * 2
def baseEnd_744888 : Nat := 254990385177591237316219

theorem tailTrace_744888 : CollatzResearch.WordTrace tailWord_744888 prefixEnd_744888 254990385177591237316219 := by
  unfold tailWord_744888
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584148662702733793633659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18112198216936978391511545 13584148662702733793633659)
  ·
    refine ⟨20376222994054100690450489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13584148662702733793633659 20376222994054100690450489)
    ·
      refine ⟨15282167245540575517837867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20376222994054100690450489 15282167245540575517837867)
      ·
        refine ⟨22923250868310863276756801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15282167245540575517837867 22923250868310863276756801)
        ·
          refine ⟨17192438151233147457567601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22923250868310863276756801 17192438151233147457567601)
          ·
            refine ⟨12894328613424860593175701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17192438151233147457567601 12894328613424860593175701)
            ·
              refine ⟨604421653754290340305111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12894328613424860593175701 604421653754290340305111)
              ·
                refine ⟨906632480631435510457667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604421653754290340305111 906632480631435510457667)
                ·
                  refine ⟨1359948720947153265686501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906632480631435510457667 1359948720947153265686501)
                  ·
                    refine ⟨254990385177591237316219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1359948720947153265686501 254990385177591237316219)
                    ·
                      rfl

theorem cell22_744888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_744888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744888 prefixEnd_744888 := by exact prefixLift 744888
  have htrace : WordTrace (prefixWord ++ tailWord_744888) baseStart_744888 baseEnd_744888 := by
    simpa [prefixWord, tailWord_744888, baseEnd_744888] using wordTrace_append hprefix tailTrace_744888
  have hstable : (prefixWord ++ tailWord_744888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744888).length < 2 ^ (prefixWord ++ tailWord_744888).sum := by decide
  have hdescent : baseEnd_744888 < baseStart_744888 := by decide
  rcases family_descends (prefixWord ++ tailWord_744888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744931 : List Nat := [1, 1, 1, 6, 2, 2, 1, 8]
def baseStart_744931 : Nat := 118140960795 + 744931 * 2 ^ 59
def prefixEnd_744931 : Nat := 4983230072969 + 3 ^ 40 * 744931 * 2
def baseEnd_744931 : Nat := 28333900550705939832343

theorem tailTrace_744931 : CollatzResearch.WordTrace tailWord_744931 prefixEnd_744931 28333900550705939832343 := by
  unfold tailWord_744931
  simp only [CollatzResearch.WordTrace]
  refine ⟨27169865664249685931082647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18113243776166457287388431 27169865664249685931082647)
  ·
    refine ⟨40754798496374528896623971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27169865664249685931082647 40754798496374528896623971)
    ·
      refine ⟨61132197744561793344935957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40754798496374528896623971 61132197744561793344935957)
      ·
        refine ⟨2865571769276334063043873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61132197744561793344935957 2865571769276334063043873)
        ·
          refine ⟨2149178826957250547282905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2865571769276334063043873 2149178826957250547282905)
          ·
            refine ⟨1611884120217937910462179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2149178826957250547282905 1611884120217937910462179)
            ·
              refine ⟨2417826180326906865693269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611884120217937910462179 2417826180326906865693269)
              ·
                refine ⟨28333900550705939832343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2417826180326906865693269 28333900550705939832343)
                ·
                  rfl

theorem cell22_744931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 8].length) (baseStart_744931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_744931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_744931 prefixEnd_744931 := by exact prefixLift 744931
  have htrace : WordTrace (prefixWord ++ tailWord_744931) baseStart_744931 baseEnd_744931 := by
    simpa [prefixWord, tailWord_744931, baseEnd_744931] using wordTrace_append hprefix tailTrace_744931
  have hstable : (prefixWord ++ tailWord_744931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744931).length < 2 ^ (prefixWord ++ tailWord_744931).sum := by decide
  have hdescent : baseEnd_744931 < baseStart_744931 := by decide
  rcases family_descends (prefixWord ++ tailWord_744931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745014 : List Nat := [5, 1, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_745014 : Nat := 118140960795 + 745014 * 2 ^ 59
def prefixEnd_745014 : Nat := 4983230072969 + 3 ^ 40 * 745014 * 2
def baseEnd_745014 : Nat := 255033517552568908665833

theorem tailTrace_745014 : CollatzResearch.WordTrace tailWord_745014 prefixEnd_745014 255033517552568908665833 := by
  unfold tailWord_745014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698305807684311944147131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18115261948632660737569397 1698305807684311944147131)
  ·
    refine ⟨2547458711526467916220697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698305807684311944147131 2547458711526467916220697)
    ·
      refine ⟨1910594033644850937165523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2547458711526467916220697 1910594033644850937165523)
      ·
        refine ⟨2865891050467276405748285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910594033644850937165523 2865891050467276405748285)
        ·
          refine ⟨1074709143925228652155607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2865891050467276405748285 1074709143925228652155607)
          ·
            refine ⟨1612063715887842978233411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074709143925228652155607 1612063715887842978233411)
            ·
              refine ⟨2418095573831764467350117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612063715887842978233411 2418095573831764467350117)
              ·
                refine ⟨453392920093455837628147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2418095573831764467350117 453392920093455837628147)
                ·
                  refine ⟨680089380140183756442221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453392920093455837628147 680089380140183756442221)
                  ·
                    refine ⟨255033517552568908665833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680089380140183756442221 255033517552568908665833)
                    ·
                      rfl

theorem cell22_745014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_745014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745014 prefixEnd_745014 := by exact prefixLift 745014
  have htrace : WordTrace (prefixWord ++ tailWord_745014) baseStart_745014 baseEnd_745014 := by
    simpa [prefixWord, tailWord_745014, baseEnd_745014] using wordTrace_append hprefix tailTrace_745014
  have hstable : (prefixWord ++ tailWord_745014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745014).length < 2 ^ (prefixWord ++ tailWord_745014).sum := by decide
  have hdescent : baseEnd_745014 < baseStart_745014 := by decide
  rcases family_descends (prefixWord ++ tailWord_745014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745145 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 5]
def baseStart_745145 : Nat := 118140960795 + 745145 * 2 ^ 59
def prefixEnd_745145 : Nat := 4983230072969 + 3 ^ 40 * 745145 * 2
def baseEnd_745145 : Nat := 85026120509909411213477

theorem tailTrace_745145 : CollatzResearch.WordTrace tailWord_745145 prefixEnd_745145 85026120509909411213477 := by
  unfold tailWord_745145
  simp only [CollatzResearch.WordTrace]
  refine ⟨27177670885474400479372889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18118447256982933652915259 27177670885474400479372889)
  ·
    refine ⟨20383253164105800359529667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27177670885474400479372889 20383253164105800359529667)
    ·
      refine ⟨30574879746158700539294501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20383253164105800359529667 30574879746158700539294501)
      ·
        refine ⟨5732789952404756351117719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30574879746158700539294501 5732789952404756351117719)
        ·
          refine ⟨8599184928607134526676579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732789952404756351117719 8599184928607134526676579)
          ·
            refine ⟨12898777392910701790014869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8599184928607134526676579 12898777392910701790014869)
            ·
              refine ⟨604630190292689146406947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12898777392910701790014869 604630190292689146406947)
              ·
                refine ⟨906945285439033719610421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604630190292689146406947 906945285439033719610421)
                ·
                  refine ⟨85026120509909411213477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 906945285439033719610421 85026120509909411213477)
                  ·
                    rfl

theorem cell22_745145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_745145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745145 prefixEnd_745145 := by exact prefixLift 745145
  have htrace : WordTrace (prefixWord ++ tailWord_745145) baseStart_745145 baseEnd_745145 := by
    simpa [prefixWord, tailWord_745145, baseEnd_745145] using wordTrace_append hprefix tailTrace_745145
  have hstable : (prefixWord ++ tailWord_745145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745145).length < 2 ^ (prefixWord ++ tailWord_745145).sum := by decide
  have hdescent : baseEnd_745145 < baseStart_745145 := by decide
  rcases family_descends (prefixWord ++ tailWord_745145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745188 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_745188 : Nat := 118140960795 + 745188 * 2 ^ 59
def prefixEnd_745188 : Nat := 4983230072969 + 3 ^ 40 * 745188 * 2
def baseEnd_745188 : Nat := 255093081308490454815299

theorem tailTrace_745188 : CollatzResearch.WordTrace tailWord_745188 prefixEnd_745188 255093081308490454815299 := by
  unfold tailWord_745188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13589619612159309411594109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18119492816212412548792145 13589619612159309411594109)
  ·
    refine ⟨5096107354559741029347791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13589619612159309411594109 5096107354559741029347791)
    ·
      refine ⟨7644161031839611544021687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5096107354559741029347791 7644161031839611544021687)
      ·
        refine ⟨11466241547759417316032531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7644161031839611544021687 11466241547759417316032531)
        ·
          refine ⟨17199362321639125974048797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11466241547759417316032531 17199362321639125974048797)
          ·
            refine ⟨6449760870614672240268299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17199362321639125974048797 6449760870614672240268299)
            ·
              refine ⟨9674641305922008360402449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6449760870614672240268299 9674641305922008360402449)
              ·
                refine ⟨7255980979441506270301837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9674641305922008360402449 7255980979441506270301837)
                ·
                  refine ⟨2720992867290564851363189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7255980979441506270301837 2720992867290564851363189)
                  ·
                    refine ⟨255093081308490454815299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2720992867290564851363189 255093081308490454815299)
                    ·
                      rfl

theorem cell22_745188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_745188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745188 prefixEnd_745188 := by exact prefixLift 745188
  have htrace : WordTrace (prefixWord ++ tailWord_745188) baseStart_745188 baseEnd_745188 := by
    simpa [prefixWord, tailWord_745188, baseEnd_745188] using wordTrace_append hprefix tailTrace_745188
  have hstable : (prefixWord ++ tailWord_745188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745188).length < 2 ^ (prefixWord ++ tailWord_745188).sum := by decide
  have hdescent : baseEnd_745188 < baseStart_745188 := by decide
  rcases family_descends (prefixWord ++ tailWord_745188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745203 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 4, 4]
def baseStart_745203 : Nat := 118140960795 + 745203 * 2 ^ 59
def prefixEnd_745203 : Nat := 4983230072969 + 3 ^ 40 * 745203 * 2
def baseEnd_745203 : Nat := 255098216115035415690253

theorem tailTrace_745203 : CollatzResearch.WordTrace tailWord_745203 prefixEnd_745203 255098216115035415690253 := by
  unfold tailWord_745203
  simp only [CollatzResearch.WordTrace]
  refine ⟨27179786319264276384984263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18119857546176184256656175 27179786319264276384984263)
  ·
    refine ⟨40769679478896414577476395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27179786319264276384984263 40769679478896414577476395)
    ·
      refine ⟨61154519218344621866214593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40769679478896414577476395 61154519218344621866214593)
      ·
        refine ⟨45865889413758466399660945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61154519218344621866214593 45865889413758466399660945)
        ·
          refine ⟨34399417060318849799745709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45865889413758466399660945 34399417060318849799745709)
          ·
            refine ⟨12899781397619568674904641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34399417060318849799745709 12899781397619568674904641)
            ·
              refine ⟨9674836048214676506178481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12899781397619568674904641 9674836048214676506178481)
              ·
                refine ⟨7256127036161007379633861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9674836048214676506178481 7256127036161007379633861)
                ·
                  refine ⟨1360523819280188883681349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7256127036161007379633861 1360523819280188883681349)
                  ·
                    refine ⟨255098216115035415690253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1360523819280188883681349 255098216115035415690253)
                    ·
                      rfl

theorem cell22_745203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_745203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745203 prefixEnd_745203 := by exact prefixLift 745203
  have htrace : WordTrace (prefixWord ++ tailWord_745203) baseStart_745203 baseEnd_745203 := by
    simpa [prefixWord, tailWord_745203, baseEnd_745203] using wordTrace_append hprefix tailTrace_745203
  have hstable : (prefixWord ++ tailWord_745203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745203).length < 2 ^ (prefixWord ++ tailWord_745203).sum := by decide
  have hdescent : baseEnd_745203 < baseStart_745203 := by decide
  rcases family_descends (prefixWord ++ tailWord_745203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745220 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_745220 : Nat := 118140960795 + 745220 * 2 ^ 59
def prefixEnd_745220 : Nat := 4983230072969 + 3 ^ 40 * 745220 * 2
def baseEnd_745220 : Nat := 255104035562453038015201

theorem tailTrace_745220 : CollatzResearch.WordTrace tailWord_745220 prefixEnd_745220 255104035562453038015201 := by
  unfold tailWord_745220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13590203180101344144176557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18120270906801792192235409 13590203180101344144176557)
  ·
    refine ⟨5096326192538004054066209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13590203180101344144176557 5096326192538004054066209)
    ·
      refine ⟨3822244644403503040549657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5096326192538004054066209 3822244644403503040549657)
      ·
        refine ⟨2866683483302627280412243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3822244644403503040549657 2866683483302627280412243)
        ·
          refine ⟨4300025224953940920618365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866683483302627280412243 4300025224953940920618365)
          ·
            refine ⟨1612509459357727845231887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4300025224953940920618365 1612509459357727845231887)
            ·
              refine ⟨2418764189036591767847831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612509459357727845231887 2418764189036591767847831)
              ·
                refine ⟨3628146283554887651771747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418764189036591767847831 3628146283554887651771747)
                ·
                  refine ⟨5442219425332331477657621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628146283554887651771747 5442219425332331477657621)
                  ·
                    refine ⟨255104035562453038015201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5442219425332331477657621 255104035562453038015201)
                    ·
                      rfl

theorem cell22_745220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_745220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_745220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_745220 prefixEnd_745220 := by exact prefixLift 745220
  have htrace : WordTrace (prefixWord ++ tailWord_745220) baseStart_745220 baseEnd_745220 := by
    simpa [prefixWord, tailWord_745220, baseEnd_745220] using wordTrace_append hprefix tailTrace_745220
  have hstable : (prefixWord ++ tailWord_745220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745220).length < 2 ^ (prefixWord ++ tailWord_745220).sum := by decide
  have hdescent : baseEnd_745220 < baseStart_745220 := by decide
  rcases family_descends (prefixWord ++ tailWord_745220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
