import V185TrunkScan23Chunk0836

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4953409 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4953409 : Nat := 118140960795 + 4953409 * 2 ^ 59
def prefixEnd_4953409 : Nat := 4983230072969 + 3 ^ 40 * 4953409 * 2
def baseEnd_4953409 : Nat := 2543479695306915498207193

theorem tailTrace_4953409 : CollatzResearch.WordTrace tailWord_4953409 prefixEnd_4953409 2543479695306915498207193 := by
  unfold tailWord_4953409
  simp only [CollatzResearch.WordTrace]
  refine ⟨180665668511652642750807281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120443779007768428500538187 180665668511652642750807281)
  ·
    refine ⟨135499251383739482063105461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180665668511652642750807281 135499251383739482063105461)
    ·
      refine ⟨12703054817225576443416137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135499251383739482063105461 12703054817225576443416137)
      ·
        refine ⟨9527291112919182332562103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12703054817225576443416137 9527291112919182332562103)
        ·
          refine ⟨14290936669378773498843155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9527291112919182332562103 14290936669378773498843155)
          ·
            refine ⟨21436405004068160248264733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14290936669378773498843155 21436405004068160248264733)
            ·
              refine ⟨8038651876525560093099275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21436405004068160248264733 8038651876525560093099275)
              ·
                refine ⟨12057977814788340139648913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8038651876525560093099275 12057977814788340139648913)
                ·
                  refine ⟨9043483361091255104736685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12057977814788340139648913 9043483361091255104736685)
                  ·
                    refine ⟨3391306260409220664276257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9043483361091255104736685 3391306260409220664276257)
                    ·
                      refine ⟨2543479695306915498207193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391306260409220664276257 2543479695306915498207193)
                      ·
                        rfl

theorem cell23_4953409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4953409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953409 prefixEnd_4953409 := by exact prefixLift 4953409
  have htrace : WordTrace (prefixWord ++ tailWord_4953409) baseStart_4953409 baseEnd_4953409 := by
    simpa [prefixWord, tailWord_4953409, baseEnd_4953409] using wordTrace_append hprefix tailTrace_4953409
  have hstable : (prefixWord ++ tailWord_4953409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953409).length < 2 ^ (prefixWord ++ tailWord_4953409).sum := by decide
  have hdescent : baseEnd_4953409 < baseStart_4953409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953422 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_4953422 : Nat := 118140960795 + 4953422 * 2 ^ 59
def prefixEnd_4953422 : Nat := 4983230072969 + 3 ^ 40 * 4953422 * 2
def baseEnd_4953422 : Nat := 2543486370555423947344633

theorem tailTrace_4953422 : CollatzResearch.WordTrace tailWord_4953422 prefixEnd_4953422 2543486370555423947344633 := by
  unfold tailWord_4953422
  simp only [CollatzResearch.WordTrace]
  refine ⟨22583267832575693246378815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120444095107070363980687013 22583267832575693246378815)
  ·
    refine ⟨33874901748863539869568223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22583267832575693246378815 33874901748863539869568223)
    ·
      refine ⟨50812352623295309804352335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33874901748863539869568223 50812352623295309804352335)
      ·
        refine ⟨76218528934942964706528503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50812352623295309804352335 76218528934942964706528503)
        ·
          refine ⟨114327793402414447059792755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76218528934942964706528503 114327793402414447059792755)
          ·
            refine ⟨171491690103621670589689133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114327793402414447059792755 171491690103621670589689133)
            ·
              refine ⟨64309383788858126471133425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171491690103621670589689133 64309383788858126471133425)
              ·
                refine ⟨48232037841643594853350069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64309383788858126471133425 48232037841643594853350069)
                ·
                  refine ⟨4521753547654087017501569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48232037841643594853350069 4521753547654087017501569)
                  ·
                    refine ⟨3391315160740565263126177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521753547654087017501569 3391315160740565263126177)
                    ·
                      refine ⟨2543486370555423947344633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391315160740565263126177 2543486370555423947344633)
                      ·
                        rfl

theorem cell23_4953422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_4953422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953422 prefixEnd_4953422 := by exact prefixLift 4953422
  have htrace : WordTrace (prefixWord ++ tailWord_4953422) baseStart_4953422 baseEnd_4953422 := by
    simpa [prefixWord, tailWord_4953422, baseEnd_4953422] using wordTrace_append hprefix tailTrace_4953422
  have hstable : (prefixWord ++ tailWord_4953422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953422).length < 2 ^ (prefixWord ++ tailWord_4953422).sum := by decide
  have hdescent : baseEnd_4953422 < baseStart_4953422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953428 : List Nat := [2, 4, 1, 1, 2, 1, 12]
def baseStart_4953428 : Nat := 118140960795 + 4953428 * 2 ^ 59
def prefixEnd_4953428 : Nat := 4983230072969 + 3 ^ 40 * 4953428 * 2
def baseEnd_4953428 : Nat := 31401104338757418813205

theorem tailTrace_4953428 : CollatzResearch.WordTrace tailWord_4953428 prefixEnd_4953428 31401104338757418813205 := by
  unfold tailWord_4953428
  simp only [CollatzResearch.WordTrace]
  refine ⟨90333180749291904497874469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120444240999055872663832625 90333180749291904497874469)
  ·
    refine ⟨16937471390492232093351463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90333180749291904497874469 16937471390492232093351463)
    ·
      refine ⟨25406207085738348140027195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16937471390492232093351463 25406207085738348140027195)
      ·
        refine ⟨38109310628607522210040793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25406207085738348140027195 38109310628607522210040793)
        ·
          refine ⟨28581982971455641657530595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38109310628607522210040793 28581982971455641657530595)
          ·
            refine ⟨42872974457183462486295893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28581982971455641657530595 42872974457183462486295893)
            ·
              refine ⟨31401104338757418813205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 42872974457183462486295893 31401104338757418813205)
              ·
                rfl

theorem cell23_4953428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 12].length) (baseStart_4953428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953428 prefixEnd_4953428 := by exact prefixLift 4953428
  have htrace : WordTrace (prefixWord ++ tailWord_4953428) baseStart_4953428 baseEnd_4953428 := by
    simpa [prefixWord, tailWord_4953428, baseEnd_4953428] using wordTrace_append hprefix tailTrace_4953428
  have hstable : (prefixWord ++ tailWord_4953428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953428).length < 2 ^ (prefixWord ++ tailWord_4953428).sum := by decide
  have hdescent : baseEnd_4953428 < baseStart_4953428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953452 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_4953452 : Nat := 118140960795 + 4953452 * 2 ^ 59
def prefixEnd_4953452 : Nat := 4983230072969 + 3 ^ 40 * 4953452 * 2
def baseEnd_4953452 : Nat := 2543501774975058829969495

theorem tailTrace_4953452 : CollatzResearch.WordTrace tailWord_4953452 prefixEnd_4953452 2543501774975058829969495 := by
  unfold tailWord_4953452
  simp only [CollatzResearch.WordTrace]
  refine ⟨90333618425248430547311305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120444824566997907396415073 90333618425248430547311305)
  ·
    refine ⟨67750213818936322910483479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90333618425248430547311305 67750213818936322910483479)
    ·
      refine ⟨101625320728404484365725219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67750213818936322910483479 101625320728404484365725219)
      ·
        refine ⟨152437981092606726548587829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101625320728404484365725219 152437981092606726548587829)
        ·
          refine ⟨14291060727431880613930109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152437981092606726548587829 14291060727431880613930109)
          ·
            refine ⟨5359147772786955230223791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14291060727431880613930109 5359147772786955230223791)
            ·
              refine ⟨8038721659180432845335687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5359147772786955230223791 8038721659180432845335687)
              ·
                refine ⟨12058082488770649268003531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8038721659180432845335687 12058082488770649268003531)
                ·
                  refine ⟨18087123733155973902005297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12058082488770649268003531 18087123733155973902005297)
                  ·
                    refine ⟨13565342799866980426503973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18087123733155973902005297 13565342799866980426503973)
                    ·
                      refine ⟨2543501774975058829969495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13565342799866980426503973 2543501774975058829969495)
                      ·
                        rfl

theorem cell23_4953452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_4953452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953452 prefixEnd_4953452 := by exact prefixLift 4953452
  have htrace : WordTrace (prefixWord ++ tailWord_4953452) baseStart_4953452 baseEnd_4953452 := by
    simpa [prefixWord, tailWord_4953452, baseEnd_4953452] using wordTrace_append hprefix tailTrace_4953452
  have hstable : (prefixWord ++ tailWord_4953452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953452).length < 2 ^ (prefixWord ++ tailWord_4953452).sum := by decide
  have hdescent : baseEnd_4953452 < baseStart_4953452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953468 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_4953468 : Nat := 118140960795 + 4953468 * 2 ^ 59
def prefixEnd_4953468 : Nat := 4983230072969 + 3 ^ 40 * 4953468 * 2
def baseEnd_4953468 : Nat := 2543509990665530767369421

theorem tailTrace_4953468 : CollatzResearch.WordTrace tailWord_4953468 prefixEnd_4953468 2543509990665530767369421 := by
  unfold tailWord_4953468
  simp only [CollatzResearch.WordTrace]
  refine ⟨90333910209219447913602529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120445213612292597218136705 90333910209219447913602529)
  ·
    refine ⟨67750432656914585935201897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90333910209219447913602529 67750432656914585935201897)
    ·
      refine ⟨50812824492685939451401423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67750432656914585935201897 50812824492685939451401423)
      ·
        refine ⟨76219236739028909177102135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50812824492685939451401423 76219236739028909177102135)
        ·
          refine ⟨114328855108543363765653203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76219236739028909177102135 114328855108543363765653203)
          ·
            refine ⟨171493282662815045648479805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114328855108543363765653203 171493282662815045648479805)
            ·
              refine ⟨64309980998555642118179927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171493282662815045648479805 64309980998555642118179927)
              ·
                refine ⟨96464971497833463177269891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64309980998555642118179927 96464971497833463177269891)
                ·
                  refine ⟨144697457246750194765904837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96464971497833463177269891 144697457246750194765904837)
                  ·
                    refine ⟨27130773233765661518607157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144697457246750194765904837 27130773233765661518607157)
                    ·
                      refine ⟨2543509990665530767369421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27130773233765661518607157 2543509990665530767369421)
                      ·
                        rfl

theorem cell23_4953468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_4953468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953468 prefixEnd_4953468 := by exact prefixLift 4953468
  have htrace : WordTrace (prefixWord ++ tailWord_4953468) baseStart_4953468 baseEnd_4953468 := by
    simpa [prefixWord, tailWord_4953468, baseEnd_4953468] using wordTrace_append hprefix tailTrace_4953468
  have hstable : (prefixWord ++ tailWord_4953468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953468).length < 2 ^ (prefixWord ++ tailWord_4953468).sum := by decide
  have hdescent : baseEnd_4953468 < baseStart_4953468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953490 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4953490 : Nat := 118140960795 + 4953490 * 2 ^ 59
def prefixEnd_4953490 : Nat := 4983230072969 + 3 ^ 40 * 4953490 * 2
def baseEnd_4953490 : Nat := 2543521287239929681294321

theorem tailTrace_4953490 : CollatzResearch.WordTrace tailWord_4953490 prefixEnd_4953490 2543521287239929681294321 := by
  unfold tailWord_4953490
  simp only [CollatzResearch.WordTrace]
  refine ⟨45167155706089798396126481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120445748549572795723003949 45167155706089798396126481)
  ·
    refine ⟨33875366779567348797094861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45167155706089798396126481 33875366779567348797094861)
    ·
      refine ⟨12703262542337755798910573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33875366779567348797094861 12703262542337755798910573)
      ·
        refine ⟨4763723453376658424591465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12703262542337755798910573 4763723453376658424591465)
        ·
          refine ⟨3572792590032493818443599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4763723453376658424591465 3572792590032493818443599)
          ·
            refine ⟨5359188885048740727665399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572792590032493818443599 5359188885048740727665399)
            ·
              refine ⟨8038783327573111091498099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5359188885048740727665399 8038783327573111091498099)
              ·
                refine ⟨12058174991359666637247149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8038783327573111091498099 12058174991359666637247149)
                ·
                  refine ⟨4521815621759874988967681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12058174991359666637247149 4521815621759874988967681)
                  ·
                    refine ⟨3391361716319906241725761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521815621759874988967681 3391361716319906241725761)
                    ·
                      refine ⟨2543521287239929681294321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391361716319906241725761 2543521287239929681294321)
                      ·
                        rfl

theorem cell23_4953490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4953490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953490 prefixEnd_4953490 := by exact prefixLift 4953490
  have htrace : WordTrace (prefixWord ++ tailWord_4953490) baseStart_4953490 baseEnd_4953490 := by
    simpa [prefixWord, tailWord_4953490, baseEnd_4953490] using wordTrace_append hprefix tailTrace_4953490
  have hstable : (prefixWord ++ tailWord_4953490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953490).length < 2 ^ (prefixWord ++ tailWord_4953490).sum := by decide
  have hdescent : baseEnd_4953490 < baseStart_4953490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953506 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_4953506 : Nat := 118140960795 + 4953506 * 2 ^ 59
def prefixEnd_4953506 : Nat := 4983230072969 + 3 ^ 40 * 4953506 * 2
def baseEnd_4953506 : Nat := 2543529502930401618694247

theorem tailTrace_4953506 : CollatzResearch.WordTrace tailWord_4953506 prefixEnd_4953506 2543529502930401618694247 := by
  unfold tailWord_4953506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45167301598075307079272093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120446137594867485544725581 45167301598075307079272093)
  ·
    refine ⟨16937738099278240154727035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45167301598075307079272093 16937738099278240154727035)
    ·
      refine ⟨25406607148917360232090553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16937738099278240154727035 25406607148917360232090553)
      ·
        refine ⟨19054955361688020174067915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25406607148917360232090553 19054955361688020174067915)
        ·
          refine ⟨28582433042532030261101873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19054955361688020174067915 28582433042532030261101873)
          ·
            refine ⟨21436824781899022695826405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28582433042532030261101873 21436824781899022695826405)
            ·
              refine ⟨4019404646606066755467451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21436824781899022695826405 4019404646606066755467451)
              ·
                refine ⟨6029106969909100133201177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019404646606066755467451 6029106969909100133201177)
                ·
                  refine ⟨4521830227431825099900883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6029106969909100133201177 4521830227431825099900883)
                  ·
                    refine ⟨6782745341147737649851325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4521830227431825099900883 6782745341147737649851325)
                    ·
                      refine ⟨2543529502930401618694247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6782745341147737649851325 2543529502930401618694247)
                      ·
                        rfl

theorem cell23_4953506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_4953506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953506 prefixEnd_4953506 := by exact prefixLift 4953506
  have htrace : WordTrace (prefixWord ++ tailWord_4953506) baseStart_4953506 baseEnd_4953506 := by
    simpa [prefixWord, tailWord_4953506, baseEnd_4953506] using wordTrace_append hprefix tailTrace_4953506
  have hstable : (prefixWord ++ tailWord_4953506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953506).length < 2 ^ (prefixWord ++ tailWord_4953506).sum := by decide
  have hdescent : baseEnd_4953506 < baseStart_4953506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953529 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 1, 4, 2]
def baseStart_4953529 : Nat := 118140960795 + 4953529 * 2 ^ 59
def prefixEnd_4953529 : Nat := 4983230072969 + 3 ^ 40 * 4953529 * 2
def baseEnd_4953529 : Nat := 2543541312985455028706641

theorem tailTrace_4953529 : CollatzResearch.WordTrace tailWord_4953529 prefixEnd_4953529 2543541312985455028706641 := by
  unfold tailWord_4953529
  simp only [CollatzResearch.WordTrace]
  refine ⟨180670045271217903245175641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120446696847478602163450427 180670045271217903245175641)
  ·
    refine ⟨135502533953413427433881731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180670045271217903245175641 135502533953413427433881731)
    ·
      refine ⟨203253800930120141150822597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135502533953413427433881731 203253800930120141150822597)
      ·
        refine ⟨38110087674397526465779237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203253800930120141150822597 38110087674397526465779237)
        ·
          refine ⟨7145641438949536212333607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38110087674397526465779237 7145641438949536212333607)
          ·
            refine ⟨10718462158424304318500411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7145641438949536212333607 10718462158424304318500411)
            ·
              refine ⟨16077693237636456477750617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10718462158424304318500411 16077693237636456477750617)
              ·
                refine ⟨12058269928227342358312963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16077693237636456477750617 12058269928227342358312963)
                ·
                  refine ⟨18087404892341013537469445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12058269928227342358312963 18087404892341013537469445)
                  ·
                    refine ⟨3391388417313940038275521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18087404892341013537469445 3391388417313940038275521)
                    ·
                      refine ⟨2543541312985455028706641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391388417313940038275521 2543541312985455028706641)
                      ·
                        rfl

theorem cell23_4953529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_4953529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953529 prefixEnd_4953529 := by exact prefixLift 4953529
  have htrace : WordTrace (prefixWord ++ tailWord_4953529) baseStart_4953529 baseEnd_4953529 := by
    simpa [prefixWord, tailWord_4953529, baseEnd_4953529] using wordTrace_append hprefix tailTrace_4953529
  have hstable : (prefixWord ++ tailWord_4953529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953529).length < 2 ^ (prefixWord ++ tailWord_4953529).sum := by decide
  have hdescent : baseEnd_4953529 < baseStart_4953529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953545 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 3]
def baseStart_4953545 : Nat := 118140960795 + 4953545 * 2 ^ 59
def prefixEnd_4953545 : Nat := 4983230072969 + 3 ^ 40 * 4953545 * 2
def baseEnd_4953545 : Nat := 2543549528675926966106567

theorem tailTrace_4953545 : CollatzResearch.WordTrace tailWord_4953545 prefixEnd_4953545 2543549528675926966106567 := by
  unfold tailWord_4953545
  simp only [CollatzResearch.WordTrace]
  refine ⟨180670628839159937977758089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120447085892773291985172059 180670628839159937977758089)
  ·
    refine ⟨135502971629369953483318567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180670628839159937977758089 135502971629369953483318567)
    ·
      refine ⟨203254457444054930224977851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135502971629369953483318567 203254457444054930224977851)
      ·
        refine ⟨304881686166082395337466777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203254457444054930224977851 304881686166082395337466777)
        ·
          refine ⟨228661264624561796503100083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304881686166082395337466777 228661264624561796503100083)
          ·
            refine ⟨342991896936842694754650125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228661264624561796503100083 342991896936842694754650125)
            ·
              refine ⟨128621961351316010532993797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342991896936842694754650125 128621961351316010532993797)
              ·
                refine ⟨24116617753371751974936337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128621961351316010532993797 24116617753371751974936337)
                ·
                  refine ⟨18087463315028813981202253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24116617753371751974936337 18087463315028813981202253)
                  ·
                    refine ⟨6782798743135805242950845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18087463315028813981202253 6782798743135805242950845)
                    ·
                      refine ⟨2543549528675926966106567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6782798743135805242950845 2543549528675926966106567)
                      ·
                        rfl

theorem cell23_4953545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_4953545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953545 prefixEnd_4953545 := by exact prefixLift 4953545
  have htrace : WordTrace (prefixWord ++ tailWord_4953545) baseStart_4953545 baseEnd_4953545 := by
    simpa [prefixWord, tailWord_4953545, baseEnd_4953545] using wordTrace_append hprefix tailTrace_4953545
  have hstable : (prefixWord ++ tailWord_4953545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953545).length < 2 ^ (prefixWord ++ tailWord_4953545).sum := by decide
  have hdescent : baseEnd_4953545 < baseStart_4953545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953546 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_4953546 : Nat := 118140960795 + 4953546 * 2 ^ 59
def prefixEnd_4953546 : Nat := 4983230072969 + 3 ^ 40 * 4953546 * 2
def baseEnd_4953546 : Nat := 2543550042156581462194063

theorem tailTrace_4953546 : CollatzResearch.WordTrace tailWord_4953546 prefixEnd_4953546 2543550042156581462194063 := by
  unfold tailWord_4953546
  simp only [CollatzResearch.WordTrace]
  refine ⟨45167666328039078787136123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120447110208104210099029661 45167666328039078787136123)
  ·
    refine ⟨67751499492058618180704185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45167666328039078787136123 67751499492058618180704185)
    ·
      refine ⟨50813624619043963635528139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67751499492058618180704185 50813624619043963635528139)
      ·
        refine ⟨76220436928565945453292209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50813624619043963635528139 76220436928565945453292209)
        ·
          refine ⟨57165327696424459089969157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76220436928565945453292209 57165327696424459089969157)
          ·
            refine ⟨10718498943079586079369217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57165327696424459089969157 10718498943079586079369217)
            ·
              refine ⟨8038874207309689559526913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10718498943079586079369217 8038874207309689559526913)
              ·
                refine ⟨6029155655482267169645185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8038874207309689559526913 6029155655482267169645185)
                ·
                  refine ⟨4521866741611700377233889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6029155655482267169645185 4521866741611700377233889)
                  ·
                    refine ⟨3391400056208775282925417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4521866741611700377233889 3391400056208775282925417)
                    ·
                      refine ⟨2543550042156581462194063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391400056208775282925417 2543550042156581462194063)
                      ·
                        rfl

theorem cell23_4953546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_4953546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953546 prefixEnd_4953546 := by exact prefixLift 4953546
  have htrace : WordTrace (prefixWord ++ tailWord_4953546) baseStart_4953546 baseEnd_4953546 := by
    simpa [prefixWord, tailWord_4953546, baseEnd_4953546] using wordTrace_append hprefix tailTrace_4953546
  have hstable : (prefixWord ++ tailWord_4953546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953546).length < 2 ^ (prefixWord ++ tailWord_4953546).sum := by decide
  have hdescent : baseEnd_4953546 < baseStart_4953546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953562 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_4953562 : Nat := 118140960795 + 4953562 * 2 ^ 59
def prefixEnd_4953562 : Nat := 4983230072969 + 3 ^ 40 * 4953562 * 2
def baseEnd_4953562 : Nat := 2543558257847053399593989

theorem tailTrace_4953562 : CollatzResearch.WordTrace tailWord_4953562 prefixEnd_4953562 2543558257847053399593989 := by
  unfold tailWord_4953562
  simp only [CollatzResearch.WordTrace]
  refine ⟨45167812220024587470281735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120447499253398899920751293 45167812220024587470281735)
  ·
    refine ⟨67751718330036881205422603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45167812220024587470281735 67751718330036881205422603)
    ·
      refine ⟨101627577495055321808133905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67751718330036881205422603 101627577495055321808133905)
      ·
        refine ⟨76220683121291491356100429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101627577495055321808133905 76220683121291491356100429)
        ·
          refine ⟨28582756170484309258537661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76220683121291491356100429 28582756170484309258537661)
          ·
            refine ⟨10718533563931615971951623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28582756170484309258537661 10718533563931615971951623)
            ·
              refine ⟨16077800345897423957927435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10718533563931615971951623 16077800345897423957927435)
              ·
                refine ⟨24116700518846135936891153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16077800345897423957927435 24116700518846135936891153)
                ·
                  refine ⟨18087525389134601952668365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24116700518846135936891153 18087525389134601952668365)
                  ·
                    refine ⟨6782822020925475732250637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18087525389134601952668365 6782822020925475732250637)
                    ·
                      refine ⟨2543558257847053399593989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6782822020925475732250637 2543558257847053399593989)
                      ·
                        rfl

theorem cell23_4953562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_4953562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953562 prefixEnd_4953562 := by exact prefixLift 4953562
  have htrace : WordTrace (prefixWord ++ tailWord_4953562) baseStart_4953562 baseEnd_4953562 := by
    simpa [prefixWord, tailWord_4953562, baseEnd_4953562] using wordTrace_append hprefix tailTrace_4953562
  have hstable : (prefixWord ++ tailWord_4953562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953562).length < 2 ^ (prefixWord ++ tailWord_4953562).sum := by decide
  have hdescent : baseEnd_4953562 < baseStart_4953562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953675 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4]
def baseStart_4953675 : Nat := 118140960795 + 4953675 * 2 ^ 59
def prefixEnd_4953675 : Nat := 4983230072969 + 3 ^ 40 * 4953675 * 2
def baseEnd_4953675 : Nat := 2543616281161011457480969

theorem tailTrace_4953675 : CollatzResearch.WordTrace tailWord_4953675 prefixEnd_4953675 2543616281161011457480969 := by
  unfold tailWord_4953675
  simp only [CollatzResearch.WordTrace]
  refine ⟨180675370328688970179990479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120450246885792646786660319 180675370328688970179990479)
  ·
    refine ⟨271013055493033455269985719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180675370328688970179990479 271013055493033455269985719)
    ·
      refine ⟨406519583239550182904978579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271013055493033455269985719 406519583239550182904978579)
      ·
        refine ⟨609779374859325274357467869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406519583239550182904978579 609779374859325274357467869)
        ·
          refine ⟨228667265572246977884050451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609779374859325274357467869 228667265572246977884050451)
          ·
            refine ⟨343000898358370466826075677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228667265572246977884050451 343000898358370466826075677)
            ·
              refine ⟨128625336884388925059778379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343000898358370466826075677 128625336884388925059778379)
              ·
                refine ⟨192938005326583387589667569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128625336884388925059778379 192938005326583387589667569)
                ·
                  refine ⟨144703503994937540692250677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192938005326583387589667569 144703503994937540692250677)
                  ·
                    refine ⟨13565953499525394439898501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144703503994937540692250677 13565953499525394439898501)
                    ·
                      refine ⟨2543616281161011457480969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13565953499525394439898501 2543616281161011457480969)
                      ·
                        rfl

theorem cell23_4953675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_4953675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953675 prefixEnd_4953675 := by exact prefixLift 4953675
  have htrace : WordTrace (prefixWord ++ tailWord_4953675) baseStart_4953675 baseEnd_4953675 := by
    simpa [prefixWord, tailWord_4953675, baseEnd_4953675] using wordTrace_append hprefix tailTrace_4953675
  have hstable : (prefixWord ++ tailWord_4953675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953675).length < 2 ^ (prefixWord ++ tailWord_4953675).sum := by decide
  have hdescent : baseEnd_4953675 < baseStart_4953675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953695 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_4953695 : Nat := 118140960795 + 4953695 * 2 ^ 59
def prefixEnd_4953695 : Nat := 4983230072969 + 3 ^ 40 * 4953695 * 2
def baseEnd_4953695 : Nat := 2543626550774101379230877

theorem tailTrace_4953695 : CollatzResearch.WordTrace tailWord_4953695 prefixEnd_4953695 2543626550774101379230877 := by
  unfold tailWord_4953695
  simp only [CollatzResearch.WordTrace]
  refine ⟨180676099788616513595718539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120450733192411009063812359 180676099788616513595718539)
  ·
    refine ⟨271014149682924770393577809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180676099788616513595718539 271014149682924770393577809)
    ·
      refine ⟨203260612262193577795183357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271014149682924770393577809 203260612262193577795183357)
      ·
        refine ⟨76222729598322591673193759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203260612262193577795183357 76222729598322591673193759)
        ·
          refine ⟨114334094397483887509790639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76222729598322591673193759 114334094397483887509790639)
          ·
            refine ⟨171501141596225831264685959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114334094397483887509790639 171501141596225831264685959)
            ·
              refine ⟨257251712394338746897028939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171501141596225831264685959 257251712394338746897028939)
              ·
                refine ⟨385877568591508120345543409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257251712394338746897028939 385877568591508120345543409)
                ·
                  refine ⟨289408176443631090259157557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385877568591508120345543409 289408176443631090259157557)
                  ·
                    refine ⟨27132016541590414711796021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 289408176443631090259157557 27132016541590414711796021)
                    ·
                      refine ⟨2543626550774101379230877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27132016541590414711796021 2543626550774101379230877)
                      ·
                        rfl

theorem cell23_4953695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_4953695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953695 prefixEnd_4953695 := by exact prefixLift 4953695
  have htrace : WordTrace (prefixWord ++ tailWord_4953695) baseStart_4953695 baseEnd_4953695 := by
    simpa [prefixWord, tailWord_4953695, baseEnd_4953695] using wordTrace_append hprefix tailTrace_4953695
  have hstable : (prefixWord ++ tailWord_4953695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953695).length < 2 ^ (prefixWord ++ tailWord_4953695).sum := by decide
  have hdescent : baseEnd_4953695 < baseStart_4953695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953706 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_4953706 : Nat := 118140960795 + 4953706 * 2 ^ 59
def prefixEnd_4953706 : Nat := 4983230072969 + 3 ^ 40 * 4953706 * 2
def baseEnd_4953706 : Nat := 847877399687100278731109

theorem tailTrace_4953706 : CollatzResearch.WordTrace tailWord_4953706 prefixEnd_4953706 847877399687100278731109 := by
  unfold tailWord_4953706
  simp only [CollatzResearch.WordTrace]
  refine ⟨45169125247894165618592243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120451000661051108316245981 45169125247894165618592243)
  ·
    refine ⟨67753687871841248427888365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45169125247894165618592243 67753687871841248427888365)
    ·
      refine ⟨25407632951940468160458137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67753687871841248427888365 25407632951940468160458137)
      ·
        refine ⟨19055724713955351120343603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25407632951940468160458137 19055724713955351120343603)
        ·
          refine ⟨28583587070933026680515405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19055724713955351120343603 28583587070933026680515405)
          ·
            refine ⟨10718845151599885005193277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28583587070933026680515405 10718845151599885005193277)
            ·
              refine ⟨4019566931849956876947479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10718845151599885005193277 4019566931849956876947479)
              ·
                refine ⟨6029350397774935315421219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019566931849956876947479 6029350397774935315421219)
                ·
                  refine ⟨9044025596662402973131829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6029350397774935315421219 9044025596662402973131829)
                  ·
                    refine ⟨847877399687100278731109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9044025596662402973131829 847877399687100278731109)
                    ·
                      rfl

theorem cell23_4953706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_4953706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953706 prefixEnd_4953706 := by exact prefixLift 4953706
  have htrace : WordTrace (prefixWord ++ tailWord_4953706) baseStart_4953706 baseEnd_4953706 := by
    simpa [prefixWord, tailWord_4953706, baseEnd_4953706] using wordTrace_append hprefix tailTrace_4953706
  have hstable : (prefixWord ++ tailWord_4953706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953706).length < 2 ^ (prefixWord ++ tailWord_4953706).sum := by decide
  have hdescent : baseEnd_4953706 < baseStart_4953706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953729 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4953729 : Nat := 118140960795 + 4953729 * 2 ^ 59
def prefixEnd_4953729 : Nat := 4983230072969 + 3 ^ 40 * 4953729 * 2
def baseEnd_4953729 : Nat := 2543644009116354246205721

theorem tailTrace_4953729 : CollatzResearch.WordTrace tailWord_4953729 prefixEnd_4953729 2543644009116354246205721 := by
  unfold tailWord_4953729
  simp only [CollatzResearch.WordTrace]
  refine ⟨180677339870493337402456241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120451559913662224934970827 180677339870493337402456241)
  ·
    refine ⟨135508004902870003051842181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180677339870493337402456241 135508004902870003051842181)
    ·
      refine ⟨25407750919288125572220409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135508004902870003051842181 25407750919288125572220409)
      ·
        refine ⟨19055813189466094179165307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25407750919288125572220409 19055813189466094179165307)
        ·
          refine ⟨28583719784199141268747961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19055813189466094179165307 28583719784199141268747961)
          ·
            refine ⟨21437789838149355951560971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28583719784199141268747961 21437789838149355951560971)
            ·
              refine ⟨32156684757224033927341457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21437789838149355951560971 32156684757224033927341457)
              ·
                refine ⟨24117513567918025445506093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32156684757224033927341457 24117513567918025445506093)
                ·
                  refine ⟨9044067587969259542064785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24117513567918025445506093 9044067587969259542064785)
                  ·
                    refine ⟨6783050690976944656548589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9044067587969259542064785 6783050690976944656548589)
                    ·
                      refine ⟨2543644009116354246205721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783050690976944656548589 2543644009116354246205721)
                      ·
                        rfl

theorem cell23_4953729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4953729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953729 prefixEnd_4953729 := by exact prefixLift 4953729
  have htrace : WordTrace (prefixWord ++ tailWord_4953729) baseStart_4953729 baseEnd_4953729 := by
    simpa [prefixWord, tailWord_4953729, baseEnd_4953729] using wordTrace_append hprefix tailTrace_4953729
  have hstable : (prefixWord ++ tailWord_4953729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953729).length < 2 ^ (prefixWord ++ tailWord_4953729).sum := by decide
  have hdescent : baseEnd_4953729 < baseStart_4953729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953736 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 1, 6]
def baseStart_4953736 : Nat := 118140960795 + 4953736 * 2 ^ 59
def prefixEnd_4953736 : Nat := 4983230072969 + 3 ^ 40 * 4953736 * 2
def baseEnd_4953736 : Nat := 847882534493645239606063

theorem tailTrace_4953736 : CollatzResearch.WordTrace tailWord_4953736 prefixEnd_4953736 847882534493645239606063 := by
  unfold tailWord_4953736
  simp only [CollatzResearch.WordTrace]
  refine ⟨90338797590733988798980531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120451730120978651731974041 90338797590733988798980531)
  ·
    refine ⟨135508196386100983198470797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90338797590733988798980531 135508196386100983198470797)
    ·
      refine ⟨50815573644787868699426549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135508196386100983198470797 50815573644787868699426549)
      ·
        refine ⟨4763960029198862690571239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50815573644787868699426549 4763960029198862690571239)
        ·
          refine ⟨7145940043798294035856859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763960029198862690571239 7145940043798294035856859)
          ·
            refine ⟨10718910065697441053785289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7145940043798294035856859 10718910065697441053785289)
            ·
              refine ⟨8039182549273080790338967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10718910065697441053785289 8039182549273080790338967)
              ·
                refine ⟨12058773823909621185508451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8039182549273080790338967 12058773823909621185508451)
                ·
                  refine ⟨18088160735864431778262677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12058773823909621185508451 18088160735864431778262677)
                  ·
                    refine ⟨847882534493645239606063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18088160735864431778262677 847882534493645239606063)
                    ·
                      rfl

theorem cell23_4953736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_4953736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953736 prefixEnd_4953736 := by exact prefixLift 4953736
  have htrace : WordTrace (prefixWord ++ tailWord_4953736) baseStart_4953736 baseEnd_4953736 := by
    simpa [prefixWord, tailWord_4953736, baseEnd_4953736] using wordTrace_append hprefix tailTrace_4953736
  have hstable : (prefixWord ++ tailWord_4953736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953736).length < 2 ^ (prefixWord ++ tailWord_4953736).sum := by decide
  have hdescent : baseEnd_4953736 < baseStart_4953736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953760 : List Nat := [2, 1, 1, 4, 3, 2, 2, 3, 1, 2, 2]
def baseStart_4953760 : Nat := 118140960795 + 4953760 * 2 ^ 59
def prefixEnd_4953760 : Nat := 4983230072969 + 3 ^ 40 * 4953760 * 2
def baseEnd_4953760 : Nat := 2543659927016643624918079

theorem tailTrace_4953760 : CollatzResearch.WordTrace tailWord_4953760 prefixEnd_4953760 2543659927016643624918079 := by
  unfold tailWord_4953760
  simp only [CollatzResearch.WordTrace]
  refine ⟨90339235266690514848417367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120452313688920686464556489 90339235266690514848417367)
  ·
    refine ⟨135508852900035772272626051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90339235266690514848417367 135508852900035772272626051)
    ·
      refine ⟨203263279350053658408939077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135508852900035772272626051 203263279350053658408939077)
      ·
        refine ⟨38111864878135060951676077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203263279350053658408939077 38111864878135060951676077)
        ·
          refine ⟨14291949329300647856878529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38111864878135060951676077 14291949329300647856878529)
          ·
            refine ⟨10718961996975485892658897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14291949329300647856878529 10718961996975485892658897)
            ·
              refine ⟨8039221497731614419494173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10718961996975485892658897 8039221497731614419494173)
              ·
                refine ⟨3014708061649355407310315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8039221497731614419494173 3014708061649355407310315)
                ·
                  refine ⟨4522062092474033110965473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014708061649355407310315 4522062092474033110965473)
                  ·
                    refine ⟨3391546569355524833224105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4522062092474033110965473 3391546569355524833224105)
                    ·
                      refine ⟨2543659927016643624918079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391546569355524833224105 2543659927016643624918079)
                      ·
                        rfl

theorem cell23_4953760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_4953760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953760 prefixEnd_4953760 := by exact prefixLift 4953760
  have htrace : WordTrace (prefixWord ++ tailWord_4953760) baseStart_4953760 baseEnd_4953760 := by
    simpa [prefixWord, tailWord_4953760, baseEnd_4953760] using wordTrace_append hprefix tailTrace_4953760
  have hstable : (prefixWord ++ tailWord_4953760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953760).length < 2 ^ (prefixWord ++ tailWord_4953760).sum := by decide
  have hdescent : baseEnd_4953760 < baseStart_4953760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953776 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 2, 1, 3]
def baseStart_4953776 : Nat := 118140960795 + 4953776 * 2 ^ 59
def prefixEnd_4953776 : Nat := 4983230072969 + 3 ^ 40 * 4953776 * 2
def baseEnd_4953776 : Nat := 2543668142707115562318005

theorem tailTrace_4953776 : CollatzResearch.WordTrace tailWord_4953776 prefixEnd_4953776 2543668142707115562318005 := by
  unfold tailWord_4953776
  simp only [CollatzResearch.WordTrace]
  refine ⟨90339527050661532214708591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120452702734215376286278121 90339527050661532214708591)
  ·
    refine ⟨135509290575992298322062887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90339527050661532214708591 135509290575992298322062887)
    ·
      refine ⟨203263935863988447483094331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135509290575992298322062887 203263935863988447483094331)
      ·
        refine ⟨304895903795982671224641497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203263935863988447483094331 304895903795982671224641497)
        ·
          refine ⟨228671927846987003418481123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304895903795982671224641497 228671927846987003418481123)
          ·
            refine ⟨343007891770480505127721685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228671927846987003418481123 343007891770480505127721685)
            ·
              refine ⟨8039247463370636838930977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 343007891770480505127721685 8039247463370636838930977)
              ·
                refine ⟨6029435597527977629198233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8039247463370636838930977 6029435597527977629198233)
                ·
                  refine ⟨4522076698145983221898675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6029435597527977629198233 4522076698145983221898675)
                  ·
                    refine ⟨6783115047218974832848013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4522076698145983221898675 6783115047218974832848013)
                    ·
                      refine ⟨2543668142707115562318005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783115047218974832848013 2543668142707115562318005)
                      ·
                        rfl

theorem cell23_4953776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 1, 3].length) (baseStart_4953776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953776 prefixEnd_4953776 := by exact prefixLift 4953776
  have htrace : WordTrace (prefixWord ++ tailWord_4953776) baseStart_4953776 baseEnd_4953776 := by
    simpa [prefixWord, tailWord_4953776, baseEnd_4953776] using wordTrace_append hprefix tailTrace_4953776
  have hstable : (prefixWord ++ tailWord_4953776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953776).length < 2 ^ (prefixWord ++ tailWord_4953776).sum := by decide
  have hdescent : baseEnd_4953776 < baseStart_4953776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953792 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 2, 6]
def baseStart_4953792 : Nat := 118140960795 + 4953792 * 2 ^ 59
def prefixEnd_4953792 : Nat := 4983230072969 + 3 ^ 40 * 4953792 * 2
def baseEnd_4953792 : Nat := 847892119465862499905977

theorem tailTrace_4953792 : CollatzResearch.WordTrace tailWord_4953792 prefixEnd_4953792 847892119465862499905977 := by
  unfold tailWord_4953792
  simp only [CollatzResearch.WordTrace]
  refine ⟨90339818834632549580999815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120453091779510066107999753 90339818834632549580999815)
  ·
    refine ⟨135509728251948824371499723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90339818834632549580999815 135509728251948824371499723)
    ·
      refine ⟨203264592377923236557249585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135509728251948824371499723 203264592377923236557249585)
      ·
        refine ⟨152448444283442427417937189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203264592377923236557249585 152448444283442427417937189)
        ·
          refine ⟨28584083303145455140863223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152448444283442427417937189 28584083303145455140863223)
          ·
            refine ⟨42876124954718182711294835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28584083303145455140863223 42876124954718182711294835)
            ·
              refine ⟨64314187432077274066942253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42876124954718182711294835 64314187432077274066942253)
              ·
                refine ⟨24117820287028977775103345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64314187432077274066942253 24117820287028977775103345)
                ·
                  refine ⟨18088365215271733331327509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24117820287028977775103345 18088365215271733331327509)
                  ·
                    refine ⟨847892119465862499905977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18088365215271733331327509 847892119465862499905977)
                    ·
                      rfl

theorem cell23_4953792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_4953792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953792 prefixEnd_4953792 := by exact prefixLift 4953792
  have htrace : WordTrace (prefixWord ++ tailWord_4953792) baseStart_4953792 baseEnd_4953792 := by
    simpa [prefixWord, tailWord_4953792, baseEnd_4953792] using wordTrace_append hprefix tailTrace_4953792
  have hstable : (prefixWord ++ tailWord_4953792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953792).length < 2 ^ (prefixWord ++ tailWord_4953792).sum := by decide
  have hdescent : baseEnd_4953792 < baseStart_4953792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953816 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 6, 2, 2]
def baseStart_4953816 : Nat := 118140960795 + 4953816 * 2 ^ 59
def prefixEnd_4953816 : Nat := 4983230072969 + 3 ^ 40 * 4953816 * 2
def baseEnd_4953816 : Nat := 2543688681933295405817821

theorem tailTrace_4953816 : CollatzResearch.WordTrace tailWord_4953816 prefixEnd_4953816 2543688681933295405817821 := by
  unfold tailWord_4953816
  simp only [CollatzResearch.WordTrace]
  refine ⟨90340256510589075630436651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120453675347452100840582201 90340256510589075630436651)
  ·
    refine ⟨135510384765883613445654977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90340256510589075630436651 135510384765883613445654977)
    ·
      refine ⟨101632788574412710084241233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135510384765883613445654977 101632788574412710084241233)
      ·
        refine ⟨76224591430809532563180925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101632788574412710084241233 76224591430809532563180925)
        ·
          refine ⟨28584221786553574711192847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76224591430809532563180925 28584221786553574711192847)
          ·
            refine ⟨42876332679830362066789271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28584221786553574711192847 42876332679830362066789271)
            ·
              refine ⟨64314499019745543100183907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42876332679830362066789271 64314499019745543100183907)
              ·
                refine ⟨96471748529618314650275861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64314499019745543100183907 96471748529618314650275861)
                ·
                  refine ⟨4522113212325858499231681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96471748529618314650275861 4522113212325858499231681)
                  ·
                    refine ⟨3391584909244393874423761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4522113212325858499231681 3391584909244393874423761)
                    ·
                      refine ⟨2543688681933295405817821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391584909244393874423761 2543688681933295405817821)
                      ·
                        rfl

theorem cell23_4953816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_4953816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953816 prefixEnd_4953816 := by exact prefixLift 4953816
  have htrace : WordTrace (prefixWord ++ tailWord_4953816) baseStart_4953816 baseEnd_4953816 := by
    simpa [prefixWord, tailWord_4953816, baseEnd_4953816] using wordTrace_append hprefix tailTrace_4953816
  have hstable : (prefixWord ++ tailWord_4953816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953816).length < 2 ^ (prefixWord ++ tailWord_4953816).sum := by decide
  have hdescent : baseEnd_4953816 < baseStart_4953816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953844 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4953844 : Nat := 118140960795 + 4953844 * 2 ^ 59
def prefixEnd_4953844 : Nat := 4983230072969 + 3 ^ 40 * 4953844 * 2
def baseEnd_4953844 : Nat := 2543703059391621296267693

theorem tailTrace_4953844 : CollatzResearch.WordTrace tailWord_4953844 prefixEnd_4953844 2543703059391621296267693 := by
  unfold tailWord_4953844
  simp only [CollatzResearch.WordTrace]
  refine ⟨90340767132538356021446293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120454356176717808028595057 90340767132538356021446293)
  ·
    refine ⟨4234723459337735438505295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90340767132538356021446293 4234723459337735438505295)
    ·
      refine ⟨6352085189006603157757943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4234723459337735438505295 6352085189006603157757943)
      ·
        refine ⟨9528127783509904736636915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6352085189006603157757943 9528127783509904736636915)
        ·
          refine ⟨14292191675264857104955373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9528127783509904736636915 14292191675264857104955373)
          ·
            refine ⟨5359571878224321414358265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14292191675264857104955373 5359571878224321414358265)
            ·
              refine ⟨4019678908668241060768699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5359571878224321414358265 4019678908668241060768699)
              ·
                refine ⟨6029518363002361591153049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019678908668241060768699 6029518363002361591153049)
                ·
                  refine ⟨4522138772251771193364787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6029518363002361591153049 4522138772251771193364787)
                  ·
                    refine ⟨6783208158377656790047181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4522138772251771193364787 6783208158377656790047181)
                    ·
                      refine ⟨2543703059391621296267693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783208158377656790047181 2543703059391621296267693)
                      ·
                        rfl

theorem cell23_4953844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4953844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953844 prefixEnd_4953844 := by exact prefixLift 4953844
  have htrace : WordTrace (prefixWord ++ tailWord_4953844) baseStart_4953844 baseEnd_4953844 := by
    simpa [prefixWord, tailWord_4953844, baseEnd_4953844] using wordTrace_append hprefix tailTrace_4953844
  have hstable : (prefixWord ++ tailWord_4953844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953844).length < 2 ^ (prefixWord ++ tailWord_4953844).sum := by decide
  have hdescent : baseEnd_4953844 < baseStart_4953844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953879 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4953879 : Nat := 118140960795 + 4953879 * 2 ^ 59
def prefixEnd_4953879 : Nat := 4983230072969 + 3 ^ 40 * 4953879 * 2
def baseEnd_4953879 : Nat := 2543721031214528659330031

theorem tailTrace_4953879 : CollatzResearch.WordTrace tailWord_4953879 prefixEnd_4953879 2543721031214528659330031 := by
  unfold tailWord_4953879
  simp only [CollatzResearch.WordTrace]
  refine ⟨180682810819949913020416691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120455207213299942013611127 180682810819949913020416691)
  ·
    refine ⟨271024216229924869530625037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180682810819949913020416691 271024216229924869530625037)
    ·
      refine ⟨101634081086221826073984389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271024216229924869530625037 101634081086221826073984389)
      ·
        refine ⟨19056390203666592388872073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101634081086221826073984389 19056390203666592388872073)
        ·
          refine ⟨14292292652749944291654055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19056390203666592388872073 14292292652749944291654055)
          ·
            refine ⟨21438438979124916437481083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14292292652749944291654055 21438438979124916437481083)
            ·
              refine ⟨32157658468687374656221625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21438438979124916437481083 32157658468687374656221625)
              ·
                refine ⟨24118243851515530992166219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32157658468687374656221625 24118243851515530992166219)
                ·
                  refine ⟨36177365777273296488249329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24118243851515530992166219 36177365777273296488249329)
                  ·
                    refine ⟨27133024332954972366186997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36177365777273296488249329 27133024332954972366186997)
                    ·
                      refine ⟨2543721031214528659330031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27133024332954972366186997 2543721031214528659330031)
                      ·
                        rfl

theorem cell23_4953879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4953879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953879 prefixEnd_4953879 := by exact prefixLift 4953879
  have htrace : WordTrace (prefixWord ++ tailWord_4953879) baseStart_4953879 baseEnd_4953879 := by
    simpa [prefixWord, tailWord_4953879, baseEnd_4953879] using wordTrace_append hprefix tailTrace_4953879
  have hstable : (prefixWord ++ tailWord_4953879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953879).length < 2 ^ (prefixWord ++ tailWord_4953879).sum := by decide
  have hdescent : baseEnd_4953879 < baseStart_4953879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953906 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_4953906 : Nat := 118140960795 + 4953906 * 2 ^ 59
def prefixEnd_4953906 : Nat := 4983230072969 + 3 ^ 40 * 4953906 * 2
def baseEnd_4953906 : Nat := 2543734895192200053692407

theorem tailTrace_4953906 : CollatzResearch.WordTrace tailWord_4953906 prefixEnd_4953906 2543734895192200053692407 := by
  unfold tailWord_4953906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45170948897713024157912393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120455863727234731087766381 45170948897713024157912393)
  ·
    refine ⟨33878211673284768118434295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45170948897713024157912393 33878211673284768118434295)
    ·
      refine ⟨50817317509927152177651443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33878211673284768118434295 50817317509927152177651443)
      ·
        refine ⟨76225976264890728266477165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50817317509927152177651443 76225976264890728266477165)
        ·
          refine ⟨28584741099334023099928937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76225976264890728266477165 28584741099334023099928937)
          ·
            refine ⟨21438555824500517324946703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28584741099334023099928937 21438555824500517324946703)
            ·
              refine ⟨32157833736750775987420055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21438555824500517324946703 32157833736750775987420055)
              ·
                refine ⟨48236750605126163981130083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32157833736750775987420055 48236750605126163981130083)
                ·
                  refine ⟨72355125907689245971695125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48236750605126163981130083 72355125907689245971695125)
                  ·
                    refine ⟨3391646526922933404923209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72355125907689245971695125 3391646526922933404923209)
                    ·
                      refine ⟨2543734895192200053692407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391646526922933404923209 2543734895192200053692407)
                      ·
                        rfl

theorem cell23_4953906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_4953906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953906 prefixEnd_4953906 := by exact prefixLift 4953906
  have htrace : WordTrace (prefixWord ++ tailWord_4953906) baseStart_4953906 baseEnd_4953906 := by
    simpa [prefixWord, tailWord_4953906, baseEnd_4953906] using wordTrace_append hprefix tailTrace_4953906
  have hstable : (prefixWord ++ tailWord_4953906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953906).length < 2 ^ (prefixWord ++ tailWord_4953906).sum := by decide
  have hdescent : baseEnd_4953906 < baseStart_4953906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953973 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_4953973 : Nat := 118140960795 + 4953973 * 2 ^ 59
def prefixEnd_4953973 : Nat := 4983230072969 + 3 ^ 40 * 4953973 * 2
def baseEnd_4953973 : Nat := 2543769298396051291554599

theorem tailTrace_4953973 : CollatzResearch.WordTrace tailWord_4953973 prefixEnd_4953973 2543769298396051291554599 := by
  unfold tailWord_4953973
  simp only [CollatzResearch.WordTrace]
  refine ⟨180686239281609367074338573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120457492854406244716225715 180686239281609367074338573)
  ·
    refine ⟨67757339730603512652876965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180686239281609367074338573 67757339730603512652876965)
    ·
      refine ⟨12704501199488158622414431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67757339730603512652876965 12704501199488158622414431)
      ·
        refine ⟨19056751799232237933621647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12704501199488158622414431 19056751799232237933621647)
        ·
          refine ⟨28585127698848356900432471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19056751799232237933621647 28585127698848356900432471)
          ·
            refine ⟨42877691548272535350648707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28585127698848356900432471 42877691548272535350648707)
            ·
              refine ⟨64316537322408803025973061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42877691548272535350648707 64316537322408803025973061)
              ·
                refine ⟨12059350747951650567369949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64316537322408803025973061 12059350747951650567369949)
                ·
                  refine ⟨4522256530481868962763731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12059350747951650567369949 4522256530481868962763731)
                  ·
                    refine ⟨6783384795722803444145597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4522256530481868962763731 6783384795722803444145597)
                    ·
                      refine ⟨2543769298396051291554599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783384795722803444145597 2543769298396051291554599)
                      ·
                        rfl

theorem cell23_4953973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_4953973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953973 prefixEnd_4953973 := by exact prefixLift 4953973
  have htrace : WordTrace (prefixWord ++ tailWord_4953973) baseStart_4953973 baseEnd_4953973 := by
    simpa [prefixWord, tailWord_4953973, baseEnd_4953973] using wordTrace_append hprefix tailTrace_4953973
  have hstable : (prefixWord ++ tailWord_4953973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953973).length < 2 ^ (prefixWord ++ tailWord_4953973).sum := by decide
  have hdescent : baseEnd_4953973 < baseStart_4953973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953989 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_4953989 : Nat := 118140960795 + 4953989 * 2 ^ 59
def prefixEnd_4953989 : Nat := 4983230072969 + 3 ^ 40 * 4953989 * 2
def baseEnd_4953989 : Nat := 847925838028841076318175

theorem tailTrace_4953989 : CollatzResearch.WordTrace tailWord_4953989 prefixEnd_4953989 847925838028841076318175 := by
  unfold tailWord_4953989
  simp only [CollatzResearch.WordTrace]
  refine ⟨180686822849551401806921021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120457881899700934537947347 180686822849551401806921021)
  ·
    refine ⟨67757558568581775677595383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180686822849551401806921021 67757558568581775677595383)
    ·
      refine ⟨101636337852872663516393075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67757558568581775677595383 101636337852872663516393075)
      ·
        refine ⟨152454506779308995274589613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101636337852872663516393075 152454506779308995274589613)
        ·
          refine ⟨57170440042240873227971105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152454506779308995274589613 57170440042240873227971105)
          ·
            refine ⟨42877830031680654920978329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57170440042240873227971105 42877830031680654920978329)
            ·
              refine ⟨32158372523760491190733747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42877830031680654920978329 32158372523760491190733747)
              ·
                refine ⟨48237558785640736786100621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32158372523760491190733747 48237558785640736786100621)
                ·
                  refine ⟨18089084544615276294787733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48237558785640736786100621 18089084544615276294787733)
                  ·
                    refine ⟨847925838028841076318175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18089084544615276294787733 847925838028841076318175)
                    ·
                      rfl

theorem cell23_4953989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_4953989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953989 prefixEnd_4953989 := by exact prefixLift 4953989
  have htrace : WordTrace (prefixWord ++ tailWord_4953989) baseStart_4953989 baseEnd_4953989 := by
    simpa [prefixWord, tailWord_4953989, baseEnd_4953989] using wordTrace_append hprefix tailTrace_4953989
  have hstable : (prefixWord ++ tailWord_4953989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953989).length < 2 ^ (prefixWord ++ tailWord_4953989).sum := by decide
  have hdescent : baseEnd_4953989 < baseStart_4953989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4953999 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 3]
def baseStart_4953999 : Nat := 118140960795 + 4953999 * 2 ^ 59
def prefixEnd_4953999 : Nat := 4983230072969 + 3 ^ 40 * 4953999 * 2
def baseEnd_4953999 : Nat := 2543782648893068189829479

theorem tailTrace_4953999 : CollatzResearch.WordTrace tailWord_4953999 prefixEnd_4953999 2543782648893068189829479 := by
  unfold tailWord_4953999
  simp only [CollatzResearch.WordTrace]
  refine ⟨180687187579515173514785051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120458125053010115676523367 180687187579515173514785051)
  ·
    refine ⟨271030781369272760272177577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180687187579515173514785051 271030781369272760272177577)
    ·
      refine ⟨203273086026954570204133183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271030781369272760272177577 203273086026954570204133183)
      ·
        refine ⟨304909629040431855306199775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203273086026954570204133183 304909629040431855306199775)
        ·
          refine ⟨457364443560647782959299663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304909629040431855306199775 457364443560647782959299663)
          ·
            refine ⟨686046665340971674438949495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457364443560647782959299663 686046665340971674438949495)
            ·
              refine ⟨1029069998011457511658424243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686046665340971674438949495 1029069998011457511658424243)
              ·
                refine ⟨1543604997017186267487636365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029069998011457511658424243 1543604997017186267487636365)
                ·
                  refine ⟨578851873881444850307863637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1543604997017186267487636365 578851873881444850307863637)
                  ·
                    refine ⟨6783420397048181839545277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 578851873881444850307863637 6783420397048181839545277)
                    ·
                      refine ⟨2543782648893068189829479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783420397048181839545277 2543782648893068189829479)
                      ·
                        rfl

theorem cell23_4953999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_4953999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4953999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4953999 prefixEnd_4953999 := by exact prefixLift 4953999
  have htrace : WordTrace (prefixWord ++ tailWord_4953999) baseStart_4953999 baseEnd_4953999 := by
    simpa [prefixWord, tailWord_4953999, baseEnd_4953999] using wordTrace_append hprefix tailTrace_4953999
  have hstable : (prefixWord ++ tailWord_4953999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4953999).length < 2 ^ (prefixWord ++ tailWord_4953999).sum := by decide
  have hdescent : baseEnd_4953999 < baseStart_4953999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4953999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954007 : List Nat := [1, 1, 3, 3, 1, 4, 3, 2, 1, 1, 3]
def baseStart_4954007 : Nat := 118140960795 + 4954007 * 2 ^ 59
def prefixEnd_4954007 : Nat := 4983230072969 + 3 ^ 40 * 4954007 * 2
def baseEnd_4954007 : Nat := 2543786756738304158529443

theorem tailTrace_4954007 : CollatzResearch.WordTrace tailWord_4954007 prefixEnd_4954007 2543786756738304158529443 := by
  unfold tailWord_4954007
  simp only [CollatzResearch.WordTrace]
  refine ⟨180687479363486190881076275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120458319575657460587384183 180687479363486190881076275)
  ·
    refine ⟨271031219045229286321614413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180687479363486190881076275 271031219045229286321614413)
    ·
      refine ⟨101636707141960982370605405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271031219045229286321614413 101636707141960982370605405)
      ·
        refine ⟨38113765178235368388977027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101636707141960982370605405 38113765178235368388977027)
        ·
          refine ⟨57170647767353052583465541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38113765178235368388977027 57170647767353052583465541)
          ·
            refine ⟨10719496456378697359399789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57170647767353052583465541 10719496456378697359399789)
            ·
              refine ⟨4019811171142011509774921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10719496456378697359399789 4019811171142011509774921)
              ·
                refine ⟨3014858378356508632331191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4019811171142011509774921 3014858378356508632331191)
                ·
                  refine ⟨4522287567534762948496787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014858378356508632331191 4522287567534762948496787)
                  ·
                    refine ⟨6783431351302144422745181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4522287567534762948496787 6783431351302144422745181)
                    ·
                      refine ⟨2543786756738304158529443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783431351302144422745181 2543786756738304158529443)
                      ·
                        rfl

theorem cell23_4954007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_4954007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954007 prefixEnd_4954007 := by exact prefixLift 4954007
  have htrace : WordTrace (prefixWord ++ tailWord_4954007) baseStart_4954007 baseEnd_4954007 := by
    simpa [prefixWord, tailWord_4954007, baseEnd_4954007] using wordTrace_append hprefix tailTrace_4954007
  have hstable : (prefixWord ++ tailWord_4954007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954007).length < 2 ^ (prefixWord ++ tailWord_4954007).sum := by decide
  have hdescent : baseEnd_4954007 < baseStart_4954007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954009 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_4954009 : Nat := 118140960795 + 4954009 * 2 ^ 59
def prefixEnd_4954009 : Nat := 4983230072969 + 3 ^ 40 * 4954009 * 2
def baseEnd_4954009 : Nat := 2543787783699613150704433

theorem tailTrace_4954009 : CollatzResearch.WordTrace tailWord_4954009 prefixEnd_4954009 2543787783699613150704433 := by
  unfold tailWord_4954009
  simp only [CollatzResearch.WordTrace]
  refine ⟨180687552309478945222649081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120458368206319296815099387 180687552309478945222649081)
  ·
    refine ⟨135515664232109208916986811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180687552309478945222649081 135515664232109208916986811)
    ·
      refine ⟨203273496348163813375480217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135515664232109208916986811 203273496348163813375480217)
      ·
        refine ⟨152455122261122860031610163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203273496348163813375480217 152455122261122860031610163)
        ·
          refine ⟨228682683391684290047415245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152455122261122860031610163 228682683391684290047415245)
          ·
            refine ⟨85756006271881608767780717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228682683391684290047415245 85756006271881608767780717)
            ·
              refine ⟨32158502351955603287917769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85756006271881608767780717 32158502351955603287917769)
              ·
                refine ⟨24118876763966702465938327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32158502351955603287917769 24118876763966702465938327)
                ·
                  refine ⟨36178315145950053698907491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24118876763966702465938327 36178315145950053698907491)
                  ·
                    refine ⟨54267472718925080548361237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36178315145950053698907491 54267472718925080548361237)
                    ·
                      refine ⟨2543787783699613150704433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54267472718925080548361237 2543787783699613150704433)
                      ·
                        rfl

theorem cell23_4954009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_4954009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954009 prefixEnd_4954009 := by exact prefixLift 4954009
  have htrace : WordTrace (prefixWord ++ tailWord_4954009) baseStart_4954009 baseEnd_4954009 := by
    simpa [prefixWord, tailWord_4954009, baseEnd_4954009] using wordTrace_append hprefix tailTrace_4954009
  have hstable : (prefixWord ++ tailWord_4954009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954009).length < 2 ^ (prefixWord ++ tailWord_4954009).sum := by decide
  have hdescent : baseEnd_4954009 < baseStart_4954009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954014 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_4954014 : Nat := 118140960795 + 4954014 * 2 ^ 59
def prefixEnd_4954014 : Nat := 4983230072969 + 3 ^ 40 * 4954014 * 2
def baseEnd_4954014 : Nat := 282643372344765070126879

theorem tailTrace_4954014 : CollatzResearch.WordTrace tailWord_4954014 prefixEnd_4954014 282643372344765070126879 := by
  unfold tailWord_4954014
  simp only [CollatzResearch.WordTrace]
  refine ⟨22585966834307603884572637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120458489782973887384387397 22585966834307603884572637)
  ·
    refine ⟨8469737562865351456714739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22585966834307603884572637 8469737562865351456714739)
    ·
      refine ⟨12704606344298027185072109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8469737562865351456714739 12704606344298027185072109)
      ·
        refine ⟨4764227379111760194402041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12704606344298027185072109 4764227379111760194402041)
        ·
          refine ⟨3573170534333820145801531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764227379111760194402041 3573170534333820145801531)
          ·
            refine ⟨5359755801500730218702297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573170534333820145801531 5359755801500730218702297)
            ·
              refine ⟨4019816851125547664026723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5359755801500730218702297 4019816851125547664026723)
              ·
                refine ⟨6029725276688321496040085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019816851125547664026723 6029725276688321496040085)
                ·
                  refine ⟨282643372344765070126879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6029725276688321496040085 282643372344765070126879)
                  ·
                    rfl

theorem cell23_4954014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_4954014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954014 prefixEnd_4954014 := by exact prefixLift 4954014
  have htrace : WordTrace (prefixWord ++ tailWord_4954014) baseStart_4954014 baseEnd_4954014 := by
    simpa [prefixWord, tailWord_4954014, baseEnd_4954014] using wordTrace_append hprefix tailTrace_4954014
  have hstable : (prefixWord ++ tailWord_4954014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954014).length < 2 ^ (prefixWord ++ tailWord_4954014).sum := by decide
  have hdescent : baseEnd_4954014 < baseStart_4954014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954016 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3]
def baseStart_4954016 : Nat := 118140960795 + 4954016 * 2 ^ 59
def prefixEnd_4954016 : Nat := 4983230072969 + 3 ^ 40 * 4954016 * 2
def baseEnd_4954016 : Nat := 2543791378064194623316901

theorem tailTrace_4954016 : CollatzResearch.WordTrace tailWord_4954016 prefixEnd_4954016 2543791378064194623316901 := by
  unfold tailWord_4954016
  simp only [CollatzResearch.WordTrace]
  refine ⟨90343903810226792709076951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120458538413635723612102601 90343903810226792709076951)
  ·
    refine ⟨135515855715340189063615427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90343903810226792709076951 135515855715340189063615427)
    ·
      refine ⟨203273783573010283595423141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135515855715340189063615427 203273783573010283595423141)
      ·
        refine ⟨38113834419939428174141839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203273783573010283595423141 38113834419939428174141839)
        ·
          refine ⟨57170751629909142261212759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38113834419939428174141839 57170751629909142261212759)
          ·
            refine ⟨85756127444863713391819139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57170751629909142261212759 85756127444863713391819139)
            ·
              refine ⟨128634191167295570087728709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85756127444863713391819139 128634191167295570087728709)
              ·
                refine ⟨24118910843867919391449133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128634191167295570087728709 24118910843867919391449133)
                ·
                  refine ⟨9044591566450469771793425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24118910843867919391449133 9044591566450469771793425)
                  ·
                    refine ⟨6783443674837852328845069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9044591566450469771793425 6783443674837852328845069)
                    ·
                      refine ⟨2543791378064194623316901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783443674837852328845069 2543791378064194623316901)
                      ·
                        rfl

theorem cell23_4954016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_4954016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954016 prefixEnd_4954016 := by exact prefixLift 4954016
  have htrace : WordTrace (prefixWord ++ tailWord_4954016) baseStart_4954016 baseEnd_4954016 := by
    simpa [prefixWord, tailWord_4954016, baseEnd_4954016] using wordTrace_append hprefix tailTrace_4954016
  have hstable : (prefixWord ++ tailWord_4954016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954016).length < 2 ^ (prefixWord ++ tailWord_4954016).sum := by decide
  have hdescent : baseEnd_4954016 < baseStart_4954016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954033 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_4954033 : Nat := 118140960795 + 4954033 * 2 ^ 59
def prefixEnd_4954033 : Nat := 4983230072969 + 3 ^ 40 * 4954033 * 2
def baseEnd_4954033 : Nat := 2543800107235321056804323

theorem tailTrace_4954033 : CollatzResearch.WordTrace tailWord_4954033 prefixEnd_4954033 2543800107235321056804323 := by
  unfold tailWord_4954033
  simp only [CollatzResearch.WordTrace]
  refine ⟨180688427661391997321522753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120458951774261331547681835 180688427661391997321522753)
  ·
    refine ⟨135516320746043997991142065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180688427661391997321522753 135516320746043997991142065)
    ·
      refine ⟨101637240559532998493356549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135516320746043997991142065 101637240559532998493356549)
      ·
        refine ⟨19056982604912437217504353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101637240559532998493356549 19056982604912437217504353)
        ·
          refine ⟨14292736953684327913128265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19056982604912437217504353 14292736953684327913128265)
          ·
            refine ⟨10719552715263245934846199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14292736953684327913128265 10719552715263245934846199)
            ·
              refine ⟨16079329072894868902269299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10719552715263245934846199 16079329072894868902269299)
              ·
                refine ⟨24118993609342303353403949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16079329072894868902269299 24118993609342303353403949)
                ·
                  refine ⟨9044622603503363757526481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24118993609342303353403949 9044622603503363757526481)
                  ·
                    refine ⟨6783466952627522818144861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9044622603503363757526481 6783466952627522818144861)
                    ·
                      refine ⟨2543800107235321056804323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783466952627522818144861 2543800107235321056804323)
                      ·
                        rfl

theorem cell23_4954033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_4954033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954033 prefixEnd_4954033 := by exact prefixLift 4954033
  have htrace : WordTrace (prefixWord ++ tailWord_4954033) baseStart_4954033 baseEnd_4954033 := by
    simpa [prefixWord, tailWord_4954033, baseEnd_4954033] using wordTrace_append hprefix tailTrace_4954033
  have hstable : (prefixWord ++ tailWord_4954033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954033).length < 2 ^ (prefixWord ++ tailWord_4954033).sum := by decide
  have hdescent : baseEnd_4954033 < baseStart_4954033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954070 : List Nat := [5, 2, 1, 1, 3, 2, 1, 8]
def baseStart_4954070 : Nat := 118140960795 + 4954070 * 2 ^ 59
def prefixEnd_4954070 : Nat := 4983230072969 + 3 ^ 40 * 4954070 * 2
def baseEnd_4954070 : Nat := 94215522445168052297839

theorem tailTrace_4954070 : CollatzResearch.WordTrace tailWord_4954070 prefixEnd_4954070 94215522445168052297839 := by
  unfold tailWord_4954070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11293111072641122040038729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120459851441505301760413109 11293111072641122040038729)
  ·
    refine ⟨8469833304480841530029047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11293111072641122040038729 8469833304480841530029047)
    ·
      refine ⟨12704749956721262295043571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8469833304480841530029047 12704749956721262295043571)
      ·
        refine ⟨19057124935081893442565357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12704749956721262295043571 19057124935081893442565357)
        ·
          refine ⟨7146421850655710040962009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19057124935081893442565357 7146421850655710040962009)
          ·
            refine ⟨5359816387991782530721507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7146421850655710040962009 5359816387991782530721507)
            ·
              refine ⟨8039724581987673796082261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5359816387991782530721507 8039724581987673796082261)
              ·
                refine ⟨94215522445168052297839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8039724581987673796082261 94215522445168052297839)
                ·
                  rfl

theorem cell23_4954070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_4954070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954070 prefixEnd_4954070 := by exact prefixLift 4954070
  have htrace : WordTrace (prefixWord ++ tailWord_4954070) baseStart_4954070 baseEnd_4954070 := by
    simpa [prefixWord, tailWord_4954070, baseEnd_4954070] using wordTrace_append hprefix tailTrace_4954070
  have hstable : (prefixWord ++ tailWord_4954070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954070).length < 2 ^ (prefixWord ++ tailWord_4954070).sum := by decide
  have hdescent : baseEnd_4954070 < baseStart_4954070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954090 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_4954090 : Nat := 118140960795 + 4954090 * 2 ^ 59
def prefixEnd_4954090 : Nat := 4983230072969 + 3 ^ 40 * 4954090 * 2
def baseEnd_4954090 : Nat := 2543829375632627333791561

theorem tailTrace_4954090 : CollatzResearch.WordTrace tailWord_4954090 prefixEnd_4954090 2543829375632627333791561 := by
  unfold tailWord_4954090
  simp only [CollatzResearch.WordTrace]
  refine ⟨45172626655546374014086931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120460337748123664037565149 45172626655546374014086931)
  ·
    refine ⟨67758939983319561021130397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45172626655546374014086931 67758939983319561021130397)
    ·
      refine ⟨25409602493744835382923899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67758939983319561021130397 25409602493744835382923899)
      ·
        refine ⟨38114403740617253074385849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25409602493744835382923899 38114403740617253074385849)
        ·
          refine ⟨28585802805462939805789387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38114403740617253074385849 28585802805462939805789387)
          ·
            refine ⟨42878704208194409708684081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28585802805462939805789387 42878704208194409708684081)
            ·
              refine ⟨32159028156145807281513061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42878704208194409708684081 32159028156145807281513061)
              ·
                refine ⟨6029817779277338865283699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32159028156145807281513061 6029817779277338865283699)
                ·
                  refine ⟨9044726668916008297925549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6029817779277338865283699 9044726668916008297925549)
                  ·
                    refine ⟨3391772500843503111722081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9044726668916008297925549 3391772500843503111722081)
                    ·
                      refine ⟨2543829375632627333791561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391772500843503111722081 2543829375632627333791561)
                      ·
                        rfl

theorem cell23_4954090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_4954090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954090 prefixEnd_4954090 := by exact prefixLift 4954090
  have htrace : WordTrace (prefixWord ++ tailWord_4954090) baseStart_4954090 baseEnd_4954090 := by
    simpa [prefixWord, tailWord_4954090, baseEnd_4954090] using wordTrace_append hprefix tailTrace_4954090
  have hstable : (prefixWord ++ tailWord_4954090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954090).length < 2 ^ (prefixWord ++ tailWord_4954090).sum := by decide
  have hdescent : baseEnd_4954090 < baseStart_4954090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954120 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_4954120 : Nat := 118140960795 + 4954120 * 2 ^ 59
def prefixEnd_4954120 : Nat := 4983230072969 + 3 ^ 40 * 4954120 * 2
def baseEnd_4954120 : Nat := 2543844780052262216416423

theorem tailTrace_4954120 : CollatzResearch.WordTrace tailWord_4954120 prefixEnd_4954120 2543844780052262216416423 := by
  unfold tailWord_4954120
  simp only [CollatzResearch.WordTrace]
  refine ⟨90345800406038405589969907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120461067208051207453293209 90345800406038405589969907)
  ·
    refine ⟨135518700609057608384954861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90345800406038405589969907 135518700609057608384954861)
    ·
      refine ⟨50819512728396603144358073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135518700609057608384954861 50819512728396603144358073)
      ·
        refine ⟨38114634546297452358268555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50819512728396603144358073 38114634546297452358268555)
        ·
          refine ⟨57171951819446178537402833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38114634546297452358268555 57171951819446178537402833)
          ·
            refine ⟨42878963864584633903052125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57171951819446178537402833 42878963864584633903052125)
            ·
              refine ⟨16079611449219237713644547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42878963864584633903052125 16079611449219237713644547)
              ·
                refine ⟨24119417173828856570466821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16079611449219237713644547 24119417173828856570466821)
                ·
                  refine ⟨4522390720092910606962529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24119417173828856570466821 4522390720092910606962529)
                  ·
                    refine ⟨3391793040069682955221897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4522390720092910606962529 3391793040069682955221897)
                    ·
                      refine ⟨2543844780052262216416423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391793040069682955221897 2543844780052262216416423)
                      ·
                        rfl

theorem cell23_4954120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_4954120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954120 prefixEnd_4954120 := by exact prefixLift 4954120
  have htrace : WordTrace (prefixWord ++ tailWord_4954120) baseStart_4954120 baseEnd_4954120 := by
    simpa [prefixWord, tailWord_4954120, baseEnd_4954120] using wordTrace_append hprefix tailTrace_4954120
  have hstable : (prefixWord ++ tailWord_4954120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954120).length < 2 ^ (prefixWord ++ tailWord_4954120).sum := by decide
  have hdescent : baseEnd_4954120 < baseStart_4954120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954160 : List Nat := [2, 1, 1, 1, 2, 7, 1, 3, 5]
def baseStart_4954160 : Nat := 118140960795 + 4954160 * 2 ^ 59
def prefixEnd_4954160 : Nat := 4983230072969 + 3 ^ 40 * 4954160 * 2
def baseEnd_4954160 : Nat := 282651702142049117768471

theorem tailTrace_4954160 : CollatzResearch.WordTrace tailWord_4954160 prefixEnd_4954160 282651702142049117768471 := by
  unfold tailWord_4954160
  simp only [CollatzResearch.WordTrace]
  refine ⟨90346529865965949005697967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120462039821287932007597289 90346529865965949005697967)
  ·
    refine ⟨135519794798948923508546951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90346529865965949005697967 135519794798948923508546951)
    ·
      refine ⟨203279692198423385262820427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135519794798948923508546951 203279692198423385262820427)
      ·
        refine ⟨304919538297635077894230641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203279692198423385262820427 304919538297635077894230641)
        ·
          refine ⟨228689653723226308420672981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304919538297635077894230641 228689653723226308420672981)
          ·
            refine ⟨5359913759138116603609523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 228689653723226308420672981 5359913759138116603609523)
            ·
              refine ⟨8039870638707174905414285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5359913759138116603609523 8039870638707174905414285)
              ·
                refine ⟨3014951489515190589530357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8039870638707174905414285 3014951489515190589530357)
                ·
                  refine ⟨282651702142049117768471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3014951489515190589530357 282651702142049117768471)
                  ·
                    rfl

theorem cell23_4954160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 5].length) (baseStart_4954160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954160 prefixEnd_4954160 := by exact prefixLift 4954160
  have htrace : WordTrace (prefixWord ++ tailWord_4954160) baseStart_4954160 baseEnd_4954160 := by
    simpa [prefixWord, tailWord_4954160, baseEnd_4954160] using wordTrace_append hprefix tailTrace_4954160
  have hstable : (prefixWord ++ tailWord_4954160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954160).length < 2 ^ (prefixWord ++ tailWord_4954160).sum := by decide
  have hdescent : baseEnd_4954160 < baseStart_4954160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954173 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_4954173 : Nat := 118140960795 + 4954173 * 2 ^ 59
def prefixEnd_4954173 : Nat := 4983230072969 + 3 ^ 40 * 4954173 * 2
def baseEnd_4954173 : Nat := 847957331508983503017893

theorem tailTrace_4954173 : CollatzResearch.WordTrace tailWord_4954173 prefixEnd_4954173 847957331508983503017893 := by
  unfold tailWord_4954173
  simp only [CollatzResearch.WordTrace]
  refine ⟨180693533880884801231619173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120462355920589867487746115 180693533880884801231619173)
  ·
    refine ⟨33880037602665900230928595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180693533880884801231619173 33880037602665900230928595)
    ·
      refine ⟨50820056403998850346392893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33880037602665900230928595 50820056403998850346392893)
      ·
        refine ⟨19057521151499568879897335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50820056403998850346392893 19057521151499568879897335)
        ·
          refine ⟨28586281727249353319846003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19057521151499568879897335 28586281727249353319846003)
          ·
            refine ⟨42879422590874029979769005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28586281727249353319846003 42879422590874029979769005)
            ·
              refine ⟨16079783471577761242413377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42879422590874029979769005 16079783471577761242413377)
              ·
                refine ⟨12059837603683320931810033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16079783471577761242413377 12059837603683320931810033)
                ·
                  refine ⟨9044878202762490698857525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12059837603683320931810033 9044878202762490698857525)
                  ·
                    refine ⟨847957331508983503017893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9044878202762490698857525 847957331508983503017893)
                    ·
                      rfl

theorem cell23_4954173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_4954173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954173 prefixEnd_4954173 := by exact prefixLift 4954173
  have htrace : WordTrace (prefixWord ++ tailWord_4954173) baseStart_4954173 baseEnd_4954173 := by
    simpa [prefixWord, tailWord_4954173, baseEnd_4954173] using wordTrace_append hprefix tailTrace_4954173
  have hstable : (prefixWord ++ tailWord_4954173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954173).length < 2 ^ (prefixWord ++ tailWord_4954173).sum := by decide
  have hdescent : baseEnd_4954173 < baseStart_4954173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954177 : List Nat := [1, 2, 5, 1, 2, 2, 3, 2, 5]
def baseStart_4954177 : Nat := 118140960795 + 4954177 * 2 ^ 59
def prefixEnd_4954177 : Nat := 4983230072969 + 3 ^ 40 * 4954177 * 2
def baseEnd_4954177 : Nat := 282652672049952054822629

theorem tailTrace_4954177 : CollatzResearch.WordTrace tailWord_4954177 prefixEnd_4954177 282652672049952054822629 := by
  unfold tailWord_4954177
  simp only [CollatzResearch.WordTrace]
  refine ⟨180693679772870309914764785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120462453181913539943176523 180693679772870309914764785)
  ·
    refine ⟨135520259829652732436073589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180693679772870309914764785 135520259829652732436073589)
    ·
      refine ⟨12705024359029943665881899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135520259829652732436073589 12705024359029943665881899)
      ·
        refine ⟨19057536538544915498822849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12705024359029943665881899 19057536538544915498822849)
        ·
          refine ⟨14293152403908686624117137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19057536538544915498822849 14293152403908686624117137)
          ·
            refine ⟨10719864302931514968087853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14293152403908686624117137 10719864302931514968087853)
            ·
              refine ⟨4019949113599318113032945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10719864302931514968087853 4019949113599318113032945)
              ·
                refine ⟨3014961835199488584774709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4019949113599318113032945 3014961835199488584774709)
                ·
                  refine ⟨282652672049952054822629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3014961835199488584774709 282652672049952054822629)
                  ·
                    rfl

theorem cell23_4954177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 5].length) (baseStart_4954177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954177 prefixEnd_4954177 := by exact prefixLift 4954177
  have htrace : WordTrace (prefixWord ++ tailWord_4954177) baseStart_4954177 baseEnd_4954177 := by
    simpa [prefixWord, tailWord_4954177, baseEnd_4954177] using wordTrace_append hprefix tailTrace_4954177
  have hstable : (prefixWord ++ tailWord_4954177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954177).length < 2 ^ (prefixWord ++ tailWord_4954177).sum := by decide
  have hdescent : baseEnd_4954177 < baseStart_4954177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954193 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 1, 6, 2]
def baseStart_4954193 : Nat := 118140960795 + 4954193 * 2 ^ 59
def prefixEnd_4954193 : Nat := 4983230072969 + 3 ^ 40 * 4954193 * 2
def baseEnd_4954193 : Nat := 2543882264140040430803587

theorem tailTrace_4954193 : CollatzResearch.WordTrace tailWord_4954193 prefixEnd_4954193 2543882264140040430803587 := by
  unfold tailWord_4954193
  simp only [CollatzResearch.WordTrace]
  refine ⟨180694263340812344647347233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120462842227208229764898155 180694263340812344647347233)
  ·
    refine ⟨135520697505609258485510425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180694263340812344647347233 135520697505609258485510425)
    ·
      refine ⟨101640523129206943864132819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135520697505609258485510425 101640523129206943864132819)
      ·
        refine ⟨152460784693810415796199229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101640523129206943864132819 152460784693810415796199229)
        ·
          refine ⟨57172794260178905923574711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152460784693810415796199229 57172794260178905923574711)
          ·
            refine ⟨85759191390268358885362067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57172794260178905923574711 85759191390268358885362067)
            ·
              refine ⟨128638787085402538328043101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85759191390268358885362067 128638787085402538328043101)
              ·
                refine ⟨48239545157025951873016163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128638787085402538328043101 48239545157025951873016163)
                ·
                  refine ⟨72359317735538927809524245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48239545157025951873016163 72359317735538927809524245)
                  ·
                    refine ⟨3391843018853387241071449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72359317735538927809524245 3391843018853387241071449)
                    ·
                      refine ⟨2543882264140040430803587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391843018853387241071449 2543882264140040430803587)
                      ·
                        rfl

theorem cell23_4954193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_4954193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954193 prefixEnd_4954193 := by exact prefixLift 4954193
  have htrace : WordTrace (prefixWord ++ tailWord_4954193) baseStart_4954193 baseEnd_4954193 := by
    simpa [prefixWord, tailWord_4954193, baseEnd_4954193] using wordTrace_append hprefix tailTrace_4954193
  have hstable : (prefixWord ++ tailWord_4954193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954193).length < 2 ^ (prefixWord ++ tailWord_4954193).sum := by decide
  have hdescent : baseEnd_4954193 < baseStart_4954193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954233 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 6]
def baseStart_4954233 : Nat := 118140960795 + 4954233 * 2 ^ 59
def prefixEnd_4954233 : Nat := 4983230072969 + 3 ^ 40 * 4954233 * 2
def baseEnd_4954233 : Nat := 282655867040691141589267

theorem tailTrace_4954233 : CollatzResearch.WordTrace tailWord_4954233 prefixEnd_4954233 282655867040691141589267 := by
  unfold tailWord_4954233
  simp only [CollatzResearch.WordTrace]
  refine ⟨180695722260667431478803353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120463814840444954319202235 180695722260667431478803353)
  ·
    refine ⟨135521791695500573609102515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180695722260667431478803353 135521791695500573609102515)
    ·
      refine ⟨203282687543250860413653773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135521791695500573609102515 203282687543250860413653773)
      ·
        refine ⟨76231007828719072655120165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203282687543250860413653773 76231007828719072655120165)
        ·
          refine ⟨14293313967884826122835031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76231007828719072655120165 14293313967884826122835031)
          ·
            refine ⟨21439970951827239184252547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14293313967884826122835031 21439970951827239184252547)
            ·
              refine ⟨32159956427740858776378821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21439970951827239184252547 32159956427740858776378821)
              ·
                refine ⟨6029991830201411020571029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32159956427740858776378821 6029991830201411020571029)
                ·
                  refine ⟨282655867040691141589267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6029991830201411020571029 282655867040691141589267)
                  ·
                    rfl

theorem cell23_4954233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 6].length) (baseStart_4954233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954233 prefixEnd_4954233 := by exact prefixLift 4954233
  have htrace : WordTrace (prefixWord ++ tailWord_4954233) baseStart_4954233 baseEnd_4954233 := by
    simpa [prefixWord, tailWord_4954233, baseEnd_4954233] using wordTrace_append hprefix tailTrace_4954233
  have hstable : (prefixWord ++ tailWord_4954233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954233).length < 2 ^ (prefixWord ++ tailWord_4954233).sum := by decide
  have hdescent : baseEnd_4954233 < baseStart_4954233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954237 : List Nat := [1, 4, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_4954237 : Nat := 118140960795 + 4954237 * 2 ^ 59
def prefixEnd_4954237 : Nat := 4983230072969 + 3 ^ 40 * 4954237 * 2
def baseEnd_4954237 : Nat := 847968285762946086217795

theorem tailTrace_4954237 : CollatzResearch.WordTrace tailWord_4954237 prefixEnd_4954237 847968285762946086217795 := by
  unfold tailWord_4954237
  simp only [CollatzResearch.WordTrace]
  refine ⟨180695868152652940161948965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120463912101768626774632643 180695868152652940161948965)
  ·
    refine ⟨33880475278622426280365431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180695868152652940161948965 33880475278622426280365431)
    ·
      refine ⟨50820712917933639420548147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33880475278622426280365431 50820712917933639420548147)
      ·
        refine ⟨76231069376900459130822221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50820712917933639420548147 76231069376900459130822221)
        ·
          refine ⟨28586651016337672174058333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76231069376900459130822221 28586651016337672174058333)
          ·
            refine ⟨10719994131126627065271875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28586651016337672174058333 10719994131126627065271875)
            ·
              refine ⟨16079991196689940597907813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10719994131126627065271875 16079991196689940597907813)
              ·
                refine ⟨3014998349379363862107715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16079991196689940597907813 3014998349379363862107715)
                ·
                  refine ⟨4522497524069045793161573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014998349379363862107715 4522497524069045793161573)
                  ·
                    refine ⟨847968285762946086217795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522497524069045793161573 847968285762946086217795)
                    ·
                      rfl

theorem cell23_4954237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_4954237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954237 prefixEnd_4954237 := by exact prefixLift 4954237
  have htrace : WordTrace (prefixWord ++ tailWord_4954237) baseStart_4954237 baseEnd_4954237 := by
    simpa [prefixWord, tailWord_4954237, baseEnd_4954237] using wordTrace_append hprefix tailTrace_4954237
  have hstable : (prefixWord ++ tailWord_4954237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954237).length < 2 ^ (prefixWord ++ tailWord_4954237).sum := by decide
  have hdescent : baseEnd_4954237 < baseStart_4954237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954256 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_4954256 : Nat := 118140960795 + 4954256 * 2 ^ 59
def prefixEnd_4954256 : Nat := 4983230072969 + 3 ^ 40 * 4954256 * 2
def baseEnd_4954256 : Nat := 2543914613421273684315797

theorem tailTrace_4954256 : CollatzResearch.WordTrace tailWord_4954256 prefixEnd_4954256 2543914613421273684315797 := by
  unfold tailWord_4954256
  simp only [CollatzResearch.WordTrace]
  refine ⟨90348280569792053203445311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120464374093056070937927081 90348280569792053203445311)
  ·
    refine ⟨135522420854688079805167967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90348280569792053203445311 135522420854688079805167967)
    ·
      refine ⟨203283631282032119707751951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135522420854688079805167967 203283631282032119707751951)
      ·
        refine ⟨304925446923048179561627927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203283631282032119707751951 304925446923048179561627927)
        ·
          refine ⟨457388170384572269342441891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304925446923048179561627927 457388170384572269342441891)
          ·
            refine ⟨686082255576858404013662837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457388170384572269342441891 686082255576858404013662837)
            ·
              refine ⟨64320211460330475376280891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 686082255576858404013662837 64320211460330475376280891)
              ·
                refine ⟨96480317190495713064421337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64320211460330475376280891 96480317190495713064421337)
                ·
                  refine ⟨72360237892871784798316003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96480317190495713064421337 72360237892871784798316003)
                  ·
                    refine ⟨108540356839307677197474005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72360237892871784798316003 108540356839307677197474005)
                    ·
                      refine ⟨2543914613421273684315797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108540356839307677197474005 2543914613421273684315797)
                      ·
                        rfl

theorem cell23_4954256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_4954256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954256 prefixEnd_4954256 := by exact prefixLift 4954256
  have htrace : WordTrace (prefixWord ++ tailWord_4954256) baseStart_4954256 baseEnd_4954256 := by
    simpa [prefixWord, tailWord_4954256, baseEnd_4954256] using wordTrace_append hprefix tailTrace_4954256
  have hstable : (prefixWord ++ tailWord_4954256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954256).length < 2 ^ (prefixWord ++ tailWord_4954256).sum := by decide
  have hdescent : baseEnd_4954256 < baseStart_4954256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954264 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 2, 2, 3]
def baseStart_4954264 : Nat := 118140960795 + 4954264 * 2 ^ 59
def prefixEnd_4954264 : Nat := 4983230072969 + 3 ^ 40 * 4954264 * 2
def baseEnd_4954264 : Nat := 2543918721266509653015761

theorem tailTrace_4954264 : CollatzResearch.WordTrace tailWord_4954264 prefixEnd_4954264 2543918721266509653015761 := by
  unfold tailWord_4954264
  simp only [CollatzResearch.WordTrace]
  refine ⟨90348426461777561886590923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120464568615703415848787897 90348426461777561886590923)
  ·
    refine ⟨135522639692666342829886385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90348426461777561886590923 135522639692666342829886385)
    ·
      refine ⟨101641979769499757122414789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135522639692666342829886385 101641979769499757122414789)
      ·
        refine ⟨19057871206781204460452773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101641979769499757122414789 19057871206781204460452773)
        ·
          refine ⟨3573350851271475836334895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19057871206781204460452773 3573350851271475836334895)
          ·
            refine ⟨5360026276907213754502343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573350851271475836334895 5360026276907213754502343)
            ·
              refine ⟨8040039415360820631753515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360026276907213754502343 8040039415360820631753515)
              ·
                refine ⟨12060059123041230947630273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8040039415360820631753515 12060059123041230947630273)
                ·
                  refine ⟨9045044342280923210722705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12060059123041230947630273 9045044342280923210722705)
                  ·
                    refine ⟨6783783256710692408042029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9045044342280923210722705 6783783256710692408042029)
                    ·
                      refine ⟨2543918721266509653015761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783783256710692408042029 2543918721266509653015761)
                      ·
                        rfl

theorem cell23_4954264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_4954264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954264 prefixEnd_4954264 := by exact prefixLift 4954264
  have htrace : WordTrace (prefixWord ++ tailWord_4954264) baseStart_4954264 baseEnd_4954264 := by
    simpa [prefixWord, tailWord_4954264, baseEnd_4954264] using wordTrace_append hprefix tailTrace_4954264
  have hstable : (prefixWord ++ tailWord_4954264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954264).length < 2 ^ (prefixWord ++ tailWord_4954264).sum := by decide
  have hdescent : baseEnd_4954264 < baseStart_4954264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954313 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_4954313 : Nat := 118140960795 + 4954313 * 2 ^ 59
def prefixEnd_4954313 : Nat := 4983230072969 + 3 ^ 40 * 4954313 * 2
def baseEnd_4954313 : Nat := 2543943881818579961303035

theorem tailTrace_4954313 : CollatzResearch.WordTrace tailWord_4954313 prefixEnd_4954313 2543943881818579961303035 := by
  unfold tailWord_4954313
  simp only [CollatzResearch.WordTrace]
  refine ⟨180698640100377605141715593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120465760066918403427810395 180698640100377605141715593)
  ·
    refine ⟨135523980075283203856286695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180698640100377605141715593 135523980075283203856286695)
    ·
      refine ⟨203285970112924805784430043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135523980075283203856286695 203285970112924805784430043)
      ·
        refine ⟨304928955169387208676645065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203285970112924805784430043 304928955169387208676645065)
        ·
          refine ⟨228696716377040406507483799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304928955169387208676645065 228696716377040406507483799)
          ·
            refine ⟨343045074565560609761225699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228696716377040406507483799 343045074565560609761225699)
            ·
              refine ⟨514567611848340914641838549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343045074565560609761225699 514567611848340914641838549)
              ·
                refine ⟨12060178402695490186918091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 514567611848340914641838549 12060178402695490186918091)
                ·
                  refine ⟨18090267604043235280377137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12060178402695490186918091 18090267604043235280377137)
                  ·
                    refine ⟨13567700703032426460282853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18090267604043235280377137 13567700703032426460282853)
                    ·
                      refine ⟨2543943881818579961303035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13567700703032426460282853 2543943881818579961303035)
                      ·
                        rfl

theorem cell23_4954313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_4954313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954313 prefixEnd_4954313 := by exact prefixLift 4954313
  have htrace : WordTrace (prefixWord ++ tailWord_4954313) baseStart_4954313 baseEnd_4954313 := by
    simpa [prefixWord, tailWord_4954313, baseEnd_4954313] using wordTrace_append hprefix tailTrace_4954313
  have hstable : (prefixWord ++ tailWord_4954313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954313).length < 2 ^ (prefixWord ++ tailWord_4954313).sum := by decide
  have hdescent : baseEnd_4954313 < baseStart_4954313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954338 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4954338 : Nat := 118140960795 + 4954338 * 2 ^ 59
def prefixEnd_4954338 : Nat := 4983230072969 + 3 ^ 40 * 4954338 * 2
def baseEnd_4954338 : Nat := 2543956718834942363490421

theorem tailTrace_4954338 : CollatzResearch.WordTrace tailWord_4954338 prefixEnd_4954338 2543956718834942363490421 := by
  unfold tailWord_4954338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45174887981321758602843917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120466367950191356274250445 45174887981321758602843917)
  ·
    refine ⟨16940582992995659476066469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45174887981321758602843917 16940582992995659476066469)
    ·
      refine ⟨3176359311186686151762463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16940582992995659476066469 3176359311186686151762463)
      ·
        refine ⟨4764538966780029227643695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176359311186686151762463 4764538966780029227643695)
        ·
          refine ⟨7146808450170043841465543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764538966780029227643695 7146808450170043841465543)
          ·
            refine ⟨10720212675255065762198315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7146808450170043841465543 10720212675255065762198315)
            ·
              refine ⟨16080319012882598643297473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10720212675255065762198315 16080319012882598643297473)
              ·
                refine ⟨12060239259661948982473105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16080319012882598643297473 12060239259661948982473105)
                ·
                  refine ⟨9045179444746461736854829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12060239259661948982473105 9045179444746461736854829)
                  ·
                    refine ⟨3391942291779923151320561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9045179444746461736854829 3391942291779923151320561)
                    ·
                      refine ⟨2543956718834942363490421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391942291779923151320561 2543956718834942363490421)
                      ·
                        rfl

theorem cell23_4954338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4954338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954338 prefixEnd_4954338 := by exact prefixLift 4954338
  have htrace : WordTrace (prefixWord ++ tailWord_4954338) baseStart_4954338 baseEnd_4954338 := by
    simpa [prefixWord, tailWord_4954338, baseEnd_4954338] using wordTrace_append hprefix tailTrace_4954338
  have hstable : (prefixWord ++ tailWord_4954338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954338).length < 2 ^ (prefixWord ++ tailWord_4954338).sum := by decide
  have hdescent : baseEnd_4954338 < baseStart_4954338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954367 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 3]
def baseStart_4954367 : Nat := 118140960795 + 4954367 * 2 ^ 59
def prefixEnd_4954367 : Nat := 4983230072969 + 3 ^ 40 * 4954367 * 2
def baseEnd_4954367 : Nat := 2543971609773922750027787

theorem tailTrace_4954367 : CollatzResearch.WordTrace tailWord_4954367 prefixEnd_4954367 2543971609773922750027787 := by
  unfold tailWord_4954367
  simp only [CollatzResearch.WordTrace]
  refine ⟨180700609642181972364181355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120467073094787981576120903 180700609642181972364181355)
  ·
    refine ⟨271050914463272958546272033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180700609642181972364181355 271050914463272958546272033)
    ·
      refine ⟨203288185847454718909704025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271050914463272958546272033 203288185847454718909704025)
      ·
        refine ⟨152466139385591039182278019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203288185847454718909704025 152466139385591039182278019)
        ·
          refine ⟨228699209078386558773417029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152466139385591039182278019 228699209078386558773417029)
          ·
            refine ⟨42881101702197479770015693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228699209078386558773417029 42881101702197479770015693)
            ·
              refine ⟨16080413138324054913755885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42881101702197479770015693 16080413138324054913755885)
              ·
                refine ⟨6030154926871520592658457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16080413138324054913755885 6030154926871520592658457)
                ·
                  refine ⟨4522616195153640444493843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6030154926871520592658457 4522616195153640444493843)
                  ·
                    refine ⟨6783924292730460666740765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4522616195153640444493843 6783924292730460666740765)
                    ·
                      refine ⟨2543971609773922750027787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6783924292730460666740765 2543971609773922750027787)
                      ·
                        rfl

theorem cell23_4954367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_4954367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954367 prefixEnd_4954367 := by exact prefixLift 4954367
  have htrace : WordTrace (prefixWord ++ tailWord_4954367) baseStart_4954367 baseEnd_4954367 := by
    simpa [prefixWord, tailWord_4954367, baseEnd_4954367] using wordTrace_append hprefix tailTrace_4954367
  have hstable : (prefixWord ++ tailWord_4954367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954367).length < 2 ^ (prefixWord ++ tailWord_4954367).sum := by decide
  have hdescent : baseEnd_4954367 < baseStart_4954367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954373 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_4954373 : Nat := 118140960795 + 4954373 * 2 ^ 59
def prefixEnd_4954373 : Nat := 4983230072969 + 3 ^ 40 * 4954373 * 2
def baseEnd_4954373 : Nat := 2543974690657849726552759

theorem tailTrace_4954373 : CollatzResearch.WordTrace tailWord_4954373 prefixEnd_4954373 2543974690657849726552759 := by
  unfold tailWord_4954373
  simp only [CollatzResearch.WordTrace]
  refine ⟨180700828480160235388899773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120467218986773490259266515 180700828480160235388899773)
  ·
    refine ⟨67762810680060088270837415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180700828480160235388899773 67762810680060088270837415)
    ·
      refine ⟨101644216020090132406256123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67762810680060088270837415 101644216020090132406256123)
      ·
        refine ⟨152466324030135198609384185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101644216020090132406256123 152466324030135198609384185)
        ·
          refine ⟨114349743022601398957038139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152466324030135198609384185 114349743022601398957038139)
          ·
            refine ⟨171524614533902098435557209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114349743022601398957038139 171524614533902098435557209)
            ·
              refine ⟨128643460900426573826667907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171524614533902098435557209 128643460900426573826667907)
              ·
                refine ⟨192965191350639860740001861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128643460900426573826667907 192965191350639860740001861)
                ·
                  refine ⟨36180973378244973888750349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192965191350639860740001861 36180973378244973888750349)
                  ·
                    refine ⟨13567865016841865208281381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36180973378244973888750349 13567865016841865208281381)
                    ·
                      refine ⟨2543974690657849726552759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13567865016841865208281381 2543974690657849726552759)
                      ·
                        rfl

theorem cell23_4954373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_4954373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954373 prefixEnd_4954373 := by exact prefixLift 4954373
  have htrace : WordTrace (prefixWord ++ tailWord_4954373) baseStart_4954373 baseEnd_4954373 := by
    simpa [prefixWord, tailWord_4954373, baseEnd_4954373] using wordTrace_append hprefix tailTrace_4954373
  have hstable : (prefixWord ++ tailWord_4954373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954373).length < 2 ^ (prefixWord ++ tailWord_4954373).sum := by decide
  have hdescent : baseEnd_4954373 < baseStart_4954373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954377 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 3, 3, 2]
def baseStart_4954377 : Nat := 118140960795 + 4954377 * 2 ^ 59
def prefixEnd_4954377 : Nat := 4983230072969 + 3 ^ 40 * 4954377 * 2
def baseEnd_4954377 : Nat := 2543976744580467710902741

theorem tailTrace_4954377 : CollatzResearch.WordTrace tailWord_4954377 prefixEnd_4954377 2543976744580467710902741 := by
  unfold tailWord_4954377
  simp only [CollatzResearch.WordTrace]
  refine ⟨180700974372145744072045385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120467316248097162714696923 180700974372145744072045385)
  ·
    refine ⟨135525730779109308054034039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180700974372145744072045385 135525730779109308054034039)
    ·
      refine ⟨203288596168663962081051059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135525730779109308054034039 203288596168663962081051059)
      ·
        refine ⟨304932894252995943121576589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203288596168663962081051059 304932894252995943121576589)
        ·
          refine ⟨114349835344873478670591221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304932894252995943121576589 114349835344873478670591221)
          ·
            refine ⟨10720297063581888625367927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114349835344873478670591221 10720297063581888625367927)
            ·
              refine ⟨16080445595372832938051891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10720297063581888625367927 16080445595372832938051891)
              ·
                refine ⟨24120668393059249407077837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16080445595372832938051891 24120668393059249407077837)
                ·
                  refine ⟨9045250647397218527654189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24120668393059249407077837 9045250647397218527654189)
                  ·
                    refine ⟨3391968992773956947870321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9045250647397218527654189 3391968992773956947870321)
                    ·
                      refine ⟨2543976744580467710902741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3391968992773956947870321 2543976744580467710902741)
                      ·
                        rfl

theorem cell23_4954377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 3, 2].length) (baseStart_4954377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954377 prefixEnd_4954377 := by exact prefixLift 4954377
  have htrace : WordTrace (prefixWord ++ tailWord_4954377) baseStart_4954377 baseEnd_4954377 := by
    simpa [prefixWord, tailWord_4954377, baseEnd_4954377] using wordTrace_append hprefix tailTrace_4954377
  have hstable : (prefixWord ++ tailWord_4954377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954377).length < 2 ^ (prefixWord ++ tailWord_4954377).sum := by decide
  have hdescent : baseEnd_4954377 < baseStart_4954377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954424 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 2, 2, 2]
def baseStart_4954424 : Nat := 118140960795 + 4954424 * 2 ^ 59
def prefixEnd_4954424 : Nat := 4983230072969 + 3 ^ 40 * 4954424 * 2
def baseEnd_4954424 : Nat := 2544000878171229027015025

theorem tailTrace_4954424 : CollatzResearch.WordTrace tailWord_4954424 prefixEnd_4954424 2544000878171229027015025 := by
  unfold tailWord_4954424
  simp only [CollatzResearch.WordTrace]
  refine ⟨90351344301487735549503163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120468459068650314066004217 90351344301487735549503163)
  ·
    refine ⟨135527016452231603324254745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90351344301487735549503163 135527016452231603324254745)
    ·
      refine ⟨101645262339173702493191059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135527016452231603324254745 101645262339173702493191059)
      ·
        refine ⟨152467893508760553739786589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101645262339173702493191059 152467893508760553739786589)
        ·
          refine ⟨57175460065785207652419971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152467893508760553739786589 57175460065785207652419971)
          ·
            refine ⟨85763190098677811478629957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57175460065785207652419971 85763190098677811478629957)
            ·
              refine ⟨16080598143502089652243117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85763190098677811478629957 16080598143502089652243117)
              ·
                refine ⟨6030224303813283619591169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16080598143502089652243117 6030224303813283619591169)
                ·
                  refine ⟨4522668227859962714693377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6030224303813283619591169 4522668227859962714693377)
                  ·
                    refine ⟨3392001170894972036020033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4522668227859962714693377 3392001170894972036020033)
                    ·
                      refine ⟨2544000878171229027015025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392001170894972036020033 2544000878171229027015025)
                      ·
                        rfl

theorem cell23_4954424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_4954424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954424 prefixEnd_4954424 := by exact prefixLift 4954424
  have htrace : WordTrace (prefixWord ++ tailWord_4954424) baseStart_4954424 baseEnd_4954424 := by
    simpa [prefixWord, tailWord_4954424, baseEnd_4954424] using wordTrace_append hprefix tailTrace_4954424
  have hstable : (prefixWord ++ tailWord_4954424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954424).length < 2 ^ (prefixWord ++ tailWord_4954424).sum := by decide
  have hdescent : baseEnd_4954424 < baseStart_4954424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954430 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_4954430 : Nat := 118140960795 + 4954430 * 2 ^ 59
def prefixEnd_4954430 : Nat := 4983230072969 + 3 ^ 40 * 4954430 * 2
def baseEnd_4954430 : Nat := 282667106561684000393333

theorem tailTrace_4954430 : CollatzResearch.WordTrace tailWord_4954430 prefixEnd_4954430 282667106561684000393333 := by
  unfold tailWord_4954430
  simp only [CollatzResearch.WordTrace]
  refine ⟨22587863430119216765465593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120468604960635822749149829 22587863430119216765465593)
  ·
    refine ⟨16940897572589412574099195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22587863430119216765465593 16940897572589412574099195)
    ·
      refine ⟨25411346358884118861148793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16940897572589412574099195 25411346358884118861148793)
      ·
        refine ⟨19058509769163089145861595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25411346358884118861148793 19058509769163089145861595)
        ·
          refine ⟨28587764653744633718792393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19058509769163089145861595 28587764653744633718792393)
          ·
            refine ⟨21440823490308475289094295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28587764653744633718792393 21440823490308475289094295)
            ·
              refine ⟨32161235235462712933641443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21440823490308475289094295 32161235235462712933641443)
              ·
                refine ⟨48241852853194069400462165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32161235235462712933641443 48241852853194069400462165)
                ·
                  refine ⟨282667106561684000393333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48241852853194069400462165 282667106561684000393333)
                  ·
                    rfl

theorem cell23_4954430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_4954430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954430 prefixEnd_4954430 := by exact prefixLift 4954430
  have htrace : WordTrace (prefixWord ++ tailWord_4954430) baseStart_4954430 baseEnd_4954430 := by
    simpa [prefixWord, tailWord_4954430, baseEnd_4954430] using wordTrace_append hprefix tailTrace_4954430
  have hstable : (prefixWord ++ tailWord_4954430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954430).length < 2 ^ (prefixWord ++ tailWord_4954430).sum := by decide
  have hdescent : baseEnd_4954430 < baseStart_4954430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954480 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_4954480 : Nat := 118140960795 + 4954480 * 2 ^ 59
def prefixEnd_4954480 : Nat := 4983230072969 + 3 ^ 40 * 4954480 * 2
def baseEnd_4954480 : Nat := 2544029633087880807914767

theorem tailTrace_4954480 : CollatzResearch.WordTrace tailWord_4954480 prefixEnd_4954480 2544029633087880807914767 := by
  unfold tailWord_4954480
  simp only [CollatzResearch.WordTrace]
  refine ⟨90352365545386296331522447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120469820727181728442029929 90352365545386296331522447)
  ·
    refine ⟨135528548318079444497283671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90352365545386296331522447 135528548318079444497283671)
    ·
      refine ⟨203292822477119166745925507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135528548318079444497283671 203292822477119166745925507)
      ·
        refine ⟨304939233715678750118888261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203292822477119166745925507 304939233715678750118888261)
        ·
          refine ⟨57176106321689765647291549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304939233715678750118888261 57176106321689765647291549)
          ·
            refine ⟨21441039870633662117734331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57176106321689765647291549 21441039870633662117734331)
            ·
              refine ⟨32161559805950493176601497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21441039870633662117734331 32161559805950493176601497)
              ·
                refine ⟨24121169854462869882451123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32161559805950493176601497 24121169854462869882451123)
                ·
                  refine ⟨36181754781694304823676685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24121169854462869882451123 36181754781694304823676685)
                  ·
                    refine ⟨13568158043135364308878757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36181754781694304823676685 13568158043135364308878757)
                    ·
                      refine ⟨2544029633087880807914767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13568158043135364308878757 2544029633087880807914767)
                      ·
                        rfl

theorem cell23_4954480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_4954480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954480 prefixEnd_4954480 := by exact prefixLift 4954480
  have htrace : WordTrace (prefixWord ++ tailWord_4954480) baseStart_4954480 baseEnd_4954480 := by
    simpa [prefixWord, tailWord_4954480, baseEnd_4954480] using wordTrace_append hprefix tailTrace_4954480
  have hstable : (prefixWord ++ tailWord_4954480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954480).length < 2 ^ (prefixWord ++ tailWord_4954480).sum := by decide
  have hdescent : baseEnd_4954480 < baseStart_4954480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954497 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4954497 : Nat := 118140960795 + 4954497 * 2 ^ 59
def prefixEnd_4954497 : Nat := 4983230072969 + 3 ^ 40 * 4954497 * 2
def baseEnd_4954497 : Nat := 2544038362259007241402189

theorem tailTrace_4954497 : CollatzResearch.WordTrace tailWord_4954497 prefixEnd_4954497 2544038362259007241402189 := by
  unfold tailWord_4954497
  simp only [CollatzResearch.WordTrace]
  refine ⟨180705351131711004566413745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120470234087807336377609163 180705351131711004566413745)
  ·
    refine ⟨135529013348783253424810309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180705351131711004566413745 135529013348783253424810309)
    ·
      refine ⟨25411690002896860017151933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135529013348783253424810309 25411690002896860017151933)
      ·
        refine ⟨9529383751086322506431975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25411690002896860017151933 9529383751086322506431975)
        ·
          refine ⟨14294075626629483759647963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9529383751086322506431975 14294075626629483759647963)
          ·
            refine ⟨21441113439944225639471945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14294075626629483759647963 21441113439944225639471945)
            ·
              refine ⟨16080835079958169229603959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21441113439944225639471945 16080835079958169229603959)
              ·
                refine ⟨24121252619937253844405939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16080835079958169229603959 24121252619937253844405939)
                ·
                  refine ⟨36181878929905880766608909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24121252619937253844405939 36181878929905880766608909)
                  ·
                    refine ⟨13568204598714705287478341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36181878929905880766608909 13568204598714705287478341)
                    ·
                      refine ⟨2544038362259007241402189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13568204598714705287478341 2544038362259007241402189)
                      ·
                        rfl

theorem cell23_4954497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4954497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954497 prefixEnd_4954497 := by exact prefixLift 4954497
  have htrace : WordTrace (prefixWord ++ tailWord_4954497) baseStart_4954497 baseEnd_4954497 := by
    simpa [prefixWord, tailWord_4954497, baseEnd_4954497] using wordTrace_append hprefix tailTrace_4954497
  have hstable : (prefixWord ++ tailWord_4954497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954497).length < 2 ^ (prefixWord ++ tailWord_4954497).sum := by decide
  have hdescent : baseEnd_4954497 < baseStart_4954497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954498 : List Nat := [3, 4, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4954498 : Nat := 118140960795 + 4954498 * 2 ^ 59
def prefixEnd_4954498 : Nat := 4983230072969 + 3 ^ 40 * 4954498 * 2
def baseEnd_4954498 : Nat := 282670986193295748609965

theorem tailTrace_4954498 : CollatzResearch.WordTrace tailWord_4954498 prefixEnd_4954498 282670986193295748609965 := by
  unfold tailWord_4954498
  simp only [CollatzResearch.WordTrace]
  refine ⟨45176346901176845434300037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120470258403138254491466765 45176346901176845434300037)
  ·
    refine ⟨8470565043970658518931257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45176346901176845434300037 8470565043970658518931257)
    ·
      refine ⟨6352923782977993889198443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8470565043970658518931257 6352923782977993889198443)
      ·
        refine ⟨9529385674466990833797665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6352923782977993889198443 9529385674466990833797665)
        ·
          refine ⟨7147039255850243125348249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9529385674466990833797665 7147039255850243125348249)
          ·
            refine ⟨5360279441887682344011187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7147039255850243125348249 5360279441887682344011187)
            ·
              refine ⟨8040419162831523516016781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360279441887682344011187 8040419162831523516016781)
              ·
                refine ⟨3015157186061821318506293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8040419162831523516016781 3015157186061821318506293)
                ·
                  refine ⟨282670986193295748609965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3015157186061821318506293 282670986193295748609965)
                  ·
                    rfl

theorem cell23_4954498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4954498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954498 prefixEnd_4954498 := by exact prefixLift 4954498
  have htrace : WordTrace (prefixWord ++ tailWord_4954498) baseStart_4954498 baseEnd_4954498 := by
    simpa [prefixWord, tailWord_4954498, baseEnd_4954498] using wordTrace_append hprefix tailTrace_4954498
  have hstable : (prefixWord ++ tailWord_4954498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954498).length < 2 ^ (prefixWord ++ tailWord_4954498).sum := by decide
  have hdescent : baseEnd_4954498 < baseStart_4954498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954548 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4954548 : Nat := 118140960795 + 4954548 * 2 ^ 59
def prefixEnd_4954548 : Nat := 4983230072969 + 3 ^ 40 * 4954548 * 2
def baseEnd_4954548 : Nat := 2544064549772386541864455

theorem tailTrace_4954548 : CollatzResearch.WordTrace tailWord_4954548 prefixEnd_4954548 2544064549772386541864455 := by
  unfold tailWord_4954548
  simp only [CollatzResearch.WordTrace]
  refine ⟨90353605627263120138260149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120471474169684160184346865 90353605627263120138260149)
  ·
    refine ⟨8470650527555917512961889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90353605627263120138260149 8470650527555917512961889)
    ·
      refine ⟨6352987895666938134721417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8470650527555917512961889 6352987895666938134721417)
      ·
        refine ⟨4764740921750203601041063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6352987895666938134721417 4764740921750203601041063)
        ·
          refine ⟨7147111382625305401561595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764740921750203601041063 7147111382625305401561595)
          ·
            refine ⟨10720667073937958102342393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147111382625305401561595 10720667073937958102342393)
            ·
              refine ⟨8040500305453468576756795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10720667073937958102342393 8040500305453468576756795)
              ·
                refine ⟨12060750458180202865135193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8040500305453468576756795 12060750458180202865135193)
                ·
                  refine ⟨9045562843635152148851395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12060750458180202865135193 9045562843635152148851395)
                  ·
                    refine ⟨13568344265452728223277093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9045562843635152148851395 13568344265452728223277093)
                    ·
                      refine ⟨2544064549772386541864455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13568344265452728223277093 2544064549772386541864455)
                      ·
                        rfl

theorem cell23_4954548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4954548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954548 prefixEnd_4954548 := by exact prefixLift 4954548
  have htrace : WordTrace (prefixWord ++ tailWord_4954548) baseStart_4954548 baseEnd_4954548 := by
    simpa [prefixWord, tailWord_4954548, baseEnd_4954548] using wordTrace_append hprefix tailTrace_4954548
  have hstable : (prefixWord ++ tailWord_4954548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954548).length < 2 ^ (prefixWord ++ tailWord_4954548).sum := by decide
  have hdescent : baseEnd_4954548 < baseStart_4954548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954614 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_4954614 : Nat := 118140960795 + 4954614 * 2 ^ 59
def prefixEnd_4954614 : Nat := 4983230072969 + 3 ^ 40 * 4954614 * 2
def baseEnd_4954614 : Nat := 848032813165194427879717

theorem tailTrace_4954614 : CollatzResearch.WordTrace tailWord_4954614 prefixEnd_4954614 848032813165194427879717 := by
  unfold tailWord_4954614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294351154517945846776431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120473078981524755698948597 11294351154517945846776431)
  ·
    refine ⟨16941526731776918770164647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11294351154517945846776431 16941526731776918770164647)
    ·
      refine ⟨25412290097665378155246971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16941526731776918770164647 25412290097665378155246971)
      ·
        refine ⟨38118435146498067232870457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25412290097665378155246971 38118435146498067232870457)
        ·
          refine ⟨28588826359873550424652843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38118435146498067232870457 28588826359873550424652843)
          ·
            refine ⟨42883239539810325636979265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28588826359873550424652843 42883239539810325636979265)
            ·
              refine ⟨32162429654857744227734449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42883239539810325636979265 32162429654857744227734449)
              ·
                refine ⟨24121822241143308170800837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32162429654857744227734449 24121822241143308170800837)
                ·
                  refine ⟨4522841670214370282025157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24121822241143308170800837 4522841670214370282025157)
                  ·
                    refine ⟨848032813165194427879717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522841670214370282025157 848032813165194427879717)
                    ·
                      rfl

theorem cell23_4954614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_4954614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954614 prefixEnd_4954614 := by exact prefixLift 4954614
  have htrace : WordTrace (prefixWord ++ tailWord_4954614) baseStart_4954614 baseEnd_4954614 := by
    simpa [prefixWord, tailWord_4954614, baseEnd_4954614] using wordTrace_append hprefix tailTrace_4954614
  have hstable : (prefixWord ++ tailWord_4954614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954614).length < 2 ^ (prefixWord ++ tailWord_4954614).sum := by decide
  have hdescent : baseEnd_4954614 < baseStart_4954614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954617 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_4954617 : Nat := 118140960795 + 4954617 * 2 ^ 59
def prefixEnd_4954617 : Nat := 4983230072969 + 3 ^ 40 * 4954617 * 2
def baseEnd_4954617 : Nat := 2544099979937546771901637

theorem tailTrace_4954617 : CollatzResearch.WordTrace tailWord_4954617 prefixEnd_4954617 2544099979937546771901637 := by
  unfold tailWord_4954617
  simp only [CollatzResearch.WordTrace]
  refine ⟨180709727891276265060782105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120473151927517510040521403 180709727891276265060782105)
  ·
    refine ⟨135532295918457198795586579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180709727891276265060782105 135532295918457198795586579)
    ·
      refine ⟨203298443877685798193379869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135532295918457198795586579 203298443877685798193379869)
      ·
        refine ⟨76236916454132174322517451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203298443877685798193379869 76236916454132174322517451)
        ·
          refine ⟨114355374681198261483776177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76236916454132174322517451 114355374681198261483776177)
          ·
            refine ⟨85766531010898696112832133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114355374681198261483776177 85766531010898696112832133)
            ·
              refine ⟨16081224564543505521156025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85766531010898696112832133 16081224564543505521156025)
              ·
                refine ⟨12060918423407629140867019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16081224564543505521156025 12060918423407629140867019)
                ·
                  refine ⟨18091377635111443711300529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12060918423407629140867019 18091377635111443711300529)
                  ·
                    refine ⟨13568533226333582783475397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18091377635111443711300529 13568533226333582783475397)
                    ·
                      refine ⟨2544099979937546771901637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13568533226333582783475397 2544099979937546771901637)
                      ·
                        rfl

theorem cell23_4954617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_4954617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954617 prefixEnd_4954617 := by exact prefixLift 4954617
  have htrace : WordTrace (prefixWord ++ tailWord_4954617) baseStart_4954617 baseEnd_4954617 := by
    simpa [prefixWord, tailWord_4954617, baseEnd_4954617] using wordTrace_append hprefix tailTrace_4954617
  have hstable : (prefixWord ++ tailWord_4954617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954617).length < 2 ^ (prefixWord ++ tailWord_4954617).sum := by decide
  have hdescent : baseEnd_4954617 < baseStart_4954617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954638 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_4954638 : Nat := 118140960795 + 4954638 * 2 ^ 59
def prefixEnd_4954638 : Nat := 4983230072969 + 3 ^ 40 * 4954638 * 2
def baseEnd_4954638 : Nat := 2544110763031291189739041

theorem tailTrace_4954638 : CollatzResearch.WordTrace tailWord_4954638 prefixEnd_4954638 2544110763031291189739041 := by
  unfold tailWord_4954638
  simp only [CollatzResearch.WordTrace]
  refine ⟨22588811728025023205912071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120473662549466790431531045 22588811728025023205912071)
  ·
    refine ⟨33883217592037534808868107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22588811728025023205912071 33883217592037534808868107)
    ·
      refine ⟨50824826388056302213302161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33883217592037534808868107 50824826388056302213302161)
      ·
        refine ⟨38118619791042226659976621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50824826388056302213302161 38118619791042226659976621)
        ·
          refine ⟨14294482421640834997491233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38118619791042226659976621 14294482421640834997491233)
          ·
            refine ⟨10720861816230626248118425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14294482421640834997491233 10720861816230626248118425)
            ·
              refine ⟨8040646362172969686088819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10720861816230626248118425 8040646362172969686088819)
              ·
                refine ⟨12060969543259454529133229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8040646362172969686088819 12060969543259454529133229)
                ·
                  refine ⟨4522863578722295448424961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12060969543259454529133229 4522863578722295448424961)
                  ·
                    refine ⟨3392147684041721586318721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4522863578722295448424961 3392147684041721586318721)
                    ·
                      refine ⟨2544110763031291189739041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392147684041721586318721 2544110763031291189739041)
                      ·
                        rfl

theorem cell23_4954638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_4954638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954638 prefixEnd_4954638 := by exact prefixLift 4954638
  have htrace : WordTrace (prefixWord ++ tailWord_4954638) baseStart_4954638 baseEnd_4954638 := by
    simpa [prefixWord, tailWord_4954638, baseEnd_4954638] using wordTrace_append hprefix tailTrace_4954638
  have hstable : (prefixWord ++ tailWord_4954638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954638).length < 2 ^ (prefixWord ++ tailWord_4954638).sum := by decide
  have hdescent : baseEnd_4954638 < baseStart_4954638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954640 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 6, 7]
def baseStart_4954640 : Nat := 118140960795 + 4954640 * 2 ^ 59
def prefixEnd_4954640 : Nat := 4983230072969 + 3 ^ 40 * 4954640 * 2
def baseEnd_4954640 : Nat := 848037263330866727304677

theorem tailTrace_4954640 : CollatzResearch.WordTrace tailWord_4954640 prefixEnd_4954640 848037263330866727304677 := by
  unfold tailWord_4954640
  simp only [CollatzResearch.WordTrace]
  refine ⟨90355283385096469994434687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120473711180128626659246249 90355283385096469994434687)
  ·
    refine ⟨135532925077644704991652031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90355283385096469994434687 135532925077644704991652031)
    ·
      refine ⟨203299387616467057487478047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135532925077644704991652031 203299387616467057487478047)
      ·
        refine ⟨304949081424700586231217071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203299387616467057487478047 304949081424700586231217071)
        ·
          refine ⟨457423622137050879346825607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304949081424700586231217071 457423622137050879346825607)
          ·
            refine ⟨686135433205576319020238411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457423622137050879346825607 686135433205576319020238411)
            ·
              refine ⟨1029203149808364478530357617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686135433205576319020238411 1029203149808364478530357617)
              ·
                refine ⟨771902362356273358897768213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029203149808364478530357617 771902362356273358897768213)
                ·
                  refine ⟨36182923235450313698332885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 771902362356273358897768213 36182923235450313698332885)
                  ·
                    refine ⟨848037263330866727304677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36182923235450313698332885 848037263330866727304677)
                    ·
                      rfl

theorem cell23_4954640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_4954640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954640 prefixEnd_4954640 := by exact prefixLift 4954640
  have htrace : WordTrace (prefixWord ++ tailWord_4954640) baseStart_4954640 baseEnd_4954640 := by
    simpa [prefixWord, tailWord_4954640, baseEnd_4954640] using wordTrace_append hprefix tailTrace_4954640
  have hstable : (prefixWord ++ tailWord_4954640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954640).length < 2 ^ (prefixWord ++ tailWord_4954640).sum := by decide
  have hdescent : baseEnd_4954640 < baseStart_4954640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954681 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 1, 3, 2]
def baseStart_4954681 : Nat := 118140960795 + 4954681 * 2 ^ 59
def prefixEnd_4954681 : Nat := 4983230072969 + 3 ^ 40 * 4954681 * 2
def baseEnd_4954681 : Nat := 2544132842699434521501343

theorem tailTrace_4954681 : CollatzResearch.WordTrace tailWord_4954681 prefixEnd_4954681 2544132842699434521501343 := by
  unfold tailWord_4954681
  simp only [CollatzResearch.WordTrace]
  refine ⟨180712062163044403991111897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120474708108696269327407931 180712062163044403991111897)
  ·
    refine ⟨135534046622283302993333923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180712062163044403991111897 135534046622283302993333923)
    ·
      refine ⟨203301069933424954490000885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135534046622283302993333923 203301069933424954490000885)
      ·
        refine ⟨19059475306258589483437583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203301069933424954490000885 19059475306258589483437583)
        ·
          refine ⟨28589212959387884225156375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19059475306258589483437583 28589212959387884225156375)
          ·
            refine ⟨42883819439081826337734563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28589212959387884225156375 42883819439081826337734563)
            ·
              refine ⟨64325729158622739506601845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42883819439081826337734563 64325729158622739506601845)
              ·
                refine ⟨6030537108620881828743923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64325729158622739506601845 6030537108620881828743923)
                ·
                  refine ⟨9045805662931322743115885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6030537108620881828743923 9045805662931322743115885)
                  ·
                    refine ⟨3392177123599246028668457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9045805662931322743115885 3392177123599246028668457)
                    ·
                      refine ⟨2544132842699434521501343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392177123599246028668457 2544132842699434521501343)
                      ·
                        rfl

theorem cell23_4954681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_4954681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954681 prefixEnd_4954681 := by exact prefixLift 4954681
  have htrace : WordTrace (prefixWord ++ tailWord_4954681) baseStart_4954681 baseEnd_4954681 := by
    simpa [prefixWord, tailWord_4954681, baseEnd_4954681] using wordTrace_append hprefix tailTrace_4954681
  have hstable : (prefixWord ++ tailWord_4954681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954681).length < 2 ^ (prefixWord ++ tailWord_4954681).sum := by decide
  have hdescent : baseEnd_4954681 < baseStart_4954681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954728 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4954728 : Nat := 118140960795 + 4954728 * 2 ^ 59
def prefixEnd_4954728 : Nat := 4983230072969 + 3 ^ 40 * 4954728 * 2
def baseEnd_4954728 : Nat := 2544156976290195837613627

theorem tailTrace_4954728 : CollatzResearch.WordTrace tailWord_4954728 prefixEnd_4954728 2544156976290195837613627 := by
  unfold tailWord_4954728
  simp only [CollatzResearch.WordTrace]
  refine ⟨90356888196937065509036419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120475850929249420678715225 90356888196937065509036419)
  ·
    refine ⟨135535332295405598263554629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90356888196937065509036419 135535332295405598263554629)
    ·
      refine ⟨25412874805388549674416493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135535332295405598263554629 25412874805388549674416493)
      ·
        refine ⟨9529828052020706127906185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25412874805388549674416493 9529828052020706127906185)
        ·
          refine ⟨7147371039015529595929639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9529828052020706127906185 7147371039015529595929639)
          ·
            refine ⟨10721056558523294393894459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147371039015529595929639 10721056558523294393894459)
            ·
              refine ⟨16081584837784941590841689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10721056558523294393894459 16081584837784941590841689)
              ·
                refine ⟨12061188628338706193131267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16081584837784941590841689 12061188628338706193131267)
                ·
                  refine ⟨18091782942508059289696901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12061188628338706193131267 18091782942508059289696901)
                  ·
                    refine ⟨3392209301720261116818169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18091782942508059289696901 3392209301720261116818169)
                    ·
                      refine ⟨2544156976290195837613627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392209301720261116818169 2544156976290195837613627)
                      ·
                        rfl

theorem cell23_4954728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4954728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954728 prefixEnd_4954728 := by exact prefixLift 4954728
  have htrace : WordTrace (prefixWord ++ tailWord_4954728) baseStart_4954728 baseEnd_4954728 := by
    simpa [prefixWord, tailWord_4954728, baseEnd_4954728] using wordTrace_append hprefix tailTrace_4954728
  have hstable : (prefixWord ++ tailWord_4954728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954728).length < 2 ^ (prefixWord ++ tailWord_4954728).sum := by decide
  have hdescent : baseEnd_4954728 < baseStart_4954728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954747 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 4, 5]
def baseStart_4954747 : Nat := 118140960795 + 4954747 * 2 ^ 59
def prefixEnd_4954747 : Nat := 4983230072969 + 3 ^ 40 * 4954747 * 2
def baseEnd_4954747 : Nat := 848055577474210421092013

theorem tailTrace_4954747 : CollatzResearch.WordTrace tailWord_4954747 prefixEnd_4954747 848055577474210421092013 := by
  unfold tailWord_4954747
  simp only [CollatzResearch.WordTrace]
  refine ⟨180714469380805297263014495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120476312920536864842009663 180714469380805297263014495)
  ·
    refine ⟨271071704071207945894521743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180714469380805297263014495 271071704071207945894521743)
    ·
      refine ⟨406607556106811918841782615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271071704071207945894521743 406607556106811918841782615)
      ·
        refine ⟨609911334160217878262673923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406607556106811918841782615 609911334160217878262673923)
        ·
          refine ⟨914867001240326817394010885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609911334160217878262673923 914867001240326817394010885)
          ·
            refine ⟨171537562732561278261377041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 914867001240326817394010885 171537562732561278261377041)
            ·
              refine ⟨128653172049420958696032781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171537562732561278261377041 128653172049420958696032781)
              ·
                refine ⟨48244939518532859511012293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128653172049420958696032781 48244939518532859511012293)
                ·
                  refine ⟨9045926159724911158314805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48244939518532859511012293 9045926159724911158314805)
                  ·
                    refine ⟨848055577474210421092013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9045926159724911158314805 848055577474210421092013)
                    ·
                      rfl

theorem cell23_4954747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 5].length) (baseStart_4954747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954747 prefixEnd_4954747 := by exact prefixLift 4954747
  have htrace : WordTrace (prefixWord ++ tailWord_4954747) baseStart_4954747 baseEnd_4954747 := by
    simpa [prefixWord, tailWord_4954747, baseEnd_4954747] using wordTrace_append hprefix tailTrace_4954747
  have hstable : (prefixWord ++ tailWord_4954747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954747).length < 2 ^ (prefixWord ++ tailWord_4954747).sum := by decide
  have hdescent : baseEnd_4954747 < baseStart_4954747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954767 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_4954767 : Nat := 118140960795 + 4954767 * 2 ^ 59
def prefixEnd_4954767 : Nat := 4983230072969 + 3 ^ 40 * 4954767 * 2
def baseEnd_4954767 : Nat := 2544177002035721185025947

theorem tailTrace_4954767 : CollatzResearch.WordTrace tailWord_4954767 prefixEnd_4954767 2544177002035721185025947 := by
  unfold tailWord_4954767
  simp only [CollatzResearch.WordTrace]
  refine ⟨180715198840732840678742555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120476799227155227119161703 180715198840732840678742555)
  ·
    refine ⟨271072798261099261018113833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180715198840732840678742555 271072798261099261018113833)
    ·
      refine ⟨203304598695824445763585375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271072798261099261018113833 203304598695824445763585375)
      ·
        refine ⟨304956898043736668645378063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203304598695824445763585375 304956898043736668645378063)
        ·
          refine ⟨457435347065605002968067095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304956898043736668645378063 457435347065605002968067095)
          ·
            refine ⟨686153020598407504452100643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457435347065605002968067095 686153020598407504452100643)
            ·
              refine ⟨1029229530897611256678150965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686153020598407504452100643 1029229530897611256678150965)
              ·
                refine ⟨96490268521651055313576653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1029229530897611256678150965 96490268521651055313576653)
                ·
                  refine ⟨36183850695619145742591245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96490268521651055313576653 36183850695619145742591245)
                  ·
                    refine ⟨13568944010857179653471717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36183850695619145742591245 13568944010857179653471717)
                    ·
                      refine ⟨2544177002035721185025947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13568944010857179653471717 2544177002035721185025947)
                      ·
                        rfl

theorem cell23_4954767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_4954767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954767 prefixEnd_4954767 := by exact prefixLift 4954767
  have htrace : WordTrace (prefixWord ++ tailWord_4954767) baseStart_4954767 baseEnd_4954767 := by
    simpa [prefixWord, tailWord_4954767, baseEnd_4954767] using wordTrace_append hprefix tailTrace_4954767
  have hstable : (prefixWord ++ tailWord_4954767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954767).length < 2 ^ (prefixWord ++ tailWord_4954767).sum := by decide
  have hdescent : baseEnd_4954767 < baseStart_4954767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954787 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4954787 : Nat := 118140960795 + 4954787 * 2 ^ 59
def prefixEnd_4954787 : Nat := 4983230072969 + 3 ^ 40 * 4954787 * 2
def baseEnd_4954787 : Nat := 2544187271648811106775855

theorem tailTrace_4954787 : CollatzResearch.WordTrace tailWord_4954787 prefixEnd_4954787 2544187271648811106775855 := by
  unfold tailWord_4954787
  simp only [CollatzResearch.WordTrace]
  refine ⟨180715928300660384094470615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120477285533773589396313743 180715928300660384094470615)
  ·
    refine ⟨271073892450990576141705923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180715928300660384094470615 271073892450990576141705923)
    ·
      refine ⟨406610838676485864212558885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271073892450990576141705923 406610838676485864212558885)
      ·
        refine ⟨76239532251841099539854791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 406610838676485864212558885 76239532251841099539854791)
        ·
          refine ⟨114359298377761649309782187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76239532251841099539854791 114359298377761649309782187)
          ·
            refine ⟨171538947566642473964673281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114359298377761649309782187 171538947566642473964673281)
            ·
              refine ⟨128654210674981855473504961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171538947566642473964673281 128654210674981855473504961)
              ·
                refine ⟨96490658006236391605128721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128654210674981855473504961 96490658006236391605128721)
                ·
                  refine ⟨72367993504677293703846541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96490658006236391605128721 72367993504677293703846541)
                  ·
                    refine ⟨27137997564253985138942453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72367993504677293703846541 27137997564253985138942453)
                    ·
                      refine ⟨2544187271648811106775855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27137997564253985138942453 2544187271648811106775855)
                      ·
                        rfl

theorem cell23_4954787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4954787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954787 prefixEnd_4954787 := by exact prefixLift 4954787
  have htrace : WordTrace (prefixWord ++ tailWord_4954787) baseStart_4954787 baseEnd_4954787 := by
    simpa [prefixWord, tailWord_4954787, baseEnd_4954787] using wordTrace_append hprefix tailTrace_4954787
  have hstable : (prefixWord ++ tailWord_4954787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954787).length < 2 ^ (prefixWord ++ tailWord_4954787).sum := by decide
  have hdescent : baseEnd_4954787 < baseStart_4954787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954814 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4954814 : Nat := 118140960795 + 4954814 * 2 ^ 59
def prefixEnd_4954814 : Nat := 4983230072969 + 3 ^ 40 * 4954814 * 2
def baseEnd_4954814 : Nat := 2544201135626482501138231

theorem tailTrace_4954814 : CollatzResearch.WordTrace tailWord_4954814 prefixEnd_4954814 2544201135626482501138231 := by
  unfold tailWord_4954814
  simp only [CollatzResearch.WordTrace]
  refine ⟨22589614133945320963212937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120477942047708378470468997 22589614133945320963212937)
  ·
    refine ⟨16942210600458990722409703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22589614133945320963212937 16942210600458990722409703)
    ·
      refine ⟨25413315900688486083614555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16942210600458990722409703 25413315900688486083614555)
      ·
        refine ⟨38119973851032729125421833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25413315900688486083614555 38119973851032729125421833)
        ·
          refine ⟨28589980388274546844066375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38119973851032729125421833 28589980388274546844066375)
          ·
            refine ⟨42884970582411820266099563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28589980388274546844066375 42884970582411820266099563)
            ·
              refine ⟨64327455873617730399149345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42884970582411820266099563 64327455873617730399149345)
              ·
                refine ⟨48245591905213297799362009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64327455873617730399149345 48245591905213297799362009)
                ·
                  refine ⟨36184193928909973349521507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48245591905213297799362009 36184193928909973349521507)
                  ·
                    refine ⟨54276290893364960024282261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36184193928909973349521507 54276290893364960024282261)
                    ·
                      refine ⟨2544201135626482501138231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54276290893364960024282261 2544201135626482501138231)
                      ·
                        rfl

theorem cell23_4954814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4954814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954814 prefixEnd_4954814 := by exact prefixLift 4954814
  have htrace : WordTrace (prefixWord ++ tailWord_4954814) baseStart_4954814 baseEnd_4954814 := by
    simpa [prefixWord, tailWord_4954814, baseEnd_4954814] using wordTrace_append hprefix tailTrace_4954814
  have hstable : (prefixWord ++ tailWord_4954814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954814).length < 2 ^ (prefixWord ++ tailWord_4954814).sum := by decide
  have hdescent : baseEnd_4954814 < baseStart_4954814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954888 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 1, 5]
def baseStart_4954888 : Nat := 118140960795 + 4954888 * 2 ^ 59
def prefixEnd_4954888 : Nat := 4983230072969 + 3 ^ 40 * 4954888 * 2
def baseEnd_4954888 : Nat := 848079711064971737204297

theorem tailTrace_4954888 : CollatzResearch.WordTrace tailWord_4954888 prefixEnd_4954888 848079711064971737204297 := by
  unfold tailWord_4954888
  simp only [CollatzResearch.WordTrace]
  refine ⟨90359806036647239171948659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120479741382196318895931545 90359806036647239171948659)
  ·
    refine ⟨135539709054970858757922989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90359806036647239171948659 135539709054970858757922989)
    ·
      refine ⟨50827390895614072034221121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135539709054970858757922989 50827390895614072034221121)
      ·
        refine ⟨38120543171710554025665841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50827390895614072034221121 38120543171710554025665841)
        ·
          refine ⟨28590407378782915519249381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38120543171710554025665841 28590407378782915519249381)
          ·
            refine ⟨5360701383521796659859259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28590407378782915519249381 5360701383521796659859259)
            ·
              refine ⟨8041052075282694989788889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360701383521796659859259 8041052075282694989788889)
              ·
                refine ⟨6030789056462021242341667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8041052075282694989788889 6030789056462021242341667)
                ·
                  refine ⟨9046183584693031863512501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6030789056462021242341667 9046183584693031863512501)
                  ·
                    refine ⟨848079711064971737204297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9046183584693031863512501 848079711064971737204297)
                    ·
                      rfl

theorem cell23_4954888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_4954888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954888 prefixEnd_4954888 := by exact prefixLift 4954888
  have htrace : WordTrace (prefixWord ++ tailWord_4954888) baseStart_4954888 baseEnd_4954888 := by
    simpa [prefixWord, tailWord_4954888, baseEnd_4954888] using wordTrace_append hprefix tailTrace_4954888
  have hstable : (prefixWord ++ tailWord_4954888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954888).length < 2 ^ (prefixWord ++ tailWord_4954888).sum := by decide
  have hdescent : baseEnd_4954888 < baseStart_4954888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954911 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 5]
def baseStart_4954911 : Nat := 118140960795 + 4954911 * 2 ^ 59
def prefixEnd_4954911 : Nat := 4983230072969 + 3 ^ 40 * 4954911 * 2
def baseEnd_4954911 : Nat := 2544250943249968621625285

theorem tailTrace_4954911 : CollatzResearch.WordTrace tailWord_4954911 prefixEnd_4954911 2544250943249968621625285 := by
  unfold tailWord_4954911
  simp only [CollatzResearch.WordTrace]
  refine ⟨180720450952211153271984587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120480300634807435514656391 180720450952211153271984587)
  ·
    refine ⟨271080676428316729907976881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180720450952211153271984587 271080676428316729907976881)
    ·
      refine ⟨203310507321237547430982661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271080676428316729907976881 203310507321237547430982661)
      ·
        refine ⟨38120720122732040143309249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203310507321237547430982661 38120720122732040143309249)
        ·
          refine ⟨28590540092049030107481937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38120720122732040143309249 28590540092049030107481937)
          ·
            refine ⟨21442905069036772580611453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28590540092049030107481937 21442905069036772580611453)
            ·
              refine ⟨8041089400888789717729295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21442905069036772580611453 8041089400888789717729295)
              ·
                refine ⟨12061634101333184576593943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8041089400888789717729295 12061634101333184576593943)
                ·
                  refine ⟨18092451151999776864890915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12061634101333184576593943 18092451151999776864890915)
                  ·
                    refine ⟨27138676727999665297336373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18092451151999776864890915 27138676727999665297336373)
                    ·
                      refine ⟨2544250943249968621625285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27138676727999665297336373 2544250943249968621625285)
                      ·
                        rfl

theorem cell23_4954911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_4954911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954911 prefixEnd_4954911 := by exact prefixLift 4954911
  have htrace : WordTrace (prefixWord ++ tailWord_4954911) baseStart_4954911 baseEnd_4954911 := by
    simpa [prefixWord, tailWord_4954911, baseEnd_4954911] using wordTrace_append hprefix tailTrace_4954911
  have hstable : (prefixWord ++ tailWord_4954911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954911).length < 2 ^ (prefixWord ++ tailWord_4954911).sum := by decide
  have hdescent : baseEnd_4954911 < baseStart_4954911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954914 : List Nat := [3, 3, 1, 1, 2, 13]
def baseStart_4954914 : Nat := 118140960795 + 4954914 * 2 ^ 59
def prefixEnd_4954914 : Nat := 4983230072969 + 3 ^ 40 * 4954914 * 2
def baseEnd_4954914 : Nat := 10470174830007951069497

theorem tailTrace_4954914 : CollatzResearch.WordTrace tailWord_4954914 prefixEnd_4954914 10470174830007951069497 := by
  unfold tailWord_4954914
  simp only [CollatzResearch.WordTrace]
  refine ⟨45180140092800071196085949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120480373580800189856229197 45180140092800071196085949)
  ·
    refine ⟨16942552534800026698532231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45180140092800071196085949 16942552534800026698532231)
    ·
      refine ⟨25413828802200040047798347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16942552534800026698532231 25413828802200040047798347)
      ·
        refine ⟨38120743203300060071697521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25413828802200040047798347 38120743203300060071697521)
        ·
          refine ⟨28590557402475045053773141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38120743203300060071697521 28590557402475045053773141)
          ·
            refine ⟨10470174830007951069497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 28590557402475045053773141 10470174830007951069497)
            ·
              rfl

theorem cell23_4954914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 13].length) (baseStart_4954914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954914 prefixEnd_4954914 := by exact prefixLift 4954914
  have htrace : WordTrace (prefixWord ++ tailWord_4954914) baseStart_4954914 baseEnd_4954914 := by
    simpa [prefixWord, tailWord_4954914, baseEnd_4954914] using wordTrace_append hprefix tailTrace_4954914
  have hstable : (prefixWord ++ tailWord_4954914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954914).length < 2 ^ (prefixWord ++ tailWord_4954914).sum := by decide
  have hdescent : baseEnd_4954914 < baseStart_4954914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954931 : List Nat := [1, 1, 1, 2, 6, 3, 1, 8]
def baseStart_4954931 : Nat := 118140960795 + 4954931 * 2 ^ 59
def prefixEnd_4954931 : Nat := 4983230072969 + 3 ^ 40 * 4954931 * 2
def baseEnd_4954931 : Nat := 94231896772705871976859

theorem tailTrace_4954931 : CollatzResearch.WordTrace tailWord_4954931 prefixEnd_4954931 94231896772705871976859 := by
  unfold tailWord_4954931
  simp only [CollatzResearch.WordTrace]
  refine ⟨180721180412138696687712647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120480786941425797791808431 180721180412138696687712647)
  ·
    refine ⟨271081770618208045031568971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180721180412138696687712647 271081770618208045031568971)
    ·
      refine ⟨406622655927312067547353457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271081770618208045031568971 406622655927312067547353457)
      ·
        refine ⟨304966991945484050660515093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406622655927312067547353457 304966991945484050660515093)
        ·
          refine ⟨14295327747444564874711645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 304966991945484050660515093 14295327747444564874711645)
          ·
            refine ⟨5360747905291711828016867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14295327747444564874711645 5360747905291711828016867)
            ·
              refine ⟨8041121857937567742025301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360747905291711828016867 8041121857937567742025301)
              ·
                refine ⟨94231896772705871976859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8041121857937567742025301 94231896772705871976859)
                ·
                  rfl

theorem cell23_4954931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 8].length) (baseStart_4954931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954931 prefixEnd_4954931 := by exact prefixLift 4954931
  have htrace : WordTrace (prefixWord ++ tailWord_4954931) baseStart_4954931 baseEnd_4954931 := by
    simpa [prefixWord, tailWord_4954931, baseEnd_4954931] using wordTrace_append hprefix tailTrace_4954931
  have hstable : (prefixWord ++ tailWord_4954931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954931).length < 2 ^ (prefixWord ++ tailWord_4954931).sum := by decide
  have hdescent : baseEnd_4954931 < baseStart_4954931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954938 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_4954938 : Nat := 118140960795 + 4954938 * 2 ^ 59
def prefixEnd_4954938 : Nat := 4983230072969 + 3 ^ 40 * 4954938 * 2
def baseEnd_4954938 : Nat := 2544264807227640015987661

theorem tailTrace_4954938 : CollatzResearch.WordTrace tailWord_4954938 prefixEnd_4954938 2544264807227640015987661 := by
  unfold tailWord_4954938
  simp only [CollatzResearch.WordTrace]
  refine ⟨45180358930778334220804367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120480957148742224588811645 45180358930778334220804367)
  ·
    refine ⟨67770538396167501331206551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45180358930778334220804367 67770538396167501331206551)
    ·
      refine ⟨101655807594251251996809827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67770538396167501331206551 101655807594251251996809827)
      ·
        refine ⟨152483711391376877995214741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101655807594251251996809827 152483711391376877995214741)
        ·
          refine ⟨7147673971470791156025691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152483711391376877995214741 7147673971470791156025691)
          ·
            refine ⟨10721510957206186734038537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147673971470791156025691 10721510957206186734038537)
            ·
              refine ⟨8041133217904640050528903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10721510957206186734038537 8041133217904640050528903)
              ·
                refine ⟨12061699826856960075793355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8041133217904640050528903 12061699826856960075793355)
                ·
                  refine ⟨18092549740285440113690033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12061699826856960075793355 18092549740285440113690033)
                  ·
                    refine ⟨13569412305214080085267525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18092549740285440113690033 13569412305214080085267525)
                    ·
                      refine ⟨2544264807227640015987661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13569412305214080085267525 2544264807227640015987661)
                      ·
                        rfl

theorem cell23_4954938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_4954938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954938 prefixEnd_4954938 := by exact prefixLift 4954938
  have htrace : WordTrace (prefixWord ++ tailWord_4954938) baseStart_4954938 baseEnd_4954938 := by
    simpa [prefixWord, tailWord_4954938, baseEnd_4954938] using wordTrace_append hprefix tailTrace_4954938
  have hstable : (prefixWord ++ tailWord_4954938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954938).length < 2 ^ (prefixWord ++ tailWord_4954938).sum := by decide
  have hdescent : baseEnd_4954938 < baseStart_4954938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4954942 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_4954942 : Nat := 118140960795 + 4954942 * 2 ^ 59
def prefixEnd_4954942 : Nat := 4983230072969 + 3 ^ 40 * 4954942 * 2
def baseEnd_4954942 : Nat := 2544266861150258000337643

theorem tailTrace_4954942 : CollatzResearch.WordTrace tailWord_4954942 prefixEnd_4954942 2544266861150258000337643 := by
  unfold tailWord_4954942
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590197701887355695795385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120481054410065897044242053 22590197701887355695795385)
  ·
    refine ⟨16942648276415516771846539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22590197701887355695795385 16942648276415516771846539)
    ·
      refine ⟨25413972414623275157769809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16942648276415516771846539 25413972414623275157769809)
      ·
        refine ⟨19060479310967456368327357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25413972414623275157769809 19060479310967456368327357)
        ·
          refine ⟨7147679741612796138122759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19060479310967456368327357 7147679741612796138122759)
          ·
            refine ⟨10721519612419194207184139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147679741612796138122759 10721519612419194207184139)
            ·
              refine ⟨16082279418628791310776209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10721519612419194207184139 16082279418628791310776209)
              ·
                refine ⟨12061709563971593483082157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16082279418628791310776209 12061709563971593483082157)
                ·
                  refine ⟨4523141086489347556155809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12061709563971593483082157 4523141086489347556155809)
                  ·
                    refine ⟨3392355814867010667116857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4523141086489347556155809 3392355814867010667116857)
                    ·
                      refine ⟨2544266861150258000337643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392355814867010667116857 2544266861150258000337643)
                      ·
                        rfl

theorem cell23_4954942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_4954942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4954942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4954942 prefixEnd_4954942 := by exact prefixLift 4954942
  have htrace : WordTrace (prefixWord ++ tailWord_4954942) baseStart_4954942 baseEnd_4954942 := by
    simpa [prefixWord, tailWord_4954942, baseEnd_4954942] using wordTrace_append hprefix tailTrace_4954942
  have hstable : (prefixWord ++ tailWord_4954942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4954942).length < 2 ^ (prefixWord ++ tailWord_4954942).sum := by decide
  have hdescent : baseEnd_4954942 < baseStart_4954942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4954942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955010 : List Nat := [3, 4, 2, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4955010 : Nat := 118140960795 + 4955010 * 2 ^ 59
def prefixEnd_4955010 : Nat := 4983230072969 + 3 ^ 40 * 4955010 * 2
def baseEnd_4955010 : Nat := 2544301777834763734287331

theorem tailTrace_4955010 : CollatzResearch.WordTrace tailWord_4955010 prefixEnd_4955010 2544301777834763734287331 := by
  unfold tailWord_4955010
  simp only [CollatzResearch.WordTrace]
  refine ⟨45181015444713123294959621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120482707852568328786558989 45181015444713123294959621)
  ·
    refine ⟨8471440395883710617804929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45181015444713123294959621 8471440395883710617804929)
    ·
      refine ⟨6353580296912782963353697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8471440395883710617804929 6353580296912782963353697)
      ·
        refine ⟨4765185222684587222515273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6353580296912782963353697 4765185222684587222515273)
        ·
          refine ⟨3573888917013440416886455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4765185222684587222515273 3573888917013440416886455)
          ·
            refine ⟨5360833375520160625329683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573888917013440416886455 5360833375520160625329683)
            ·
              refine ⟨8041250063280240937994525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5360833375520160625329683 8041250063280240937994525)
              ·
                refine ⟨3015468773730090351747947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8041250063280240937994525 3015468773730090351747947)
                ·
                  refine ⟨4523203160595135527621921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015468773730090351747947 4523203160595135527621921)
                  ·
                    refine ⟨3392402370446351645716441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4523203160595135527621921 3392402370446351645716441)
                    ·
                      refine ⟨2544301777834763734287331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392402370446351645716441 2544301777834763734287331)
                      ·
                        rfl

theorem cell23_4955010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4955010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955010 prefixEnd_4955010 := by exact prefixLift 4955010
  have htrace : WordTrace (prefixWord ++ tailWord_4955010) baseStart_4955010 baseEnd_4955010 := by
    simpa [prefixWord, tailWord_4955010, baseEnd_4955010] using wordTrace_append hprefix tailTrace_4955010
  have hstable : (prefixWord ++ tailWord_4955010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955010).length < 2 ^ (prefixWord ++ tailWord_4955010).sum := by decide
  have hdescent : baseEnd_4955010 < baseStart_4955010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955015 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_4955015 : Nat := 118140960795 + 4955015 * 2 ^ 59
def prefixEnd_4955015 : Nat := 4983230072969 + 3 ^ 40 * 4955015 * 2
def baseEnd_4955015 : Nat := 2544304345238036214724807

theorem tailTrace_4955015 : CollatzResearch.WordTrace tailWord_4955015 prefixEnd_4955015 2544304345238036214724807 := by
  unfold tailWord_4955015
  simp only [CollatzResearch.WordTrace]
  refine ⟨180724244143834379033770499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120482829429222919355846999 180724244143834379033770499)
  ·
    refine ⟨271086366215751568550655749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180724244143834379033770499 271086366215751568550655749)
    ·
      refine ⟨50828693665453419103247953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271086366215751568550655749 50828693665453419103247953)
      ·
        refine ⟨38121520249090064327435965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50828693665453419103247953 38121520249090064327435965)
        ·
          refine ⟨14295570093408774122788487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38121520249090064327435965 14295570093408774122788487)
          ·
            refine ⟨21443355140113161184182731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14295570093408774122788487 21443355140113161184182731)
            ·
              refine ⟨32165032710169741776274097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21443355140113161184182731 32165032710169741776274097)
              ·
                refine ⟨24123774532627306332205573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32165032710169741776274097 24123774532627306332205573)
                ·
                  refine ⟨4523207724867619937288545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24123774532627306332205573 4523207724867619937288545)
                  ·
                    refine ⟨3392405793650714952966409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4523207724867619937288545 3392405793650714952966409)
                    ·
                      refine ⟨2544304345238036214724807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392405793650714952966409 2544304345238036214724807)
                      ·
                        rfl

theorem cell23_4955015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_4955015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955015 prefixEnd_4955015 := by exact prefixLift 4955015
  have htrace : WordTrace (prefixWord ++ tailWord_4955015) baseStart_4955015 baseEnd_4955015 := by
    simpa [prefixWord, tailWord_4955015, baseEnd_4955015] using wordTrace_append hprefix tailTrace_4955015
  have hstable : (prefixWord ++ tailWord_4955015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955015).length < 2 ^ (prefixWord ++ tailWord_4955015).sum := by decide
  have hdescent : baseEnd_4955015 < baseStart_4955015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955018 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4955018 : Nat := 118140960795 + 4955018 * 2 ^ 59
def prefixEnd_4955018 : Nat := 4983230072969 + 3 ^ 40 * 4955018 * 2
def baseEnd_4955018 : Nat := 2544305885679999702987293

theorem tailTrace_4955018 : CollatzResearch.WordTrace tailWord_4955018 prefixEnd_4955018 2544305885679999702987293 := by
  unfold tailWord_4955018
  simp only [CollatzResearch.WordTrace]
  refine ⟨45181088390705877636532427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120482902375215673697419805 45181088390705877636532427)
  ·
    refine ⟨67771632586058816454798641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45181088390705877636532427 67771632586058816454798641)
    ·
      refine ⟨50828724439544112341098981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67771632586058816454798641 50828724439544112341098981)
      ·
        refine ⟨9530385832414521063956059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50828724439544112341098981 9530385832414521063956059)
        ·
          refine ⟨14295578748621781595934089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9530385832414521063956059 14295578748621781595934089)
          ·
            refine ⟨10721684061466336196950567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14295578748621781595934089 10721684061466336196950567)
            ·
              refine ⟨16082526092199504295425851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10721684061466336196950567 16082526092199504295425851)
              ·
                refine ⟨24123789138299256443138777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16082526092199504295425851 24123789138299256443138777)
                ·
                  refine ⟨18092841853724442332354083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24123789138299256443138777 18092841853724442332354083)
                  ·
                    refine ⟨27139262780586663498531125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18092841853724442332354083 27139262780586663498531125)
                    ·
                      refine ⟨2544305885679999702987293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27139262780586663498531125 2544305885679999702987293)
                      ·
                        rfl

theorem cell23_4955018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4955018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955018 prefixEnd_4955018 := by exact prefixLift 4955018
  have htrace : WordTrace (prefixWord ++ tailWord_4955018) baseStart_4955018 baseEnd_4955018 := by
    simpa [prefixWord, tailWord_4955018, baseEnd_4955018] using wordTrace_append hprefix tailTrace_4955018
  have hstable : (prefixWord ++ tailWord_4955018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955018).length < 2 ^ (prefixWord ++ tailWord_4955018).sum := by decide
  have hdescent : baseEnd_4955018 < baseStart_4955018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955024 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_4955024 : Nat := 118140960795 + 4955024 * 2 ^ 59
def prefixEnd_4955024 : Nat := 4983230072969 + 3 ^ 40 * 4955024 * 2
def baseEnd_4955024 : Nat := 2544308966563926679512265

theorem tailTrace_4955024 : CollatzResearch.WordTrace tailWord_4955024 prefixEnd_4955024 2544308966563926679512265 := by
  unfold tailWord_4955024
  simp only [CollatzResearch.WordTrace]
  refine ⟨90362286200400886785424063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120483048267201182380565417 90362286200400886785424063)
  ·
    refine ⟨135543429300601330178136095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90362286200400886785424063 135543429300601330178136095)
    ·
      refine ⟨203315143950901995267204143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135543429300601330178136095 203315143950901995267204143)
      ·
        refine ⟨304972715926352992900806215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203315143950901995267204143 304972715926352992900806215)
        ·
          refine ⟨457459073889529489351209323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304972715926352992900806215 457459073889529489351209323)
          ·
            refine ⟨686188610834294234026813985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457459073889529489351209323 686188610834294234026813985)
            ·
              refine ⟨514641458125720675520110489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686188610834294234026813985 514641458125720675520110489)
              ·
                refine ⟨385981093594290506640082867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514641458125720675520110489 385981093594290506640082867)
                ·
                  refine ⟨578971640391435759960124301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385981093594290506640082867 578971640391435759960124301)
                  ·
                    refine ⟨217114365146788409985046613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578971640391435759960124301 217114365146788409985046613)
                    ·
                      refine ⟨2544308966563926679512265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 217114365146788409985046613 2544308966563926679512265)
                      ·
                        rfl

theorem cell23_4955024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_4955024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955024 prefixEnd_4955024 := by exact prefixLift 4955024
  have htrace : WordTrace (prefixWord ++ tailWord_4955024) baseStart_4955024 baseEnd_4955024 := by
    simpa [prefixWord, tailWord_4955024, baseEnd_4955024] using wordTrace_append hprefix tailTrace_4955024
  have hstable : (prefixWord ++ tailWord_4955024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955024).length < 2 ^ (prefixWord ++ tailWord_4955024).sum := by decide
  have hdescent : baseEnd_4955024 < baseStart_4955024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955061 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4955061 : Nat := 118140960795 + 4955061 * 2 ^ 59
def prefixEnd_4955061 : Nat := 4983230072969 + 3 ^ 40 * 4955061 * 2
def baseEnd_4955061 : Nat := 2544327965348143034749595

theorem tailTrace_4955061 : CollatzResearch.WordTrace tailWord_4955061 prefixEnd_4955061 2544327965348143034749595 := by
  unfold tailWord_4955061
  simp only [CollatzResearch.WordTrace]
  refine ⟨180725921901667728889945037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120483947934445152593296691 180725921901667728889945037)
  ·
    refine ⟨67772220713125398333729389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180725921901667728889945037 67772220713125398333729389)
    ·
      refine ⟨25414582767422024375148521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67772220713125398333729389 25414582767422024375148521)
      ·
        refine ⟨19060937075566518281361391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25414582767422024375148521 19060937075566518281361391)
        ·
          refine ⟨28591405613349777422042087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19060937075566518281361391 28591405613349777422042087)
          ·
            refine ⟨42887108420024666133063131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28591405613349777422042087 42887108420024666133063131)
            ·
              refine ⟨64330662630036999199594697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42887108420024666133063131 64330662630036999199594697)
              ·
                refine ⟨48247996972527749399696023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64330662630036999199594697 48247996972527749399696023)
                ·
                  refine ⟨72371995458791624099544035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48247996972527749399696023 72371995458791624099544035)
                  ·
                    refine ⟨108557993188187436149316053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72371995458791624099544035 108557993188187436149316053)
                    ·
                      refine ⟨2544327965348143034749595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108557993188187436149316053 2544327965348143034749595)
                      ·
                        rfl

theorem cell23_4955061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4955061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955061 prefixEnd_4955061 := by exact prefixLift 4955061
  have htrace : WordTrace (prefixWord ++ tailWord_4955061) baseStart_4955061 baseEnd_4955061 := by
    simpa [prefixWord, tailWord_4955061, baseEnd_4955061] using wordTrace_append hprefix tailTrace_4955061
  have hstable : (prefixWord ++ tailWord_4955061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955061).length < 2 ^ (prefixWord ++ tailWord_4955061).sum := by decide
  have hdescent : baseEnd_4955061 < baseStart_4955061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955088 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 2, 4, 2]
def baseStart_4955088 : Nat := 118140960795 + 4955088 * 2 ^ 59
def prefixEnd_4955088 : Nat := 4983230072969 + 3 ^ 40 * 4955088 * 2
def baseEnd_4955088 : Nat := 2544341829325814429111971

theorem tailTrace_4955088 : CollatzResearch.WordTrace tailWord_4955088 prefixEnd_4955088 2544341829325814429111971 := by
  unfold tailWord_4955088
  simp only [CollatzResearch.WordTrace]
  refine ⟨90363453336284956250588959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120484604448379941667451945 90363453336284956250588959)
  ·
    refine ⟨135545180004427434375883439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90363453336284956250588959 135545180004427434375883439)
    ·
      refine ⟨203317770006641151563825159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135545180004427434375883439 203317770006641151563825159)
      ·
        refine ⟨304976655009961727345737739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203317770006641151563825159 304976655009961727345737739)
        ·
          refine ⟨457464982514942591018606609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304976655009961727345737739 457464982514942591018606609)
          ·
            refine ⟨343098736886206943263954957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457464982514942591018606609 343098736886206943263954957)
            ·
              refine ⟨128662026332327603723983109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343098736886206943263954957 128662026332327603723983109)
              ·
                refine ⟨24124129937311425698246833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128662026332327603723983109 24124129937311425698246833)
                ·
                  refine ⟨18093097452983569273685125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24124129937311425698246833 18093097452983569273685125)
                  ·
                    refine ⟨3392455772434419238815961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18093097452983569273685125 3392455772434419238815961)
                    ·
                      refine ⟨2544341829325814429111971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392455772434419238815961 2544341829325814429111971)
                      ·
                        rfl

theorem cell23_4955088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 4, 2].length) (baseStart_4955088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955088 prefixEnd_4955088 := by exact prefixLift 4955088
  have htrace : WordTrace (prefixWord ++ tailWord_4955088) baseStart_4955088 baseEnd_4955088 := by
    simpa [prefixWord, tailWord_4955088, baseEnd_4955088] using wordTrace_append hprefix tailTrace_4955088
  have hstable : (prefixWord ++ tailWord_4955088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955088).length < 2 ^ (prefixWord ++ tailWord_4955088).sum := by decide
  have hdescent : baseEnd_4955088 < baseStart_4955088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955132 : List Nat := [2, 2, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_4955132 : Nat := 118140960795 + 4955132 * 2 ^ 59
def prefixEnd_4955132 : Nat := 4983230072969 + 3 ^ 40 * 4955132 * 2
def baseEnd_4955132 : Nat := 848121474158204085653923

theorem tailTrace_4955132 : CollatzResearch.WordTrace tailWord_4955132 prefixEnd_4955132 848121474158204085653923 := by
  unfold tailWord_4955132
  simp only [CollatzResearch.WordTrace]
  refine ⟨90364255742205254007889825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120485674322940338677186433 90364255742205254007889825)
  ·
    refine ⟨67773191806653940505917369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90364255742205254007889825 67773191806653940505917369)
    ·
      refine ⟨50829893854990455379438027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67773191806653940505917369 50829893854990455379438027)
      ·
        refine ⟨76244840782485683069157041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50829893854990455379438027 76244840782485683069157041)
        ·
          refine ⟨57183630586864262301867781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76244840782485683069157041 57183630586864262301867781)
          ·
            refine ⟨10721930735037049181600209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57183630586864262301867781 10721930735037049181600209)
            ·
              refine ⟨8041448051277786886200157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10721930735037049181600209 8041448051277786886200157)
              ·
                refine ⟨3015543019229170082325059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8041448051277786886200157 3015543019229170082325059)
                ·
                  refine ⟨4523314528843755123487589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015543019229170082325059 4523314528843755123487589)
                  ·
                    refine ⟨848121474158204085653923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4523314528843755123487589 848121474158204085653923)
                    ·
                      rfl

theorem cell23_4955132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_4955132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955132 prefixEnd_4955132 := by exact prefixLift 4955132
  have htrace : WordTrace (prefixWord ++ tailWord_4955132) baseStart_4955132 baseEnd_4955132 := by
    simpa [prefixWord, tailWord_4955132, baseEnd_4955132] using wordTrace_append hprefix tailTrace_4955132
  have hstable : (prefixWord ++ tailWord_4955132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955132).length < 2 ^ (prefixWord ++ tailWord_4955132).sum := by decide
  have hdescent : baseEnd_4955132 < baseStart_4955132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955172 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4955172 : Nat := 118140960795 + 4955172 * 2 ^ 59
def prefixEnd_4955172 : Nat := 4983230072969 + 3 ^ 40 * 4955172 * 2
def baseEnd_4955172 : Nat := 2544384961700792100461585

theorem tailTrace_4955172 : CollatzResearch.WordTrace tailWord_4955172 prefixEnd_4955172 2544384961700792100461585 := by
  unfold tailWord_4955172
  simp only [CollatzResearch.WordTrace]
  refine ⟨90364985202132797423617885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120486646936177063231490513 90364985202132797423617885)
  ·
    refine ⟨33886869450799799033856707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90364985202132797423617885 33886869450799799033856707)
    ·
      refine ⟨50830304176199698550785061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33886869450799799033856707 50830304176199698550785061)
      ·
        refine ⟨9530682033037443478272199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50830304176199698550785061 9530682033037443478272199)
        ·
          refine ⟨14296023049556165217408299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9530682033037443478272199 14296023049556165217408299)
          ·
            refine ⟨21444034574334247826112449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14296023049556165217408299 21444034574334247826112449)
            ·
              refine ⟨16083025930750685869584337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21444034574334247826112449 16083025930750685869584337)
              ·
                refine ⟨12062269448063014402188253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16083025930750685869584337 12062269448063014402188253)
                ·
                  refine ⟨4523351043023630400820595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12062269448063014402188253 4523351043023630400820595)
                  ·
                    refine ⟨6785026564535445601230893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4523351043023630400820595 6785026564535445601230893)
                    ·
                      refine ⟨2544384961700792100461585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6785026564535445601230893 2544384961700792100461585)
                      ·
                        rfl

theorem cell23_4955172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4955172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955172 prefixEnd_4955172 := by exact prefixLift 4955172
  have htrace : WordTrace (prefixWord ++ tailWord_4955172) baseStart_4955172 baseEnd_4955172 := by
    simpa [prefixWord, tailWord_4955172, baseEnd_4955172] using wordTrace_append hprefix tailTrace_4955172
  have hstable : (prefixWord ++ tailWord_4955172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955172).length < 2 ^ (prefixWord ++ tailWord_4955172).sum := by decide
  have hdescent : baseEnd_4955172 < baseStart_4955172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955182 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_4955182 : Nat := 118140960795 + 4955182 * 2 ^ 59
def prefixEnd_4955182 : Nat := 4983230072969 + 3 ^ 40 * 4955182 * 2
def baseEnd_4955182 : Nat := 2544390096507337061336539

theorem tailTrace_4955182 : CollatzResearch.WordTrace tailWord_4955182 prefixEnd_4955182 2544390096507337061336539 := by
  unfold tailWord_4955182
  simp only [CollatzResearch.WordTrace]
  refine ⟨22591291891778670819387475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120486890089486244370066533 22591291891778670819387475)
  ·
    refine ⟨33886937837668006229081213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22591291891778670819387475 33886937837668006229081213)
    ·
      refine ⟨12707601689125502335905455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33886937837668006229081213 12707601689125502335905455)
      ·
        refine ⟨19061402533688253503858183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12707601689125502335905455 19061402533688253503858183)
        ·
          refine ⟨28592103800532380255787275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19061402533688253503858183 28592103800532380255787275)
          ·
            refine ⟨42888155700798570383680913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28592103800532380255787275 42888155700798570383680913)
            ·
              refine ⟨32166116775598927787760685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42888155700798570383680913 32166116775598927787760685)
              ·
                refine ⟨12062293790849597920410257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32166116775598927787760685 12062293790849597920410257)
                ·
                  refine ⟨9046720343137198440307693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12062293790849597920410257 9046720343137198440307693)
                  ·
                    refine ⟨3392520128676449415115385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9046720343137198440307693 3392520128676449415115385)
                    ·
                      refine ⟨2544390096507337061336539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392520128676449415115385 2544390096507337061336539)
                      ·
                        rfl

theorem cell23_4955182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_4955182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955182 prefixEnd_4955182 := by exact prefixLift 4955182
  have htrace : WordTrace (prefixWord ++ tailWord_4955182) baseStart_4955182 baseEnd_4955182 := by
    simpa [prefixWord, tailWord_4955182, baseEnd_4955182] using wordTrace_append hprefix tailTrace_4955182
  have hstable : (prefixWord ++ tailWord_4955182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955182).length < 2 ^ (prefixWord ++ tailWord_4955182).sum := by decide
  have hdescent : baseEnd_4955182 < baseStart_4955182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955206 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_4955206 : Nat := 118140960795 + 4955206 * 2 ^ 59
def prefixEnd_4955206 : Nat := 4983230072969 + 3 ^ 40 * 4955206 * 2
def baseEnd_4955206 : Nat := 2544402420043044967436429

theorem tailTrace_4955206 : CollatzResearch.WordTrace tailWord_4955206 prefixEnd_4955206 2544402420043044967436429 := by
  unfold tailWord_4955206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647850327691950582936671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120487473657428279102648981 5647850327691950582936671)
  ·
    refine ⟨8471775491537925874405007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5647850327691950582936671 8471775491537925874405007)
    ·
      refine ⟨12707663237306888811607511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8471775491537925874405007 12707663237306888811607511)
      ·
        refine ⟨19061494855960333217411267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12707663237306888811607511 19061494855960333217411267)
        ·
          refine ⟨28592242283940499826116901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19061494855960333217411267 28592242283940499826116901)
          ·
            refine ⟨5361045428238843717396919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28592242283940499826116901 5361045428238843717396919)
            ·
              refine ⟨8041568142358265576095379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361045428238843717396919 8041568142358265576095379)
              ·
                refine ⟨12062352213537398364143069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8041568142358265576095379 12062352213537398364143069)
                ·
                  refine ⟨4523382080076524386553651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12062352213537398364143069 4523382080076524386553651)
                  ·
                    refine ⟨6785073120114786579830477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4523382080076524386553651 6785073120114786579830477)
                    ·
                      refine ⟨2544402420043044967436429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6785073120114786579830477 2544402420043044967436429)
                      ·
                        rfl

theorem cell23_4955206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_4955206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955206 prefixEnd_4955206 := by exact prefixLift 4955206
  have htrace : WordTrace (prefixWord ++ tailWord_4955206) baseStart_4955206 baseEnd_4955206 := by
    simpa [prefixWord, tailWord_4955206, baseEnd_4955206] using wordTrace_append hprefix tailTrace_4955206
  have hstable : (prefixWord ++ tailWord_4955206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955206).length < 2 ^ (prefixWord ++ tailWord_4955206).sum := by decide
  have hdescent : baseEnd_4955206 < baseStart_4955206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955211 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7]
def baseStart_4955211 : Nat := 118140960795 + 4955211 * 2 ^ 59
def prefixEnd_4955211 : Nat := 4983230072969 + 3 ^ 40 * 4955211 * 2
def baseEnd_4955211 : Nat := 2544404987446317447873905

theorem tailTrace_4955211 : CollatzResearch.WordTrace tailWord_4955211 prefixEnd_4955211 2544404987446317447873905 := by
  unfold tailWord_4955211
  simp only [CollatzResearch.WordTrace]
  refine ⟨180731392851124304507905487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120487595234082869671936991 180731392851124304507905487)
  ·
    refine ⟨271097089276686456761858231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180731392851124304507905487 271097089276686456761858231)
    ·
      refine ⟨406645633915029685142787347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271097089276686456761858231 406645633915029685142787347)
      ·
        refine ⟨609968450872544527714181021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406645633915029685142787347 609968450872544527714181021)
        ·
          refine ⟨228738169077204197892817883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609968450872544527714181021 228738169077204197892817883)
          ·
            refine ⟨343107253615806296839226825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228738169077204197892817883 343107253615806296839226825)
            ·
              refine ⟨257330440211854722629420119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343107253615806296839226825 257330440211854722629420119)
              ·
                refine ⟨385995660317782083944130179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257330440211854722629420119 385995660317782083944130179)
                ·
                  refine ⟨578993490476673125916195269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385995660317782083944130179 578993490476673125916195269)
                  ·
                    refine ⟨108561279464376211109286613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578993490476673125916195269 108561279464376211109286613)
                    ·
                      refine ⟨2544404987446317447873905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108561279464376211109286613 2544404987446317447873905)
                      ·
                        rfl

theorem cell23_4955211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_4955211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955211 prefixEnd_4955211 := by exact prefixLift 4955211
  have htrace : WordTrace (prefixWord ++ tailWord_4955211) baseStart_4955211 baseEnd_4955211 := by
    simpa [prefixWord, tailWord_4955211, baseEnd_4955211] using wordTrace_append hprefix tailTrace_4955211
  have hstable : (prefixWord ++ tailWord_4955211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955211).length < 2 ^ (prefixWord ++ tailWord_4955211).sum := by decide
  have hdescent : baseEnd_4955211 < baseStart_4955211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955218 : List Nat := [3, 2, 2, 1, 3, 1, 1, 10]
def baseStart_4955218 : Nat := 118140960795 + 4955218 * 2 ^ 59
def prefixEnd_4955218 : Nat := 4983230072969 + 3 ^ 40 * 4955218 * 2
def baseEnd_4955218 : Nat := 94237354881885145203199

theorem tailTrace_4955218 : CollatzResearch.WordTrace tailWord_4955218 prefixEnd_4955218 94237354881885145203199 := by
  unfold tailWord_4955218
  simp only [CollatzResearch.WordTrace]
  refine ⟨45182912040524736175852577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120487765441399296468940205 45182912040524736175852577)
  ·
    refine ⟨33887184030393552131889433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45182912040524736175852577 33887184030393552131889433)
    ·
      refine ⟨25415388022795164098917075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33887184030393552131889433 25415388022795164098917075)
      ·
        refine ⟨38123082034192746148375613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25415388022795164098917075 38123082034192746148375613)
        ·
          refine ⟨14296155762822279805640855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38123082034192746148375613 14296155762822279805640855)
          ·
            refine ⟨21444233644233419708461283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14296155762822279805640855 21444233644233419708461283)
            ·
              refine ⟨32166350466350129562691925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21444233644233419708461283 32166350466350129562691925)
              ·
                refine ⟨94237354881885145203199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32166350466350129562691925 94237354881885145203199)
                ·
                  rfl

theorem cell23_4955218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 10].length) (baseStart_4955218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955218 prefixEnd_4955218 := by exact prefixLift 4955218
  have htrace : WordTrace (prefixWord ++ tailWord_4955218) baseStart_4955218 baseEnd_4955218 := by
    simpa [prefixWord, tailWord_4955218, baseEnd_4955218] using wordTrace_append hprefix tailTrace_4955218
  have hstable : (prefixWord ++ tailWord_4955218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955218).length < 2 ^ (prefixWord ++ tailWord_4955218).sum := by decide
  have hdescent : baseEnd_4955218 < baseStart_4955218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955245 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_4955245 : Nat := 118140960795 + 4955245 * 2 ^ 59
def prefixEnd_4955245 : Nat := 4983230072969 + 3 ^ 40 * 4955245 * 2
def baseEnd_4955245 : Nat := 2544422445788570314848749

theorem tailTrace_4955245 : CollatzResearch.WordTrace tailWord_4955245 prefixEnd_4955245 2544422445788570314848749 := by
  unfold tailWord_4955245
  simp only [CollatzResearch.WordTrace]
  refine ⟨180732632933001128314643189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120488421955334085543095459 180732632933001128314643189)
  ·
    refine ⟨16943684337468855779497799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180732632933001128314643189 16943684337468855779497799)
    ·
      refine ⟨25415526506203283669246699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16943684337468855779497799 25415526506203283669246699)
      ·
        refine ⟨38123289759304925503870049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25415526506203283669246699 38123289759304925503870049)
        ·
          refine ⟨28592467319478694127902537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38123289759304925503870049 28592467319478694127902537)
          ·
            refine ⟨21444350489609020595926903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28592467319478694127902537 21444350489609020595926903)
            ·
              refine ⟨32166525734413530893890355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21444350489609020595926903 32166525734413530893890355)
              ·
                refine ⟨48249788601620296340835533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32166525734413530893890355 48249788601620296340835533)
                ·
                  refine ⟨18093670725607611127813325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48249788601620296340835533 18093670725607611127813325)
                  ·
                    refine ⟨6785126522102854172929997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18093670725607611127813325 6785126522102854172929997)
                    ·
                      refine ⟨2544422445788570314848749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6785126522102854172929997 2544422445788570314848749)
                      ·
                        rfl

theorem cell23_4955245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_4955245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955245 prefixEnd_4955245 := by exact prefixLift 4955245
  have htrace : WordTrace (prefixWord ++ tailWord_4955245) baseStart_4955245 baseEnd_4955245 := by
    simpa [prefixWord, tailWord_4955245, baseEnd_4955245] using wordTrace_append hprefix tailTrace_4955245
  have hstable : (prefixWord ++ tailWord_4955245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955245).length < 2 ^ (prefixWord ++ tailWord_4955245).sum := by decide
  have hdescent : baseEnd_4955245 < baseStart_4955245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955306 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4955306 : Nat := 118140960795 + 4955306 * 2 ^ 59
def prefixEnd_4955306 : Nat := 4983230072969 + 3 ^ 40 * 4955306 * 2
def baseEnd_4955306 : Nat := 2544453768108494576185969

theorem tailTrace_4955306 : CollatzResearch.WordTrace tailWord_4955306 prefixEnd_4955306 2544453768108494576185969 := by
  unfold tailWord_4955306
  simp only [CollatzResearch.WordTrace]
  refine ⟨45183714446445033933153443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120489905190520090488409181 45183714446445033933153443)
  ·
    refine ⟨67775571669667550899730165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45183714446445033933153443 67775571669667550899730165)
    ·
      refine ⟨6353959844031332896849703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67775571669667550899730165 6353959844031332896849703)
      ·
        refine ⟨9530939766046999345274555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353959844031332896849703 9530939766046999345274555)
        ·
          refine ⟨14296409649070499017911833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9530939766046999345274555 14296409649070499017911833)
          ·
            refine ⟨10722307236802874263433875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14296409649070499017911833 10722307236802874263433875)
            ·
              refine ⟨16083460855204311395150813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10722307236802874263433875 16083460855204311395150813)
              ·
                refine ⟨6031297820701616773181555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16083460855204311395150813 6031297820701616773181555)
                ·
                  refine ⟨9046946731052425159772333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6031297820701616773181555 9046946731052425159772333)
                  ·
                    refine ⟨3392605024144659434914625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9046946731052425159772333 3392605024144659434914625)
                    ·
                      refine ⟨2544453768108494576185969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392605024144659434914625 2544453768108494576185969)
                      ·
                        rfl

theorem cell23_4955306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4955306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955306 prefixEnd_4955306 := by exact prefixLift 4955306
  have htrace : WordTrace (prefixWord ++ tailWord_4955306) baseStart_4955306 baseEnd_4955306 := by
    simpa [prefixWord, tailWord_4955306, baseEnd_4955306] using wordTrace_append hprefix tailTrace_4955306
  have hstable : (prefixWord ++ tailWord_4955306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955306).length < 2 ^ (prefixWord ++ tailWord_4955306).sum := by decide
  have hdescent : baseEnd_4955306 < baseStart_4955306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955330 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_4955330 : Nat := 118140960795 + 4955330 * 2 ^ 59
def prefixEnd_4955330 : Nat := 4983230072969 + 3 ^ 40 * 4955330 * 2
def baseEnd_4955330 : Nat := 2544466091644202482285859

theorem tailTrace_4955330 : CollatzResearch.WordTrace tailWord_4955330 prefixEnd_4955330 2544466091644202482285859 := by
  unfold tailWord_4955330
  simp only [CollatzResearch.WordTrace]
  refine ⟨45183933284423296957871861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120490488758462125220991629 45183933284423296957871861)
  ·
    refine ⟨4235993745414684089800487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45183933284423296957871861 4235993745414684089800487)
    ·
      refine ⟨6353990618122026134700731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235993745414684089800487 6353990618122026134700731)
      ·
        refine ⟨9530985927183039202051097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353990618122026134700731 9530985927183039202051097)
        ·
          refine ⟨7148239445387279401538323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9530985927183039202051097 7148239445387279401538323)
          ·
            refine ⟨10722359168080919102307485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7148239445387279401538323 10722359168080919102307485)
            ·
              refine ⟨4020884688030344663365307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10722359168080919102307485 4020884688030344663365307)
              ·
                refine ⟨6031327032045516995047961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020884688030344663365307 6031327032045516995047961)
                ·
                  refine ⟨4523495274034137746285971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6031327032045516995047961 4523495274034137746285971)
                  ·
                    refine ⟨6785242911051206619428957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4523495274034137746285971 6785242911051206619428957)
                    ·
                      refine ⟨2544466091644202482285859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6785242911051206619428957 2544466091644202482285859)
                      ·
                        rfl

theorem cell23_4955330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_4955330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955330 prefixEnd_4955330 := by exact prefixLift 4955330
  have htrace : WordTrace (prefixWord ++ tailWord_4955330) baseStart_4955330 baseEnd_4955330 := by
    simpa [prefixWord, tailWord_4955330, baseEnd_4955330] using wordTrace_append hprefix tailTrace_4955330
  have hstable : (prefixWord ++ tailWord_4955330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955330).length < 2 ^ (prefixWord ++ tailWord_4955330).sum := by decide
  have hdescent : baseEnd_4955330 < baseStart_4955330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955432 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 6]
def baseStart_4955432 : Nat := 118140960795 + 4955432 * 2 ^ 59
def prefixEnd_4955432 : Nat := 4983230072969 + 3 ^ 40 * 4955432 * 2
def baseEnd_4955432 : Nat := 282724274074551231467821

theorem tailTrace_4955432 : CollatzResearch.WordTrace tailWord_4955432 prefixEnd_4955432 282724274074551231467821 := by
  unfold tailWord_4955432
  simp only [CollatzResearch.WordTrace]
  refine ⟨90369726691661829625850275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120492968922215772834467033 90369726691661829625850275)
  ·
    refine ⟨135554590037492744438775413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90369726691661829625850275 135554590037492744438775413)
    ·
      refine ⟨12708242816014944791135195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135554590037492744438775413 12708242816014944791135195)
      ·
        refine ⟨19062364224022417186702793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12708242816014944791135195 19062364224022417186702793)
        ·
          refine ⟨14296773168016812890027095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19062364224022417186702793 14296773168016812890027095)
          ·
            refine ⟨21445159752025219335040643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14296773168016812890027095 21445159752025219335040643)
            ·
              refine ⟨32167739628037829002560965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21445159752025219335040643 32167739628037829002560965)
              ·
                refine ⟨6031451180257092937980181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32167739628037829002560965 6031451180257092937980181)
                ·
                  refine ⟨282724274074551231467821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6031451180257092937980181 282724274074551231467821)
                  ·
                    rfl

theorem cell23_4955432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 6].length) (baseStart_4955432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955432 prefixEnd_4955432 := by exact prefixLift 4955432
  have htrace : WordTrace (prefixWord ++ tailWord_4955432) baseStart_4955432 baseEnd_4955432 := by
    simpa [prefixWord, tailWord_4955432, baseEnd_4955432] using wordTrace_append hprefix tailTrace_4955432
  have hstable : (prefixWord ++ tailWord_4955432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955432).length < 2 ^ (prefixWord ++ tailWord_4955432).sum := by decide
  have hdescent : baseEnd_4955432 < baseStart_4955432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955475 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 1, 6]
def baseStart_4955475 : Nat := 118140960795 + 4955475 * 2 ^ 59
def prefixEnd_4955475 : Nat := 4983230072969 + 3 ^ 40 * 4955475 * 2
def baseEnd_4955475 : Nat := 848180182113034804990897

theorem tailTrace_4955475 : CollatzResearch.WordTrace tailWord_4955475 prefixEnd_4955475 848180182113034804990897 := by
  unfold tailWord_4955475
  simp only [CollatzResearch.WordTrace]
  refine ⟨180741021722167877595515879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120494014481445251730343919 180741021722167877595515879)
  ·
    refine ⟨271111532583251816393273819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180741021722167877595515879 271111532583251816393273819)
    ·
      refine ⟨406667298874877724589910729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271111532583251816393273819 406667298874877724589910729)
      ·
        refine ⟨305000474156158293442433047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406667298874877724589910729 305000474156158293442433047)
        ·
          refine ⟨457500711234237440163649571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305000474156158293442433047 457500711234237440163649571)
          ·
            refine ⟨686251066851356160245474357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457500711234237440163649571 686251066851356160245474357)
            ·
              refine ⟨64336037517314640023013221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 686251066851356160245474357 64336037517314640023013221)
              ·
                refine ⟨12063007034496495004314979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64336037517314640023013221 12063007034496495004314979)
                ·
                  refine ⟨18094510551744742506472469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12063007034496495004314979 18094510551744742506472469)
                  ·
                    refine ⟨848180182113034804990897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18094510551744742506472469 848180182113034804990897)
                    ·
                      rfl

theorem cell23_4955475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 6].length) (baseStart_4955475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955475 prefixEnd_4955475 := by exact prefixLift 4955475
  have htrace : WordTrace (prefixWord ++ tailWord_4955475) baseStart_4955475 baseEnd_4955475 := by
    simpa [prefixWord, tailWord_4955475, baseEnd_4955475] using wordTrace_append hprefix tailTrace_4955475
  have hstable : (prefixWord ++ tailWord_4955475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955475).length < 2 ^ (prefixWord ++ tailWord_4955475).sum := by decide
  have hdescent : baseEnd_4955475 < baseStart_4955475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955479 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 1, 5]
def baseStart_4955479 : Nat := 118140960795 + 4955479 * 2 ^ 59
def prefixEnd_4955479 : Nat := 4983230072969 + 3 ^ 40 * 4955479 * 2
def baseEnd_4955479 : Nat := 848180866753907466440891

theorem tailTrace_4955479 : CollatzResearch.WordTrace tailWord_4955479 prefixEnd_4955479 848180866753907466440891 := by
  unfold tailWord_4955479
  simp only [CollatzResearch.WordTrace]
  refine ⟨180741167614153386278661491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120494111742768924185774327 180741167614153386278661491)
  ·
    refine ⟨271111751421230079417992237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180741167614153386278661491 271111751421230079417992237)
    ·
      refine ⟨101666906782961279781747089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271111751421230079417992237 101666906782961279781747089)
      ·
        refine ⟨76250180087220959836310317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101666906782961279781747089 76250180087220959836310317)
        ·
          refine ⟨28593817532707859938616369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76250180087220959836310317 28593817532707859938616369)
          ·
            refine ⟨21445363149530894953962277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28593817532707859938616369 21445363149530894953962277)
            ·
              refine ⟨4021005590537042803867927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21445363149530894953962277 4021005590537042803867927)
              ·
                refine ⟨6031508385805564205801891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021005590537042803867927 6031508385805564205801891)
                ·
                  refine ⟨9047262578708346308702837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6031508385805564205801891 9047262578708346308702837)
                  ·
                    refine ⟨848180866753907466440891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9047262578708346308702837 848180866753907466440891)
                    ·
                      rfl

theorem cell23_4955479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_4955479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955479 prefixEnd_4955479 := by exact prefixLift 4955479
  have htrace : WordTrace (prefixWord ++ tailWord_4955479) baseStart_4955479 baseEnd_4955479 := by
    simpa [prefixWord, tailWord_4955479, baseEnd_4955479] using wordTrace_append hprefix tailTrace_4955479
  have hstable : (prefixWord ++ tailWord_4955479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955479).length < 2 ^ (prefixWord ++ tailWord_4955479).sum := by decide
  have hdescent : baseEnd_4955479 < baseStart_4955479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955532 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_4955532 : Nat := 118140960795 + 4955532 * 2 ^ 59
def prefixEnd_4955532 : Nat := 4983230072969 + 3 ^ 40 * 4955532 * 2
def baseEnd_4955532 : Nat := 2544569814736410691959929

theorem tailTrace_4955532 : CollatzResearch.WordTrace tailWord_4955532 prefixEnd_4955532 2544569814736410691959929 := by
  unfold tailWord_4955532
  simp only [CollatzResearch.WordTrace]
  refine ⟨90371550341480688165170425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120495400455307584220227233 90371550341480688165170425)
  ·
    refine ⟨67778662756110516123877819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90371550341480688165170425 67778662756110516123877819)
    ·
      refine ⟨101667994134165774185816729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67778662756110516123877819 101667994134165774185816729)
      ·
        refine ⟨76250995600624330639362547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101667994134165774185816729 76250995600624330639362547)
        ·
          refine ⟨114376493400936495959043821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76250995600624330639362547 114376493400936495959043821)
          ·
            refine ⟨42891185025351185984641433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114376493400936495959043821 42891185025351185984641433)
            ·
              refine ⟨32168388769013389488481075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42891185025351185984641433 32168388769013389488481075)
              ·
                refine ⟨48252583153520084232721613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32168388769013389488481075 48252583153520084232721613)
                ·
                  refine ⟨18094718682570031587270605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48252583153520084232721613 18094718682570031587270605)
                  ·
                    refine ⟨6785519505963761845226477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18094718682570031587270605 6785519505963761845226477)
                    ·
                      refine ⟨2544569814736410691959929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6785519505963761845226477 2544569814736410691959929)
                      ·
                        rfl

theorem cell23_4955532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_4955532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955532 prefixEnd_4955532 := by exact prefixLift 4955532
  have htrace : WordTrace (prefixWord ++ tailWord_4955532) baseStart_4955532 baseEnd_4955532 := by
    simpa [prefixWord, tailWord_4955532, baseEnd_4955532] using wordTrace_append hprefix tailTrace_4955532
  have hstable : (prefixWord ++ tailWord_4955532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955532).length < 2 ^ (prefixWord ++ tailWord_4955532).sum := by decide
  have hdescent : baseEnd_4955532 < baseStart_4955532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955560 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4955560 : Nat := 118140960795 + 4955560 * 2 ^ 59
def prefixEnd_4955560 : Nat := 4983230072969 + 3 ^ 40 * 4955560 * 2
def baseEnd_4955560 : Nat := 848194730731578860803267

theorem tailTrace_4955560 : CollatzResearch.WordTrace tailWord_4955560 prefixEnd_4955560 848194730731578860803267 := by
  unfold tailWord_4955560
  simp only [CollatzResearch.WordTrace]
  refine ⟨90372060963429968556180067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120496081284573291408240089 90372060963429968556180067)
  ·
    refine ⟨135558091445144952834270101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90372060963429968556180067 135558091445144952834270101)
    ·
      refine ⟨6354285536491169664106411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 135558091445144952834270101 6354285536491169664106411)
      ·
        refine ⟨9531428304736754496159617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354285536491169664106411 9531428304736754496159617)
        ·
          refine ⟨7148571228552565872119713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9531428304736754496159617 7148571228552565872119713)
          ·
            refine ⟨5361428421414424404089785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7148571228552565872119713 5361428421414424404089785)
            ·
              refine ⟨4021071316060818303067339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5361428421414424404089785 4021071316060818303067339)
              ·
                refine ⟨6031606974091227454601009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021071316060818303067339 6031606974091227454601009)
                ·
                  refine ⟨4523705230568420590950757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6031606974091227454601009 4523705230568420590950757)
                  ·
                    refine ⟨848194730731578860803267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4523705230568420590950757 848194730731578860803267)
                    ·
                      rfl

theorem cell23_4955560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4955560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955560 prefixEnd_4955560 := by exact prefixLift 4955560
  have htrace : WordTrace (prefixWord ++ tailWord_4955560) baseStart_4955560 baseEnd_4955560 := by
    simpa [prefixWord, tailWord_4955560, baseEnd_4955560] using wordTrace_append hprefix tailTrace_4955560
  have hstable : (prefixWord ++ tailWord_4955560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955560).length < 2 ^ (prefixWord ++ tailWord_4955560).sum := by decide
  have hdescent : baseEnd_4955560 < baseStart_4955560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955576 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 1, 3, 2]
def baseStart_4955576 : Nat := 118140960795 + 4955576 * 2 ^ 59
def prefixEnd_4955576 : Nat := 4983230072969 + 3 ^ 40 * 4955576 * 2
def baseEnd_4955576 : Nat := 2544592407885208519809727

theorem tailTrace_4955576 : CollatzResearch.WordTrace tailWord_4955576 prefixEnd_4955576 2544592407885208519809727 := by
  unfold tailWord_4955576
  simp only [CollatzResearch.WordTrace]
  refine ⟨90372352747400985922471291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120496470329867981229961721 90372352747400985922471291)
  ·
    refine ⟨135558529121101478883706937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90372352747400985922471291 135558529121101478883706937)
    ·
      refine ⟨101668896840826109162780203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135558529121101478883706937 101668896840826109162780203)
      ·
        refine ⟨152503345261239163744170305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101668896840826109162780203 152503345261239163744170305)
        ·
          refine ⟨114377508945929372808127729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152503345261239163744170305 114377508945929372808127729)
          ·
            refine ⟨85783131709447029606095797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114377508945929372808127729 85783131709447029606095797)
            ·
              refine ⟨8042168597760659025571481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85783131709447029606095797 8042168597760659025571481)
              ·
                refine ⟨6031626448320494269178611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8042168597760659025571481 6031626448320494269178611)
                ·
                  refine ⟨9047439672480741403767917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6031626448320494269178611 9047439672480741403767917)
                  ·
                    refine ⟨3392789877180278026412969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9047439672480741403767917 3392789877180278026412969)
                    ·
                      refine ⟨2544592407885208519809727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392789877180278026412969 2544592407885208519809727)
                      ·
                        rfl

theorem cell23_4955576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_4955576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955576 prefixEnd_4955576 := by exact prefixLift 4955576
  have htrace : WordTrace (prefixWord ++ tailWord_4955576) baseStart_4955576 baseEnd_4955576 := by
    simpa [prefixWord, tailWord_4955576, baseEnd_4955576] using wordTrace_append hprefix tailTrace_4955576
  have hstable : (prefixWord ++ tailWord_4955576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955576).length < 2 ^ (prefixWord ++ tailWord_4955576).sum := by decide
  have hdescent : baseEnd_4955576 < baseStart_4955576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955582 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_4955582 : Nat := 118140960795 + 4955582 * 2 ^ 59
def prefixEnd_4955582 : Nat := 4983230072969 + 3 ^ 40 * 4955582 * 2
def baseEnd_4955582 : Nat := 848198496256378498778233

theorem tailTrace_4955582 : CollatzResearch.WordTrace tailWord_4955582 prefixEnd_4955582 848198496256378498778233 := by
  unfold tailWord_4955582
  simp only [CollatzResearch.WordTrace]
  refine ⟨22593115541597529358707625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120496616221853489913107333 22593115541597529358707625)
  ·
    refine ⟨16944836656198147019030719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22593115541597529358707625 16944836656198147019030719)
    ·
      refine ⟨25417254984297220528546079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16944836656198147019030719 25417254984297220528546079)
      ·
        refine ⟨38125882476445830792819119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25417254984297220528546079 38125882476445830792819119)
        ·
          refine ⟨57188823714668746189228679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38125882476445830792819119 57188823714668746189228679)
          ·
            refine ⟨85783235572003119283843019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57188823714668746189228679 85783235572003119283843019)
            ·
              refine ⟨128674853358004678925764529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85783235572003119283843019 128674853358004678925764529)
              ·
                refine ⟨96506140018503509194323397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128674853358004678925764529 96506140018503509194323397)
                ·
                  refine ⟨18094901253469407973935637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96506140018503509194323397 18094901253469407973935637)
                  ·
                    refine ⟨848198496256378498778233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18094901253469407973935637 848198496256378498778233)
                    ·
                      rfl

theorem cell23_4955582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_4955582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955582 prefixEnd_4955582 := by exact prefixLift 4955582
  have htrace : WordTrace (prefixWord ++ tailWord_4955582) baseStart_4955582 baseEnd_4955582 := by
    simpa [prefixWord, tailWord_4955582, baseEnd_4955582] using wordTrace_append hprefix tailTrace_4955582
  have hstable : (prefixWord ++ tailWord_4955582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955582).length < 2 ^ (prefixWord ++ tailWord_4955582).sum := by decide
  have hdescent : baseEnd_4955582 < baseStart_4955582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955592 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_4955592 : Nat := 118140960795 + 4955592 * 2 ^ 59
def prefixEnd_4955592 : Nat := 4983230072969 + 3 ^ 40 * 4955592 * 2
def baseEnd_4955592 : Nat := 2544600623575680457209653

theorem tailTrace_4955592 : CollatzResearch.WordTrace tailWord_4955592 prefixEnd_4955592 2544600623575680457209653 := by
  unfold tailWord_4955592
  simp only [CollatzResearch.WordTrace]
  refine ⟨90372644531372003288762515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120496859375162671051683353 90372644531372003288762515)
  ·
    refine ⟨135558966797058004933143773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90372644531372003288762515 135558966797058004933143773)
    ·
      refine ⟨50834612548896751849928915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135558966797058004933143773 50834612548896751849928915)
      ·
        refine ⟨76251918823345127774893373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50834612548896751849928915 76251918823345127774893373)
        ·
          refine ⟨28594469558754422915585015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76251918823345127774893373 28594469558754422915585015)
          ·
            refine ⟨42891704338131634373377523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28594469558754422915585015 42891704338131634373377523)
            ·
              refine ⟨64337556507197451560066285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42891704338131634373377523 64337556507197451560066285)
              ·
                refine ⟨24126583690199044335024857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64337556507197451560066285 24126583690199044335024857)
                ·
                  refine ⟨18094937767649283251268643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24126583690199044335024857 18094937767649283251268643)
                  ·
                    refine ⟨27142406651473924876902965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18094937767649283251268643 27142406651473924876902965)
                    ·
                      refine ⟨2544600623575680457209653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27142406651473924876902965 2544600623575680457209653)
                      ·
                        rfl

theorem cell23_4955592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_4955592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955592 prefixEnd_4955592 := by exact prefixLift 4955592
  have htrace : WordTrace (prefixWord ++ tailWord_4955592) baseStart_4955592 baseEnd_4955592 := by
    simpa [prefixWord, tailWord_4955592, baseEnd_4955592] using wordTrace_append hprefix tailTrace_4955592
  have hstable : (prefixWord ++ tailWord_4955592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955592).length < 2 ^ (prefixWord ++ tailWord_4955592).sum := by decide
  have hdescent : baseEnd_4955592 < baseStart_4955592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955619 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4955619 : Nat := 118140960795 + 4955619 * 2 ^ 59
def prefixEnd_4955619 : Nat := 4983230072969 + 3 ^ 40 * 4955619 * 2
def baseEnd_4955619 : Nat := 2544614487553351851572029

theorem tailTrace_4955619 : CollatzResearch.WordTrace tailWord_4955619 prefixEnd_4955619 2544614487553351851572029 := by
  unfold tailWord_4955619
  simp only [CollatzResearch.WordTrace]
  refine ⟨180746273833646190188757911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120497515889097460125838607 180746273833646190188757911)
  ·
    refine ⟨271119410750469285283136867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180746273833646190188757911 271119410750469285283136867)
    ·
      refine ⟨406679116125703927924705301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271119410750469285283136867 406679116125703927924705301)
      ·
        refine ⟨19063083568392371621470561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 406679116125703927924705301 19063083568392371621470561)
        ·
          refine ⟨14297312676294278716102921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19063083568392371621470561 14297312676294278716102921)
          ·
            refine ⟨10722984507220709037077191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14297312676294278716102921 10722984507220709037077191)
            ·
              refine ⟨16084476760831063555615787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10722984507220709037077191 16084476760831063555615787)
              ·
                refine ⟨24126715141246595333423681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16084476760831063555615787 24126715141246595333423681)
                ·
                  refine ⟨18095036355934946500067761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24126715141246595333423681 18095036355934946500067761)
                  ·
                    refine ⟨13571277266951209875050821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18095036355934946500067761 13571277266951209875050821)
                    ·
                      refine ⟨2544614487553351851572029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13571277266951209875050821 2544614487553351851572029)
                      ·
                        rfl

theorem cell23_4955619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4955619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955619 prefixEnd_4955619 := by exact prefixLift 4955619
  have htrace : WordTrace (prefixWord ++ tailWord_4955619) baseStart_4955619 baseEnd_4955619 := by
    simpa [prefixWord, tailWord_4955619, baseEnd_4955619] using wordTrace_append hprefix tailTrace_4955619
  have hstable : (prefixWord ++ tailWord_4955619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955619).length < 2 ^ (prefixWord ++ tailWord_4955619).sum := by decide
  have hdescent : baseEnd_4955619 < baseStart_4955619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955623 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_4955623 : Nat := 118140960795 + 4955623 * 2 ^ 59
def prefixEnd_4955623 : Nat := 4983230072969 + 3 ^ 40 * 4955623 * 2
def baseEnd_4955623 : Nat := 2544616541475969835922011

theorem tailTrace_4955623 : CollatzResearch.WordTrace tailWord_4955623 prefixEnd_4955623 2544616541475969835922011 := by
  unfold tailWord_4955623
  simp only [CollatzResearch.WordTrace]
  refine ⟨180746419725631698871903523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120497613150421132581269015 180746419725631698871903523)
  ·
    refine ⟨271119629588447548307855285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180746419725631698871903523 271119629588447548307855285)
    ·
      refine ⟨25417465273916957653861433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271119629588447548307855285 25417465273916957653861433)
      ·
        refine ⟨19063098955437718240396075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25417465273916957653861433 19063098955437718240396075)
        ·
          refine ⟨28594648433156577360594113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19063098955437718240396075 28594648433156577360594113)
          ·
            refine ⟨21445986324867433020445585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28594648433156577360594113 21445986324867433020445585)
            ·
              refine ⟨16084489743650574765334189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21445986324867433020445585 16084489743650574765334189)
              ·
                refine ⟨6031683653868965537000321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16084489743650574765334189 6031683653868965537000321)
                ·
                  refine ⟨4523762740401724152750241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6031683653868965537000321 4523762740401724152750241)
                  ·
                    refine ⟨3392822055301293114562681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4523762740401724152750241 3392822055301293114562681)
                    ·
                      refine ⟨2544616541475969835922011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392822055301293114562681 2544616541475969835922011)
                      ·
                        rfl

theorem cell23_4955623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_4955623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955623 prefixEnd_4955623 := by exact prefixLift 4955623
  have htrace : WordTrace (prefixWord ++ tailWord_4955623) baseStart_4955623 baseEnd_4955623 := by
    simpa [prefixWord, tailWord_4955623, baseEnd_4955623] using wordTrace_append hprefix tailTrace_4955623
  have hstable : (prefixWord ++ tailWord_4955623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955623).length < 2 ^ (prefixWord ++ tailWord_4955623).sum := by decide
  have hdescent : baseEnd_4955623 < baseStart_4955623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955642 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_4955642 : Nat := 118140960795 + 4955642 * 2 ^ 59
def prefixEnd_4955642 : Nat := 4983230072969 + 3 ^ 40 * 4955642 * 2
def baseEnd_4955642 : Nat := 848208765869468420528141

theorem tailTrace_4955642 : CollatzResearch.WordTrace tailWord_4955642 prefixEnd_4955642 848208765869468420528141 := by
  unfold tailWord_4955642
  simp only [CollatzResearch.WordTrace]
  refine ⟨45186778178140716279211295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120498075141708576744563453 45186778178140716279211295)
  ·
    refine ⟨67780167267211074418816943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45186778178140716279211295 67780167267211074418816943)
    ·
      refine ⟨101670250900816611628225415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67780167267211074418816943 101670250900816611628225415)
      ·
        refine ⟨152505376351224917442338123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101670250900816611628225415 152505376351224917442338123)
        ·
          refine ⟨228758064526837376163507185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152505376351224917442338123 228758064526837376163507185)
          ·
            refine ⟨171568548395128032122630389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228758064526837376163507185 171568548395128032122630389)
            ·
              refine ⟨16084551412043253011496599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171568548395128032122630389 16084551412043253011496599)
              ·
                refine ⟨24126827118064879517244899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16084551412043253011496599 24126827118064879517244899)
                ·
                  refine ⟨36190240677097319275867349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24126827118064879517244899 36190240677097319275867349)
                  ·
                    refine ⟨848208765869468420528141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36190240677097319275867349 848208765869468420528141)
                    ·
                      rfl

theorem cell23_4955642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_4955642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955642 prefixEnd_4955642 := by exact prefixLift 4955642
  have htrace : WordTrace (prefixWord ++ tailWord_4955642) baseStart_4955642 baseEnd_4955642 := by
    simpa [prefixWord, tailWord_4955642, baseEnd_4955642] using wordTrace_append hprefix tailTrace_4955642
  have hstable : (prefixWord ++ tailWord_4955642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955642).length < 2 ^ (prefixWord ++ tailWord_4955642).sum := by decide
  have hdescent : baseEnd_4955642 < baseStart_4955642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955699 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 3]
def baseStart_4955699 : Nat := 118140960795 + 4955699 * 2 ^ 59
def prefixEnd_4955699 : Nat := 4983230072969 + 3 ^ 40 * 4955699 * 2
def baseEnd_4955699 : Nat := 2544655566005711538571661

theorem tailTrace_4955699 : CollatzResearch.WordTrace tailWord_4955699 prefixEnd_4955699 2544655566005711538571661 := by
  unfold tailWord_4955699
  simp only [CollatzResearch.WordTrace]
  refine ⟨180749191673356363851670151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120499461115570909234446767 180749191673356363851670151)
  ·
    refine ⟨271123787510034545777505227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180749191673356363851670151 271123787510034545777505227)
    ·
      refine ⟨406685681265051818666257841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271123787510034545777505227 406685681265051818666257841)
      ·
        refine ⟨305014260948788863999693381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406685681265051818666257841 305014260948788863999693381)
        ·
          refine ⟨57190173927897911999942509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305014260948788863999693381 57190173927897911999942509)
          ·
            refine ⟨21446315222961716999978441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57190173927897911999942509 21446315222961716999978441)
            ·
              refine ⟨16084736417221287749983831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21446315222961716999978441 16084736417221287749983831)
              ·
                refine ⟨24127104625831931624975747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16084736417221287749983831 24127104625831931624975747)
                ·
                  refine ⟨36190656938747897437463621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24127104625831931624975747 36190656938747897437463621)
                  ·
                    refine ⟨6785748176015230769524429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36190656938747897437463621 6785748176015230769524429)
                    ·
                      refine ⟨2544655566005711538571661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6785748176015230769524429 2544655566005711538571661)
                      ·
                        rfl

theorem cell23_4955699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_4955699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955699 prefixEnd_4955699 := by exact prefixLift 4955699
  have htrace : WordTrace (prefixWord ++ tailWord_4955699) baseStart_4955699 baseEnd_4955699 := by
    simpa [prefixWord, tailWord_4955699, baseEnd_4955699] using wordTrace_append hprefix tailTrace_4955699
  have hstable : (prefixWord ++ tailWord_4955699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955699).length < 2 ^ (prefixWord ++ tailWord_4955699).sum := by decide
  have hdescent : baseEnd_4955699 < baseStart_4955699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955773 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_4955773 : Nat := 118140960795 + 4955773 * 2 ^ 59
def prefixEnd_4955773 : Nat := 4983230072969 + 3 ^ 40 * 4955773 * 2
def baseEnd_4955773 : Nat := 2544693563574144249046321

theorem tailTrace_4955773 : CollatzResearch.WordTrace tailWord_4955773 prefixEnd_4955773 2544693563574144249046321 := by
  unfold tailWord_4955773
  simp only [CollatzResearch.WordTrace]
  refine ⟨180751890675088274489863973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120501260450058849659909315 180751890675088274489863973)
  ·
    refine ⟨33890979501579051466849495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180751890675088274489863973 33890979501579051466849495)
    ·
      refine ⟨50836469252368577200274243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33890979501579051466849495 50836469252368577200274243)
      ·
        refine ⟨76254703878552865800411365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50836469252368577200274243 76254703878552865800411365)
        ·
          refine ⟨14297756977228662337577131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76254703878552865800411365 14297756977228662337577131)
          ·
            refine ⟨21446635465842993506365697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14297756977228662337577131 21446635465842993506365697)
            ·
              refine ⟨16084976599382245129774273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21446635465842993506365697 16084976599382245129774273)
              ·
                refine ⟨12063732449536683847330705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16084976599382245129774273 12063732449536683847330705)
                ·
                  refine ⟨9047799337152512885498029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12063732449536683847330705 9047799337152512885498029)
                  ·
                    refine ⟨3392924751432192332061761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9047799337152512885498029 3392924751432192332061761)
                    ·
                      refine ⟨2544693563574144249046321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392924751432192332061761 2544693563574144249046321)
                      ·
                        rfl

theorem cell23_4955773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_4955773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955773 prefixEnd_4955773 := by exact prefixLift 4955773
  have htrace : WordTrace (prefixWord ++ tailWord_4955773) baseStart_4955773 baseEnd_4955773 := by
    simpa [prefixWord, tailWord_4955773, baseEnd_4955773] using wordTrace_append hprefix tailTrace_4955773
  have hstable : (prefixWord ++ tailWord_4955773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955773).length < 2 ^ (prefixWord ++ tailWord_4955773).sum := by decide
  have hdescent : baseEnd_4955773 < baseStart_4955773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955786 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4955786 : Nat := 118140960795 + 4955786 * 2 ^ 59
def prefixEnd_4955786 : Nat := 4983230072969 + 3 ^ 40 * 4955786 * 2
def baseEnd_4955786 : Nat := 2544700238822652698183761

theorem tailTrace_4955786 : CollatzResearch.WordTrace tailWord_4955786 prefixEnd_4955786 2544700238822652698183761 := by
  unfold tailWord_4955786
  simp only [CollatzResearch.WordTrace]
  refine ⟨45188091206010294427521803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120501576549360785140058141 45188091206010294427521803)
  ·
    refine ⟨67782136809015441641282705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45188091206010294427521803 67782136809015441641282705)
    ·
      refine ⟨50836602606761581230962029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67782136809015441641282705 50836602606761581230962029)
      ·
        refine ⟨19063725977535592961610761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50836602606761581230962029 19063725977535592961610761)
        ·
          refine ⟨14297794483151694721208071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19063725977535592961610761 14297794483151694721208071)
          ·
            refine ⟨21446691724727542081812107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14297794483151694721208071 21446691724727542081812107)
            ·
              refine ⟨32170037587091313122718161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21446691724727542081812107 32170037587091313122718161)
              ·
                refine ⟨24127528190318484842038621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32170037587091313122718161 24127528190318484842038621)
                ·
                  refine ⟨9047823071369431815764483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24127528190318484842038621 9047823071369431815764483)
                  ·
                    refine ⟨13571734607054147723646725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9047823071369431815764483 13571734607054147723646725)
                    ·
                      refine ⟨2544700238822652698183761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13571734607054147723646725 2544700238822652698183761)
                      ·
                        rfl

theorem cell23_4955786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4955786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955786 prefixEnd_4955786 := by exact prefixLift 4955786
  have htrace : WordTrace (prefixWord ++ tailWord_4955786) baseStart_4955786 baseEnd_4955786 := by
    simpa [prefixWord, tailWord_4955786, baseEnd_4955786] using wordTrace_append hprefix tailTrace_4955786
  have hstable : (prefixWord ++ tailWord_4955786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955786).length < 2 ^ (prefixWord ++ tailWord_4955786).sum := by decide
  have hdescent : baseEnd_4955786 < baseStart_4955786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955807 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4955807 : Nat := 118140960795 + 4955807 * 2 ^ 59
def prefixEnd_4955807 : Nat := 4983230072969 + 3 ^ 40 * 4955807 * 2
def baseEnd_4955807 : Nat := 2544711021916397116021165

theorem tailTrace_4955807 : CollatzResearch.WordTrace tailWord_4955807 prefixEnd_4955807 2544711021916397116021165 := by
  unfold tailWord_4955807
  simp only [CollatzResearch.WordTrace]
  refine ⟨180753130756965098296601675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120502087171310065531067783 180753130756965098296601675)
  ·
    refine ⟨271129696135447647444902513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180753130756965098296601675 271129696135447647444902513)
    ·
      refine ⟨203347272101585735583676885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271129696135447647444902513 203347272101585735583676885)
      ·
        refine ⟨4765951689880915677742427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 203347272101585735583676885 4765951689880915677742427)
        ·
          refine ⟨7148927534821373516613641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4765951689880915677742427 7148927534821373516613641)
          ·
            refine ⟨5361695651116030137460231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7148927534821373516613641 5361695651116030137460231)
            ·
              refine ⟨8042543476674045206190347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361695651116030137460231 8042543476674045206190347)
              ·
                refine ⟨12063815215011067809285521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042543476674045206190347 12063815215011067809285521)
                ·
                  refine ⟨9047861411258300856964141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12063815215011067809285521 9047861411258300856964141)
                  ·
                    refine ⟨3392948029221862821361553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9047861411258300856964141 3392948029221862821361553)
                    ·
                      refine ⟨2544711021916397116021165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392948029221862821361553 2544711021916397116021165)
                      ·
                        rfl

theorem cell23_4955807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4955807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955807 prefixEnd_4955807 := by exact prefixLift 4955807
  have htrace : WordTrace (prefixWord ++ tailWord_4955807) baseStart_4955807 baseEnd_4955807 := by
    simpa [prefixWord, tailWord_4955807, baseEnd_4955807] using wordTrace_append hprefix tailTrace_4955807
  have hstable : (prefixWord ++ tailWord_4955807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955807).length < 2 ^ (prefixWord ++ tailWord_4955807).sum := by decide
  have hdescent : baseEnd_4955807 < baseStart_4955807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955830 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4955830 : Nat := 118140960795 + 4955830 * 2 ^ 59
def prefixEnd_4955830 : Nat := 4983230072969 + 3 ^ 40 * 4955830 * 2
def baseEnd_4955830 : Nat := 848240943990483508677853

theorem tailTrace_4955830 : CollatzResearch.WordTrace tailWord_4955830 prefixEnd_4955830 848240943990483508677853 := by
  unfold tailWord_4955830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11297123102242610826543059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120502646423921182149792629 11297123102242610826543059)
  ·
    refine ⟨16945684653363916239814589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11297123102242610826543059 16945684653363916239814589)
    ·
      refine ⟨6354631745011468589930471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16945684653363916239814589 6354631745011468589930471)
      ·
        refine ⟨9531947617517202884895707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354631745011468589930471 9531947617517202884895707)
        ·
          refine ⟨14297921426275804327343561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531947617517202884895707 14297921426275804327343561)
          ·
            refine ⟨10723441069706853245507671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14297921426275804327343561 10723441069706853245507671)
            ·
              refine ⟨16085161604560279868261507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10723441069706853245507671 16085161604560279868261507)
              ·
                refine ⟨24127742406840419802392261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16085161604560279868261507 24127742406840419802392261)
                ·
                  refine ⟨4523951701282578712948549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24127742406840419802392261 4523951701282578712948549)
                  ·
                    refine ⟨848240943990483508677853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4523951701282578712948549 848240943990483508677853)
                    ·
                      rfl

theorem cell23_4955830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4955830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955830 prefixEnd_4955830 := by exact prefixLift 4955830
  have htrace : WordTrace (prefixWord ++ tailWord_4955830) baseStart_4955830 baseEnd_4955830 := by
    simpa [prefixWord, tailWord_4955830, baseEnd_4955830] using wordTrace_append hprefix tailTrace_4955830
  have hstable : (prefixWord ++ tailWord_4955830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955830).length < 2 ^ (prefixWord ++ tailWord_4955830).sum := by decide
  have hdescent : baseEnd_4955830 < baseStart_4955830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955850 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_4955850 : Nat := 118140960795 + 4955850 * 2 ^ 59
def prefixEnd_4955850 : Nat := 4983230072969 + 3 ^ 40 * 4955850 * 2
def baseEnd_4955850 : Nat := 2544733101584540447783467

theorem tailTrace_4955850 : CollatzResearch.WordTrace tailWord_4955850 prefixEnd_4955850 2544733101584540447783467 := by
  unfold tailWord_4955850
  simp only [CollatzResearch.WordTrace]
  refine ⟨45188674773952329160104251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120503132730539544426944669 45188674773952329160104251)
  ·
    refine ⟨67783012160928493740156377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45188674773952329160104251 67783012160928493740156377)
    ·
      refine ⟨50837259120696370305117283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67783012160928493740156377 50837259120696370305117283)
      ·
        refine ⟨76255888681044555457675925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50837259120696370305117283 76255888681044555457675925)
        ·
          refine ⟨3574494781923963537078559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76255888681044555457675925 3574494781923963537078559)
          ·
            refine ⟨5361742172885945305617839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574494781923963537078559 5361742172885945305617839)
            ·
              refine ⟨8042613259328917958426759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361742172885945305617839 8042613259328917958426759)
              ·
                refine ⟨12063919888993376937640139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042613259328917958426759 12063919888993376937640139)
                ·
                  refine ⟨18095879833490065406460209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12063919888993376937640139 18095879833490065406460209)
                  ·
                    refine ⟨13571909875117549054845157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18095879833490065406460209 13571909875117549054845157)
                    ·
                      refine ⟨2544733101584540447783467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13571909875117549054845157 2544733101584540447783467)
                      ·
                        rfl

theorem cell23_4955850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_4955850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955850 prefixEnd_4955850 := by exact prefixLift 4955850
  have htrace : WordTrace (prefixWord ++ tailWord_4955850) baseStart_4955850 baseEnd_4955850 := by
    simpa [prefixWord, tailWord_4955850, baseEnd_4955850] using wordTrace_append hprefix tailTrace_4955850
  have hstable : (prefixWord ++ tailWord_4955850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955850).length < 2 ^ (prefixWord ++ tailWord_4955850).sum := by decide
  have hdescent : baseEnd_4955850 < baseStart_4955850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955880 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_4955880 : Nat := 118140960795 + 4955880 * 2 ^ 59
def prefixEnd_4955880 : Nat := 4983230072969 + 3 ^ 40 * 4955880 * 2
def baseEnd_4955880 : Nat := 2544748506004175330408329

theorem tailTrace_4955880 : CollatzResearch.WordTrace tailWord_4955880 prefixEnd_4955880 2544748506004175330408329 := by
  unfold tailWord_4955880
  simp only [CollatzResearch.WordTrace]
  refine ⟨90377896642850315882004547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120503862190467087842672729 90377896642850315882004547)
  ·
    refine ⟨135566844964275473823006821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90377896642850315882004547 135566844964275473823006821)
    ·
      refine ⟨25418783430801651341813779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135566844964275473823006821 25418783430801651341813779)
      ·
        refine ⟨38128175146202477012720669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25418783430801651341813779 38128175146202477012720669)
        ·
          refine ⟨14298065679825928879770251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38128175146202477012720669 14298065679825928879770251)
          ·
            refine ⟨21447098519738893319655377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14298065679825928879770251 21447098519738893319655377)
            ·
              refine ⟨16085323889804169989741533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21447098519738893319655377 16085323889804169989741533)
              ·
                refine ⟨6031996458676563746153075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16085323889804169989741533 6031996458676563746153075)
                ·
                  refine ⟨9047994688014845619229613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6031996458676563746153075 9047994688014845619229613)
                  ·
                    refine ⟨3392998008005567107211105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9047994688014845619229613 3392998008005567107211105)
                    ·
                      refine ⟨2544748506004175330408329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3392998008005567107211105 2544748506004175330408329)
                      ·
                        rfl

theorem cell23_4955880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_4955880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955880 prefixEnd_4955880 := by exact prefixLift 4955880
  have htrace : WordTrace (prefixWord ++ tailWord_4955880) baseStart_4955880 baseEnd_4955880 := by
    simpa [prefixWord, tailWord_4955880, baseEnd_4955880] using wordTrace_append hprefix tailTrace_4955880
  have hstable : (prefixWord ++ tailWord_4955880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955880).length < 2 ^ (prefixWord ++ tailWord_4955880).sum := by decide
  have hdescent : baseEnd_4955880 < baseStart_4955880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955899 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 7]
def baseStart_4955899 : Nat := 118140960795 + 4955899 * 2 ^ 59
def prefixEnd_4955899 : Nat := 4983230072969 + 3 ^ 40 * 4955899 * 2
def baseEnd_4955899 : Nat := 282750918015178972896749

theorem tailTrace_4955899 : CollatzResearch.WordTrace tailWord_4955899 prefixEnd_4955899 282750918015178972896749 := by
  unfold tailWord_4955899
  simp only [CollatzResearch.WordTrace]
  refine ⟨180756486272631798008950751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120504324181754532005967167 180756486272631798008950751)
  ·
    refine ⟨271134729408947697013426127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180756486272631798008950751 271134729408947697013426127)
    ·
      refine ⟨406702094113421545520139191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271134729408947697013426127 406702094113421545520139191)
      ·
        refine ⟨610053141170132318280208787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406702094113421545520139191 610053141170132318280208787)
        ·
          refine ⟨915079711755198477420313181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610053141170132318280208787 915079711755198477420313181)
          ·
            refine ⟨343154891908199429032617443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 915079711755198477420313181 343154891908199429032617443)
            ·
              refine ⟨514732337862299143548926165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343154891908199429032617443 514732337862299143548926165)
              ·
                refine ⟨12064039168647636176927957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 514732337862299143548926165 12064039168647636176927957)
                ·
                  refine ⟨282750918015178972896749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12064039168647636176927957 282750918015178972896749)
                  ·
                    rfl

theorem cell23_4955899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 7].length) (baseStart_4955899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955899 prefixEnd_4955899 := by exact prefixLift 4955899
  have htrace : WordTrace (prefixWord ++ tailWord_4955899) baseStart_4955899 baseEnd_4955899 := by
    simpa [prefixWord, tailWord_4955899, baseEnd_4955899] using wordTrace_append hprefix tailTrace_4955899
  have hstable : (prefixWord ++ tailWord_4955899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955899).length < 2 ^ (prefixWord ++ tailWord_4955899).sum := by decide
  have hdescent : baseEnd_4955899 < baseStart_4955899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955929 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 5, 7]
def baseStart_4955929 : Nat := 118140960795 + 4955929 * 2 ^ 59
def prefixEnd_4955929 : Nat := 4983230072969 + 3 ^ 40 * 4955929 * 2
def baseEnd_4955929 : Nat := 848257888852081879565201

theorem tailTrace_4955929 : CollatzResearch.WordTrace tailWord_4955929 prefixEnd_4955929 848257888852081879565201 := by
  unfold tailWord_4955929
  simp only [CollatzResearch.WordTrace]
  refine ⟨180757580462523113132542841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120505053641682075421695227 180757580462523113132542841)
  ·
    refine ⟨135568185346892334849407131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180757580462523113132542841 135568185346892334849407131)
    ·
      refine ⟨203352278020338502274110697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135568185346892334849407131 203352278020338502274110697)
      ·
        refine ⟨152514208515253876705583023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203352278020338502274110697 152514208515253876705583023)
        ·
          refine ⟨228771312772880815058374535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152514208515253876705583023 228771312772880815058374535)
          ·
            refine ⟨343156969159321222587561803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228771312772880815058374535 343156969159321222587561803)
            ·
              refine ⟨514735453738981833881342705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343156969159321222587561803 514735453738981833881342705)
              ·
                refine ⟨386051590304236375411007029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514735453738981833881342705 386051590304236375411007029)
                ·
                  refine ⟨36192336591022160194781909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 386051590304236375411007029 36192336591022160194781909)
                  ·
                    refine ⟨848257888852081879565201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36192336591022160194781909 848257888852081879565201)
                    ·
                      rfl

theorem cell23_4955929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_4955929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955929 prefixEnd_4955929 := by exact prefixLift 4955929
  have htrace : WordTrace (prefixWord ++ tailWord_4955929) baseStart_4955929 baseEnd_4955929 := by
    simpa [prefixWord, tailWord_4955929, baseEnd_4955929] using wordTrace_append hprefix tailTrace_4955929
  have hstable : (prefixWord ++ tailWord_4955929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955929).length < 2 ^ (prefixWord ++ tailWord_4955929).sum := by decide
  have hdescent : baseEnd_4955929 < baseStart_4955929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955953 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 2, 5, 2]
def baseStart_4955953 : Nat := 118140960795 + 4955953 * 2 ^ 59
def prefixEnd_4955953 : Nat := 4983230072969 + 3 ^ 40 * 4955953 * 2
def baseEnd_4955953 : Nat := 2544785990091953544795493

theorem tailTrace_4955953 : CollatzResearch.WordTrace tailWord_4955953 prefixEnd_4955953 2544785990091953544795493 := by
  unfold tailWord_4955953
  simp only [CollatzResearch.WordTrace]
  refine ⟨180758455814436165231416513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120505637209624110154277675 180758455814436165231416513)
  ·
    refine ⟨135568841860827123923562385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180758455814436165231416513 135568841860827123923562385)
    ·
      refine ⟨101676631395620342942671789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135568841860827123923562385 101676631395620342942671789)
      ·
        refine ⟨38128736773357628603501921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101676631395620342942671789 38128736773357628603501921)
        ·
          refine ⟨28596552580018221452626441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38128736773357628603501921 28596552580018221452626441)
          ·
            refine ⟨21447414435013666089469831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28596552580018221452626441 21447414435013666089469831)
            ·
              refine ⟨32171121652520499134204747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21447414435013666089469831 32171121652520499134204747)
              ·
                refine ⟨48256682478780748701307121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32171121652520499134204747 48256682478780748701307121)
                ·
                  refine ⟨36192511859085561525980341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48256682478780748701307121 36192511859085561525980341)
                  ·
                    refine ⟨3393047986789271393060657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36192511859085561525980341 3393047986789271393060657)
                    ·
                      refine ⟨2544785990091953544795493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393047986789271393060657 2544785990091953544795493)
                      ·
                        rfl

theorem cell23_4955953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_4955953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955953 prefixEnd_4955953 := by exact prefixLift 4955953
  have htrace : WordTrace (prefixWord ++ tailWord_4955953) baseStart_4955953 baseEnd_4955953 := by
    simpa [prefixWord, tailWord_4955953, baseEnd_4955953] using wordTrace_append hprefix tailTrace_4955953
  have hstable : (prefixWord ++ tailWord_4955953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955953).length < 2 ^ (prefixWord ++ tailWord_4955953).sum := by decide
  have hdescent : baseEnd_4955953 < baseStart_4955953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4955980 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_4955980 : Nat := 118140960795 + 4955980 * 2 ^ 59
def prefixEnd_4955980 : Nat := 4983230072969 + 3 ^ 40 * 4955980 * 2
def baseEnd_4955980 : Nat := 848266618023208313052623

theorem tailTrace_4955980 : CollatzResearch.WordTrace tailWord_4955980 prefixEnd_4955980 848266618023208313052623 := by
  unfold tailWord_4955980
  simp only [CollatzResearch.WordTrace]
  refine ⟨90379720292669174421324697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120506293723558899228432929 90379720292669174421324697)
  ·
    refine ⟨67784790219501880815993523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90379720292669174421324697 67784790219501880815993523)
    ·
      refine ⟨101677185329252821223990285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67784790219501880815993523 101677185329252821223990285)
      ·
        refine ⟨38128944498469807958996357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101677185329252821223990285 38128944498469807958996357)
        ·
          refine ⟨7149177093463088992311817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38128944498469807958996357 7149177093463088992311817)
          ·
            refine ⟨5361882820097316744233863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7149177093463088992311817 5361882820097316744233863)
            ·
              refine ⟨8042824230145975116350795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361882820097316744233863 8042824230145975116350795)
              ·
                refine ⟨12064236345218962674526193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042824230145975116350795 12064236345218962674526193)
                ·
                  refine ⟨9048177258914222005894645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12064236345218962674526193 9048177258914222005894645)
                  ·
                    refine ⟨848266618023208313052623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9048177258914222005894645 848266618023208313052623)
                    ·
                      rfl

theorem cell23_4955980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_4955980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4955980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4955980 prefixEnd_4955980 := by exact prefixLift 4955980
  have htrace : WordTrace (prefixWord ++ tailWord_4955980) baseStart_4955980 baseEnd_4955980 := by
    simpa [prefixWord, tailWord_4955980, baseEnd_4955980] using wordTrace_append hprefix tailTrace_4955980
  have hstable : (prefixWord ++ tailWord_4955980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4955980).length < 2 ^ (prefixWord ++ tailWord_4955980).sum := by decide
  have hdescent : baseEnd_4955980 < baseStart_4955980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4955980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956053 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_4956053 : Nat := 118140960795 + 4956053 * 2 ^ 59
def prefixEnd_4956053 : Nat := 4983230072969 + 3 ^ 40 * 4956053 * 2
def baseEnd_4956053 : Nat := 848279112719134384515011

theorem tailTrace_4956053 : CollatzResearch.WordTrace tailWord_4956053 prefixEnd_4956053 848279112719134384515011 := by
  unfold tailWord_4956053
  simp only [CollatzResearch.WordTrace]
  refine ⟨180762103114073882310056813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120508068742715921540037875 180762103114073882310056813)
  ·
    refine ⟨67785788667777705866271305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180762103114073882310056813 67785788667777705866271305)
    ·
      refine ⟨50839341500833279399703479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67785788667777705866271305 50839341500833279399703479)
      ·
        refine ⟨76259012251249919099555219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50839341500833279399703479 76259012251249919099555219)
        ·
          refine ⟨114388518376874878649332829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76259012251249919099555219 114388518376874878649332829)
          ·
            refine ⟨42895694391328079493499811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114388518376874878649332829 42895694391328079493499811)
            ·
              refine ⟨64343541586992119240249717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42895694391328079493499811 64343541586992119240249717)
              ·
                refine ⟨6032207023780511178773411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64343541586992119240249717 6032207023780511178773411)
                ·
                  refine ⟨9048310535670766768160117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6032207023780511178773411 9048310535670766768160117)
                  ·
                    refine ⟨848279112719134384515011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9048310535670766768160117 848279112719134384515011)
                    ·
                      rfl

theorem cell23_4956053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_4956053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956053 prefixEnd_4956053 := by exact prefixLift 4956053
  have htrace : WordTrace (prefixWord ++ tailWord_4956053) baseStart_4956053 baseEnd_4956053 := by
    simpa [prefixWord, tailWord_4956053, baseEnd_4956053] using wordTrace_append hprefix tailTrace_4956053
  have hstable : (prefixWord ++ tailWord_4956053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956053).length < 2 ^ (prefixWord ++ tailWord_4956053).sum := by decide
  have hdescent : baseEnd_4956053 < baseStart_4956053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956073 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 2, 6, 2]
def baseStart_4956073 : Nat := 118140960795 + 4956073 * 2 ^ 59
def prefixEnd_4956073 : Nat := 4983230072969 + 3 ^ 40 * 4956073 * 2
def baseEnd_4956073 : Nat := 2544847607770493075294941

theorem tailTrace_4956073 : CollatzResearch.WordTrace tailWord_4956073 prefixEnd_4956073 2544847607770493075294941 := by
  unfold tailWord_4956073
  simp only [CollatzResearch.WordTrace]
  refine ⟨180762832574001425725784873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120508555049334283817189915 180762832574001425725784873)
  ·
    refine ⟨135572124430501069294338655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180762832574001425725784873 135572124430501069294338655)
    ·
      refine ⟨203358186645751603941507983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135572124430501069294338655 203358186645751603941507983)
      ·
        refine ⟨305037279968627405912261975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203358186645751603941507983 305037279968627405912261975)
        ·
          refine ⟨457555919952941108868392963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305037279968627405912261975 457555919952941108868392963)
          ·
            refine ⟨686333879929411663302589445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457555919952941108868392963 686333879929411663302589445)
            ·
              refine ⟨128687602486764686869235521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 686333879929411663302589445 128687602486764686869235521)
              ·
                refine ⟨96515701865073515151926641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128687602486764686869235521 96515701865073515151926641)
                ·
                  refine ⟨72386776398805136363944981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96515701865073515151926641 72386776398805136363944981)
                  ·
                    refine ⟨3393130143693990767059921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72386776398805136363944981 3393130143693990767059921)
                    ·
                      refine ⟨2544847607770493075294941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393130143693990767059921 2544847607770493075294941)
                      ·
                        rfl

theorem cell23_4956073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 6, 2].length) (baseStart_4956073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956073 prefixEnd_4956073 := by exact prefixLift 4956073
  have htrace : WordTrace (prefixWord ++ tailWord_4956073) baseStart_4956073 baseEnd_4956073 := by
    simpa [prefixWord, tailWord_4956073, baseEnd_4956073] using wordTrace_append hprefix tailTrace_4956073
  have hstable : (prefixWord ++ tailWord_4956073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956073).length < 2 ^ (prefixWord ++ tailWord_4956073).sum := by decide
  have hdescent : baseEnd_4956073 < baseStart_4956073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956096 : List Nat := [2, 1, 1, 2, 3, 2, 1, 11]
def baseStart_4956096 : Nat := 118140960795 + 4956096 * 2 ^ 59
def prefixEnd_4956096 : Nat := 4983230072969 + 3 ^ 40 * 4956096 * 2
def baseEnd_4956096 : Nat := 94254052512057277233605

theorem tailTrace_4956096 : CollatzResearch.WordTrace tailWord_4956096 prefixEnd_4956096 94254052512057277233605 := by
  unfold tailWord_4956096
  simp only [CollatzResearch.WordTrace]
  refine ⟨90381835726459050326936071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120509114301945400435914761 90381835726459050326936071)
  ·
    refine ⟨135572753589688575490404107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90381835726459050326936071 135572753589688575490404107)
    ·
      refine ⟨203359130384532863235606161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135572753589688575490404107 203359130384532863235606161)
      ·
        refine ⟨152519347788399647426704621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203359130384532863235606161 152519347788399647426704621)
        ·
          refine ⟨57194755420649867785014233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152519347788399647426704621 57194755420649867785014233)
          ·
            refine ⟨42896066565487400838760675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57194755420649867785014233 42896066565487400838760675)
            ·
              refine ⟨64344099848231101258141013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42896066565487400838760675 64344099848231101258141013)
              ·
                refine ⟨94254052512057277233605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 64344099848231101258141013 94254052512057277233605)
                ·
                  rfl

theorem cell23_4956096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 11].length) (baseStart_4956096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956096 prefixEnd_4956096 := by exact prefixLift 4956096
  have htrace : WordTrace (prefixWord ++ tailWord_4956096) baseStart_4956096 baseEnd_4956096 := by
    simpa [prefixWord, tailWord_4956096, baseEnd_4956096] using wordTrace_append hprefix tailTrace_4956096
  have hstable : (prefixWord ++ tailWord_4956096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956096).length < 2 ^ (prefixWord ++ tailWord_4956096).sum := by decide
  have hdescent : baseEnd_4956096 < baseStart_4956096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956117 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_4956117 : Nat := 118140960795 + 4956117 * 2 ^ 59
def prefixEnd_4956117 : Nat := 4983230072969 + 3 ^ 40 * 4956117 * 2
def baseEnd_4956117 : Nat := 848290066973096967714913

theorem tailTrace_4956117 : CollatzResearch.WordTrace tailWord_4956117 prefixEnd_4956117 848290066973096967714913 := by
  unfold tailWord_4956117
  simp only [CollatzResearch.WordTrace]
  refine ⟨180764437385842021240386605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120509624923894680826924403 180764437385842021240386605)
  ·
    refine ⟨67786664019690757965144977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180764437385842021240386605 67786664019690757965144977)
    ·
      refine ⟨50839998014768068473858733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67786664019690757965144977 50839998014768068473858733)
      ·
        refine ⟨19064999255538025677697025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50839998014768068473858733 19064999255538025677697025)
        ·
          refine ⟨14298749441653519258272769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19064999255538025677697025 14298749441653519258272769)
          ·
            refine ⟨10724062081240139443704577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14298749441653519258272769 10724062081240139443704577)
            ·
              refine ⟨8043046560930104582778433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10724062081240139443704577 8043046560930104582778433)
              ·
                refine ⟨6032284920697578437083825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8043046560930104582778433 6032284920697578437083825)
                ·
                  refine ⟨4524213690523183827812869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6032284920697578437083825 4524213690523183827812869)
                  ·
                    refine ⟨848290066973096967714913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4524213690523183827812869 848290066973096967714913)
                    ·
                      rfl

theorem cell23_4956117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_4956117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956117 prefixEnd_4956117 := by exact prefixLift 4956117
  have htrace : WordTrace (prefixWord ++ tailWord_4956117) baseStart_4956117 baseEnd_4956117 := by
    simpa [prefixWord, tailWord_4956117, baseEnd_4956117] using wordTrace_append hprefix tailTrace_4956117
  have hstable : (prefixWord ++ tailWord_4956117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956117).length < 2 ^ (prefixWord ++ tailWord_4956117).sum := by decide
  have hdescent : baseEnd_4956117 < baseStart_4956117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956141 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4956141 : Nat := 118140960795 + 4956141 * 2 ^ 59
def prefixEnd_4956141 : Nat := 4983230072969 + 3 ^ 40 * 4956141 * 2
def baseEnd_4956141 : Nat := 2544882524454998809244629

theorem tailTrace_4956141 : CollatzResearch.WordTrace tailWord_4956141 prefixEnd_4956141 2544882524454998809244629 := by
  unfold tailWord_4956141
  simp only [CollatzResearch.WordTrace]
  refine ⟨180765312737755073339260277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120510208491836715559506851 180765312737755073339260277)
  ·
    refine ⟨16946748069164538125555651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180765312737755073339260277 16946748069164538125555651)
    ·
      refine ⟨25420122103746807188333477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16946748069164538125555651 25420122103746807188333477)
      ·
        refine ⟨4766272894452526347812527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25420122103746807188333477 4766272894452526347812527)
        ·
          refine ⟨7149409341678789521718791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766272894452526347812527 7149409341678789521718791)
          ·
            refine ⟨10724114012518184282578187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149409341678789521718791 10724114012518184282578187)
            ·
              refine ⟨16086171018777276423867281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10724114012518184282578187 16086171018777276423867281)
              ·
                refine ⟨12064628264082957317900461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16086171018777276423867281 12064628264082957317900461)
                ·
                  refine ⟨4524235599031108994212673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12064628264082957317900461 4524235599031108994212673)
                  ·
                    refine ⟨3393176699273331745659505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524235599031108994212673 3393176699273331745659505)
                    ·
                      refine ⟨2544882524454998809244629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393176699273331745659505 2544882524454998809244629)
                      ·
                        rfl

theorem cell23_4956141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4956141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956141 prefixEnd_4956141 := by exact prefixLift 4956141
  have htrace : WordTrace (prefixWord ++ tailWord_4956141) baseStart_4956141 baseEnd_4956141 := by
    simpa [prefixWord, tailWord_4956141, baseEnd_4956141] using wordTrace_append hprefix tailTrace_4956141
  have hstable : (prefixWord ++ tailWord_4956141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956141).length < 2 ^ (prefixWord ++ tailWord_4956141).sum := by decide
  have hdescent : baseEnd_4956141 < baseStart_4956141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956158 : List Nat := [4, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4956158 : Nat := 118140960795 + 4956158 * 2 ^ 59
def prefixEnd_4956158 : Nat := 4983230072969 + 3 ^ 40 * 4956158 * 2
def baseEnd_4956158 : Nat := 2544891253626125242732051

theorem tailTrace_4956158 : CollatzResearch.WordTrace tailWord_4956158 prefixEnd_4956158 2544891253626125242732051 := by
  unfold tailWord_4956158
  simp only [CollatzResearch.WordTrace]
  refine ⟨22595741597336685655328641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120510621852462323495086085 22595741597336685655328641)
  ·
    refine ⟨16946806198002514241496481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22595741597336685655328641 16946806198002514241496481)
    ·
      refine ⟨12710104648501885681122361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16946806198002514241496481 12710104648501885681122361)
      ·
        refine ⟨9532578486376414260841771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12710104648501885681122361 9532578486376414260841771)
        ·
          refine ⟨14298867729564621391262657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9532578486376414260841771 14298867729564621391262657)
          ·
            refine ⟨10724150797173466043446993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14298867729564621391262657 10724150797173466043446993)
            ·
              refine ⟨8043113097880099532585245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10724150797173466043446993 8043113097880099532585245)
              ·
                refine ⟨3016167411705037324719467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8043113097880099532585245 3016167411705037324719467)
                ·
                  refine ⟨4524251117557555987079201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016167411705037324719467 4524251117557555987079201)
                  ·
                    refine ⟨3393188338168166990309401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524251117557555987079201 3393188338168166990309401)
                    ·
                      refine ⟨2544891253626125242732051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393188338168166990309401 2544891253626125242732051)
                      ·
                        rfl

theorem cell23_4956158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4956158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956158 prefixEnd_4956158 := by exact prefixLift 4956158
  have htrace : WordTrace (prefixWord ++ tailWord_4956158) baseStart_4956158 baseEnd_4956158 := by
    simpa [prefixWord, tailWord_4956158, baseEnd_4956158] using wordTrace_append hprefix tailTrace_4956158
  have hstable : (prefixWord ++ tailWord_4956158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956158).length < 2 ^ (prefixWord ++ tailWord_4956158).sum := by decide
  have hdescent : baseEnd_4956158 < baseStart_4956158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956197 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 1, 4, 2]
def baseStart_4956197 : Nat := 118140960795 + 4956197 * 2 ^ 59
def prefixEnd_4956197 : Nat := 4983230072969 + 3 ^ 40 * 4956197 * 2
def baseEnd_4956197 : Nat := 2544911279371650590144371

theorem tailTrace_4956197 : CollatzResearch.WordTrace tailWord_4956197 prefixEnd_4956197 2544911279371650590144371 := by
  unfold tailWord_4956197
  simp only [CollatzResearch.WordTrace]
  refine ⟨180767355225552194903298845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120511570150368129935532563 180767355225552194903298845)
  ·
    refine ⟨67787758209582073088737067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180767355225552194903298845 67787758209582073088737067)
    ·
      refine ⟨101681637314373109633105601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67787758209582073088737067 101681637314373109633105601)
      ·
        refine ⟨76261227985779832224829201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101681637314373109633105601 76261227985779832224829201)
        ·
          refine ⟨57195920989334874168621901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76261227985779832224829201 57195920989334874168621901)
          ·
            refine ⟨21448470371000577813233213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57195920989334874168621901 21448470371000577813233213)
            ·
              refine ⟨8043176389125216679962455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21448470371000577813233213 8043176389125216679962455)
              ·
                refine ⟨12064764583687825019943683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8043176389125216679962455 12064764583687825019943683)
                ·
                  refine ⟨18097146875531737529915525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12064764583687825019943683 18097146875531737529915525)
                  ·
                    refine ⟨3393215039162200786859161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18097146875531737529915525 3393215039162200786859161)
                    ·
                      refine ⟨2544911279371650590144371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393215039162200786859161 2544911279371650590144371)
                      ·
                        rfl

theorem cell23_4956197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_4956197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956197 prefixEnd_4956197 := by exact prefixLift 4956197
  have htrace : WordTrace (prefixWord ++ tailWord_4956197) baseStart_4956197 baseEnd_4956197 := by
    simpa [prefixWord, tailWord_4956197, baseEnd_4956197] using wordTrace_append hprefix tailTrace_4956197
  have hstable : (prefixWord ++ tailWord_4956197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956197).length < 2 ^ (prefixWord ++ tailWord_4956197).sum := by decide
  have hdescent : baseEnd_4956197 < baseStart_4956197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956214 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_4956214 : Nat := 118140960795 + 4956214 * 2 ^ 59
def prefixEnd_4956214 : Nat := 4983230072969 + 3 ^ 40 * 4956214 * 2
def baseEnd_4956214 : Nat := 2544920008542777023631793

theorem tailTrace_4956214 : CollatzResearch.WordTrace tailWord_4956214 prefixEnd_4956214 2544920008542777023631793 := by
  unfold tailWord_4956214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11297998454155662925416731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120511983510993737871111797 11297998454155662925416731)
  ·
    refine ⟨16946997681233494388125097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11297998454155662925416731 16946997681233494388125097)
    ·
      refine ⟨12710248260925120791093823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16946997681233494388125097 12710248260925120791093823)
      ·
        refine ⟨19065372391387681186640735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12710248260925120791093823 19065372391387681186640735)
        ·
          refine ⟨28598058587081521779961103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19065372391387681186640735 28598058587081521779961103)
          ·
            refine ⟨42897087880622282669941655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28598058587081521779961103 42897087880622282669941655)
            ·
              refine ⟨64345631820933424004912483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42897087880622282669941655 64345631820933424004912483)
              ·
                refine ⟨96518447731400136007368725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64345631820933424004912483 96518447731400136007368725)
                ·
                  refine ⟨4524302237409381375345409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96518447731400136007368725 4524302237409381375345409)
                  ·
                    refine ⟨3393226678057036031509057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524302237409381375345409 3393226678057036031509057)
                    ·
                      refine ⟨2544920008542777023631793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393226678057036031509057 2544920008542777023631793)
                      ·
                        rfl

theorem cell23_4956214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_4956214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956214 prefixEnd_4956214 := by exact prefixLift 4956214
  have htrace : WordTrace (prefixWord ++ tailWord_4956214) baseStart_4956214 baseEnd_4956214 := by
    simpa [prefixWord, tailWord_4956214, baseEnd_4956214] using wordTrace_append hprefix tailTrace_4956214
  have hstable : (prefixWord ++ tailWord_4956214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956214).length < 2 ^ (prefixWord ++ tailWord_4956214).sum := by decide
  have hdescent : baseEnd_4956214 < baseStart_4956214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956314 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_4956314 : Nat := 118140960795 + 4956314 * 2 ^ 59
def prefixEnd_4956314 : Nat := 4983230072969 + 3 ^ 40 * 4956314 * 2
def baseEnd_4956314 : Nat := 848323785536075544127111

theorem tailTrace_4956314 : CollatzResearch.WordTrace tailWord_4956314 prefixEnd_4956314 848323785536075544127111 := by
  unfold tailWord_4956314
  simp only [CollatzResearch.WordTrace]
  refine ⟨45192905641532080971326999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120514415044085549256871997 45192905641532080971326999)
  ·
    refine ⟨67789358462298121456990499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45192905641532080971326999 67789358462298121456990499)
    ·
      refine ⟨101684037693447182185485749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67789358462298121456990499 101684037693447182185485749)
      ·
        refine ⟨9532878533760673329889289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101684037693447182185485749 9532878533760673329889289)
        ·
          refine ⟨7149658900320504997416967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9532878533760673329889289 7149658900320504997416967)
          ·
            refine ⟨10724488350480757496125451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149658900320504997416967 10724488350480757496125451)
            ·
              refine ⟨16086732525721136244188177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10724488350480757496125451 16086732525721136244188177)
              ·
                refine ⟨12065049394290852183141133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16086732525721136244188177 12065049394290852183141133)
                ·
                  refine ⟨4524393522859069568677925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12065049394290852183141133 4524393522859069568677925)
                  ·
                    refine ⟨848323785536075544127111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4524393522859069568677925 848323785536075544127111)
                    ·
                      rfl

theorem cell23_4956314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_4956314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956314 prefixEnd_4956314 := by exact prefixLift 4956314
  have htrace : WordTrace (prefixWord ++ tailWord_4956314) baseStart_4956314 baseEnd_4956314 := by
    simpa [prefixWord, tailWord_4956314, baseEnd_4956314] using wordTrace_append hprefix tailTrace_4956314
  have hstable : (prefixWord ++ tailWord_4956314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956314).length < 2 ^ (prefixWord ++ tailWord_4956314).sum := by decide
  have hdescent : baseEnd_4956314 < baseStart_4956314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956347 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 4, 3, 2]
def baseStart_4956347 : Nat := 118140960795 + 4956347 * 2 ^ 59
def prefixEnd_4956347 : Nat := 4983230072969 + 3 ^ 40 * 4956347 * 2
def baseEnd_4956347 : Nat := 2544988301469825003268681

theorem tailTrace_4956347 : CollatzResearch.WordTrace tailWord_4956347 prefixEnd_4956347 2544988301469825003268681 := by
  unfold tailWord_4956347
  simp only [CollatzResearch.WordTrace]
  refine ⟨180772826175008770521259295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120515217450005847014172863 180772826175008770521259295)
  ·
    refine ⟨271159239262513155781888943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180772826175008770521259295 271159239262513155781888943)
    ·
      refine ⟨406738858893769733672833415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271159239262513155781888943 406738858893769733672833415)
      ·
        refine ⟨610108288340654600509250123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406738858893769733672833415 610108288340654600509250123)
        ·
          refine ⟨915162432510981900763875185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610108288340654600509250123 915162432510981900763875185)
          ·
            refine ⟨686371824383236425572906389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 915162432510981900763875185 686371824383236425572906389)
            ·
              refine ⟨32173679267964207448729987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 686371824383236425572906389 32173679267964207448729987)
              ·
                refine ⟨48260518901946311173094981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32173679267964207448729987 48260518901946311173094981)
                ·
                  refine ⟨9048847294114933344955309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48260518901946311173094981 9048847294114933344955309)
                  ·
                    refine ⟨3393317735293100004358241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9048847294114933344955309 3393317735293100004358241)
                    ·
                      refine ⟨2544988301469825003268681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393317735293100004358241 2544988301469825003268681)
                      ·
                        rfl

theorem cell23_4956347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3, 2].length) (baseStart_4956347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956347 prefixEnd_4956347 := by exact prefixLift 4956347
  have htrace : WordTrace (prefixWord ++ tailWord_4956347) baseStart_4956347 baseEnd_4956347 := by
    simpa [prefixWord, tailWord_4956347, baseEnd_4956347] using wordTrace_append hprefix tailTrace_4956347
  have hstable : (prefixWord ++ tailWord_4956347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956347).length < 2 ^ (prefixWord ++ tailWord_4956347).sum := by decide
  have hdescent : baseEnd_4956347 < baseStart_4956347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956377 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 4]
def baseStart_4956377 : Nat := 118140960795 + 4956377 * 2 ^ 59
def prefixEnd_4956377 : Nat := 4983230072969 + 3 ^ 40 * 4956377 * 2
def baseEnd_4956377 : Nat := 2545003705889459885893543

theorem tailTrace_4956377 : CollatzResearch.WordTrace tailWord_4956377 prefixEnd_4956377 2545003705889459885893543 := by
  unfold tailWord_4956377
  simp only [CollatzResearch.WordTrace]
  refine ⟨180773920364900085644851385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120515946909933390429900923 180773920364900085644851385)
  ·
    refine ⟨135580440273675064233638539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180773920364900085644851385 135580440273675064233638539)
    ·
      refine ⟨203370660410512596350457809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135580440273675064233638539 203370660410512596350457809)
      ·
        refine ⟨152527995307884447262843357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203370660410512596350457809 152527995307884447262843357)
        ·
          refine ⟨57197998240456667723566259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152527995307884447262843357 57197998240456667723566259)
          ·
            refine ⟨85796997360685001585349389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57197998240456667723566259 85796997360685001585349389)
            ·
              refine ⟨32173874010256875594506021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85796997360685001585349389 32173874010256875594506021)
              ·
                refine ⟨6032601376923164173969879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32173874010256875594506021 6032601376923164173969879)
                ·
                  refine ⟨9048902065384746260954819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6032601376923164173969879 9048902065384746260954819)
                  ·
                    refine ⟨13573353098077119391432229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9048902065384746260954819 13573353098077119391432229)
                    ·
                      refine ⟨2545003705889459885893543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13573353098077119391432229 2545003705889459885893543)
                      ·
                        rfl

theorem cell23_4956377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_4956377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956377 prefixEnd_4956377 := by exact prefixLift 4956377
  have htrace : WordTrace (prefixWord ++ tailWord_4956377) baseStart_4956377 baseEnd_4956377 := by
    simpa [prefixWord, tailWord_4956377, baseEnd_4956377] using wordTrace_append hprefix tailTrace_4956377
  have hstable : (prefixWord ++ tailWord_4956377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956377).length < 2 ^ (prefixWord ++ tailWord_4956377).sum := by decide
  have hdescent : baseEnd_4956377 < baseStart_4956377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956414 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4956414 : Nat := 118140960795 + 4956414 * 2 ^ 59
def prefixEnd_4956414 : Nat := 4983230072969 + 3 ^ 40 * 4956414 * 2
def baseEnd_4956414 : Nat := 2545022704673676241130873

theorem tailTrace_4956414 : CollatzResearch.WordTrace tailWord_4956414 prefixEnd_4956414 2545022704673676241130873 := by
  unfold tailWord_4956414
  simp only [CollatzResearch.WordTrace]
  refine ⟨22596908733220755120493537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120516846577177360642632197 22596908733220755120493537)
  ·
    refine ⟨16947681549915566340370153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22596908733220755120493537 16947681549915566340370153)
    ·
      refine ⟨12710761162436674755277615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16947681549915566340370153 12710761162436674755277615)
      ·
        refine ⟨19066141743655012132916423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12710761162436674755277615 19066141743655012132916423)
        ·
          refine ⟨28599212615482518199374635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19066141743655012132916423 28599212615482518199374635)
          ·
            refine ⟨42898818923223777299061953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28599212615482518199374635 42898818923223777299061953)
            ·
              refine ⟨32174114192417832974296465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42898818923223777299061953 32174114192417832974296465)
              ·
                refine ⟨24130585644313374730722349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32174114192417832974296465 24130585644313374730722349)
                ·
                  refine ⟨9048969616617515524020881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24130585644313374730722349 9048969616617515524020881)
                  ·
                    refine ⟨6786727212463136643015661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9048969616617515524020881 6786727212463136643015661)
                    ·
                      refine ⟨2545022704673676241130873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6786727212463136643015661 2545022704673676241130873)
                      ·
                        rfl

theorem cell23_4956414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4956414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956414 prefixEnd_4956414 := by exact prefixLift 4956414
  have htrace : WordTrace (prefixWord ++ tailWord_4956414) baseStart_4956414 baseEnd_4956414 := by
    simpa [prefixWord, tailWord_4956414, baseEnd_4956414] using wordTrace_append hprefix tailTrace_4956414
  have hstable : (prefixWord ++ tailWord_4956414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956414).length < 2 ^ (prefixWord ++ tailWord_4956414).sum := by decide
  have hdescent : baseEnd_4956414 < baseStart_4956414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956427 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 3]
def baseStart_4956427 : Nat := 118140960795 + 4956427 * 2 ^ 59
def prefixEnd_4956427 : Nat := 4983230072969 + 3 ^ 40 * 4956427 * 2
def baseEnd_4956427 : Nat := 2545029379922184690268313

theorem tailTrace_4956427 : CollatzResearch.WordTrace tailWord_4956427 prefixEnd_4956427 2545029379922184690268313 := by
  unfold tailWord_4956427
  simp only [CollatzResearch.WordTrace]
  refine ⟨180775744014718944184171535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120517162676479296122781023 180775744014718944184171535)
  ·
    refine ⟨271163616022078416276257303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180775744014718944184171535 271163616022078416276257303)
    ·
      refine ⟨406745424033117624414385955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271163616022078416276257303 406745424033117624414385955)
      ·
        refine ⟨610118136049676436621578933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406745424033117624414385955 610118136049676436621578933)
        ·
          refine ⟨57198575254657165933273025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 610118136049676436621578933 57198575254657165933273025)
          ·
            refine ⟨42898931440992874449954769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57198575254657165933273025 42898931440992874449954769)
            ·
              refine ⟨32174198580744655837466077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42898931440992874449954769 32174198580744655837466077)
              ·
                refine ⟨12065324467779245939049779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32174198580744655837466077 12065324467779245939049779)
                ·
                  refine ⟨18097986701668868908574669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12065324467779245939049779 18097986701668868908574669)
                  ·
                    refine ⟨6786745013125825840715501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18097986701668868908574669 6786745013125825840715501)
                    ·
                      refine ⟨2545029379922184690268313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6786745013125825840715501 2545029379922184690268313)
                      ·
                        rfl

theorem cell23_4956427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 3].length) (baseStart_4956427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956427 prefixEnd_4956427 := by exact prefixLift 4956427
  have htrace : WordTrace (prefixWord ++ tailWord_4956427) baseStart_4956427 baseEnd_4956427 := by
    simpa [prefixWord, tailWord_4956427, baseEnd_4956427] using wordTrace_append hprefix tailTrace_4956427
  have hstable : (prefixWord ++ tailWord_4956427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956427).length < 2 ^ (prefixWord ++ tailWord_4956427).sum := by decide
  have hdescent : baseEnd_4956427 < baseStart_4956427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956455 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4956455 : Nat := 118140960795 + 4956455 * 2 ^ 59
def prefixEnd_4956455 : Nat := 4983230072969 + 3 ^ 40 * 4956455 * 2
def baseEnd_4956455 : Nat := 848347919126836860239395

theorem tailTrace_4956455 : CollatzResearch.WordTrace tailWord_4956455 prefixEnd_4956455 848347919126836860239395 := by
  unfold tailWord_4956455
  simp only [CollatzResearch.WordTrace]
  refine ⟨180776765258617504966190819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120517843505745003310793879 180776765258617504966190819)
  ·
    refine ⟨271165147887926257449286229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180776765258617504966190819 271165147887926257449286229)
    ·
      refine ⟨3177716576811635829483823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 271165147887926257449286229 3177716576811635829483823)
      ·
        refine ⟨4766574865217453744225735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177716576811635829483823 4766574865217453744225735)
        ·
          refine ⟨7149862297826180616338603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766574865217453744225735 7149862297826180616338603)
          ·
            refine ⟨10724793446739270924507905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149862297826180616338603 10724793446739270924507905)
            ·
              refine ⟨8043595085054453193380929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10724793446739270924507905 8043595085054453193380929)
              ·
                refine ⟨6032696313790839895035697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8043595085054453193380929 6032696313790839895035697)
                ·
                  refine ⟨4524522235343129921276773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6032696313790839895035697 4524522235343129921276773)
                  ·
                    refine ⟨848347919126836860239395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4524522235343129921276773 848347919126836860239395)
                    ·
                      rfl

theorem cell23_4956455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4956455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956455 prefixEnd_4956455 := by exact prefixLift 4956455
  have htrace : WordTrace (prefixWord ++ tailWord_4956455) baseStart_4956455 baseEnd_4956455 := by
    simpa [prefixWord, tailWord_4956455, baseEnd_4956455] using wordTrace_append hprefix tailTrace_4956455
  have hstable : (prefixWord ++ tailWord_4956455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956455).length < 2 ^ (prefixWord ++ tailWord_4956455).sum := by decide
  have hdescent : baseEnd_4956455 < baseStart_4956455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956462 : List Nat := [4, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4956462 : Nat := 118140960795 + 4956462 * 2 ^ 59
def prefixEnd_4956462 : Nat := 4983230072969 + 3 ^ 40 * 4956462 * 2
def baseEnd_4956462 : Nat := 2545047351745092053330653

theorem tailTrace_4956462 : CollatzResearch.WordTrace tailWord_4956462 prefixEnd_4956462 2545047351745092053330653 := by
  unfold tailWord_4956462
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597127571199018145211955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120518013713061430107797093 22597127571199018145211955)
  ·
    refine ⟨33895691356798527217817933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22597127571199018145211955 33895691356798527217817933)
    ·
      refine ⟨12710884258799447706681725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33895691356798527217817933 12710884258799447706681725)
      ·
        refine ⟨4766581597049792890005647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12710884258799447706681725 4766581597049792890005647)
        ·
          refine ⟨7149872395574689335008471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766581597049792890005647 7149872395574689335008471)
          ·
            refine ⟨10724808593362034002512707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149872395574689335008471 10724808593362034002512707)
            ·
              refine ⟨16087212890043051003769061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10724808593362034002512707 16087212890043051003769061)
              ·
                refine ⟨3016352416883072063206699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16087212890043051003769061 3016352416883072063206699)
                ·
                  refine ⟨4524528625324608094810049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016352416883072063206699 4524528625324608094810049)
                  ·
                    refine ⟨3393396468993456071107537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524528625324608094810049 3393396468993456071107537)
                    ·
                      refine ⟨2545047351745092053330653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393396468993456071107537 2545047351745092053330653)
                      ·
                        rfl

theorem cell23_4956462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4956462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956462 prefixEnd_4956462 := by exact prefixLift 4956462
  have htrace : WordTrace (prefixWord ++ tailWord_4956462) baseStart_4956462 baseEnd_4956462 := by
    simpa [prefixWord, tailWord_4956462, baseEnd_4956462] using wordTrace_append hprefix tailTrace_4956462
  have hstable : (prefixWord ++ tailWord_4956462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956462).length < 2 ^ (prefixWord ++ tailWord_4956462).sum := by decide
  have hdescent : baseEnd_4956462 < baseStart_4956462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956487 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_4956487 : Nat := 118140960795 + 4956487 * 2 ^ 59
def prefixEnd_4956487 : Nat := 4983230072969 + 3 ^ 40 * 4956487 * 2
def baseEnd_4956487 : Nat := 2545060188761454455518037

theorem tailTrace_4956487 : CollatzResearch.WordTrace tailWord_4956487 prefixEnd_4956487 2545060188761454455518037 := by
  unfold tailWord_4956487
  simp only [CollatzResearch.WordTrace]
  refine ⟨180777932394501574431355715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120518621596334382954237143 180777932394501574431355715)
  ·
    refine ⟨271166898591752361647033573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180777932394501574431355715 271166898591752361647033573)
    ·
      refine ⟨50843793485953567808818795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271166898591752361647033573 50843793485953567808818795)
      ·
        refine ⟨76265690228930351713228193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50843793485953567808818795 76265690228930351713228193)
        ·
          refine ⟨57199267671697763784921145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76265690228930351713228193 57199267671697763784921145)
          ·
            refine ⟨42899450753773322838690859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57199267671697763784921145 42899450753773322838690859)
            ·
              refine ⟨64349176130659984258036289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42899450753773322838690859 64349176130659984258036289)
              ·
                refine ⟨48261882097994988193527217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64349176130659984258036289 48261882097994988193527217)
                ·
                  refine ⟨36196411573496241145145413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48261882097994988193527217 36196411573496241145145413)
                  ·
                    refine ⟨6786827170030545214714765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36196411573496241145145413 6786827170030545214714765)
                    ·
                      refine ⟨2545060188761454455518037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6786827170030545214714765 2545060188761454455518037)
                      ·
                        rfl

theorem cell23_4956487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_4956487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956487 prefixEnd_4956487 := by exact prefixLift 4956487
  have htrace : WordTrace (prefixWord ++ tailWord_4956487) baseStart_4956487 baseEnd_4956487 := by
    simpa [prefixWord, tailWord_4956487, baseEnd_4956487] using wordTrace_append hprefix tailTrace_4956487
  have hstable : (prefixWord ++ tailWord_4956487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956487).length < 2 ^ (prefixWord ++ tailWord_4956487).sum := by decide
  have hdescent : baseEnd_4956487 < baseStart_4956487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956514 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4956514 : Nat := 118140960795 + 4956514 * 2 ^ 59
def prefixEnd_4956514 : Nat := 4983230072969 + 3 ^ 40 * 4956514 * 2
def baseEnd_4956514 : Nat := 2545074052739125849880413

theorem tailTrace_4956514 : CollatzResearch.WordTrace tailWord_4956514 prefixEnd_4956514 2545074052739125849880413 := by
  unfold tailWord_4956514
  simp only [CollatzResearch.WordTrace]
  refine ⟨45194729291350939510647149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120519278110269172028392397 45194729291350939510647149)
  ·
    refine ⟨16948023484256602316492681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45194729291350939510647149 16948023484256602316492681)
    ·
      refine ⟨12711017613192451737369511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16948023484256602316492681 12711017613192451737369511)
      ·
        refine ⟨19066526419788677606054267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12711017613192451737369511 19066526419788677606054267)
        ·
          refine ⟨28599789629683016409081401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19066526419788677606054267 28599789629683016409081401)
          ·
            refine ⟨21449842222262262306811051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28599789629683016409081401 21449842222262262306811051)
            ·
              refine ⟨32174763333393393460216577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21449842222262262306811051 32174763333393393460216577)
              ·
                refine ⟨24131072500045045095162433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32174763333393393460216577 24131072500045045095162433)
                ·
                  refine ⟨18098304375033783821371825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24131072500045045095162433 18098304375033783821371825)
                  ·
                    refine ⟨13573728281275337866028869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18098304375033783821371825 13573728281275337866028869)
                    ·
                      refine ⟨2545074052739125849880413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13573728281275337866028869 2545074052739125849880413)
                      ·
                        rfl

theorem cell23_4956514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4956514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956514 prefixEnd_4956514 := by exact prefixLift 4956514
  have htrace : WordTrace (prefixWord ++ tailWord_4956514) baseStart_4956514 baseEnd_4956514 := by
    simpa [prefixWord, tailWord_4956514, baseEnd_4956514] using wordTrace_append hprefix tailTrace_4956514
  have hstable : (prefixWord ++ tailWord_4956514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956514).length < 2 ^ (prefixWord ++ tailWord_4956514).sum := by decide
  have hdescent : baseEnd_4956514 < baseStart_4956514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956524 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 7]
def baseStart_4956524 : Nat := 118140960795 + 4956524 * 2 ^ 59
def prefixEnd_4956524 : Nat := 4983230072969 + 3 ^ 40 * 4956524 * 2
def baseEnd_4956524 : Nat := 282786576393963423417263

theorem tailTrace_4956524 : CollatzResearch.WordTrace tailWord_4956524 prefixEnd_4956524 282786576393963423417263 := by
  unfold tailWord_4956524
  simp only [CollatzResearch.WordTrace]
  refine ⟨90389640947683764875226313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120519521263578353166968417 90389640947683764875226313)
  ·
    refine ⟨67792230710762823656419735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90389640947683764875226313 67792230710762823656419735)
    ·
      refine ⟨101688346066144235484629603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67792230710762823656419735 101688346066144235484629603)
      ·
        refine ⟨152532519099216353226944405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101688346066144235484629603 152532519099216353226944405)
        ·
          refine ⟨7149961832775766557513019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152532519099216353226944405 7149961832775766557513019)
          ·
            refine ⟨10724942749163649836269529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149961832775766557513019 10724942749163649836269529)
            ·
              refine ⟨8043707061872737377202147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10724942749163649836269529 8043707061872737377202147)
              ·
                refine ⟨12065560592809106065803221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8043707061872737377202147 12065560592809106065803221)
                ·
                  refine ⟨282786576393963423417263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12065560592809106065803221 282786576393963423417263)
                  ·
                    rfl

theorem cell23_4956524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_4956524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956524 prefixEnd_4956524 := by exact prefixLift 4956524
  have htrace : WordTrace (prefixWord ++ tailWord_4956524) baseStart_4956524 baseEnd_4956524 := by
    simpa [prefixWord, tailWord_4956524, baseEnd_4956524] using wordTrace_append hprefix tailTrace_4956524
  have hstable : (prefixWord ++ tailWord_4956524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956524).length < 2 ^ (prefixWord ++ tailWord_4956524).sum := by decide
  have hdescent : baseEnd_4956524 < baseStart_4956524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956558 : List Nat := [4, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_4956558 : Nat := 118140960795 + 4956558 * 2 ^ 59
def prefixEnd_4956558 : Nat := 4983230072969 + 3 ^ 40 * 4956558 * 2
def baseEnd_4956558 : Nat := 282788516209769297525579

theorem tailTrace_4956558 : CollatzResearch.WordTrace tailWord_4956558 prefixEnd_4956558 282788516209769297525579 := by
  unfold tailWord_4956558
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597565247155544194648791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120520347984829569038126885 22597565247155544194648791)
  ·
    refine ⟨33896347870733316291973187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22597565247155544194648791 33896347870733316291973187)
    ·
      refine ⟨50844521806099974437959781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33896347870733316291973187 50844521806099974437959781)
      ·
        refine ⟨9533347838643745207117459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50844521806099974437959781 9533347838643745207117459)
        ·
          refine ⟨14300021757965617810676189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9533347838643745207117459 14300021757965617810676189)
          ·
            refine ⟨5362508159237106679003571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14300021757965617810676189 5362508159237106679003571)
            ·
              refine ⟨8043762238855660018505357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5362508159237106679003571 8043762238855660018505357)
              ·
                refine ⟨3016410839570872506939509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8043762238855660018505357 3016410839570872506939509)
                ·
                  refine ⟨282788516209769297525579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3016410839570872506939509 282788516209769297525579)
                  ·
                    rfl

theorem cell23_4956558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_4956558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956558 prefixEnd_4956558 := by exact prefixLift 4956558
  have htrace : WordTrace (prefixWord ++ tailWord_4956558) baseStart_4956558 baseEnd_4956558 := by
    simpa [prefixWord, tailWord_4956558, baseEnd_4956558] using wordTrace_append hprefix tailTrace_4956558
  have hstable : (prefixWord ++ tailWord_4956558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956558).length < 2 ^ (prefixWord ++ tailWord_4956558).sum := by decide
  have hdescent : baseEnd_4956558 < baseStart_4956558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956586 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4956586 : Nat := 118140960795 + 4956586 * 2 ^ 59
def prefixEnd_4956586 : Nat := 4983230072969 + 3 ^ 40 * 4956586 * 2
def baseEnd_4956586 : Nat := 2545111023346249568180083

theorem tailTrace_4956586 : CollatzResearch.WordTrace tailWord_4956586 prefixEnd_4956586 2545111023346249568180083 := by
  unfold tailWord_4956586
  simp only [CollatzResearch.WordTrace]
  refine ⟨45195385805285728584802403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120521028814095276226139741 45195385805285728584802403)
  ·
    refine ⟨67793078707928592877203605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45195385805285728584802403 67793078707928592877203605)
    ·
      refine ⟨3177800564434152791118919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67793078707928592877203605 3177800564434152791118919)
      ·
        refine ⟨4766700846651229186678379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177800564434152791118919 4766700846651229186678379)
        ·
          refine ⟨7150051269976843780017569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766700846651229186678379 7150051269976843780017569)
          ·
            refine ⟨5362538452482632835013177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7150051269976843780017569 5362538452482632835013177)
            ·
              refine ⟨4021903839361974626259883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5362538452482632835013177 4021903839361974626259883)
              ·
                refine ⟨6032855759042961939389825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021903839361974626259883 6032855759042961939389825)
                ·
                  refine ⟨4524641819282221454542369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6032855759042961939389825 4524641819282221454542369)
                  ·
                    refine ⟨3393481364461666090906777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524641819282221454542369 3393481364461666090906777)
                    ·
                      refine ⟨2545111023346249568180083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393481364461666090906777 2545111023346249568180083)
                      ·
                        rfl

theorem cell23_4956586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4956586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956586 prefixEnd_4956586 := by exact prefixLift 4956586
  have htrace : WordTrace (prefixWord ++ tailWord_4956586) baseStart_4956586 baseEnd_4956586 := by
    simpa [prefixWord, tailWord_4956586, baseEnd_4956586] using wordTrace_append hprefix tailTrace_4956586
  have hstable : (prefixWord ++ tailWord_4956586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956586).length < 2 ^ (prefixWord ++ tailWord_4956586).sum := by decide
  have hdescent : baseEnd_4956586 < baseStart_4956586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956594 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_4956594 : Nat := 118140960795 + 4956594 * 2 ^ 59
def prefixEnd_4956594 : Nat := 4983230072969 + 3 ^ 40 * 4956594 * 2
def baseEnd_4956594 : Nat := 2545115131191485536880045

theorem tailTrace_4956594 : CollatzResearch.WordTrace tailWord_4956594 prefixEnd_4956594 2545115131191485536880045 := by
  unfold tailWord_4956594
  simp only [CollatzResearch.WordTrace]
  refine ⟨45195458751278482926375209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120521223336742621137000557 45195458751278482926375209)
  ·
    refine ⟨33896594063458862194781407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45195458751278482926375209 33896594063458862194781407)
    ·
      refine ⟨50844891095188293292172111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33896594063458862194781407 50844891095188293292172111)
      ·
        refine ⟨76267336642782439938258167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50844891095188293292172111 76267336642782439938258167)
        ·
          refine ⟨114401004964173659907387251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76267336642782439938258167 114401004964173659907387251)
          ·
            refine ⟨171601507446260489861080877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114401004964173659907387251 171601507446260489861080877)
            ·
              refine ⟨64350565292347683697905329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171601507446260489861080877 64350565292347683697905329)
              ·
                refine ⟨48262923969260762773428997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64350565292347683697905329 48262923969260762773428997)
                ·
                  refine ⟨9049298244236393020017937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48262923969260762773428997 9049298244236393020017937)
                  ·
                    refine ⟨6786973683177294765013453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9049298244236393020017937 6786973683177294765013453)
                    ·
                      refine ⟨2545115131191485536880045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6786973683177294765013453 2545115131191485536880045)
                      ·
                        rfl

theorem cell23_4956594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_4956594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956594 prefixEnd_4956594 := by exact prefixLift 4956594
  have htrace : WordTrace (prefixWord ++ tailWord_4956594) baseStart_4956594 baseEnd_4956594 := by
    simpa [prefixWord, tailWord_4956594, baseEnd_4956594] using wordTrace_append hprefix tailTrace_4956594
  have hstable : (prefixWord ++ tailWord_4956594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956594).length < 2 ^ (prefixWord ++ tailWord_4956594).sum := by decide
  have hdescent : baseEnd_4956594 < baseStart_4956594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956641 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_4956641 : Nat := 118140960795 + 4956641 * 2 ^ 59
def prefixEnd_4956641 : Nat := 4983230072969 + 3 ^ 40 * 4956641 * 2
def baseEnd_4956641 : Nat := 2545139264782246852992329

theorem tailTrace_4956641 : CollatzResearch.WordTrace tailWord_4956641 prefixEnd_4956641 2545139264782246852992329 := by
  unfold tailWord_4956641
  simp only [CollatzResearch.WordTrace]
  refine ⟨180783549235943658732461777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120522366157295772488307851 180783549235943658732461777)
  ·
    refine ⟨135587661926957744049346333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180783549235943658732461777 135587661926957744049346333)
    ·
      refine ⟨50845373222609154018504875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135587661926957744049346333 50845373222609154018504875)
      ·
        refine ⟨76268059833913731027757313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50845373222609154018504875 76268059833913731027757313)
        ·
          refine ⟨57201044875435298270817985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76268059833913731027757313 57201044875435298270817985)
          ·
            refine ⟨42900783656576473703113489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57201044875435298270817985 42900783656576473703113489)
            ·
              refine ⟨32175587742432355277335117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42900783656576473703113489 32175587742432355277335117)
              ·
                refine ⟨12065845403412133229000669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32175587742432355277335117 12065845403412133229000669)
                ·
                  refine ⟨4524692026279549960875251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12065845403412133229000669 4524692026279549960875251)
                  ·
                    refine ⟨6787038039419324941312877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4524692026279549960875251 6787038039419324941312877)
                    ·
                      refine ⟨2545139264782246852992329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787038039419324941312877 2545139264782246852992329)
                      ·
                        rfl

theorem cell23_4956641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_4956641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956641 prefixEnd_4956641 := by exact prefixLift 4956641
  have htrace : WordTrace (prefixWord ++ tailWord_4956641) baseStart_4956641 baseEnd_4956641 := by
    simpa [prefixWord, tailWord_4956641, baseEnd_4956641] using wordTrace_append hprefix tailTrace_4956641
  have hstable : (prefixWord ++ tailWord_4956641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956641).length < 2 ^ (prefixWord ++ tailWord_4956641).sum := by decide
  have hdescent : baseEnd_4956641 < baseStart_4956641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956664 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_4956664 : Nat := 118140960795 + 4956664 * 2 ^ 59
def prefixEnd_4956664 : Nat := 4983230072969 + 3 ^ 40 * 4956664 * 2
def baseEnd_4956664 : Nat := 2545151074837300263004723

theorem tailTrace_4956664 : CollatzResearch.WordTrace tailWord_4956664 prefixEnd_4956664 2545151074837300263004723 := by
  unfold tailWord_4956664
  simp only [CollatzResearch.WordTrace]
  refine ⟨90392194057430166830274523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120522925409906889107032697 90392194057430166830274523)
  ·
    refine ⟨135588291086145250245411785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90392194057430166830274523 135588291086145250245411785)
    ·
      refine ⟨101691218314608937684058839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135588291086145250245411785 101691218314608937684058839)
      ·
        refine ⟨152536827471913406526088259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101691218314608937684058839 152536827471913406526088259)
        ·
          refine ⟨228805241207870109789132389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152536827471913406526088259 228805241207870109789132389)
          ·
            refine ⟨42900982726475645585462323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228805241207870109789132389 42900982726475645585462323)
            ·
              refine ⟨64351474089713468378193485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42900982726475645585462323 64351474089713468378193485)
              ·
                refine ⟨24131802783642550641822557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64351474089713468378193485 24131802783642550641822557)
                ·
                  refine ⟨9049426043865956490683459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24131802783642550641822557 9049426043865956490683459)
                  ·
                    refine ⟨13574139065798934736025189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9049426043865956490683459 13574139065798934736025189)
                    ·
                      refine ⟨2545151074837300263004723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13574139065798934736025189 2545151074837300263004723)
                      ·
                        rfl

theorem cell23_4956664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_4956664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956664 prefixEnd_4956664 := by exact prefixLift 4956664
  have htrace : WordTrace (prefixWord ++ tailWord_4956664) baseStart_4956664 baseEnd_4956664 := by
    simpa [prefixWord, tailWord_4956664, baseEnd_4956664] using wordTrace_append hprefix tailTrace_4956664
  have hstable : (prefixWord ++ tailWord_4956664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956664).length < 2 ^ (prefixWord ++ tailWord_4956664).sum := by decide
  have hdescent : baseEnd_4956664 < baseStart_4956664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956667 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5]
def baseStart_4956667 : Nat := 118140960795 + 4956667 * 2 ^ 59
def prefixEnd_4956667 : Nat := 4983230072969 + 3 ^ 40 * 4956667 * 2
def baseEnd_4956667 : Nat := 2545152615279263751267209

theorem tailTrace_4956667 : CollatzResearch.WordTrace tailWord_4956667 prefixEnd_4956667 2545152615279263751267209 := by
  unfold tailWord_4956667
  simp only [CollatzResearch.WordTrace]
  refine ⟨180784497533849465172908255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120522998355899643448605503 180784497533849465172908255)
  ·
    refine ⟨271176746300774197759362383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180784497533849465172908255 271176746300774197759362383)
    ·
      refine ⟨406765119451161296639043575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271176746300774197759362383 406765119451161296639043575)
      ·
        refine ⟨610147679176741944958565363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406765119451161296639043575 610147679176741944958565363)
        ·
          refine ⟨915221518765112917437848045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610147679176741944958565363 915221518765112917437848045)
          ·
            refine ⟨343208069536917344039193017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 915221518765112917437848045 343208069536917344039193017)
            ·
              refine ⟨257406052152688008029394763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343208069536917344039193017 257406052152688008029394763)
              ·
                refine ⟨386109078229032012044092145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257406052152688008029394763 386109078229032012044092145)
                ·
                  refine ⟨289581808671774009033069109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386109078229032012044092145 289581808671774009033069109)
                  ·
                    refine ⟨27148294562978813346850229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 289581808671774009033069109 27148294562978813346850229)
                    ·
                      refine ⟨2545152615279263751267209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27148294562978813346850229 2545152615279263751267209)
                      ·
                        rfl

theorem cell23_4956667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_4956667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956667 prefixEnd_4956667 := by exact prefixLift 4956667
  have htrace : WordTrace (prefixWord ++ tailWord_4956667) baseStart_4956667 baseEnd_4956667 := by
    simpa [prefixWord, tailWord_4956667, baseEnd_4956667] using wordTrace_append hprefix tailTrace_4956667
  have hstable : (prefixWord ++ tailWord_4956667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956667).length < 2 ^ (prefixWord ++ tailWord_4956667).sum := by decide
  have hdescent : baseEnd_4956667 < baseStart_4956667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956692 : List Nat := [2, 4, 3, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_4956692 : Nat := 118140960795 + 4956692 * 2 ^ 59
def prefixEnd_4956692 : Nat := 4983230072969 + 3 ^ 40 * 4956692 * 2
def baseEnd_4956692 : Nat := 2545165452295626153454595

theorem tailTrace_4956692 : CollatzResearch.WordTrace tailWord_4956692 prefixEnd_4956692 2545165452295626153454595 := by
  unfold tailWord_4956692
  simp only [CollatzResearch.WordTrace]
  refine ⟨90392704679379447221284165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120523606239172596295045553 90392704679379447221284165)
  ·
    refine ⟨16948632127383646353990781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90392704679379447221284165 16948632127383646353990781)
    ·
      refine ⟨6355737047768867382746543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16948632127383646353990781 6355737047768867382746543)
      ·
        refine ⟨9533605571653301074119815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6355737047768867382746543 9533605571653301074119815)
        ·
          refine ⟨14300408357479951611179723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9533605571653301074119815 14300408357479951611179723)
          ·
            refine ⟨21450612536219927416769585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14300408357479951611179723 21450612536219927416769585)
            ·
              refine ⟨16087959402164945562577189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21450612536219927416769585 16087959402164945562577189)
              ·
                refine ⟨3016492387905927292983223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16087959402164945562577189 3016492387905927292983223)
                ·
                  refine ⟨4524738581858890939474835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016492387905927292983223 4524738581858890939474835)
                  ·
                    refine ⟨6787107872788336409212253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4524738581858890939474835 6787107872788336409212253)
                    ·
                      refine ⟨2545165452295626153454595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787107872788336409212253 2545165452295626153454595)
                      ·
                        rfl

theorem cell23_4956692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_4956692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956692 prefixEnd_4956692 := by exact prefixLift 4956692
  have htrace : WordTrace (prefixWord ++ tailWord_4956692) baseStart_4956692 baseEnd_4956692 := by
    simpa [prefixWord, tailWord_4956692, baseEnd_4956692] using wordTrace_append hprefix tailTrace_4956692
  have hstable : (prefixWord ++ tailWord_4956692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956692).length < 2 ^ (prefixWord ++ tailWord_4956692).sum := by decide
  have hdescent : baseEnd_4956692 < baseStart_4956692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956698 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2]
def baseStart_4956698 : Nat := 118140960795 + 4956698 * 2 ^ 59
def prefixEnd_4956698 : Nat := 4983230072969 + 3 ^ 40 * 4956698 * 2
def baseEnd_4956698 : Nat := 2545168533179553129979567

theorem tailTrace_4956698 : CollatzResearch.WordTrace tailWord_4956698 prefixEnd_4956698 2545168533179553129979567 := by
  unfold tailWord_4956698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45196407049184289366821687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120523752131158104978191165 45196407049184289366821687)
  ·
    refine ⟨67794610573776434050232531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45196407049184289366821687 67794610573776434050232531)
    ·
      refine ⟨101691915860664651075348797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67794610573776434050232531 101691915860664651075348797)
      ·
        refine ⟨38134468447749244153255799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101691915860664651075348797 38134468447749244153255799)
        ·
          refine ⟨57201702671623866229883699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38134468447749244153255799 57201702671623866229883699)
          ·
            refine ⟨85802554007435799344825549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57201702671623866229883699 85802554007435799344825549)
            ·
              refine ⟨32175957752788424754309581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85802554007435799344825549 32175957752788424754309581)
              ·
                refine ⟨12065984157295659282866093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32175957752788424754309581 12065984157295659282866093)
                ·
                  refine ⟨4524744058985872231074785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12065984157295659282866093 4524744058985872231074785)
                  ·
                    refine ⟨3393558044239404173306089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524744058985872231074785 3393558044239404173306089)
                    ·
                      refine ⟨2545168533179553129979567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393558044239404173306089 2545168533179553129979567)
                      ·
                        rfl

theorem cell23_4956698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_4956698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956698 prefixEnd_4956698 := by exact prefixLift 4956698
  have htrace : WordTrace (prefixWord ++ tailWord_4956698) baseStart_4956698 baseEnd_4956698 := by
    simpa [prefixWord, tailWord_4956698, baseEnd_4956698] using wordTrace_append hprefix tailTrace_4956698
  have hstable : (prefixWord ++ tailWord_4956698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956698).length < 2 ^ (prefixWord ++ tailWord_4956698).sum := by decide
  have hdescent : baseEnd_4956698 < baseStart_4956698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956701 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4956701 : Nat := 118140960795 + 4956701 * 2 ^ 59
def prefixEnd_4956701 : Nat := 4983230072969 + 3 ^ 40 * 4956701 * 2
def baseEnd_4956701 : Nat := 2545170073621516618242053

theorem tailTrace_4956701 : CollatzResearch.WordTrace tailWord_4956701 prefixEnd_4956701 2545170073621516618242053 := by
  unfold tailWord_4956701
  simp only [CollatzResearch.WordTrace]
  refine ⟨180785737615726288979645957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120523825077150859319763971 180785737615726288979645957)
  ·
    refine ⟨33897325802948679183683617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180785737615726288979645957 33897325802948679183683617)
    ·
      refine ⟨25422994352211509387762713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33897325802948679183683617 25422994352211509387762713)
      ·
        refine ⟨19067245764158632040822035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25422994352211509387762713 19067245764158632040822035)
        ·
          refine ⟨28600868646237948061233053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19067245764158632040822035 28600868646237948061233053)
          ·
            refine ⟨10725325742339230522962395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28600868646237948061233053 10725325742339230522962395)
            ·
              refine ⟨16087988613508845784443593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10725325742339230522962395 16087988613508845784443593)
              ·
                refine ⟨12065991460131634338332695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16087988613508845784443593 12065991460131634338332695)
                ·
                  refine ⟨18098987190197451507499043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12065991460131634338332695 18098987190197451507499043)
                  ·
                    refine ⟨27148480785296177261248565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18098987190197451507499043 27148480785296177261248565)
                    ·
                      refine ⟨2545170073621516618242053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27148480785296177261248565 2545170073621516618242053)
                      ·
                        rfl

theorem cell23_4956701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4956701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956701 prefixEnd_4956701 := by exact prefixLift 4956701
  have htrace : WordTrace (prefixWord ++ tailWord_4956701) baseStart_4956701 baseEnd_4956701 := by
    simpa [prefixWord, tailWord_4956701, baseEnd_4956701] using wordTrace_append hprefix tailTrace_4956701
  have hstable : (prefixWord ++ tailWord_4956701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956701).length < 2 ^ (prefixWord ++ tailWord_4956701).sum := by decide
  have hdescent : baseEnd_4956701 < baseStart_4956701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956732 : List Nat := [2, 2, 2, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_4956732 : Nat := 118140960795 + 4956732 * 2 ^ 59
def prefixEnd_4956732 : Nat := 4983230072969 + 3 ^ 40 * 4956732 * 2
def baseEnd_4956732 : Nat := 2545185991521805996954411

theorem tailTrace_4956732 : CollatzResearch.WordTrace tailWord_4956732 prefixEnd_4956732 2545185991521805996954411 := by
  unfold tailWord_4956732
  simp only [CollatzResearch.WordTrace]
  refine ⟨90393434139306990637012225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120524578852409320849349633 90393434139306990637012225)
  ·
    refine ⟨67795075604480242977759169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90393434139306990637012225 67795075604480242977759169)
    ·
      refine ⟨50846306703360182233319377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67795075604480242977759169 50846306703360182233319377)
      ·
        refine ⟨38134730027520136674989533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50846306703360182233319377 38134730027520136674989533)
        ·
          refine ⟨14300523760320051253121075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38134730027520136674989533 14300523760320051253121075)
          ·
            refine ⟨21450785640480076879681613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14300523760320051253121075 21450785640480076879681613)
            ·
              refine ⟨8044044615180028829880605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21450785640480076879681613 8044044615180028829880605)
              ·
                refine ⟨3016516730692510811205227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8044044615180028829880605 3016516730692510811205227)
                ·
                  refine ⟨4524775096038766216807841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016516730692510811205227 4524775096038766216807841)
                  ·
                    refine ⟨3393581322029074662605881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524775096038766216807841 3393581322029074662605881)
                    ·
                      refine ⟨2545185991521805996954411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393581322029074662605881 2545185991521805996954411)
                      ·
                        rfl

theorem cell23_4956732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_4956732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956732 prefixEnd_4956732 := by exact prefixLift 4956732
  have htrace : WordTrace (prefixWord ++ tailWord_4956732) baseStart_4956732 baseEnd_4956732 := by
    simpa [prefixWord, tailWord_4956732, baseEnd_4956732] using wordTrace_append hprefix tailTrace_4956732
  have hstable : (prefixWord ++ tailWord_4956732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956732).length < 2 ^ (prefixWord ++ tailWord_4956732).sum := by decide
  have hdescent : baseEnd_4956732 < baseStart_4956732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956748 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_4956748 : Nat := 118140960795 + 4956748 * 2 ^ 59
def prefixEnd_4956748 : Nat := 4983230072969 + 3 ^ 40 * 4956748 * 2
def baseEnd_4956748 : Nat := 2545194207212277934354337

theorem tailTrace_4956748 : CollatzResearch.WordTrace tailWord_4956748 prefixEnd_4956748 2545194207212277934354337 := by
  unfold tailWord_4956748
  simp only [CollatzResearch.WordTrace]
  refine ⟨90393725923278008003303449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120524967897704010671071265 90393725923278008003303449)
  ·
    refine ⟨67795294442458506002477587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90393725923278008003303449 67795294442458506002477587)
    ·
      refine ⟨101692941663687759003716381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67795294442458506002477587 101692941663687759003716381)
      ·
        refine ⟨38134853123882909626393643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101692941663687759003716381 38134853123882909626393643)
        ·
          refine ⟨57202279685824364439590465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38134853123882909626393643 57202279685824364439590465)
          ·
            refine ⟨42901709764368273329692849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57202279685824364439590465 42901709764368273329692849)
            ·
              refine ⟨32176282323276204997269637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42901709764368273329692849 32176282323276204997269637)
              ·
                refine ⟨6033052935614288436988057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32176282323276204997269637 6033052935614288436988057)
                ·
                  refine ⟨4524789701710716327741043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6033052935614288436988057 4524789701710716327741043)
                  ·
                    refine ⟨6787184552566074491611565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4524789701710716327741043 6787184552566074491611565)
                    ·
                      refine ⟨2545194207212277934354337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787184552566074491611565 2545194207212277934354337)
                      ·
                        rfl

theorem cell23_4956748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_4956748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956748 prefixEnd_4956748 := by exact prefixLift 4956748
  have htrace : WordTrace (prefixWord ++ tailWord_4956748) baseStart_4956748 baseEnd_4956748 := by
    simpa [prefixWord, tailWord_4956748, baseEnd_4956748] using wordTrace_append hprefix tailTrace_4956748
  have hstable : (prefixWord ++ tailWord_4956748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956748).length < 2 ^ (prefixWord ++ tailWord_4956748).sum := by decide
  have hdescent : baseEnd_4956748 < baseStart_4956748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956766 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4956766 : Nat := 118140960795 + 4956766 * 2 ^ 59
def prefixEnd_4956766 : Nat := 4983230072969 + 3 ^ 40 * 4956766 * 2
def baseEnd_4956766 : Nat := 2545203449864058863929255

theorem tailTrace_4956766 : CollatzResearch.WordTrace tailWord_4956766 prefixEnd_4956766 2545203449864058863929255 := by
  unfold tailWord_4956766
  simp only [CollatzResearch.WordTrace]
  refine ⟨22598513545061350635095269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120525405573660536720508101 22598513545061350635095269)
  ·
    refine ⟨4237221289699003244080363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22598513545061350635095269 4237221289699003244080363)
    ·
      refine ⟨6355831934548504866120545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4237221289699003244080363 6355831934548504866120545)
      ·
        refine ⟨4766873950911378649590409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6355831934548504866120545 4766873950911378649590409)
        ·
          refine ⟨3575155463183533987192807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4766873950911378649590409 3575155463183533987192807)
          ·
            refine ⟨5362733194775300980789211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575155463183533987192807 5362733194775300980789211)
            ·
              refine ⟨8044099792162951471183817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5362733194775300980789211 8044099792162951471183817)
              ·
                refine ⟨6033074844122213603387863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8044099792162951471183817 6033074844122213603387863)
                ·
                  refine ⟨9049612266183320405081795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6033074844122213603387863 9049612266183320405081795)
                  ·
                    refine ⟨13574418399274980607622693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9049612266183320405081795 13574418399274980607622693)
                    ·
                      refine ⟨2545203449864058863929255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13574418399274980607622693 2545203449864058863929255)
                      ·
                        rfl

theorem cell23_4956766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4956766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956766 prefixEnd_4956766 := by exact prefixLift 4956766
  have htrace : WordTrace (prefixWord ++ tailWord_4956766) baseStart_4956766 baseEnd_4956766 := by
    simpa [prefixWord, tailWord_4956766, baseEnd_4956766] using wordTrace_append hprefix tailTrace_4956766
  have hstable : (prefixWord ++ tailWord_4956766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956766).length < 2 ^ (prefixWord ++ tailWord_4956766).sum := by decide
  have hdescent : baseEnd_4956766 < baseStart_4956766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956801 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4956801 : Nat := 118140960795 + 4956801 * 2 ^ 59
def prefixEnd_4956801 : Nat := 4983230072969 + 3 ^ 40 * 4956801 * 2
def baseEnd_4956801 : Nat := 2545221421686966226991593

theorem tailTrace_4956801 : CollatzResearch.WordTrace tailWord_4956801 prefixEnd_4956801 2545221421686966226991593 := by
  unfold tailWord_4956801
  simp only [CollatzResearch.WordTrace]
  refine ⟨180789384915364006058286257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120526256610242670705524171 180789384915364006058286257)
  ·
    refine ⟨135592038686523004543714693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180789384915364006058286257 135592038686523004543714693)
    ·
      refine ⟨25423507253723063351946505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135592038686523004543714693 25423507253723063351946505)
      ·
        refine ⟨19067630440292297513959879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25423507253723063351946505 19067630440292297513959879)
        ·
          refine ⟨28601445660438446270939819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19067630440292297513959879 28601445660438446270939819)
          ·
            refine ⟨42902168490657669406409729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28601445660438446270939819 42902168490657669406409729)
            ·
              refine ⟨32176626367993252054807297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42902168490657669406409729 32176626367993252054807297)
              ·
                refine ⟨24132469775994939041105473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32176626367993252054807297 24132469775994939041105473)
                ·
                  refine ⟨18099352331996204280829105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24132469775994939041105473 18099352331996204280829105)
                  ·
                    refine ⟨13574514248997153210621829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18099352331996204280829105 13574514248997153210621829)
                    ·
                      refine ⟨2545221421686966226991593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13574514248997153210621829 2545221421686966226991593)
                      ·
                        rfl

theorem cell23_4956801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4956801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956801 prefixEnd_4956801 := by exact prefixLift 4956801
  have htrace : WordTrace (prefixWord ++ tailWord_4956801) baseStart_4956801 baseEnd_4956801 := by
    simpa [prefixWord, tailWord_4956801, baseEnd_4956801] using wordTrace_append hprefix tailTrace_4956801
  have hstable : (prefixWord ++ tailWord_4956801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956801).length < 2 ^ (prefixWord ++ tailWord_4956801).sum := by decide
  have hdescent : baseEnd_4956801 < baseStart_4956801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956805 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 2, 2, 2]
def baseStart_4956805 : Nat := 118140960795 + 4956805 * 2 ^ 59
def prefixEnd_4956805 : Nat := 4983230072969 + 3 ^ 40 * 4956805 * 2
def baseEnd_4956805 : Nat := 2545223475609584211341575

theorem tailTrace_4956805 : CollatzResearch.WordTrace tailWord_4956805 prefixEnd_4956805 2545223475609584211341575 := by
  unfold tailWord_4956805
  simp only [CollatzResearch.WordTrace]
  refine ⟨180789530807349514741431869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120526353871566343160954579 180789530807349514741431869)
  ·
    refine ⟨67796074052756068028036951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180789530807349514741431869 67796074052756068028036951)
    ·
      refine ⟨101694111079134102042055427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67796074052756068028036951 101694111079134102042055427)
      ·
        refine ⟨152541166618701153063083141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101694111079134102042055427 152541166618701153063083141)
        ·
          refine ⟨28601468741006466199328089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152541166618701153063083141 28601468741006466199328089)
          ·
            refine ⟨21451101555754849649496067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28601468741006466199328089 21451101555754849649496067)
            ·
              refine ⟨32176652333632274474244101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21451101555754849649496067 32176652333632274474244101)
              ·
                refine ⟨6033122312556051463920769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32176652333632274474244101 6033122312556051463920769)
                ·
                  refine ⟨4524841734417038597940577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6033122312556051463920769 4524841734417038597940577)
                  ·
                    refine ⟨3393631300812778948455433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4524841734417038597940577 3393631300812778948455433)
                    ·
                      refine ⟨2545223475609584211341575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393631300812778948455433 2545223475609584211341575)
                      ·
                        rfl

theorem cell23_4956805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_4956805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956805 prefixEnd_4956805 := by exact prefixLift 4956805
  have htrace : WordTrace (prefixWord ++ tailWord_4956805) baseStart_4956805 baseEnd_4956805 := by
    simpa [prefixWord, tailWord_4956805, baseEnd_4956805] using wordTrace_append hprefix tailTrace_4956805
  have hstable : (prefixWord ++ tailWord_4956805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956805).length < 2 ^ (prefixWord ++ tailWord_4956805).sum := by decide
  have hdescent : baseEnd_4956805 < baseStart_4956805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956818 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4956818 : Nat := 118140960795 + 4956818 * 2 ^ 59
def prefixEnd_4956818 : Nat := 4983230072969 + 3 ^ 40 * 4956818 * 2
def baseEnd_4956818 : Nat := 2545230150858092660479015

theorem tailTrace_4956818 : CollatzResearch.WordTrace tailWord_4956818 prefixEnd_4956818 2545230150858092660479015 := by
  unfold tailWord_4956818
  simp only [CollatzResearch.WordTrace]
  refine ⟨45197501239075604490413777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120526669970868278641103405 45197501239075604490413777)
  ·
    refine ⟨33898125929306703367810333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45197501239075604490413777 33898125929306703367810333)
    ·
      refine ⟨12711797223490013762928875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33898125929306703367810333 12711797223490013762928875)
      ·
        refine ⟨19067695835235020644393313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12711797223490013762928875 19067695835235020644393313)
        ·
          refine ⟨14300771876426265483294985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19067695835235020644393313 14300771876426265483294985)
          ·
            refine ⟨10725578907319699112471239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14300771876426265483294985 10725578907319699112471239)
            ·
              refine ⟨16088368360979548668706859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10725578907319699112471239 16088368360979548668706859)
              ·
                refine ⟨24132552541469323003060289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16088368360979548668706859 24132552541469323003060289)
                ·
                  refine ⟨18099414406101992252295217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24132552541469323003060289 18099414406101992252295217)
                  ·
                    refine ⟨13574560804576494189221413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18099414406101992252295217 13574560804576494189221413)
                    ·
                      refine ⟨2545230150858092660479015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13574560804576494189221413 2545230150858092660479015)
                      ·
                        rfl

theorem cell23_4956818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4956818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956818 prefixEnd_4956818 := by exact prefixLift 4956818
  have htrace : WordTrace (prefixWord ++ tailWord_4956818) baseStart_4956818 baseEnd_4956818 := by
    simpa [prefixWord, tailWord_4956818, baseEnd_4956818] using wordTrace_append hprefix tailTrace_4956818
  have hstable : (prefixWord ++ tailWord_4956818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956818).length < 2 ^ (prefixWord ++ tailWord_4956818).sum := by decide
  have hdescent : baseEnd_4956818 < baseStart_4956818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956845 : List Nat := [1, 5, 2, 1, 1, 3, 2, 3, 5]
def baseStart_4956845 : Nat := 118140960795 + 4956845 * 2 ^ 59
def prefixEnd_4956845 : Nat := 4983230072969 + 3 ^ 40 * 4956845 * 2
def baseEnd_4956845 : Nat := 282804890537307117204599

theorem tailTrace_4956845 : CollatzResearch.WordTrace tailWord_4956845 prefixEnd_4956845 282804890537307117204599 := by
  unfold tailWord_4956845
  simp only [CollatzResearch.WordTrace]
  refine ⟨180790989727204601572887989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120527326484803067715258659 180790989727204601572887989)
  ·
    refine ⟨16949155286925431397458249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180790989727204601572887989 16949155286925431397458249)
    ·
      refine ⟨12711866465194073548093687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16949155286925431397458249 12711866465194073548093687)
      ·
        refine ⟨19067799697791110322140531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12711866465194073548093687 19067799697791110322140531)
        ·
          refine ⟨28601699546686665483210797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19067799697791110322140531 28601699546686665483210797)
          ·
            refine ⟨10725637330007499556204049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28601699546686665483210797 10725637330007499556204049)
            ·
              refine ⟨8044227997505624667153037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10725637330007499556204049 8044227997505624667153037)
              ·
                refine ⟨3016585499064609250182389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8044227997505624667153037 3016585499064609250182389)
                ·
                  refine ⟨282804890537307117204599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3016585499064609250182389 282804890537307117204599)
                  ·
                    rfl

theorem cell23_4956845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_4956845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956845 prefixEnd_4956845 := by exact prefixLift 4956845
  have htrace : WordTrace (prefixWord ++ tailWord_4956845) baseStart_4956845 baseEnd_4956845 := by
    simpa [prefixWord, tailWord_4956845, baseEnd_4956845] using wordTrace_append hprefix tailTrace_4956845
  have hstable : (prefixWord ++ tailWord_4956845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956845).length < 2 ^ (prefixWord ++ tailWord_4956845).sum := by decide
  have hdescent : baseEnd_4956845 < baseStart_4956845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956881 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_4956881 : Nat := 118140960795 + 4956881 * 2 ^ 59
def prefixEnd_4956881 : Nat := 4983230072969 + 3 ^ 40 * 4956881 * 2
def baseEnd_4956881 : Nat := 2545262500139325913991225

theorem tailTrace_4956881 : CollatzResearch.WordTrace tailWord_4956881 prefixEnd_4956881 2545262500139325913991225 := by
  unfold tailWord_4956881
  simp only [CollatzResearch.WordTrace]
  refine ⟨180792302755074179721198497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120528201836716119814132331 180792302755074179721198497)
  ·
    refine ⟨135594227066305634790898873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180792302755074179721198497 135594227066305634790898873)
    ·
      refine ⟨101695670299729226093174155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135594227066305634790898873 101695670299729226093174155)
      ·
        refine ⟨152543505449593839139761233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101695670299729226093174155 152543505449593839139761233)
        ·
          refine ⟨114407629087195379354820925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152543505449593839139761233 114407629087195379354820925)
          ·
            refine ⟨42902860907698267258057847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114407629087195379354820925 42902860907698267258057847)
            ·
              refine ⟨64354291361547400887086771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42902860907698267258057847 64354291361547400887086771)
              ·
                refine ⟨96531437042321101330630157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64354291361547400887086771 96531437042321101330630157)
                ·
                  refine ⟨36199288890870412998986309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96531437042321101330630157 36199288890870412998986309)
                  ·
                    refine ⟨6787366667038202437309933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36199288890870412998986309 6787366667038202437309933)
                    ·
                      refine ⟨2545262500139325913991225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787366667038202437309933 2545262500139325913991225)
                      ·
                        rfl

theorem cell23_4956881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_4956881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956881 prefixEnd_4956881 := by exact prefixLift 4956881
  have htrace : WordTrace (prefixWord ++ tailWord_4956881) baseStart_4956881 baseEnd_4956881 := by
    simpa [prefixWord, tailWord_4956881, baseEnd_4956881] using wordTrace_append hprefix tailTrace_4956881
  have hstable : (prefixWord ++ tailWord_4956881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956881).length < 2 ^ (prefixWord ++ tailWord_4956881).sum := by decide
  have hdescent : baseEnd_4956881 < baseStart_4956881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956888 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 3, 4]
def baseStart_4956888 : Nat := 118140960795 + 4956888 * 2 ^ 59
def prefixEnd_4956888 : Nat := 4983230072969 + 3 ^ 40 * 4956888 * 2
def baseEnd_4956888 : Nat := 848422031501302462201231

theorem tailTrace_4956888 : CollatzResearch.WordTrace tailWord_4956888 prefixEnd_4956888 848422031501302462201231 := by
  unfold tailWord_4956888
  simp only [CollatzResearch.WordTrace]
  refine ⟨90396279033024409958351659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120528372044032546611135545 90396279033024409958351659)
  ·
    refine ⟨135594418549536614937527489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90396279033024409958351659 135594418549536614937527489)
    ·
      refine ⟨101695813912152461203145617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135594418549536614937527489 101695813912152461203145617)
      ·
        refine ⟨76271860434114345902359213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101695813912152461203145617 76271860434114345902359213)
        ·
          refine ⟨28601947662792879713384705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76271860434114345902359213 28601947662792879713384705)
          ·
            refine ⟨21451460747094659785038529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28601947662792879713384705 21451460747094659785038529)
            ·
              refine ⟨16088595560320994838778897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21451460747094659785038529 16088595560320994838778897)
              ·
                refine ⟨12066446670240746129084173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16088595560320994838778897 12066446670240746129084173)
                ·
                  refine ⟨4524917501340279798406565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12066446670240746129084173 4524917501340279798406565)
                  ·
                    refine ⟨848422031501302462201231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4524917501340279798406565 848422031501302462201231)
                    ·
                      rfl

theorem cell23_4956888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_4956888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956888 prefixEnd_4956888 := by exact prefixLift 4956888
  have htrace : WordTrace (prefixWord ++ tailWord_4956888) baseStart_4956888 baseEnd_4956888 := by
    simpa [prefixWord, tailWord_4956888, baseEnd_4956888] using wordTrace_append hprefix tailTrace_4956888
  have hstable : (prefixWord ++ tailWord_4956888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956888).length < 2 ^ (prefixWord ++ tailWord_4956888).sum := by decide
  have hdescent : baseEnd_4956888 < baseStart_4956888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956901 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 8]
def baseStart_4956901 : Nat := 118140960795 + 4956901 * 2 ^ 59
def prefixEnd_4956901 : Nat := 4983230072969 + 3 ^ 40 * 4956901 * 2
def baseEnd_4956901 : Nat := 282808085528046203971237

theorem tailTrace_4956901 : CollatzResearch.WordTrace tailWord_4956901 prefixEnd_4956901 282808085528046203971237 := by
  unfold tailWord_4956901
  simp only [CollatzResearch.WordTrace]
  refine ⟨180793032215001723136926557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120528688143334482091284371 180793032215001723136926557)
  ·
    refine ⟨67797387080625646176347459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180793032215001723136926557 67797387080625646176347459)
    ·
      refine ⟨101696080620938469264521189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67797387080625646176347459 101696080620938469264521189)
      ·
        refine ⟨19068015116425962987097723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101696080620938469264521189 19068015116425962987097723)
        ·
          refine ⟨28602022674638944480646585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19068015116425962987097723 28602022674638944480646585)
          ·
            refine ⟨21451517005979208360484939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28602022674638944480646585 21451517005979208360484939)
            ·
              refine ⟨32177275508968812540727409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21451517005979208360484939 32177275508968812540727409)
              ·
                refine ⟨24132956631726609405545557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32177275508968812540727409 24132956631726609405545557)
                ·
                  refine ⟨282808085528046203971237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24132956631726609405545557 282808085528046203971237)
                  ·
                    rfl

theorem cell23_4956901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_4956901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956901 prefixEnd_4956901 := by exact prefixLift 4956901
  have htrace : WordTrace (prefixWord ++ tailWord_4956901) baseStart_4956901 baseEnd_4956901 := by
    simpa [prefixWord, tailWord_4956901, baseEnd_4956901] using wordTrace_append hprefix tailTrace_4956901
  have hstable : (prefixWord ++ tailWord_4956901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956901).length < 2 ^ (prefixWord ++ tailWord_4956901).sum := by decide
  have hdescent : baseEnd_4956901 < baseStart_4956901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956905 : List Nat := [1, 2, 1, 1, 1, 2, 7, 3, 1, 4]
def baseStart_4956905 : Nat := 118140960795 + 4956905 * 2 ^ 59
def prefixEnd_4956905 : Nat := 4983230072969 + 3 ^ 40 * 4956905 * 2
def baseEnd_4956905 : Nat := 848424941225011273363705

theorem tailTrace_4956905 : CollatzResearch.WordTrace tailWord_4956905 prefixEnd_4956905 848424941225011273363705 := by
  unfold tailWord_4956905
  simp only [CollatzResearch.WordTrace]
  refine ⟨180793178106987231820072169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120528785404658154546714779 180793178106987231820072169)
  ·
    refine ⟨135594883580240423865054127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180793178106987231820072169 135594883580240423865054127)
    ·
      refine ⟨203392325370360635797581191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135594883580240423865054127 203392325370360635797581191)
      ·
        refine ⟨305088488055540953696371787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203392325370360635797581191 305088488055540953696371787)
        ·
          refine ⟨457632732083311430544557681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305088488055540953696371787 457632732083311430544557681)
          ·
            refine ⟨343224549062483572908418261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457632732083311430544557681 343224549062483572908418261)
            ·
              refine ⟨8044325368651958740041053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 343224549062483572908418261 8044325368651958740041053)
              ·
                refine ⟨3016622013244484527515395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8044325368651958740041053 3016622013244484527515395)
                ·
                  refine ⟨4524933019866726791273093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016622013244484527515395 4524933019866726791273093)
                  ·
                    refine ⟨848424941225011273363705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4524933019866726791273093 848424941225011273363705)
                    ·
                      rfl

theorem cell23_4956905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 4].length) (baseStart_4956905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956905 prefixEnd_4956905 := by exact prefixLift 4956905
  have htrace : WordTrace (prefixWord ++ tailWord_4956905) baseStart_4956905 baseEnd_4956905 := by
    simpa [prefixWord, tailWord_4956905, baseEnd_4956905] using wordTrace_append hprefix tailTrace_4956905
  have hstable : (prefixWord ++ tailWord_4956905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956905).length < 2 ^ (prefixWord ++ tailWord_4956905).sum := by decide
  have hdescent : baseEnd_4956905 < baseStart_4956905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956918 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_4956918 : Nat := 118140960795 + 4956918 * 2 ^ 59
def prefixEnd_4956918 : Nat := 4983230072969 + 3 ^ 40 * 4956918 * 2
def baseEnd_4956918 : Nat := 282809055435949141025395

theorem tailTrace_4956918 : CollatzResearch.WordTrace tailWord_4956918 prefixEnd_4956918 282809055435949141025395 := by
  unfold tailWord_4956918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11299603265996258440018463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120529101503960090026863605 11299603265996258440018463)
  ·
    refine ⟨16949404898994387660027695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11299603265996258440018463 16949404898994387660027695)
    ·
      refine ⟨25424107348491581490041543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16949404898994387660027695 25424107348491581490041543)
      ·
        refine ⟨38136161022737372235062315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25424107348491581490041543 38136161022737372235062315)
        ·
          refine ⟨57204241534106058352593473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38136161022737372235062315 57204241534106058352593473)
          ·
            refine ⟨42903181150579543764445105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57204241534106058352593473 42903181150579543764445105)
            ·
              refine ⟨32177385862934657823333829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42903181150579543764445105 32177385862934657823333829)
              ·
                refine ⟨6033259849300248341875093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32177385862934657823333829 6033259849300248341875093)
                ·
                  refine ⟨282809055435949141025395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6033259849300248341875093 282809055435949141025395)
                  ·
                    rfl

theorem cell23_4956918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_4956918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956918 prefixEnd_4956918 := by exact prefixLift 4956918
  have htrace : WordTrace (prefixWord ++ tailWord_4956918) baseStart_4956918 baseEnd_4956918 := by
    simpa [prefixWord, tailWord_4956918, baseEnd_4956918] using wordTrace_append hprefix tailTrace_4956918
  have hstable : (prefixWord ++ tailWord_4956918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956918).length < 2 ^ (prefixWord ++ tailWord_4956918).sum := by decide
  have hdescent : baseEnd_4956918 < baseStart_4956918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956931 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 3, 5]
def baseStart_4956931 : Nat := 118140960795 + 4956931 * 2 ^ 59
def prefixEnd_4956931 : Nat := 4983230072969 + 3 ^ 40 * 4956931 * 2
def baseEnd_4956931 : Nat := 848429391390683572788665

theorem tailTrace_4956931 : CollatzResearch.WordTrace tailWord_4956931 prefixEnd_4956931 848429391390683572788665 := by
  unfold tailWord_4956931
  simp only [CollatzResearch.WordTrace]
  refine ⟨180794126404893038260518647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120529417603262025507012431 180794126404893038260518647)
  ·
    refine ⟨271191189607339557390777971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180794126404893038260518647 271191189607339557390777971)
    ·
      refine ⟨406786784411009336086166957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271191189607339557390777971 406786784411009336086166957)
      ·
        refine ⟨152545044154128501032312609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406786784411009336086166957 152545044154128501032312609)
        ·
          refine ⟨114408783115596375774234457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152545044154128501032312609 114408783115596375774234457)
          ·
            refine ⟨85806587336697281830675843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114408783115596375774234457 85806587336697281830675843)
            ·
              refine ⟨128709881005045922746013765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85806587336697281830675843 128709881005045922746013765)
              ·
                refine ⟨24133102688446110514877581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128709881005045922746013765 24133102688446110514877581)
                ·
                  refine ⟨9049913508167291443079093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24133102688446110514877581 9049913508167291443079093)
                  ·
                    refine ⟨848429391390683572788665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9049913508167291443079093 848429391390683572788665)
                    ·
                      rfl

theorem cell23_4956931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 5].length) (baseStart_4956931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956931 prefixEnd_4956931 := by exact prefixLift 4956931
  have htrace : WordTrace (prefixWord ++ tailWord_4956931) baseStart_4956931 baseEnd_4956931 := by
    simpa [prefixWord, tailWord_4956931, baseEnd_4956931] using wordTrace_append hprefix tailTrace_4956931
  have hstable : (prefixWord ++ tailWord_4956931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956931).length < 2 ^ (prefixWord ++ tailWord_4956931).sum := by decide
  have hdescent : baseEnd_4956931 < baseStart_4956931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956935 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 6]
def baseStart_4956935 : Nat := 118140960795 + 4956935 * 2 ^ 59
def prefixEnd_4956935 : Nat := 4983230072969 + 3 ^ 40 * 4956935 * 2
def baseEnd_4956935 : Nat := 282810025343852078079553

theorem tailTrace_4956935 : CollatzResearch.WordTrace tailWord_4956935 prefixEnd_4956935 282810025343852078079553 := by
  unfold tailWord_4956935
  simp only [CollatzResearch.WordTrace]
  refine ⟨180794272296878546943664259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120529514864585697962442839 180794272296878546943664259)
  ·
    refine ⟨271191408445317820415496389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180794272296878546943664259 271191408445317820415496389)
    ·
      refine ⟨50848389083497091327905573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271191408445317820415496389 50848389083497091327905573)
      ·
        refine ⟨9534072953155704623982295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50848389083497091327905573 9534072953155704623982295)
        ·
          refine ⟨14301109429733556935973443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9534072953155704623982295 14301109429733556935973443)
          ·
            refine ⟨21451664144600335403960165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14301109429733556935973443 21451664144600335403960165)
            ·
              refine ⟨4022187027112562888242531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21451664144600335403960165 4022187027112562888242531)
              ·
                refine ⟨6033280540668844332363797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022187027112562888242531 6033280540668844332363797)
                ·
                  refine ⟨282810025343852078079553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6033280540668844332363797 282810025343852078079553)
                  ·
                    rfl

theorem cell23_4956935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 6].length) (baseStart_4956935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956935 prefixEnd_4956935 := by exact prefixLift 4956935
  have htrace : WordTrace (prefixWord ++ tailWord_4956935) baseStart_4956935 baseEnd_4956935 := by
    simpa [prefixWord, tailWord_4956935, baseEnd_4956935] using wordTrace_append hprefix tailTrace_4956935
  have hstable : (prefixWord ++ tailWord_4956935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956935).length < 2 ^ (prefixWord ++ tailWord_4956935).sum := by decide
  have hdescent : baseEnd_4956935 < baseStart_4956935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956965 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_4956965 : Nat := 118140960795 + 4956965 * 2 ^ 59
def prefixEnd_4956965 : Nat := 4983230072969 + 3 ^ 40 * 4956965 * 2
def baseEnd_4956965 : Nat := 848435210838101195113613

theorem tailTrace_4956965 : CollatzResearch.WordTrace tailWord_4956965 prefixEnd_4956965 848435210838101195113613 := by
  unfold tailWord_4956965
  simp only [CollatzResearch.WordTrace]
  refine ⟨180795366486769862067256349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120530244324513241378170899 180795366486769862067256349)
  ·
    refine ⟨67798262432538698275221131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180795366486769862067256349 67798262432538698275221131)
    ·
      refine ⟨101697393648808047412831697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67798262432538698275221131 101697393648808047412831697)
      ·
        refine ⟨76273045236606035559623773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101697393648808047412831697 76273045236606035559623773)
        ·
          refine ⟨28602391963727263334858915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76273045236606035559623773 28602391963727263334858915)
          ·
            refine ⟨42903587945590895002288373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28602391963727263334858915 42903587945590895002288373)
            ·
              refine ⟨4022211369899146406464535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42903587945590895002288373 4022211369899146406464535)
              ·
                refine ⟨6033317054848719609696803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022211369899146406464535 6033317054848719609696803)
                ·
                  refine ⟨9049975582273079414545205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6033317054848719609696803 9049975582273079414545205)
                  ·
                    refine ⟨848435210838101195113613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9049975582273079414545205 848435210838101195113613)
                    ·
                      rfl

theorem cell23_4956965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_4956965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956965 prefixEnd_4956965 := by exact prefixLift 4956965
  have htrace : WordTrace (prefixWord ++ tailWord_4956965) baseStart_4956965 baseEnd_4956965 := by
    simpa [prefixWord, tailWord_4956965, baseEnd_4956965] using wordTrace_append hprefix tailTrace_4956965
  have hstable : (prefixWord ++ tailWord_4956965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956965).length < 2 ^ (prefixWord ++ tailWord_4956965).sum := by decide
  have hdescent : baseEnd_4956965 < baseStart_4956965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956973 : List Nat := [1, 5, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4956973 : Nat := 118140960795 + 4956973 * 2 ^ 59
def prefixEnd_4956973 : Nat := 4983230072969 + 3 ^ 40 * 4956973 * 2
def baseEnd_4956973 : Nat := 848436580119846518013601

theorem tailTrace_4956973 : CollatzResearch.WordTrace tailWord_4956973 prefixEnd_4956973 848436580119846518013601 := by
  unfold tailWord_4956973
  simp only [CollatzResearch.WordTrace]
  refine ⟨180795658270740879433547573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120530438847160586289031715 180795658270740879433547573)
  ·
    refine ⟨16949592962881957446895085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180795658270740879433547573 16949592962881957446895085)
    ·
      refine ⟨6356097361080734042585657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16949592962881957446895085 6356097361080734042585657)
      ·
        refine ⟨4767073020810550531939243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6356097361080734042585657 4767073020810550531939243)
        ·
          refine ⟨7150609531215825797908865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767073020810550531939243 7150609531215825797908865)
          ·
            refine ⟨5362957148411869348431649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7150609531215825797908865 5362957148411869348431649)
            ·
              refine ⟨4022217861308902011323737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5362957148411869348431649 4022217861308902011323737)
              ·
                refine ⟨3016663395981676508492803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022217861308902011323737 3016663395981676508492803)
                ·
                  refine ⟨4524995093972514762739205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016663395981676508492803 4524995093972514762739205)
                  ·
                    refine ⟨848436580119846518013601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4524995093972514762739205 848436580119846518013601)
                    ·
                      rfl

theorem cell23_4956973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4956973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956973 prefixEnd_4956973 := by exact prefixLift 4956973
  have htrace : WordTrace (prefixWord ++ tailWord_4956973) baseStart_4956973 baseEnd_4956973 := by
    simpa [prefixWord, tailWord_4956973, baseEnd_4956973] using wordTrace_append hprefix tailTrace_4956973
  have hstable : (prefixWord ++ tailWord_4956973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956973).length < 2 ^ (prefixWord ++ tailWord_4956973).sum := by decide
  have hdescent : baseEnd_4956973 < baseStart_4956973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4956979 : List Nat := [1, 1, 1, 2, 6, 1, 4, 2, 1, 1, 3]
def baseStart_4956979 : Nat := 118140960795 + 4956979 * 2 ^ 59
def prefixEnd_4956979 : Nat := 4983230072969 + 3 ^ 40 * 4956979 * 2
def baseEnd_4956979 : Nat := 2545312821243466530565775

theorem tailTrace_4956979 : CollatzResearch.WordTrace tailWord_4956979 prefixEnd_4956979 2545312821243466530565775 := by
  unfold tailWord_4956979
  simp only [CollatzResearch.WordTrace]
  refine ⟨180795877108719142458265991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120530584739146094972177327 180795877108719142458265991)
  ·
    refine ⟨271193815663078713687398987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180795877108719142458265991 271193815663078713687398987)
    ·
      refine ⟨406790723494618070531098481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271193815663078713687398987 406790723494618070531098481)
      ·
        refine ⟨305093042620963552898323861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406790723494618070531098481 305093042620963552898323861)
        ·
          refine ⟨14301236372857666542108931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 305093042620963552898323861 14301236372857666542108931)
          ·
            refine ⟨21451854559286499813163397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14301236372857666542108931 21451854559286499813163397)
            ·
              refine ⟨4022222729866218714968137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21451854559286499813163397 4022222729866218714968137)
              ·
                refine ⟨3016667047399664036226103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022222729866218714968137 3016667047399664036226103)
                ·
                  refine ⟨4525000571099496054339155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3016667047399664036226103 4525000571099496054339155)
                  ·
                    refine ⟨6787500856649244081508733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4525000571099496054339155 6787500856649244081508733)
                    ·
                      refine ⟨2545312821243466530565775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787500856649244081508733 2545312821243466530565775)
                      ·
                        rfl

theorem cell23_4956979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 1, 3].length) (baseStart_4956979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4956979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4956979 prefixEnd_4956979 := by exact prefixLift 4956979
  have htrace : WordTrace (prefixWord ++ tailWord_4956979) baseStart_4956979 baseEnd_4956979 := by
    simpa [prefixWord, tailWord_4956979, baseEnd_4956979] using wordTrace_append hprefix tailTrace_4956979
  have hstable : (prefixWord ++ tailWord_4956979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4956979).length < 2 ^ (prefixWord ++ tailWord_4956979).sum := by decide
  have hdescent : baseEnd_4956979 < baseStart_4956979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4956979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957088 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_4957088 : Nat := 118140960795 + 4957088 * 2 ^ 59
def prefixEnd_4957088 : Nat := 4983230072969 + 3 ^ 40 * 4957088 * 2
def baseEnd_4957088 : Nat := 2545368790634806604102773

theorem tailTrace_4957088 : CollatzResearch.WordTrace tailWord_4957088 prefixEnd_4957088 2545368790634806604102773 := by
  unfold tailWord_4957088
  simp only [CollatzResearch.WordTrace]
  refine ⟨90399926332662127036991959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120533235110216169382655945 90399926332662127036991959)
  ·
    refine ⟨135599889498993190555487939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90399926332662127036991959 135599889498993190555487939)
    ·
      refine ⟨203399834248489785833231909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135599889498993190555487939 203399834248489785833231909)
      ·
        refine ⟨38137468921591834843730983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203399834248489785833231909 38137468921591834843730983)
        ·
          refine ⟨57206203382387752265596475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38137468921591834843730983 57206203382387752265596475)
          ·
            refine ⟨85809305073581628398394713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57206203382387752265596475 85809305073581628398394713)
            ·
              refine ⟨64356978805186221298796035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85809305073581628398394713 64356978805186221298796035)
              ·
                refine ⟨96535468207779331948194053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64356978805186221298796035 96535468207779331948194053)
                ·
                  refine ⟨18100400288958624740286385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96535468207779331948194053 18100400288958624740286385)
                  ·
                    refine ⟨13575300216718968555214789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18100400288958624740286385 13575300216718968555214789)
                    ·
                      refine ⟨2545368790634806604102773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13575300216718968555214789 2545368790634806604102773)
                      ·
                        rfl

theorem cell23_4957088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_4957088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957088 prefixEnd_4957088 := by exact prefixLift 4957088
  have htrace : WordTrace (prefixWord ++ tailWord_4957088) baseStart_4957088 baseEnd_4957088 := by
    simpa [prefixWord, tailWord_4957088, baseEnd_4957088] using wordTrace_append hprefix tailTrace_4957088
  have hstable : (prefixWord ++ tailWord_4957088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957088).length < 2 ^ (prefixWord ++ tailWord_4957088).sum := by decide
  have hdescent : baseEnd_4957088 < baseStart_4957088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957092 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_4957092 : Nat := 118140960795 + 4957092 * 2 ^ 59
def prefixEnd_4957092 : Nat := 4983230072969 + 3 ^ 40 * 4957092 * 2
def baseEnd_4957092 : Nat := 2545370844557424588452755

theorem tailTrace_4957092 : CollatzResearch.WordTrace tailWord_4957092 prefixEnd_4957092 2545370844557424588452755 := by
  unfold tailWord_4957092
  simp only [CollatzResearch.WordTrace]
  refine ⟨90399999278654881378564765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120533332371539841838086353 90399999278654881378564765)
  ·
    refine ⟨33899999729495580516961787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90399999278654881378564765 33899999729495580516961787)
    ·
      refine ⟨50849999594243370775442681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33899999729495580516961787 50849999594243370775442681)
      ·
        refine ⟨38137499695682528081582011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50849999594243370775442681 38137499695682528081582011)
        ·
          refine ⟨57206249543523792122373017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38137499695682528081582011 57206249543523792122373017)
          ·
            refine ⟨42904687157642844091779763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57206249543523792122373017 42904687157642844091779763)
            ·
              refine ⟨64357030736464266137669645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42904687157642844091779763 64357030736464266137669645)
              ·
                refine ⟨24133886526174099801626117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64357030736464266137669645 24133886526174099801626117)
                ·
                  refine ⟨4525103723657643712804897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24133886526174099801626117 4525103723657643712804897)
                  ·
                    refine ⟨3393827792743232784603673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4525103723657643712804897 3393827792743232784603673)
                    ·
                      refine ⟨2545370844557424588452755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393827792743232784603673 2545370844557424588452755)
                      ·
                        rfl

theorem cell23_4957092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_4957092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957092 prefixEnd_4957092 := by exact prefixLift 4957092
  have htrace : WordTrace (prefixWord ++ tailWord_4957092) baseStart_4957092 baseEnd_4957092 := by
    simpa [prefixWord, tailWord_4957092, baseEnd_4957092] using wordTrace_append hprefix tailTrace_4957092
  have hstable : (prefixWord ++ tailWord_4957092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957092).length < 2 ^ (prefixWord ++ tailWord_4957092).sum := by decide
  have hdescent : baseEnd_4957092 < baseStart_4957092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957109 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_4957109 : Nat := 118140960795 + 4957109 * 2 ^ 59
def prefixEnd_4957109 : Nat := 4983230072969 + 3 ^ 40 * 4957109 * 2
def baseEnd_4957109 : Nat := 2545379573728551021940177

theorem tailTrace_4957109 : CollatzResearch.WordTrace tailWord_4957109 prefixEnd_4957109 2545379573728551021940177 := by
  unfold tailWord_4957109
  simp only [CollatzResearch.WordTrace]
  refine ⟨180800618598248174660498381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120533745732165449773665587 180800618598248174660498381)
  ·
    refine ⟨67800231974343065497686893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180800618598248174660498381 67800231974343065497686893)
    ·
      refine ⟨25425086990378649561632585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67800231974343065497686893 25425086990378649561632585)
      ·
        refine ⟨19068815242783987171224439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25425086990378649561632585 19068815242783987171224439)
        ·
          refine ⟨28603222864175980756836659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19068815242783987171224439 28603222864175980756836659)
          ·
            refine ⟨42904834296263971135254989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28603222864175980756836659 42904834296263971135254989)
            ·
              refine ⟨16089312861098989175720621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42904834296263971135254989 16089312861098989175720621)
              ·
                refine ⟨6033492322912120940895233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16089312861098989175720621 6033492322912120940895233)
                ·
                  refine ⟨4525119242184090705671425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6033492322912120940895233 4525119242184090705671425)
                  ·
                    refine ⟨3393839431638068029253569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4525119242184090705671425 3393839431638068029253569)
                    ·
                      refine ⟨2545379573728551021940177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393839431638068029253569 2545379573728551021940177)
                      ·
                        rfl

theorem cell23_4957109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_4957109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957109 prefixEnd_4957109 := by exact prefixLift 4957109
  have htrace : WordTrace (prefixWord ++ tailWord_4957109) baseStart_4957109 baseEnd_4957109 := by
    simpa [prefixWord, tailWord_4957109, baseEnd_4957109] using wordTrace_append hprefix tailTrace_4957109
  have hstable : (prefixWord ++ tailWord_4957109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957109).length < 2 ^ (prefixWord ++ tailWord_4957109).sum := by decide
  have hdescent : baseEnd_4957109 < baseStart_4957109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957145 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 2, 5]
def baseStart_4957145 : Nat := 118140960795 + 4957145 * 2 ^ 59
def prefixEnd_4957145 : Nat := 4983230072969 + 3 ^ 40 * 4957145 * 2
def baseEnd_4957145 : Nat := 848466019677370960363337

theorem tailTrace_4957145 : CollatzResearch.WordTrace tailWord_4957145 prefixEnd_4957145 848466019677370960363337 := by
  unfold tailWord_4957145
  simp only [CollatzResearch.WordTrace]
  refine ⟨180801931626117752808808889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120534621084078501872539259 180801931626117752808808889)
  ·
    refine ⟨135601448719588314606606667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180801931626117752808808889 135601448719588314606606667)
    ·
      refine ⟨203402173079382471909910001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135601448719588314606606667 203402173079382471909910001)
      ·
        refine ⟨152551629809536853932432501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203402173079382471909910001 152551629809536853932432501)
        ·
          refine ⟨14301715294644080056165547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152551629809536853932432501 14301715294644080056165547)
          ·
            refine ⟨21452572941966120084248321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14301715294644080056165547 21452572941966120084248321)
            ·
              refine ⟨16089429706474590063186241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21452572941966120084248321 16089429706474590063186241)
              ·
                refine ⟨12067072279855942547389681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16089429706474590063186241 12067072279855942547389681)
                ·
                  refine ⟨9050304209891956910542261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12067072279855942547389681 9050304209891956910542261)
                  ·
                    refine ⟨848466019677370960363337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9050304209891956910542261 848466019677370960363337)
                    ·
                      rfl

theorem cell23_4957145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_4957145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957145 prefixEnd_4957145 := by exact prefixLift 4957145
  have htrace : WordTrace (prefixWord ++ tailWord_4957145) baseStart_4957145 baseEnd_4957145 := by
    simpa [prefixWord, tailWord_4957145, baseEnd_4957145] using wordTrace_append hprefix tailTrace_4957145
  have hstable : (prefixWord ++ tailWord_4957145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957145).length < 2 ^ (prefixWord ++ tailWord_4957145).sum := by decide
  have hdescent : baseEnd_4957145 < baseStart_4957145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957149 : List Nat := [1, 4, 3, 1, 2, 1, 4, 2, 5]
def baseStart_4957149 : Nat := 118140960795 + 4957149 * 2 ^ 59
def prefixEnd_4957149 : Nat := 4983230072969 + 3 ^ 40 * 4957149 * 2
def baseEnd_4957149 : Nat := 282822234772747873937777

theorem tailTrace_4957149 : CollatzResearch.WordTrace tailWord_4957149 prefixEnd_4957149 282822234772747873937777 := by
  unfold tailWord_4957149
  simp only [CollatzResearch.WordTrace]
  refine ⟨180802077518103261491954501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120534718345402174327969667 180802077518103261491954501)
  ·
    refine ⟨33900389534644361529741469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180802077518103261491954501 33900389534644361529741469)
    ·
      refine ⟨12712646075491635573653051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33900389534644361529741469 12712646075491635573653051)
      ·
        refine ⟨19068969113237453360479577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12712646075491635573653051 19068969113237453360479577)
        ·
          refine ⟨14301726834928090020359683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19068969113237453360479577 14301726834928090020359683)
          ·
            refine ⟨21452590252392135030539525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14301726834928090020359683 21452590252392135030539525)
            ·
              refine ⟨4022360672323525318226161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21452590252392135030539525 4022360672323525318226161)
              ·
                refine ⟨3016770504242643988669621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022360672323525318226161 3016770504242643988669621)
                ·
                  refine ⟨282822234772747873937777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3016770504242643988669621 282822234772747873937777)
                  ·
                    rfl

theorem cell23_4957149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_4957149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957149 prefixEnd_4957149 := by exact prefixLift 4957149
  have htrace : WordTrace (prefixWord ++ tailWord_4957149) baseStart_4957149 baseEnd_4957149 := by
    simpa [prefixWord, tailWord_4957149, baseEnd_4957149] using wordTrace_append hprefix tailTrace_4957149
  have hstable : (prefixWord ++ tailWord_4957149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957149).length < 2 ^ (prefixWord ++ tailWord_4957149).sum := by decide
  have hdescent : baseEnd_4957149 < baseStart_4957149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957178 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_4957178 : Nat := 118140960795 + 4957178 * 2 ^ 59
def prefixEnd_4957178 : Nat := 4983230072969 + 3 ^ 40 * 4957178 * 2
def baseEnd_4957178 : Nat := 2545415003893711251977359

theorem tailTrace_4957178 : CollatzResearch.WordTrace tailWord_4957178 prefixEnd_4957178 2545415003893711251977359 := by
  unfold tailWord_4957178
  simp only [CollatzResearch.WordTrace]
  refine ⟨45200783808749549861190047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120535423489998799629840125 45200783808749549861190047)
  ·
    refine ⟨67801175713124324791785071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45200783808749549861190047 67801175713124324791785071)
    ·
      refine ⟨101701763569686487187677607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67801175713124324791785071 101701763569686487187677607)
      ·
        refine ⟨152552645354529730781516411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101701763569686487187677607 152552645354529730781516411)
        ·
          refine ⟨228828968031794596172274617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152552645354529730781516411 228828968031794596172274617)
          ·
            refine ⟨171621726023845947129205963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228828968031794596172274617 171621726023845947129205963)
            ·
              refine ⟨257432589035768920693808945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171621726023845947129205963 257432589035768920693808945)
              ·
                refine ⟨193074441776826690520356709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257432589035768920693808945 193074441776826690520356709)
                ·
                  refine ⟨36201457833155004472566883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193074441776826690520356709 36201457833155004472566883)
                  ·
                    refine ⟨54302186749732506708850325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36201457833155004472566883 54302186749732506708850325)
                    ·
                      refine ⟨2545415003893711251977359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54302186749732506708850325 2545415003893711251977359)
                      ·
                        rfl

theorem cell23_4957178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_4957178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957178 prefixEnd_4957178 := by exact prefixLift 4957178
  have htrace : WordTrace (prefixWord ++ tailWord_4957178) baseStart_4957178 baseEnd_4957178 := by
    simpa [prefixWord, tailWord_4957178, baseEnd_4957178] using wordTrace_append hprefix tailTrace_4957178
  have hstable : (prefixWord ++ tailWord_4957178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957178).length < 2 ^ (prefixWord ++ tailWord_4957178).sum := by decide
  have hdescent : baseEnd_4957178 < baseStart_4957178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957205 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 8]
def baseStart_4957205 : Nat := 118140960795 + 4957205 * 2 ^ 59
def prefixEnd_4957205 : Nat := 4983230072969 + 3 ^ 40 * 4957205 * 2
def baseEnd_4957205 : Nat := 282825429763486960704415

theorem tailTrace_4957205 : CollatzResearch.WordTrace tailWord_4957205 prefixEnd_4957205 282825429763486960704415 := by
  unfold tailWord_4957205
  simp only [CollatzResearch.WordTrace]
  refine ⟨180804120005900383055993069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120536080003933588703995379 180804120005900383055993069)
  ·
    refine ⟨67801545002212643645997401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180804120005900383055993069 67801545002212643645997401)
    ·
      refine ⟨50851158751659482734498051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67801545002212643645997401 50851158751659482734498051)
      ·
        refine ⟨76276738127489224101747077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50851158751659482734498051 76276738127489224101747077)
        ·
          refine ⟨14301888398904229519077577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76276738127489224101747077 14301888398904229519077577)
          ·
            refine ⟨10726416299178172139308183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14301888398904229519077577 10726416299178172139308183)
            ·
              refine ⟨16089624448767258208962275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10726416299178172139308183 16089624448767258208962275)
              ·
                refine ⟨24134436673150887313443413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16089624448767258208962275 24134436673150887313443413)
                ·
                  refine ⟨282825429763486960704415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24134436673150887313443413 282825429763486960704415)
                  ·
                    rfl

theorem cell23_4957205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_4957205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957205 prefixEnd_4957205 := by exact prefixLift 4957205
  have htrace : WordTrace (prefixWord ++ tailWord_4957205) baseStart_4957205 baseEnd_4957205 := by
    simpa [prefixWord, tailWord_4957205, baseEnd_4957205] using wordTrace_append hprefix tailTrace_4957205
  have hstable : (prefixWord ++ tailWord_4957205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957205).length < 2 ^ (prefixWord ++ tailWord_4957205).sum := by decide
  have hdescent : baseEnd_4957205 < baseStart_4957205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957232 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 3, 1, 3]
def baseStart_4957232 : Nat := 118140960795 + 4957232 * 2 ^ 59
def prefixEnd_4957232 : Nat := 4983230072969 + 3 ^ 40 * 4957232 * 2
def baseEnd_4957232 : Nat := 2545442731849054040702111

theorem tailTrace_4957232 : CollatzResearch.WordTrace tailWord_4957232 prefixEnd_4957232 2545442731849054040702111 := by
  unfold tailWord_4957232
  simp only [CollatzResearch.WordTrace]
  refine ⟨90402552388401283333612975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120536736517868377778150633 90402552388401283333612975)
  ·
    refine ⟨135603828582601925000419463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90402552388401283333612975 135603828582601925000419463)
    ·
      refine ⟨203405742873902887500629195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135603828582601925000419463 203405742873902887500629195)
      ·
        refine ⟨305108614310854331250943793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203405742873902887500629195 305108614310854331250943793)
        ·
          refine ⟨228831460733140748438207845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305108614310854331250943793 228831460733140748438207845)
          ·
            refine ⟨42905898887463890332163971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228831460733140748438207845 42905898887463890332163971)
            ·
              refine ⟨64358848331195835498245957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42905898887463890332163971 64358848331195835498245957)
              ·
                refine ⟨12067284062099219155921117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64358848331195835498245957 12067284062099219155921117)
                ·
                  refine ⟨4525231523287207183470419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12067284062099219155921117 4525231523287207183470419)
                  ·
                    refine ⟨6787847284930810775205629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4525231523287207183470419 6787847284930810775205629)
                    ·
                      refine ⟨2545442731849054040702111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787847284930810775205629 2545442731849054040702111)
                      ·
                        rfl

theorem cell23_4957232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 1, 3].length) (baseStart_4957232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957232 prefixEnd_4957232 := by exact prefixLift 4957232
  have htrace : WordTrace (prefixWord ++ tailWord_4957232) baseStart_4957232 baseEnd_4957232 := by
    simpa [prefixWord, tailWord_4957232, baseEnd_4957232] using wordTrace_append hprefix tailTrace_4957232
  have hstable : (prefixWord ++ tailWord_4957232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957232).length < 2 ^ (prefixWord ++ tailWord_4957232).sum := by decide
  have hdescent : baseEnd_4957232 < baseStart_4957232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957242 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2]
def baseStart_4957242 : Nat := 118140960795 + 4957242 * 2 ^ 59
def prefixEnd_4957242 : Nat := 4983230072969 + 3 ^ 40 * 4957242 * 2
def baseEnd_4957242 : Nat := 2545447866655599001577065

theorem tailTrace_4957242 : CollatzResearch.WordTrace tailWord_4957242 prefixEnd_4957242 2545447866655599001577065 := by
  unfold tailWord_4957242
  simp only [CollatzResearch.WordTrace]
  refine ⟨45201367376691584593772495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120536979671177558916726653 45201367376691584593772495)
  ·
    refine ⟨67802051065037376890658743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45201367376691584593772495 67802051065037376890658743)
    ·
      refine ⟨101703076597556065335988115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67802051065037376890658743 101703076597556065335988115)
      ·
        refine ⟨152554614896334098003982173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101703076597556065335988115 152554614896334098003982173)
        ·
          refine ⟨57207980586125286751493315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152554614896334098003982173 57207980586125286751493315)
          ·
            refine ⟨85811970879187930127239973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57207980586125286751493315 85811970879187930127239973)
            ·
              refine ⟨16089744539847736898857495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85811970879187930127239973 16089744539847736898857495)
              ·
                refine ⟨24134616809771605348286243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16089744539847736898857495 24134616809771605348286243)
                ·
                  refine ⟨36201925214657408022429365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24134616809771605348286243 36201925214657408022429365)
                  ·
                    refine ⟨3393930488874132002102753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36201925214657408022429365 3393930488874132002102753)
                    ·
                      refine ⟨2545447866655599001577065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3393930488874132002102753 2545447866655599001577065)
                      ·
                        rfl

theorem cell23_4957242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_4957242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957242 prefixEnd_4957242 := by exact prefixLift 4957242
  have htrace : WordTrace (prefixWord ++ tailWord_4957242) baseStart_4957242 baseEnd_4957242 := by
    simpa [prefixWord, tailWord_4957242, baseEnd_4957242] using wordTrace_append hprefix tailTrace_4957242
  have hstable : (prefixWord ++ tailWord_4957242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957242).length < 2 ^ (prefixWord ++ tailWord_4957242).sum := by decide
  have hdescent : baseEnd_4957242 < baseStart_4957242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957266 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_4957266 : Nat := 118140960795 + 4957266 * 2 ^ 59
def prefixEnd_4957266 : Nat := 4983230072969 + 3 ^ 40 * 4957266 * 2
def baseEnd_4957266 : Nat := 2545460190191306907676955

theorem tailTrace_4957266 : CollatzResearch.WordTrace tailWord_4957266 prefixEnd_4957266 2545460190191306907676955 := by
  unfold tailWord_4957266
  simp only [CollatzResearch.WordTrace]
  refine ⟨45201586214669847618490913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120537563239119593649309101 45201586214669847618490913)
  ·
    refine ⟨33901189661002385713868185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45201586214669847618490913 33901189661002385713868185)
    ·
      refine ⟨25425892245751789285401139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33901189661002385713868185 25425892245751789285401139)
      ·
        refine ⟨38138838368627683928101709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25425892245751789285401139 38138838368627683928101709)
        ·
          refine ⟨14302064388235381473038141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38138838368627683928101709 14302064388235381473038141)
          ·
            refine ⟨5363274145588268052389303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14302064388235381473038141 5363274145588268052389303)
            ·
              refine ⟨8044911218382402078583955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363274145588268052389303 8044911218382402078583955)
              ·
                refine ⟨12067366827573603117875933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8044911218382402078583955 12067366827573603117875933)
                ·
                  refine ⟨4525262560340101169203475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12067366827573603117875933 4525262560340101169203475)
                  ·
                    refine ⟨6787893840510151753805213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4525262560340101169203475 6787893840510151753805213)
                    ·
                      refine ⟨2545460190191306907676955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787893840510151753805213 2545460190191306907676955)
                      ·
                        rfl

theorem cell23_4957266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_4957266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957266 prefixEnd_4957266 := by exact prefixLift 4957266
  have htrace : WordTrace (prefixWord ++ tailWord_4957266) baseStart_4957266 baseEnd_4957266 := by
    simpa [prefixWord, tailWord_4957266, baseEnd_4957266] using wordTrace_append hprefix tailTrace_4957266
  have hstable : (prefixWord ++ tailWord_4957266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957266).length < 2 ^ (prefixWord ++ tailWord_4957266).sum := by decide
  have hdescent : baseEnd_4957266 < baseStart_4957266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957285 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_4957285 : Nat := 118140960795 + 4957285 * 2 ^ 59
def prefixEnd_4957285 : Nat := 4983230072969 + 3 ^ 40 * 4957285 * 2
def baseEnd_4957285 : Nat := 2545469946323742333339367

theorem tailTrace_4957285 : CollatzResearch.WordTrace tailWord_4957285 prefixEnd_4957285 2545469946323742333339367 := by
  unfold tailWord_4957285
  simp only [CollatzResearch.WordTrace]
  refine ⟨180807037845610556718905309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120538025230407037812603539 180807037845610556718905309)
  ·
    refine ⟨67802639192103958769589491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180807037845610556718905309 67802639192103958769589491)
    ·
      refine ⟨101703958788155938154384237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67802639192103958769589491 101703958788155938154384237)
      ·
        refine ⟨38138984545558476807894089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101703958788155938154384237 38138984545558476807894089)
        ·
          refine ⟨28604238409168857605920567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38138984545558476807894089 28604238409168857605920567)
          ·
            refine ⟨42906357613753286408880851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28604238409168857605920567 42906357613753286408880851)
            ·
              refine ⟨64359536420629929613321277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42906357613753286408880851 64359536420629929613321277)
              ·
                refine ⟨24134826157736223604995479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64359536420629929613321277 24134826157736223604995479)
                ·
                  refine ⟨36202239236604335407493219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24134826157736223604995479 36202239236604335407493219)
                  ·
                    refine ⟨54303358854906503111239829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36202239236604335407493219 54303358854906503111239829)
                    ·
                      refine ⟨2545469946323742333339367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54303358854906503111239829 2545469946323742333339367)
                      ·
                        rfl

theorem cell23_4957285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_4957285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957285 prefixEnd_4957285 := by exact prefixLift 4957285
  have htrace : WordTrace (prefixWord ++ tailWord_4957285) baseStart_4957285 baseEnd_4957285 := by
    simpa [prefixWord, tailWord_4957285, baseEnd_4957285] using wordTrace_append hprefix tailTrace_4957285
  have hstable : (prefixWord ++ tailWord_4957285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957285).length < 2 ^ (prefixWord ++ tailWord_4957285).sum := by decide
  have hdescent : baseEnd_4957285 < baseStart_4957285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957289 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 4]
def baseStart_4957289 : Nat := 118140960795 + 4957289 * 2 ^ 59
def prefixEnd_4957289 : Nat := 4983230072969 + 3 ^ 40 * 4957289 * 2
def baseEnd_4957289 : Nat := 2545472000246360317689349

theorem tailTrace_4957289 : CollatzResearch.WordTrace tailWord_4957289 prefixEnd_4957289 2545472000246360317689349 := by
  unfold tailWord_4957289
  simp only [CollatzResearch.WordTrace]
  refine ⟨180807183737596065402050921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120538122491730710268033947 180807183737596065402050921)
  ·
    refine ⟨135605387803197049051538191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180807183737596065402050921 135605387803197049051538191)
    ·
      refine ⟨203408081704795573577307287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135605387803197049051538191 203408081704795573577307287)
      ·
        refine ⟨305112122557193360365960931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203408081704795573577307287 305112122557193360365960931)
        ·
          refine ⟨457668183835790040548941397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305112122557193360365960931 457668183835790040548941397)
          ·
            refine ⟨5363299029325664537682907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 457668183835790040548941397 5363299029325664537682907)
            ·
              refine ⟨8044948543988496806524361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363299029325664537682907 8044948543988496806524361)
              ·
                refine ⟨6033711407991372604893271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8044948543988496806524361 6033711407991372604893271)
                ·
                  refine ⟨9050567111987058907339907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6033711407991372604893271 9050567111987058907339907)
                  ·
                    refine ⟨13575850667980588361009861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9050567111987058907339907 13575850667980588361009861)
                    ·
                      refine ⟨2545472000246360317689349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13575850667980588361009861 2545472000246360317689349)
                      ·
                        rfl

theorem cell23_4957289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_4957289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957289 prefixEnd_4957289 := by exact prefixLift 4957289
  have htrace : WordTrace (prefixWord ++ tailWord_4957289) baseStart_4957289 baseEnd_4957289 := by
    simpa [prefixWord, tailWord_4957289, baseEnd_4957289] using wordTrace_append hprefix tailTrace_4957289
  have hstable : (prefixWord ++ tailWord_4957289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957289).length < 2 ^ (prefixWord ++ tailWord_4957289).sum := by decide
  have hdescent : baseEnd_4957289 < baseStart_4957289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957292 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_4957292 : Nat := 118140960795 + 4957292 * 2 ^ 59
def prefixEnd_4957292 : Nat := 4983230072969 + 3 ^ 40 * 4957292 * 2
def baseEnd_4957292 : Nat := 2545473540688323805951835

theorem tailTrace_4957292 : CollatzResearch.WordTrace tailWord_4957292 prefixEnd_4957292 2545473540688323805951835 := by
  unfold tailWord_4957292
  simp only [CollatzResearch.WordTrace]
  refine ⟨90403646578292598457205065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120538195437723464609606753 90403646578292598457205065)
  ·
    refine ⟨67802734933719448842903799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90403646578292598457205065 67802734933719448842903799)
    ·
      refine ⟨101704102400579173264355699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67802734933719448842903799 101704102400579173264355699)
      ·
        refine ⟨152556153600868759896533549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101704102400579173264355699 152556153600868759896533549)
        ·
          refine ⟨57208557600325784961200081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152556153600868759896533549 57208557600325784961200081)
          ·
            refine ⟨42906418200244338720900061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57208557600325784961200081 42906418200244338720900061)
            ·
              refine ⟨16089906825091627020337523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42906418200244338720900061 16089906825091627020337523)
              ·
                refine ⟨24134860237637440530506285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16089906825091627020337523 24134860237637440530506285)
                ·
                  refine ⟨9050572589114040198939857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24134860237637440530506285 9050572589114040198939857)
                  ·
                    refine ⟨6787929441835530149204893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9050572589114040198939857 6787929441835530149204893)
                    ·
                      refine ⟨2545473540688323805951835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787929441835530149204893 2545473540688323805951835)
                      ·
                        rfl

theorem cell23_4957292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_4957292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957292 prefixEnd_4957292 := by exact prefixLift 4957292
  have htrace : WordTrace (prefixWord ++ tailWord_4957292) baseStart_4957292 baseEnd_4957292 := by
    simpa [prefixWord, tailWord_4957292, baseEnd_4957292] using wordTrace_append hprefix tailTrace_4957292
  have hstable : (prefixWord ++ tailWord_4957292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957292).length < 2 ^ (prefixWord ++ tailWord_4957292).sum := by decide
  have hdescent : baseEnd_4957292 < baseStart_4957292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957322 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_4957322 : Nat := 118140960795 + 4957322 * 2 ^ 59
def prefixEnd_4957322 : Nat := 4983230072969 + 3 ^ 40 * 4957322 * 2
def baseEnd_4957322 : Nat := 2545488945107958688576697

theorem tailTrace_4957322 : CollatzResearch.WordTrace tailWord_4957322 prefixEnd_4957322 2545488945107958688576697 := by
  unfold tailWord_4957322
  simp only [CollatzResearch.WordTrace]
  refine ⟨45202096836619128009500555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120538924897651008025334813 45202096836619128009500555)
  ·
    refine ⟨67803145254928692014250833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45202096836619128009500555 67803145254928692014250833)
    ·
      refine ⟨50852358941196519010688125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67803145254928692014250833 50852358941196519010688125)
      ·
        refine ⟨19069634602948694629008047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50852358941196519010688125 19069634602948694629008047)
        ·
          refine ⟨28604451904423041943512071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19069634602948694629008047 28604451904423041943512071)
          ·
            refine ⟨42906677856634562915268107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28604451904423041943512071 42906677856634562915268107)
            ·
              refine ⟨64360016784951844372902161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42906677856634562915268107 64360016784951844372902161)
              ·
                refine ⟨48270012588713883279676621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64360016784951844372902161 48270012588713883279676621)
                ·
                  refine ⟨18101254720767706229878733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48270012588713883279676621 18101254720767706229878733)
                  ·
                    refine ⟨6787970520287889836204525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18101254720767706229878733 6787970520287889836204525)
                    ·
                      refine ⟨2545488945107958688576697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6787970520287889836204525 2545488945107958688576697)
                      ·
                        rfl

theorem cell23_4957322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_4957322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957322 prefixEnd_4957322 := by exact prefixLift 4957322
  have htrace : WordTrace (prefixWord ++ tailWord_4957322) baseStart_4957322 baseEnd_4957322 := by
    simpa [prefixWord, tailWord_4957322, baseEnd_4957322] using wordTrace_append hprefix tailTrace_4957322
  have hstable : (prefixWord ++ tailWord_4957322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957322).length < 2 ^ (prefixWord ++ tailWord_4957322).sum := by decide
  have hdescent : baseEnd_4957322 < baseStart_4957322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957349 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 3, 3, 2]
def baseStart_4957349 : Nat := 118140960795 + 4957349 * 2 ^ 59
def prefixEnd_4957349 : Nat := 4983230072969 + 3 ^ 40 * 4957349 * 2
def baseEnd_4957349 : Nat := 2545502809085630082939073

theorem tailTrace_4957349 : CollatzResearch.WordTrace tailWord_4957349 prefixEnd_4957349 2545502809085630082939073 := by
  unfold tailWord_4957349
  simp only [CollatzResearch.WordTrace]
  refine ⟨180809372117378695649235101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120539581411585797099490067 180809372117378695649235101)
  ·
    refine ⟨67803514544017010868463163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180809372117378695649235101 67803514544017010868463163)
    ·
      refine ⟨101705271816025516302694745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67803514544017010868463163 101705271816025516302694745)
      ·
        refine ⟨76278953862019137227021059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101705271816025516302694745 76278953862019137227021059)
        ·
          refine ⟨114418430793028705840531589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76278953862019137227021059 114418430793028705840531589)
          ·
            refine ⟨21453455773692882345099673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114418430793028705840531589 21453455773692882345099673)
            ·
              refine ⟨16090091830269661758824755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21453455773692882345099673 16090091830269661758824755)
              ·
                refine ⟨24135137745404492638237133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16090091830269661758824755 24135137745404492638237133)
                ·
                  refine ⟨9050676654526684739338925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24135137745404492638237133 9050676654526684739338925)
                  ·
                    refine ⟨3394003745447506777252097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9050676654526684739338925 3394003745447506777252097)
                    ·
                      refine ⟨2545502809085630082939073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394003745447506777252097 2545502809085630082939073)
                      ·
                        rfl

theorem cell23_4957349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_4957349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957349 prefixEnd_4957349 := by exact prefixLift 4957349
  have htrace : WordTrace (prefixWord ++ tailWord_4957349) baseStart_4957349 baseEnd_4957349 := by
    simpa [prefixWord, tailWord_4957349, baseEnd_4957349] using wordTrace_append hprefix tailTrace_4957349
  have hstable : (prefixWord ++ tailWord_4957349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957349).length < 2 ^ (prefixWord ++ tailWord_4957349).sum := by decide
  have hdescent : baseEnd_4957349 < baseStart_4957349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957372 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_4957372 : Nat := 118140960795 + 4957372 * 2 ^ 59
def prefixEnd_4957372 : Nat := 4983230072969 + 3 ^ 40 * 4957372 * 2
def baseEnd_4957372 : Nat := 848504873046894497650489

theorem tailTrace_4957372 : CollatzResearch.WordTrace tailWord_4957372 prefixEnd_4957372 848504873046894497650489 := by
  unfold tailWord_4957372
  simp only [CollatzResearch.WordTrace]
  refine ⟨90405105498147685288661185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120540140664196913718214913 90405105498147685288661185)
  ·
    refine ⟨67803829123610763966495889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90405105498147685288661185 67803829123610763966495889)
    ·
      refine ⟨50852871842708072974871917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67803829123610763966495889 50852871842708072974871917)
      ·
        refine ⟨19069826941015527365576969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50852871842708072974871917 19069826941015527365576969)
        ·
          refine ⟨14302370205761645524182727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19069826941015527365576969 14302370205761645524182727)
          ·
            refine ⟨21453555308642468286274091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14302370205761645524182727 21453555308642468286274091)
            ·
              refine ⟨32180332962963702429411137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21453555308642468286274091 32180332962963702429411137)
              ·
                refine ⟨24135249722222776822058353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32180332962963702429411137 24135249722222776822058353)
                ·
                  refine ⟨18101437291667082616543765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24135249722222776822058353 18101437291667082616543765)
                  ·
                    refine ⟨848504873046894497650489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18101437291667082616543765 848504873046894497650489)
                    ·
                      rfl

theorem cell23_4957372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_4957372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957372 prefixEnd_4957372 := by exact prefixLift 4957372
  have htrace : WordTrace (prefixWord ++ tailWord_4957372) baseStart_4957372 baseEnd_4957372 := by
    simpa [prefixWord, tailWord_4957372, baseEnd_4957372] using wordTrace_append hprefix tailTrace_4957372
  have hstable : (prefixWord ++ tailWord_4957372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957372).length < 2 ^ (prefixWord ++ tailWord_4957372).sum := by decide
  have hdescent : baseEnd_4957372 < baseStart_4957372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957412 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_4957412 : Nat := 118140960795 + 4957412 * 2 ^ 59
def prefixEnd_4957412 : Nat := 4983230072969 + 3 ^ 40 * 4957412 * 2
def baseEnd_4957412 : Nat := 2545535158366863336451283

theorem tailTrace_4957412 : CollatzResearch.WordTrace tailWord_4957412 prefixEnd_4957412 2545535158366863336451283 := by
  unfold tailWord_4957412
  simp only [CollatzResearch.WordTrace]
  refine ⟨90405834958075228704389245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120541113277433638272518993 90405834958075228704389245)
  ·
    refine ⟨33902188109278210764145967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90405834958075228704389245 33902188109278210764145967)
    ·
      refine ⟨50853282163917316146218951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33902188109278210764145967 50853282163917316146218951)
      ·
        refine ⟨76279923245875974219328427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50853282163917316146218951 76279923245875974219328427)
        ·
          refine ⟨114419884868813961328992641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76279923245875974219328427 114419884868813961328992641)
          ·
            refine ⟨85814913651610470996744481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114419884868813961328992641 85814913651610470996744481)
            ·
              refine ⟨64361185238707853247558361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85814913651610470996744481 64361185238707853247558361)
              ·
                refine ⟨48270888929030889935668771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64361185238707853247558361 48270888929030889935668771)
                ·
                  refine ⟨72406333393546334903503157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48270888929030889935668771 72406333393546334903503157)
                  ·
                    refine ⟨6788093755644968897203421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72406333393546334903503157 6788093755644968897203421)
                    ·
                      refine ⟨2545535158366863336451283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6788093755644968897203421 2545535158366863336451283)
                      ·
                        rfl

theorem cell23_4957412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_4957412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957412 prefixEnd_4957412 := by exact prefixLift 4957412
  have htrace : WordTrace (prefixWord ++ tailWord_4957412) baseStart_4957412 baseEnd_4957412 := by
    simpa [prefixWord, tailWord_4957412, baseEnd_4957412] using wordTrace_append hprefix tailTrace_4957412
  have hstable : (prefixWord ++ tailWord_4957412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957412).length < 2 ^ (prefixWord ++ tailWord_4957412).sum := by decide
  have hdescent : baseEnd_4957412 < baseStart_4957412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957419 : List Nat := [1, 1, 1, 1, 2, 6, 3, 3, 5]
def baseStart_4957419 : Nat := 118140960795 + 4957419 * 2 ^ 59
def prefixEnd_4957419 : Nat := 4983230072969 + 3 ^ 40 * 4957419 * 2
def baseEnd_4957419 : Nat := 282837639192382756562639

theorem tailTrace_4957419 : CollatzResearch.WordTrace tailWord_4957419 prefixEnd_4957419 282837639192382756562639 := by
  unfold tailWord_4957419
  simp only [CollatzResearch.WordTrace]
  refine ⟨180811925227125097604283311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120541283484750065069522207 180811925227125097604283311)
  ·
    refine ⟨271217887840687646406424967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180811925227125097604283311 271217887840687646406424967)
    ·
      refine ⟨406826831761031469609637451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271217887840687646406424967 406826831761031469609637451)
      ·
        refine ⟨610240247641547204414456177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406826831761031469609637451 610240247641547204414456177)
        ·
          refine ⟨457680185731160403310842133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610240247641547204414456177 457680185731160403310842133)
          ·
            refine ⟨21453758706148143905195725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 457680185731160403310842133 21453758706148143905195725)
            ·
              refine ⟨8045159514805553964448397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21453758706148143905195725 8045159514805553964448397)
              ·
                refine ⟨3016934818052082736668149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8045159514805553964448397 3016934818052082736668149)
                ·
                  refine ⟨282837639192382756562639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3016934818052082736668149 282837639192382756562639)
                  ·
                    rfl

theorem cell23_4957419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 5].length) (baseStart_4957419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957419 prefixEnd_4957419 := by exact prefixLift 4957419
  have htrace : WordTrace (prefixWord ++ tailWord_4957419) baseStart_4957419 baseEnd_4957419 := by
    simpa [prefixWord, tailWord_4957419, baseEnd_4957419] using wordTrace_append hprefix tailTrace_4957419
  have hstable : (prefixWord ++ tailWord_4957419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957419).length < 2 ^ (prefixWord ++ tailWord_4957419).sum := by decide
  have hdescent : baseEnd_4957419 < baseStart_4957419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957435 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8]
def baseStart_4957435 : Nat := 118140960795 + 4957435 * 2 ^ 59
def prefixEnd_4957435 : Nat := 4983230072969 + 3 ^ 40 * 4957435 * 2
def baseEnd_4957435 : Nat := 2545546968421916746463677

theorem tailTrace_4957435 : CollatzResearch.WordTrace tailWord_4957435 prefixEnd_4957435 2545546968421916746463677 := by
  unfold tailWord_4957435
  simp only [CollatzResearch.WordTrace]
  refine ⟨180812508795067132336865759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120541672530044754891243839 180812508795067132336865759)
  ·
    refine ⟨271218763192600698505298639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180812508795067132336865759 271218763192600698505298639)
    ·
      refine ⟨406828144788901047757947959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271218763192600698505298639 406828144788901047757947959)
      ·
        refine ⟨610242217183351571636921939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406828144788901047757947959 610242217183351571636921939)
        ·
          refine ⟨915363325775027357455382909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610242217183351571636921939 915363325775027357455382909)
          ·
            refine ⟨343261247165635259045768591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 915363325775027357455382909 343261247165635259045768591)
            ·
              refine ⟨514891870748452888568652887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343261247165635259045768591 514891870748452888568652887)
              ·
                refine ⟨772337806122679332852979331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514891870748452888568652887 772337806122679332852979331)
                ·
                  refine ⟨1158506709184018999279468997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772337806122679332852979331 1158506709184018999279468997)
                  ·
                    refine ⟨217220007972003562364900437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1158506709184018999279468997 217220007972003562364900437)
                    ·
                      refine ⟨2545546968421916746463677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 217220007972003562364900437 2545546968421916746463677)
                      ·
                        rfl

theorem cell23_4957435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_4957435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957435 prefixEnd_4957435 := by exact prefixLift 4957435
  have htrace : WordTrace (prefixWord ++ tailWord_4957435) baseStart_4957435 baseEnd_4957435 := by
    simpa [prefixWord, tailWord_4957435, baseEnd_4957435] using wordTrace_append hprefix tailTrace_4957435
  have hstable : (prefixWord ++ tailWord_4957435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957435).length < 2 ^ (prefixWord ++ tailWord_4957435).sum := by decide
  have hdescent : baseEnd_4957435 < baseStart_4957435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957436 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 7]
def baseStart_4957436 : Nat := 118140960795 + 4957436 * 2 ^ 59
def prefixEnd_4957436 : Nat := 4983230072969 + 3 ^ 40 * 4957436 * 2
def baseEnd_4957436 : Nat := 282838609100285693616797

theorem tailTrace_4957436 : CollatzResearch.WordTrace tailWord_4957436 prefixEnd_4957436 282838609100285693616797 := by
  unfold tailWord_4957436
  simp only [CollatzResearch.WordTrace]
  refine ⟨90406272634031754753826081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120541696845375673005101441 90406272634031754753826081)
  ·
    refine ⟨67804704475523816065369561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90406272634031754753826081 67804704475523816065369561)
    ·
      refine ⟨50853528356642862049027171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67804704475523816065369561 50853528356642862049027171)
      ·
        refine ⟨76280292534964293073540757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50853528356642862049027171 76280292534964293073540757)
        ·
          refine ⟨3575638712576451237822223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76280292534964293073540757 3575638712576451237822223)
          ·
            refine ⟨5363458068864676856733335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575638712576451237822223 5363458068864676856733335)
            ·
              refine ⟨8045187103297015285100003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363458068864676856733335 8045187103297015285100003)
              ·
                refine ⟨12067780654945522927650005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8045187103297015285100003 12067780654945522927650005)
                ·
                  refine ⟨282838609100285693616797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12067780654945522927650005 282838609100285693616797)
                  ·
                    rfl

theorem cell23_4957436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_4957436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957436 prefixEnd_4957436 := by exact prefixLift 4957436
  have htrace : WordTrace (prefixWord ++ tailWord_4957436) baseStart_4957436 baseEnd_4957436 := by
    simpa [prefixWord, tailWord_4957436, baseEnd_4957436] using wordTrace_append hprefix tailTrace_4957436
  have hstable : (prefixWord ++ tailWord_4957436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957436).length < 2 ^ (prefixWord ++ tailWord_4957436).sum := by decide
  have hdescent : baseEnd_4957436 < baseStart_4957436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957543 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 6]
def baseStart_4957543 : Nat := 118140960795 + 4957543 * 2 ^ 59
def prefixEnd_4957543 : Nat := 4983230072969 + 3 ^ 40 * 4957543 * 2
def baseEnd_4957543 : Nat := 282844713814733591545909

theorem tailTrace_4957543 : CollatzResearch.WordTrace tailWord_4957543 prefixEnd_4957543 282844713814733591545909 := by
  unfold tailWord_4957543
  simp only [CollatzResearch.WordTrace]
  refine ⟨180816447878675866781797283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120544298585783911187864855 180816447878675866781797283)
  ·
    refine ⟨271224671818013800172695925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180816447878675866781797283 271224671818013800172695925)
    ·
      refine ⟨25427312982938793766190243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271224671818013800172695925 25427312982938793766190243)
      ·
        refine ⟨38140969474408190649285365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25427312982938793766190243 38140969474408190649285365)
        ·
          refine ⟨3575715888225767873370503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38140969474408190649285365 3575715888225767873370503)
          ·
            refine ⟨5363573832338651810055755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575715888225767873370503 5363573832338651810055755)
            ·
              refine ⟨8045360748507977715083633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363573832338651810055755 8045360748507977715083633)
              ·
                refine ⟨6034020561380983286312725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8045360748507977715083633 6034020561380983286312725)
                ·
                  refine ⟨282844713814733591545909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6034020561380983286312725 282844713814733591545909)
                  ·
                    rfl

theorem cell23_4957543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 6].length) (baseStart_4957543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957543 prefixEnd_4957543 := by exact prefixLift 4957543
  have htrace : WordTrace (prefixWord ++ tailWord_4957543) baseStart_4957543 baseEnd_4957543 := by
    simpa [prefixWord, tailWord_4957543, baseEnd_4957543] using wordTrace_append hprefix tailTrace_4957543
  have hstable : (prefixWord ++ tailWord_4957543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957543).length < 2 ^ (prefixWord ++ tailWord_4957543).sum := by decide
  have hdescent : baseEnd_4957543 < baseStart_4957543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957553 : List Nat := [1, 2, 2, 2, 1, 2, 4, 4, 1, 1, 3]
def baseStart_4957553 : Nat := 118140960795 + 4957553 * 2 ^ 59
def prefixEnd_4957553 : Nat := 4983230072969 + 3 ^ 40 * 4957553 * 2
def baseEnd_4957553 : Nat := 2545607559139147284788135

theorem tailTrace_4957553 : CollatzResearch.WordTrace tailWord_4957553 prefixEnd_4957553 2545607559139147284788135 := by
  unfold tailWord_4957553
  simp only [CollatzResearch.WordTrace]
  refine ⟨180816812608639638489661313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120544541739093092326440875 180816812608639638489661313)
  ·
    refine ⟨135612609456479728867245985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180816812608639638489661313 135612609456479728867245985)
    ·
      refine ⟨101709457092359796650434489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135612609456479728867245985 101709457092359796650434489)
      ·
        refine ⟨76282092819269847487825867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101709457092359796650434489 76282092819269847487825867)
        ·
          refine ⟨114423139228904771231738801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76282092819269847487825867 114423139228904771231738801)
          ·
            refine ⟨85817354421678578423804101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114423139228904771231738801 85817354421678578423804101)
            ·
              refine ⟨16090753954064733454463269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85817354421678578423804101 16090753954064733454463269)
              ·
                refine ⟨3017016366387137522711863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16090753954064733454463269 3017016366387137522711863)
                ·
                  refine ⟨4525524549580706284067795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017016366387137522711863 4525524549580706284067795)
                  ·
                    refine ⟨6788286824371059426101693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4525524549580706284067795 6788286824371059426101693)
                    ·
                      refine ⟨2545607559139147284788135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6788286824371059426101693 2545607559139147284788135)
                      ·
                        rfl

theorem cell23_4957553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_4957553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957553 prefixEnd_4957553 := by exact prefixLift 4957553
  have htrace : WordTrace (prefixWord ++ tailWord_4957553) baseStart_4957553 baseEnd_4957553 := by
    simpa [prefixWord, tailWord_4957553, baseEnd_4957553] using wordTrace_append hprefix tailTrace_4957553
  have hstable : (prefixWord ++ tailWord_4957553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957553).length < 2 ^ (prefixWord ++ tailWord_4957553).sum := by decide
  have hdescent : baseEnd_4957553 < baseStart_4957553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957570 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4957570 : Nat := 118140960795 + 4957570 * 2 ^ 59
def prefixEnd_4957570 : Nat := 4983230072969 + 3 ^ 40 * 4957570 * 2
def baseEnd_4957570 : Nat := 2545616288310273718275557

theorem tailTrace_4957570 : CollatzResearch.WordTrace tailWord_4957570 prefixEnd_4957570 2545616288310273718275557 := by
  unfold tailWord_4957570
  simp only [CollatzResearch.WordTrace]
  refine ⟨45204358162394512598257541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120544955099718700262020109 45204358162394512598257541)
  ·
    refine ⟨8475817155448971112173289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45204358162394512598257541 8475817155448971112173289)
    ·
      refine ⟨6356862866586728334129967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8475817155448971112173289 6356862866586728334129967)
      ·
        refine ⟨9535294299880092501194951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6356862866586728334129967 9535294299880092501194951)
        ·
          refine ⟨14302941449820138751792427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9535294299880092501194951 14302941449820138751792427)
          ·
            refine ⟨21454412174730208127688641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14302941449820138751792427 21454412174730208127688641)
            ·
              refine ⟨16090809131047656095766481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21454412174730208127688641 16090809131047656095766481)
              ·
                refine ⟨12068106848285742071824861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16090809131047656095766481 12068106848285742071824861)
                ·
                  refine ⟨4525540068107153276934323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12068106848285742071824861 4525540068107153276934323)
                  ·
                    refine ⟨6788310102160729915401485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4525540068107153276934323 6788310102160729915401485)
                    ·
                      refine ⟨2545616288310273718275557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6788310102160729915401485 2545616288310273718275557)
                      ·
                        rfl

theorem cell23_4957570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4957570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957570 prefixEnd_4957570 := by exact prefixLift 4957570
  have htrace : WordTrace (prefixWord ++ tailWord_4957570) baseStart_4957570 baseEnd_4957570 := by
    simpa [prefixWord, tailWord_4957570, baseEnd_4957570] using wordTrace_append hprefix tailTrace_4957570
  have hstable : (prefixWord ++ tailWord_4957570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957570).length < 2 ^ (prefixWord ++ tailWord_4957570).sum := by decide
  have hdescent : baseEnd_4957570 < baseStart_4957570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957576 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4957576 : Nat := 118140960795 + 4957576 * 2 ^ 59
def prefixEnd_4957576 : Nat := 4983230072969 + 3 ^ 40 * 4957576 * 2
def baseEnd_4957576 : Nat := 2545619369194200694800529

theorem tailTrace_4957576 : CollatzResearch.WordTrace tailWord_4957576 prefixEnd_4957576 2545619369194200694800529 := by
  unfold tailWord_4957576
  simp only [CollatzResearch.WordTrace]
  refine ⟨90408825743778156708874291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120545100991704208945165721 90408825743778156708874291)
  ·
    refine ⟨135613238615667235063311437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90408825743778156708874291 135613238615667235063311437)
    ·
      refine ⟨50854964480875213148741789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135613238615667235063311437 50854964480875213148741789)
      ·
        refine ⟨19070611680328204930778171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50854964480875213148741789 19070611680328204930778171)
        ·
          refine ⟨28605917520492307396167257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19070611680328204930778171 28605917520492307396167257)
          ·
            refine ⟨21454438140369230547125443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28605917520492307396167257 21454438140369230547125443)
            ·
              refine ⟨32181657210553845820688165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21454438140369230547125443 32181657210553845820688165)
              ·
                refine ⟨6034060726978846091379031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32181657210553845820688165 6034060726978846091379031)
                ·
                  refine ⟨9051091090468269137068547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6034060726978846091379031 9051091090468269137068547)
                  ·
                    refine ⟨13576636635702403705602821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9051091090468269137068547 13576636635702403705602821)
                    ·
                      refine ⟨2545619369194200694800529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13576636635702403705602821 2545619369194200694800529)
                      ·
                        rfl

theorem cell23_4957576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4957576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957576 prefixEnd_4957576 := by exact prefixLift 4957576
  have htrace : WordTrace (prefixWord ++ tailWord_4957576) baseStart_4957576 baseEnd_4957576 := by
    simpa [prefixWord, tailWord_4957576, baseEnd_4957576] using wordTrace_append hprefix tailTrace_4957576
  have hstable : (prefixWord ++ tailWord_4957576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957576).length < 2 ^ (prefixWord ++ tailWord_4957576).sum := by decide
  have hdescent : baseEnd_4957576 < baseStart_4957576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957589 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_4957589 : Nat := 118140960795 + 4957589 * 2 ^ 59
def prefixEnd_4957589 : Nat := 4983230072969 + 3 ^ 40 * 4957589 * 2
def baseEnd_4957589 : Nat := 2545626044442709143937969

theorem tailTrace_4957589 : CollatzResearch.WordTrace tailWord_4957589 prefixEnd_4957589 2545626044442709143937969 := by
  unfold tailWord_4957589
  simp only [CollatzResearch.WordTrace]
  refine ⟨180818125636509216637971821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120545417091006144425314547 180818125636509216637971821)
  ·
    refine ⟨67806797113690956239239433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180818125636509216637971821 67806797113690956239239433)
    ·
      refine ⟨50855097835268217179429575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67806797113690956239239433 50855097835268217179429575)
      ·
        refine ⟨76282646752902325769144363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50855097835268217179429575 76282646752902325769144363)
        ·
          refine ⟨114423970129353488653716545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76282646752902325769144363 114423970129353488653716545)
          ·
            refine ⟨85817977597015116490287409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114423970129353488653716545 85817977597015116490287409)
            ·
              refine ⟨64363483197761337367715557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85817977597015116490287409 64363483197761337367715557)
              ·
                refine ⟨12068153099580250756446667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64363483197761337367715557 12068153099580250756446667)
                ·
                  refine ⟨18102229649370376134670001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12068153099580250756446667 18102229649370376134670001)
                  ·
                    refine ⟨13576672237027782101002501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18102229649370376134670001 13576672237027782101002501)
                    ·
                      refine ⟨2545626044442709143937969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13576672237027782101002501 2545626044442709143937969)
                      ·
                        rfl

theorem cell23_4957589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_4957589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957589 prefixEnd_4957589 := by exact prefixLift 4957589
  have htrace : WordTrace (prefixWord ++ tailWord_4957589) baseStart_4957589 baseEnd_4957589 := by
    simpa [prefixWord, tailWord_4957589, baseEnd_4957589] using wordTrace_append hprefix tailTrace_4957589
  have hstable : (prefixWord ++ tailWord_4957589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957589).length < 2 ^ (prefixWord ++ tailWord_4957589).sum := by decide
  have hdescent : baseEnd_4957589 < baseStart_4957589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957599 : List Nat := [1, 1, 2, 5, 1, 4, 9]
def baseStart_4957599 : Nat := 118140960795 + 4957599 * 2 ^ 59
def prefixEnd_4957599 : Nat := 4983230072969 + 3 ^ 40 * 4957599 * 2
def baseEnd_4957599 : Nat := 31427545422830297590283

theorem tailTrace_4957599 : CollatzResearch.WordTrace tailWord_4957599 prefixEnd_4957599 31427545422830297590283 := by
  unfold tailWord_4957599
  simp only [CollatzResearch.WordTrace]
  refine ⟨180818490366472988345835851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120545660244315325563890567 180818490366472988345835851)
  ·
    refine ⟨271227735549709482518753777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180818490366472988345835851 271227735549709482518753777)
    ·
      refine ⟨203420801662282111889065333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271227735549709482518753777 203420801662282111889065333)
      ·
        refine ⟨19070700155838947989599875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203420801662282111889065333 19070700155838947989599875)
        ·
          refine ⟨28606050233758421984399813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19070700155838947989599875 28606050233758421984399813)
          ·
            refine ⟨5363634418829704122074965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28606050233758421984399813 5363634418829704122074965)
            ·
              refine ⟨31427545422830297590283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5363634418829704122074965 31427545422830297590283)
              ·
                rfl

theorem cell23_4957599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 9].length) (baseStart_4957599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957599 prefixEnd_4957599 := by exact prefixLift 4957599
  have htrace : WordTrace (prefixWord ++ tailWord_4957599) baseStart_4957599 baseEnd_4957599 := by
    simpa [prefixWord, tailWord_4957599, baseEnd_4957599] using wordTrace_append hprefix tailTrace_4957599
  have hstable : (prefixWord ++ tailWord_4957599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957599).length < 2 ^ (prefixWord ++ tailWord_4957599).sum := by decide
  have hdescent : baseEnd_4957599 < baseStart_4957599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957679 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_4957679 : Nat := 118140960795 + 4957679 * 2 ^ 59
def prefixEnd_4957679 : Nat := 4983230072969 + 3 ^ 40 * 4957679 * 2
def baseEnd_4957679 : Nat := 2545672257701613791812555

theorem tailTrace_4957679 : CollatzResearch.WordTrace tailWord_4957679 prefixEnd_4957679 2545672257701613791812555 := by
  unfold tailWord_4957679
  simp only [CollatzResearch.WordTrace]
  refine ⟨180821408206183162008748091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120547605470788774672498727 180821408206183162008748091)
  ·
    refine ⟨271232112309274743013122137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180821408206183162008748091 271232112309274743013122137)
    ·
      refine ⟨203424084231956057259841603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271232112309274743013122137 203424084231956057259841603)
      ·
        refine ⟨305136126347934085889762405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203424084231956057259841603 305136126347934085889762405)
        ·
          refine ⟨57213023690237641104330451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305136126347934085889762405 57213023690237641104330451)
          ·
            refine ⟨85819535535356461656495677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57213023690237641104330451 85819535535356461656495677)
            ·
              refine ⟨32182325825758673121185879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85819535535356461656495677 32182325825758673121185879)
              ·
                refine ⟨48273488738638009681778819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32182325825758673121185879 48273488738638009681778819)
                ·
                  refine ⟨72410233107957014522668229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48273488738638009681778819 72410233107957014522668229)
                  ·
                    refine ⟨13576918707741940223000293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72410233107957014522668229 13576918707741940223000293)
                    ·
                      refine ⟨2545672257701613791812555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13576918707741940223000293 2545672257701613791812555)
                      ·
                        rfl

theorem cell23_4957679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_4957679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957679 prefixEnd_4957679 := by exact prefixLift 4957679
  have htrace : WordTrace (prefixWord ++ tailWord_4957679) baseStart_4957679 baseEnd_4957679 := by
    simpa [prefixWord, tailWord_4957679, baseEnd_4957679] using wordTrace_append hprefix tailTrace_4957679
  have hstable : (prefixWord ++ tailWord_4957679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957679).length < 2 ^ (prefixWord ++ tailWord_4957679).sum := by decide
  have hdescent : baseEnd_4957679 < baseStart_4957679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957717 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_4957717 : Nat := 118140960795 + 4957717 * 2 ^ 59
def prefixEnd_4957717 : Nat := 4983230072969 + 3 ^ 40 * 4957717 * 2
def baseEnd_4957717 : Nat := 2545691769966484643137381

theorem tailTrace_4957717 : CollatzResearch.WordTrace tailWord_4957717 prefixEnd_4957717 2545691769966484643137381 := by
  unfold tailWord_4957717
  simp only [CollatzResearch.WordTrace]
  refine ⟨180822794180045494498631405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120548529453363662999087603 180822794180045494498631405)
  ·
    refine ⟨67808547817517060436986777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180822794180045494498631405 67808547817517060436986777)
    ·
      refine ⟨50856410863137795327740083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67808547817517060436986777 50856410863137795327740083)
      ·
        refine ⟨76284616294706692991610125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50856410863137795327740083 76284616294706692991610125)
        ·
          refine ⟨28606731110515009871853797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76284616294706692991610125 28606731110515009871853797)
          ·
            refine ⟨5363762083221564350972587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28606731110515009871853797 5363762083221564350972587)
            ·
              refine ⟨8045643124832346526458881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363762083221564350972587 8045643124832346526458881)
              ·
                refine ⟨6034232343624259894844161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8045643124832346526458881 6034232343624259894844161)
                ·
                  refine ⟨4525674257718194921133121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6034232343624259894844161 4525674257718194921133121)
                  ·
                    refine ⟨3394255693288646190849841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4525674257718194921133121 3394255693288646190849841)
                    ·
                      refine ⟨2545691769966484643137381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394255693288646190849841 2545691769966484643137381)
                      ·
                        rfl

theorem cell23_4957717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_4957717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957717 prefixEnd_4957717 := by exact prefixLift 4957717
  have htrace : WordTrace (prefixWord ++ tailWord_4957717) baseStart_4957717 baseEnd_4957717 := by
    simpa [prefixWord, tailWord_4957717, baseEnd_4957717] using wordTrace_append hprefix tailTrace_4957717
  have hstable : (prefixWord ++ tailWord_4957717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957717).length < 2 ^ (prefixWord ++ tailWord_4957717).sum := by decide
  have hdescent : baseEnd_4957717 < baseStart_4957717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957757 : List Nat := [1, 4, 1, 3, 4, 1, 1, 3, 5]
def baseStart_4957757 : Nat := 118140960795 + 4957757 * 2 ^ 59
def prefixEnd_4957757 : Nat := 4983230072969 + 3 ^ 40 * 4957757 * 2
def baseEnd_4957757 : Nat := 282856923243629387404133

theorem tailTrace_4957757 : CollatzResearch.WordTrace tailWord_4957757 prefixEnd_4957757 282856923243629387404133 := by
  unfold tailWord_4957757
  simp only [CollatzResearch.WordTrace]
  refine ⟨180824253099900581330087525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120549502066600387553391683 180824253099900581330087525)
  ·
    refine ⟨33904547456231358999391411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180824253099900581330087525 33904547456231358999391411)
    ·
      refine ⟨50856821184347038499087117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33904547456231358999391411 50856821184347038499087117)
      ·
        refine ⟨19071307944130139437157669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50856821184347038499087117 19071307944130139437157669)
        ·
          refine ⟨3575870239524401144467063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19071307944130139437157669 3575870239524401144467063)
          ·
            refine ⟨5363805359286601716700595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575870239524401144467063 5363805359286601716700595)
            ·
              refine ⟨8045708038929902575050893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5363805359286601716700595 8045708038929902575050893)
              ·
                refine ⟨3017140514598713465644085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8045708038929902575050893 3017140514598713465644085)
                ·
                  refine ⟨282856923243629387404133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3017140514598713465644085 282856923243629387404133)
                  ·
                    rfl

theorem cell23_4957757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_4957757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957757 prefixEnd_4957757 := by exact prefixLift 4957757
  have htrace : WordTrace (prefixWord ++ tailWord_4957757) baseStart_4957757 baseEnd_4957757 := by
    simpa [prefixWord, tailWord_4957757, baseEnd_4957757] using wordTrace_append hprefix tailTrace_4957757
  have hstable : (prefixWord ++ tailWord_4957757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957757).length < 2 ^ (prefixWord ++ tailWord_4957757).sum := by decide
  have hdescent : baseEnd_4957757 < baseStart_4957757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957769 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_4957769 : Nat := 118140960795 + 4957769 * 2 ^ 59
def prefixEnd_4957769 : Nat := 4983230072969 + 3 ^ 40 * 4957769 * 2
def baseEnd_4957769 : Nat := 2545718470960518439687141

theorem tailTrace_4957769 : CollatzResearch.WordTrace tailWord_4957769 prefixEnd_4957769 2545718470960518439687141 := by
  unfold tailWord_4957769
  simp only [CollatzResearch.WordTrace]
  refine ⟨180824690775857107379524361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120549793850571404919682907 180824690775857107379524361)
  ·
    refine ⟨135618518081892830534643271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180824690775857107379524361 135618518081892830534643271)
    ·
      refine ⟨203427777122839245801964907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135618518081892830534643271 203427777122839245801964907)
      ·
        refine ⟨305141665684258868702947361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203427777122839245801964907 305141665684258868702947361)
        ·
          refine ⟨228856249263194151527210521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305141665684258868702947361 228856249263194151527210521)
          ·
            refine ⟨171642186947395613645407891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228856249263194151527210521 171642186947395613645407891)
            ·
              refine ⟨257463280421093420468111837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171642186947395613645407891 257463280421093420468111837)
              ·
                refine ⟨96548730157910032675541939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257463280421093420468111837 96548730157910032675541939)
                ·
                  refine ⟨144823095236865049013312909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96548730157910032675541939 144823095236865049013312909)
                  ·
                    refine ⟨54308660713824393379992341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144823095236865049013312909 54308660713824393379992341)
                    ·
                      refine ⟨2545718470960518439687141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54308660713824393379992341 2545718470960518439687141)
                      ·
                        rfl

theorem cell23_4957769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_4957769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957769 prefixEnd_4957769 := by exact prefixLift 4957769
  have htrace : WordTrace (prefixWord ++ tailWord_4957769) baseStart_4957769 baseEnd_4957769 := by
    simpa [prefixWord, tailWord_4957769, baseEnd_4957769] using wordTrace_append hprefix tailTrace_4957769
  have hstable : (prefixWord ++ tailWord_4957769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957769).length < 2 ^ (prefixWord ++ tailWord_4957769).sum := by decide
  have hdescent : baseEnd_4957769 < baseStart_4957769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957783 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 3, 4]
def baseStart_4957783 : Nat := 118140960795 + 4957783 * 2 ^ 59
def prefixEnd_4957783 : Nat := 4983230072969 + 3 ^ 40 * 4957783 * 2
def baseEnd_4957783 : Nat := 848575219896560461637359

theorem tailTrace_4957783 : CollatzResearch.WordTrace tailWord_4957783 prefixEnd_4957783 848575219896560461637359 := by
  unfold tailWord_4957783
  simp only [CollatzResearch.WordTrace]
  refine ⟨180825201397806387770534003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120550134265204258513689335 180825201397806387770534003)
  ·
    refine ⟨271237802096709581655801005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180825201397806387770534003 271237802096709581655801005)
    ·
      refine ⟨101714175786266093120925377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271237802096709581655801005 101714175786266093120925377)
      ·
        refine ⟨76285631839699569840694033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101714175786266093120925377 76285631839699569840694033)
        ·
          refine ⟨57214223879774677380520525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76285631839699569840694033 57214223879774677380520525)
          ·
            refine ⟨21455333954915504017695197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57214223879774677380520525 21455333954915504017695197)
            ·
              refine ⟨8045750233093314006635699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21455333954915504017695197 8045750233093314006635699)
              ·
                refine ⟨12068625349639971009953549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8045750233093314006635699 12068625349639971009953549)
                ·
                  refine ⟨4525734506114989128732581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12068625349639971009953549 4525734506114989128732581)
                  ·
                    refine ⟨848575219896560461637359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4525734506114989128732581 848575219896560461637359)
                    ·
                      rfl

theorem cell23_4957783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_4957783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957783 prefixEnd_4957783 := by exact prefixLift 4957783
  have htrace : WordTrace (prefixWord ++ tailWord_4957783) baseStart_4957783 baseEnd_4957783 := by
    simpa [prefixWord, tailWord_4957783, baseEnd_4957783] using wordTrace_append hprefix tailTrace_4957783
  have hstable : (prefixWord ++ tailWord_4957783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957783).length < 2 ^ (prefixWord ++ tailWord_4957783).sum := by decide
  have hdescent : baseEnd_4957783 < baseStart_4957783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957810 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_4957810 : Nat := 118140960795 + 4957810 * 2 ^ 59
def prefixEnd_4957810 : Nat := 4983230072969 + 3 ^ 40 * 4957810 * 2
def baseEnd_4957810 : Nat := 2545739523667352779274453

theorem tailTrace_4957810 : CollatzResearch.WordTrace tailWord_4957810 prefixEnd_4957810 2545739523667352779274453 := by
  unfold tailWord_4957810
  simp only [CollatzResearch.WordTrace]
  refine ⟨45206546542177142845441721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120550790779139047587844589 45206546542177142845441721)
  ·
    refine ⟨33904909906632857134081291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45206546542177142845441721 33904909906632857134081291)
    ·
      refine ⟨50857364859949285701121937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33904909906632857134081291 50857364859949285701121937)
      ·
        refine ⟨38143023644961964275841453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50857364859949285701121937 38143023644961964275841453)
        ·
          refine ⟨14303633866860736603440545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38143023644961964275841453 14303633866860736603440545)
          ·
            refine ⟨10727725400145552452580409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14303633866860736603440545 10727725400145552452580409)
            ·
              refine ⟨8045794050109164339435307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10727725400145552452580409 8045794050109164339435307)
              ·
                refine ⟨12068691075163746509152961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8045794050109164339435307 12068691075163746509152961)
                ·
                  refine ⟨9051518306372809881864721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12068691075163746509152961 9051518306372809881864721)
                  ·
                    refine ⟨6788638729779607411398541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9051518306372809881864721 6788638729779607411398541)
                    ·
                      refine ⟨2545739523667352779274453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6788638729779607411398541 2545739523667352779274453)
                      ·
                        rfl

theorem cell23_4957810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_4957810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957810 prefixEnd_4957810 := by exact prefixLift 4957810
  have htrace : WordTrace (prefixWord ++ tailWord_4957810) baseStart_4957810 baseEnd_4957810 := by
    simpa [prefixWord, tailWord_4957810, baseEnd_4957810] using wordTrace_append hprefix tailTrace_4957810
  have hstable : (prefixWord ++ tailWord_4957810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957810).length < 2 ^ (prefixWord ++ tailWord_4957810).sum := by decide
  have hdescent : baseEnd_4957810 < baseStart_4957810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957834 : List Nat := [3, 1, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_4957834 : Nat := 118140960795 + 4957834 * 2 ^ 59
def prefixEnd_4957834 : Nat := 4983230072969 + 3 ^ 40 * 4957834 * 2
def baseEnd_4957834 : Nat := 848583949067686895124781

theorem tailTrace_4957834 : CollatzResearch.WordTrace tailWord_4957834 prefixEnd_4957834 848583949067686895124781 := by
  unfold tailWord_4957834
  simp only [CollatzResearch.WordTrace]
  refine ⟨45206765380155405870160139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120551374347081082320427037 45206765380155405870160139)
  ·
    refine ⟨67810148070233108805240209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45206765380155405870160139 67810148070233108805240209)
    ·
      refine ⟨50857611052674831603930157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67810148070233108805240209 50857611052674831603930157)
      ·
        refine ⟨19071604144753061851473809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50857611052674831603930157 19071604144753061851473809)
        ·
          refine ⟨14303703108564796388605357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19071604144753061851473809 14303703108564796388605357)
          ·
            refine ⟨5363888665711798645727009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14303703108564796388605357 5363888665711798645727009)
            ·
              refine ⟨4022916499283848984295257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363888665711798645727009 4022916499283848984295257)
              ·
                refine ⟨3017187374462886738221443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022916499283848984295257 3017187374462886738221443)
                ·
                  refine ⟨4525781061694330107332165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017187374462886738221443 4525781061694330107332165)
                  ·
                    refine ⟨848583949067686895124781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4525781061694330107332165 848583949067686895124781)
                    ·
                      rfl

theorem cell23_4957834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_4957834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957834 prefixEnd_4957834 := by exact prefixLift 4957834
  have htrace : WordTrace (prefixWord ++ tailWord_4957834) baseStart_4957834 baseEnd_4957834 := by
    simpa [prefixWord, tailWord_4957834, baseEnd_4957834] using wordTrace_append hprefix tailTrace_4957834
  have hstable : (prefixWord ++ tailWord_4957834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957834).length < 2 ^ (prefixWord ++ tailWord_4957834).sum := by decide
  have hdescent : baseEnd_4957834 < baseStart_4957834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957900 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4957900 : Nat := 118140960795 + 4957900 * 2 ^ 59
def prefixEnd_4957900 : Nat := 4983230072969 + 3 ^ 40 * 4957900 * 2
def baseEnd_4957900 : Nat := 2545785736926257427149039

theorem tailTrace_4957900 : CollatzResearch.WordTrace tailWord_4957900 prefixEnd_4957900 2545785736926257427149039 := by
  unfold tailWord_4957900
  simp only [CollatzResearch.WordTrace]
  refine ⟨90414734369191258376271577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120552979158921677835028769 90414734369191258376271577)
  ·
    refine ⟨67811050776893443782203683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90414734369191258376271577 67811050776893443782203683)
    ·
      refine ⟨101716576165340165673305525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67811050776893443782203683 101716576165340165673305525)
      ·
        refine ⟨9535929015500640531872393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101716576165340165673305525 9535929015500640531872393)
        ·
          refine ⟨7151946761625480398904295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9535929015500640531872393 7151946761625480398904295)
          ·
            refine ⟨10727920142438220598356443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7151946761625480398904295 10727920142438220598356443)
            ·
              refine ⟨16091880213657330897534665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10727920142438220598356443 16091880213657330897534665)
              ·
                refine ⟨12068910160242998173150999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16091880213657330897534665 12068910160242998173150999)
                ·
                  refine ⟨18103365240364497259726499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12068910160242998173150999 18103365240364497259726499)
                  ·
                    refine ⟨27155047860546745889589749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18103365240364497259726499 27155047860546745889589749)
                    ·
                      refine ⟨2545785736926257427149039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27155047860546745889589749 2545785736926257427149039)
                      ·
                        rfl

theorem cell23_4957900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4957900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957900 prefixEnd_4957900 := by exact prefixLift 4957900
  have htrace : WordTrace (prefixWord ++ tailWord_4957900) baseStart_4957900 baseEnd_4957900 := by
    simpa [prefixWord, tailWord_4957900, baseEnd_4957900] using wordTrace_append hprefix tailTrace_4957900
  have hstable : (prefixWord ++ tailWord_4957900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957900).length < 2 ^ (prefixWord ++ tailWord_4957900).sum := by decide
  have hdescent : baseEnd_4957900 < baseStart_4957900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957930 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_4957930 : Nat := 118140960795 + 4957930 * 2 ^ 59
def prefixEnd_4957930 : Nat := 4983230072969 + 3 ^ 40 * 4957930 * 2
def baseEnd_4957930 : Nat := 2545801141345892309773901

theorem tailTrace_4957930 : CollatzResearch.WordTrace tailWord_4957930 prefixEnd_4957930 2545801141345892309773901 := by
  unfold tailWord_4957930
  simp only [CollatzResearch.WordTrace]
  refine ⟨45207640732068457969033811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120553708618849221250756829 45207640732068457969033811)
  ·
    refine ⟨67811461098102686953550717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45207640732068457969033811 67811461098102686953550717)
    ·
      refine ⟨25429297911788507607581519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67811461098102686953550717 25429297911788507607581519)
      ·
        refine ⟨38143946867682761411372279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25429297911788507607581519 38143946867682761411372279)
        ·
          refine ⟨57215920301524142117058419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38143946867682761411372279 57215920301524142117058419)
          ·
            refine ⟨85823880452286213175587629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57215920301524142117058419 85823880452286213175587629)
            ·
              refine ⟨32183955169607329940845361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85823880452286213175587629 32183955169607329940845361)
              ·
                refine ⟨24137966377205497455634021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32183955169607329940845361 24137966377205497455634021)
                ·
                  refine ⟨4525868695726030772931379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24137966377205497455634021 4525868695726030772931379)
                  ·
                    refine ⟨6788803043589046159397069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4525868695726030772931379 6788803043589046159397069)
                    ·
                      refine ⟨2545801141345892309773901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6788803043589046159397069 2545801141345892309773901)
                      ·
                        rfl

theorem cell23_4957930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_4957930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957930 prefixEnd_4957930 := by exact prefixLift 4957930
  have htrace : WordTrace (prefixWord ++ tailWord_4957930) baseStart_4957930 baseEnd_4957930 := by
    simpa [prefixWord, tailWord_4957930, baseEnd_4957930] using wordTrace_append hprefix tailTrace_4957930
  have hstable : (prefixWord ++ tailWord_4957930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957930).length < 2 ^ (prefixWord ++ tailWord_4957930).sum := by decide
  have hdescent : baseEnd_4957930 < baseStart_4957930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957965 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4957965 : Nat := 118140960795 + 4957965 * 2 ^ 59
def prefixEnd_4957965 : Nat := 4983230072969 + 3 ^ 40 * 4957965 * 2
def baseEnd_4957965 : Nat := 2545819113168799672836241

theorem tailTrace_4957965 : CollatzResearch.WordTrace tailWord_4957965 prefixEnd_4957965 2545819113168799672836241 := by
  unfold tailWord_4957965
  simp only [CollatzResearch.WordTrace]
  refine ⟨180831839483147032853659349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120554559655431355235772899 180831839483147032853659349)
  ·
    refine ⟨4238246237886258582507641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 180831839483147032853659349 4238246237886258582507641)
    ·
      refine ⟨3178684678414693936880731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4238246237886258582507641 3178684678414693936880731)
      ·
        refine ⟨4768027017622040905321097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178684678414693936880731 4768027017622040905321097)
        ·
          refine ⟨3576020263216530678990823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4768027017622040905321097 3576020263216530678990823)
          ·
            refine ⟨5364030394824796018486235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576020263216530678990823 5364030394824796018486235)
            ·
              refine ⟨8046045592237194027729353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364030394824796018486235 8046045592237194027729353)
              ·
                refine ⟨6034534194177895520797015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8046045592237194027729353 6034534194177895520797015)
                ·
                  refine ⟨9051801291266843281195523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6034534194177895520797015 9051801291266843281195523)
                  ·
                    refine ⟨13577701936900264921793285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9051801291266843281195523 13577701936900264921793285)
                    ·
                      refine ⟨2545819113168799672836241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13577701936900264921793285 2545819113168799672836241)
                      ·
                        rfl

theorem cell23_4957965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4957965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957965 prefixEnd_4957965 := by exact prefixLift 4957965
  have htrace : WordTrace (prefixWord ++ tailWord_4957965) baseStart_4957965 baseEnd_4957965 := by
    simpa [prefixWord, tailWord_4957965, baseEnd_4957965] using wordTrace_append hprefix tailTrace_4957965
  have hstable : (prefixWord ++ tailWord_4957965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957965).length < 2 ^ (prefixWord ++ tailWord_4957965).sum := by decide
  have hdescent : baseEnd_4957965 < baseStart_4957965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4957973 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_4957973 : Nat := 118140960795 + 4957973 * 2 ^ 59
def prefixEnd_4957973 : Nat := 4983230072969 + 3 ^ 40 * 4957973 * 2
def baseEnd_4957973 : Nat := 2545823221014035641536203

theorem tailTrace_4957973 : CollatzResearch.WordTrace tailWord_4957973 prefixEnd_4957973 2545823221014035641536203 := by
  unfold tailWord_4957973
  simp only [CollatzResearch.WordTrace]
  refine ⟨180832131267118050219950573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120554754178078700146633715 180832131267118050219950573)
  ·
    refine ⟨67812049225169268832481465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180832131267118050219950573 67812049225169268832481465)
    ·
      refine ⟨50859036918876951624361099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67812049225169268832481465 50859036918876951624361099)
      ·
        refine ⟨76288555378315427436541649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50859036918876951624361099 76288555378315427436541649)
        ·
          refine ⟨57216416533736570577406237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76288555378315427436541649 57216416533736570577406237)
          ·
            refine ⟨21456156200151213966527339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57216416533736570577406237 21456156200151213966527339)
            ·
              refine ⟨32184234300226820949791009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21456156200151213966527339 32184234300226820949791009)
              ·
                refine ⟨24138175725170115712343257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32184234300226820949791009 24138175725170115712343257)
                ·
                  refine ⟨18103631793877586784257443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24138175725170115712343257 18103631793877586784257443)
                  ·
                    refine ⟨27155447690816380176386165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18103631793877586784257443 27155447690816380176386165)
                    ·
                      refine ⟨2545823221014035641536203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27155447690816380176386165 2545823221014035641536203)
                      ·
                        rfl

theorem cell23_4957973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_4957973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4957973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4957973 prefixEnd_4957973 := by exact prefixLift 4957973
  have htrace : WordTrace (prefixWord ++ tailWord_4957973) baseStart_4957973 baseEnd_4957973 := by
    simpa [prefixWord, tailWord_4957973, baseEnd_4957973] using wordTrace_append hprefix tailTrace_4957973
  have hstable : (prefixWord ++ tailWord_4957973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4957973).length < 2 ^ (prefixWord ++ tailWord_4957973).sum := by decide
  have hdescent : baseEnd_4957973 < baseStart_4957973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4957973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958023 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 4, 5]
def baseStart_4958023 : Nat := 118140960795 + 4958023 * 2 ^ 59
def prefixEnd_4958023 : Nat := 4983230072969 + 3 ^ 40 * 4958023 * 2
def baseEnd_4958023 : Nat := 848616298348920148636991

theorem tailTrace_4958023 : CollatzResearch.WordTrace tailWord_4958023 prefixEnd_4958023 848616298348920148636991 := by
  unfold tailWord_4958023
  simp only [CollatzResearch.WordTrace]
  refine ⟨180833954916936908759270723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120555969944624605839513815 180833954916936908759270723)
  ·
    refine ⟨271250932375405363138906085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180833954916936908759270723 271250932375405363138906085)
    ·
      refine ⟨50859549820388505588544891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271250932375405363138906085 50859549820388505588544891)
      ·
        refine ⟨76289324730582758382817337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50859549820388505588544891 76289324730582758382817337)
        ·
          refine ⟨57216993547937068787113003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76289324730582758382817337 57216993547937068787113003)
          ·
            refine ⟨85825490321905603180669505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57216993547937068787113003 85825490321905603180669505)
            ·
              refine ⟨64369117741429202385502129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85825490321905603180669505 64369117741429202385502129)
              ·
                refine ⟨48276838306071901789126597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64369117741429202385502129 48276838306071901789126597)
                ·
                  refine ⟨9051907182388481585461237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48276838306071901789126597 9051907182388481585461237)
                  ·
                    refine ⟨848616298348920148636991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9051907182388481585461237 848616298348920148636991)
                    ·
                      rfl

theorem cell23_4958023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_4958023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958023 prefixEnd_4958023 := by exact prefixLift 4958023
  have htrace : WordTrace (prefixWord ++ tailWord_4958023) baseStart_4958023 baseEnd_4958023 := by
    simpa [prefixWord, tailWord_4958023, baseEnd_4958023] using wordTrace_append hprefix tailTrace_4958023
  have hstable : (prefixWord ++ tailWord_4958023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958023).length < 2 ^ (prefixWord ++ tailWord_4958023).sum := by decide
  have hdescent : baseEnd_4958023 < baseStart_4958023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958044 : List Nat := [2, 2, 4, 2, 2, 1, 2, 3, 5]
def baseStart_4958044 : Nat := 118140960795 + 4958044 * 2 ^ 59
def prefixEnd_4958044 : Nat := 4983230072969 + 3 ^ 40 * 4958044 * 2
def baseEnd_4958044 : Nat := 282873297571167207083153

theorem tailTrace_4958044 : CollatzResearch.WordTrace tailWord_4958044 prefixEnd_4958044 282873297571167207083153 := by
  unfold tailWord_4958044
  simp only [CollatzResearch.WordTrace]
  refine ⟨90417360424930414672892593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120556480566573886230523457 90417360424930414672892593)
  ·
    refine ⟨67813020318697811004669445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90417360424930414672892593 67813020318697811004669445)
    ·
      refine ⟨12714941309755839563375521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67813020318697811004669445 12714941309755839563375521)
      ·
        refine ⟨9536205982316879672531641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12714941309755839563375521 9536205982316879672531641)
        ·
          refine ⟨7152154486737659754398731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9536205982316879672531641 7152154486737659754398731)
          ·
            refine ⟨10728231730106489631598097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152154486737659754398731 10728231730106489631598097)
            ·
              refine ⟨8046173797579867223698573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10728231730106489631598097 8046173797579867223698573)
              ·
                refine ⟨3017315174092450208886965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8046173797579867223698573 3017315174092450208886965)
                ·
                  refine ⟨282873297571167207083153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3017315174092450208886965 282873297571167207083153)
                  ·
                    rfl

theorem cell23_4958044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_4958044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958044 prefixEnd_4958044 := by exact prefixLift 4958044
  have htrace : WordTrace (prefixWord ++ tailWord_4958044) baseStart_4958044 baseEnd_4958044 := by
    simpa [prefixWord, tailWord_4958044, baseEnd_4958044] using wordTrace_append hprefix tailTrace_4958044
  have hstable : (prefixWord ++ tailWord_4958044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958044).length < 2 ^ (prefixWord ++ tailWord_4958044).sum := by decide
  have hdescent : baseEnd_4958044 < baseStart_4958044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958073 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_4958073 : Nat := 118140960795 + 4958073 * 2 ^ 59
def prefixEnd_4958073 : Nat := 4983230072969 + 3 ^ 40 * 4958073 * 2
def baseEnd_4958073 : Nat := 2545874569079485250285743

theorem tailTrace_4958073 : CollatzResearch.WordTrace tailWord_4958073 prefixEnd_4958073 2545874569079485250285743 := by
  unfold tailWord_4958073
  simp only [CollatzResearch.WordTrace]
  refine ⟨180835778566755767298590873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120557185711170511532393915 180835778566755767298590873)
  ·
    refine ⟨135626833925066825473943155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180835778566755767298590873 135626833925066825473943155)
    ·
      refine ⟨203440250887600238210914733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135626833925066825473943155 203440250887600238210914733)
      ·
        refine ⟨76290094082850089329093025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203440250887600238210914733 76290094082850089329093025)
        ·
          refine ⟨57217570562137566996819769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76290094082850089329093025 57217570562137566996819769)
          ·
            refine ⟨42913177921603175247614827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57217570562137566996819769 42913177921603175247614827)
            ·
              refine ⟨64369766882404762871422241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42913177921603175247614827 64369766882404762871422241)
              ·
                refine ⟨48277325161803572153566681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64369766882404762871422241 48277325161803572153566681)
                ·
                  refine ⟨36207993871352679115175011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48277325161803572153566681 36207993871352679115175011)
                  ·
                    refine ⟨54311990807029018672762517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36207993871352679115175011 54311990807029018672762517)
                    ·
                      refine ⟨2545874569079485250285743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54311990807029018672762517 2545874569079485250285743)
                      ·
                        rfl

theorem cell23_4958073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_4958073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958073 prefixEnd_4958073 := by exact prefixLift 4958073
  have htrace : WordTrace (prefixWord ++ tailWord_4958073) baseStart_4958073 baseEnd_4958073 := by
    simpa [prefixWord, tailWord_4958073, baseEnd_4958073] using wordTrace_append hprefix tailTrace_4958073
  have hstable : (prefixWord ++ tailWord_4958073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958073).length < 2 ^ (prefixWord ++ tailWord_4958073).sum := by decide
  have hdescent : baseEnd_4958073 < baseStart_4958073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958100 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 8]
def baseStart_4958100 : Nat := 118140960795 + 4958100 * 2 ^ 59
def prefixEnd_4958100 : Nat := 4983230072969 + 3 ^ 40 * 4958100 * 2
def baseEnd_4958100 : Nat := 282876492561906293849791

theorem tailTrace_4958100 : CollatzResearch.WordTrace tailWord_4958100 prefixEnd_4958100 282876492561906293849791 := by
  unfold tailWord_4958100
  simp only [CollatzResearch.WordTrace]
  refine ⟨90418381668828975454911877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120557842225105300606549169 90418381668828975454911877)
  ·
    refine ⟨16953446562905432897795977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90418381668828975454911877 16953446562905432897795977)
    ·
      refine ⟨12715084922179074673346983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16953446562905432897795977 12715084922179074673346983)
      ·
        refine ⟨19072627383268612010020475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12715084922179074673346983 19072627383268612010020475)
        ·
          refine ⟨28608941074902918015030713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19072627383268612010020475 28608941074902918015030713)
          ·
            refine ⟨21456705806177188511273035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28608941074902918015030713 21456705806177188511273035)
            ·
              refine ⟨32185058709265782766909553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21456705806177188511273035 32185058709265782766909553)
              ·
                refine ⟨24138794031949337075182165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32185058709265782766909553 24138794031949337075182165)
                ·
                  refine ⟨282876492561906293849791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24138794031949337075182165 282876492561906293849791)
                  ·
                    rfl

theorem cell23_4958100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_4958100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958100 prefixEnd_4958100 := by exact prefixLift 4958100
  have htrace : WordTrace (prefixWord ++ tailWord_4958100) baseStart_4958100 baseEnd_4958100 := by
    simpa [prefixWord, tailWord_4958100, baseEnd_4958100] using wordTrace_append hprefix tailTrace_4958100
  have hstable : (prefixWord ++ tailWord_4958100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958100).length < 2 ^ (prefixWord ++ tailWord_4958100).sum := by decide
  have hdescent : baseEnd_4958100 < baseStart_4958100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958114 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4958114 : Nat := 118140960795 + 4958114 * 2 ^ 59
def prefixEnd_4958114 : Nat := 4983230072969 + 3 ^ 40 * 4958114 * 2
def baseEnd_4958114 : Nat := 2545895621786319589873055

theorem tailTrace_4958114 : CollatzResearch.WordTrace tailWord_4958114 prefixEnd_4958114 2545895621786319589873055 := by
  unfold tailWord_4958114
  simp only [CollatzResearch.WordTrace]
  refine ⟨45209318489901807825208349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120558182639738154200555597 45209318489901807825208349)
  ·
    refine ⟨16953494433713177934453131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45209318489901807825208349 16953494433713177934453131)
    ·
      refine ⟨25430241650569766901679697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16953494433713177934453131 25430241650569766901679697)
      ·
        refine ⟨19072681237927325176259773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25430241650569766901679697 19072681237927325176259773)
        ·
          refine ⟨7152255464222746941097415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19072681237927325176259773 7152255464222746941097415)
          ·
            refine ⟨10728383196334120411646123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152255464222746941097415 10728383196334120411646123)
            ·
              refine ⟨16092574794501180617469185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10728383196334120411646123 16092574794501180617469185)
              ·
                refine ⟨12069431095875885463101889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16092574794501180617469185 12069431095875885463101889)
                ·
                  refine ⟨9052073321906914097326417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12069431095875885463101889 9052073321906914097326417)
                  ·
                    refine ⟨6789054991430185572994813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9052073321906914097326417 6789054991430185572994813)
                    ·
                      refine ⟨2545895621786319589873055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6789054991430185572994813 2545895621786319589873055)
                      ·
                        rfl

theorem cell23_4958114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4958114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958114 prefixEnd_4958114 := by exact prefixLift 4958114
  have htrace : WordTrace (prefixWord ++ tailWord_4958114) baseStart_4958114 baseEnd_4958114 := by
    simpa [prefixWord, tailWord_4958114, baseEnd_4958114] using wordTrace_append hprefix tailTrace_4958114
  have hstable : (prefixWord ++ tailWord_4958114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958114).length < 2 ^ (prefixWord ++ tailWord_4958114).sum := by decide
  have hdescent : baseEnd_4958114 < baseStart_4958114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958137 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 4, 3, 2]
def baseStart_4958137 : Nat := 118140960795 + 4958137 * 2 ^ 59
def prefixEnd_4958137 : Nat := 4983230072969 + 3 ^ 40 * 4958137 * 2
def baseEnd_4958137 : Nat := 2545907431841372999885449

theorem tailTrace_4958137 : CollatzResearch.WordTrace tailWord_4958137 prefixEnd_4958137 2545907431841372999885449 := by
  unfold tailWord_4958137
  simp only [CollatzResearch.WordTrace]
  refine ⟨180838112838523906228920665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120558741892349270819280443 180838112838523906228920665)
  ·
    refine ⟨135628584628892929671690499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180838112838523906228920665 135628584628892929671690499)
    ·
      refine ⟨203442876943339394507535749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135628584628892929671690499 203442876943339394507535749)
      ·
        refine ⟨38145539426876136470162953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203442876943339394507535749 38145539426876136470162953)
        ·
          refine ⟨28609154570157102352622215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38145539426876136470162953 28609154570157102352622215)
          ·
            refine ⟨42913731855235653528933323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28609154570157102352622215 42913731855235653528933323)
            ·
              refine ⟨64370597782853480293399985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42913731855235653528933323 64370597782853480293399985)
              ·
                refine ⟨48277948337140110220049989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64370597782853480293399985 48277948337140110220049989)
                ·
                  refine ⟨9052115313213770666259373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48277948337140110220049989 9052115313213770666259373)
                  ·
                    refine ⟨3394543242455163999847265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9052115313213770666259373 3394543242455163999847265)
                    ·
                      refine ⟨2545907431841372999885449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394543242455163999847265 2545907431841372999885449)
                      ·
                        rfl

theorem cell23_4958137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_4958137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958137 prefixEnd_4958137 := by exact prefixLift 4958137
  have htrace : WordTrace (prefixWord ++ tailWord_4958137) baseStart_4958137 baseEnd_4958137 := by
    simpa [prefixWord, tailWord_4958137, baseEnd_4958137] using wordTrace_append hprefix tailTrace_4958137
  have hstable : (prefixWord ++ tailWord_4958137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958137).length < 2 ^ (prefixWord ++ tailWord_4958137).sum := by decide
  have hdescent : baseEnd_4958137 < baseStart_4958137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958160 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 6, 4]
def baseStart_4958160 : Nat := 118140960795 + 4958160 * 2 ^ 59
def prefixEnd_4958160 : Nat := 4983230072969 + 3 ^ 40 * 4958160 * 2
def baseEnd_4958160 : Nat := 848639747298808803299281

theorem tailTrace_4958160 : CollatzResearch.WordTrace tailWord_4958160 prefixEnd_4958160 848639747298808803299281 := by
  unfold tailWord_4958160
  simp only [CollatzResearch.WordTrace]
  refine ⟨90419475858720290578503967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120559301144960387438005289 90419475858720290578503967)
  ·
    refine ⟨135629213788080435867755951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90419475858720290578503967 135629213788080435867755951)
    ·
      refine ⟨203443820682120653801633927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135629213788080435867755951 203443820682120653801633927)
      ·
        refine ⟨305165731023180980702450891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203443820682120653801633927 305165731023180980702450891)
        ·
          refine ⟨457748596534771471053676337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305165731023180980702450891 457748596534771471053676337)
          ·
            refine ⟨343311447401078603290257253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457748596534771471053676337 343311447401078603290257253)
            ·
              refine ⟨64370896387702238116923235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 343311447401078603290257253 64370896387702238116923235)
              ·
                refine ⟨96556344581553357175384853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64370896387702238116923235 96556344581553357175384853)
                ·
                  refine ⟨4526078652260313617596165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96556344581553357175384853 4526078652260313617596165)
                  ·
                    refine ⟨848639747298808803299281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526078652260313617596165 848639747298808803299281)
                    ·
                      rfl

theorem cell23_4958160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_4958160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958160 prefixEnd_4958160 := by exact prefixLift 4958160
  have htrace : WordTrace (prefixWord ++ tailWord_4958160) baseStart_4958160 baseEnd_4958160 := by
    simpa [prefixWord, tailWord_4958160, baseEnd_4958160] using wordTrace_append hprefix tailTrace_4958160
  have hstable : (prefixWord ++ tailWord_4958160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958160).length < 2 ^ (prefixWord ++ tailWord_4958160).sum := by decide
  have hdescent : baseEnd_4958160 < baseStart_4958160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958163 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6]
def baseStart_4958163 : Nat := 118140960795 + 4958163 * 2 ^ 59
def prefixEnd_4958163 : Nat := 4983230072969 + 3 ^ 40 * 4958163 * 2
def baseEnd_4958163 : Nat := 2545920782338389898160329

theorem tailTrace_4958163 : CollatzResearch.WordTrace tailWord_4958163 prefixEnd_4958163 2545920782338389898160329 := by
  unfold tailWord_4958163
  simp only [CollatzResearch.WordTrace]
  refine ⟨180839061136429712669367143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120559374090953141779578095 180839061136429712669367143)
  ·
    refine ⟨271258591704644569004050715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180839061136429712669367143 271258591704644569004050715)
    ·
      refine ⟨406887887556966853506076073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271258591704644569004050715 406887887556966853506076073)
      ·
        refine ⟨305165915667725140129557055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406887887556966853506076073 305165915667725140129557055)
        ·
          refine ⟨457748873501587710194335583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305165915667725140129557055 457748873501587710194335583)
          ·
            refine ⟨686623310252381565291503375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457748873501587710194335583 686623310252381565291503375)
            ·
              refine ⟨1029934965378572347937255063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686623310252381565291503375 1029934965378572347937255063)
              ·
                refine ⟨1544902448067858521905882595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029934965378572347937255063 1544902448067858521905882595)
                ·
                  refine ⟨2317353672101787782858823893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544902448067858521905882595 2317353672101787782858823893)
                  ·
                    refine ⟨54312976689885651160753685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2317353672101787782858823893 54312976689885651160753685)
                    ·
                      refine ⟨2545920782338389898160329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54312976689885651160753685 2545920782338389898160329)
                      ·
                        rfl

theorem cell23_4958163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_4958163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958163 prefixEnd_4958163 := by exact prefixLift 4958163
  have htrace : WordTrace (prefixWord ++ tailWord_4958163) baseStart_4958163 baseEnd_4958163 := by
    simpa [prefixWord, tailWord_4958163, baseEnd_4958163] using wordTrace_append hprefix tailTrace_4958163
  have hstable : (prefixWord ++ tailWord_4958163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958163).length < 2 ^ (prefixWord ++ tailWord_4958163).sum := by decide
  have hdescent : baseEnd_4958163 < baseStart_4958163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958164 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_4958164 : Nat := 118140960795 + 4958164 * 2 ^ 59
def prefixEnd_4958164 : Nat := 4983230072969 + 3 ^ 40 * 4958164 * 2
def baseEnd_4958164 : Nat := 848640431939681464749275

theorem tailTrace_4958164 : CollatzResearch.WordTrace tailWord_4958164 prefixEnd_4958164 848640431939681464749275 := by
  unfold tailWord_4958164
  simp only [CollatzResearch.WordTrace]
  refine ⟨90419548804713044920076773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120559398406284059893435697 90419548804713044920076773)
  ·
    refine ⟨16953665400883695922514395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90419548804713044920076773 16953665400883695922514395)
    ·
      refine ⟨25430498101325543883771593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16953665400883695922514395 25430498101325543883771593)
      ·
        refine ⟨19072873575994157912828695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25430498101325543883771593 19072873575994157912828695)
        ·
          refine ⟨28609310363991236869243043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19072873575994157912828695 28609310363991236869243043)
          ·
            refine ⟨42913965545986855303864565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28609310363991236869243043 42913965545986855303864565)
            ·
              refine ⟨4023184269936267684737303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42913965545986855303864565 4023184269936267684737303)
              ·
                refine ⟨6034776404904401527105955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023184269936267684737303 6034776404904401527105955)
                ·
                  refine ⟨9052164607356602290658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6034776404904401527105955 9052164607356602290658933)
                  ·
                    refine ⟨848640431939681464749275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9052164607356602290658933 848640431939681464749275)
                    ·
                      rfl

theorem cell23_4958164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_4958164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958164 prefixEnd_4958164 := by exact prefixLift 4958164
  have htrace : WordTrace (prefixWord ++ tailWord_4958164) baseStart_4958164 baseEnd_4958164 := by
    simpa [prefixWord, tailWord_4958164, baseEnd_4958164] using wordTrace_append hprefix tailTrace_4958164
  have hstable : (prefixWord ++ tailWord_4958164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958164).length < 2 ^ (prefixWord ++ tailWord_4958164).sum := by decide
  have hdescent : baseEnd_4958164 < baseStart_4958164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958172 : List Nat := [2, 2, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4958172 : Nat := 118140960795 + 4958172 * 2 ^ 59
def prefixEnd_4958172 : Nat := 4983230072969 + 3 ^ 40 * 4958172 * 2
def baseEnd_4958172 : Nat := 848641801221426787649263

theorem tailTrace_4958172 : CollatzResearch.WordTrace tailWord_4958172 prefixEnd_4958172 848641801221426787649263 := by
  unfold tailWord_4958172
  simp only [CollatzResearch.WordTrace]
  refine ⟨90419694696698553603222385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120559592928931404804296513 90419694696698553603222385)
  ·
    refine ⟨67814771022523915202416789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90419694696698553603222385 67814771022523915202416789)
    ·
      refine ⟨3178817391680808525113287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67814771022523915202416789 3178817391680808525113287)
      ·
        refine ⟨4768226087521212787669931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3178817391680808525113287 4768226087521212787669931)
        ·
          refine ⟨7152339131281819181504897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4768226087521212787669931 7152339131281819181504897)
          ·
            refine ⟨5364254348461364386128673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7152339131281819181504897 5364254348461364386128673)
            ·
              refine ⟨4023190761346023289596505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5364254348461364386128673 4023190761346023289596505)
              ·
                refine ⟨3017393071009517467197379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4023190761346023289596505 3017393071009517467197379)
                ·
                  refine ⟨4526089606514276200796069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017393071009517467197379 4526089606514276200796069)
                  ·
                    refine ⟨848641801221426787649263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526089606514276200796069 848641801221426787649263)
                    ·
                      rfl

theorem cell23_4958172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4958172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958172 prefixEnd_4958172 := by exact prefixLift 4958172
  have htrace : WordTrace (prefixWord ++ tailWord_4958172) baseStart_4958172 baseEnd_4958172 := by
    simpa [prefixWord, tailWord_4958172, baseEnd_4958172] using wordTrace_append hprefix tailTrace_4958172
  have hstable : (prefixWord ++ tailWord_4958172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958172).length < 2 ^ (prefixWord ++ tailWord_4958172).sum := by decide
  have hdescent : baseEnd_4958172 < baseStart_4958172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958177 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 2, 4]
def baseStart_4958177 : Nat := 118140960795 + 4958177 * 2 ^ 59
def prefixEnd_4958177 : Nat := 4983230072969 + 3 ^ 40 * 4958177 * 2
def baseEnd_4958177 : Nat := 848642657022517614461755

theorem tailTrace_4958177 : CollatzResearch.WordTrace tailWord_4958177 prefixEnd_4958177 848642657022517614461755 := by
  unfold tailWord_4958177
  simp only [CollatzResearch.WordTrace]
  refine ⟨180839571758378993060376785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120559714505585995373584523 180839571758378993060376785)
  ·
    refine ⟨135629678818784244795282589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180839571758378993060376785 135629678818784244795282589)
    ·
      refine ⟨50861129557044091798230971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135629678818784244795282589 50861129557044091798230971)
      ·
        refine ⟨76291694335566137697346457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50861129557044091798230971 76291694335566137697346457)
        ·
          refine ⟨57218770751674603273009843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76291694335566137697346457 57218770751674603273009843)
          ·
            refine ⟨85828156127511904909514765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57218770751674603273009843 85828156127511904909514765)
            ·
              refine ⟨32185558547816964341068037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85828156127511904909514765 32185558547816964341068037)
              ·
                refine ⟨6034792227715680813950257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32185558547816964341068037 6034792227715680813950257)
                ·
                  refine ⟨4526094170786760610462693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6034792227715680813950257 4526094170786760610462693)
                  ·
                    refine ⟨848642657022517614461755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526094170786760610462693 848642657022517614461755)
                    ·
                      rfl

theorem cell23_4958177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_4958177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958177 prefixEnd_4958177 := by exact prefixLift 4958177
  have htrace : WordTrace (prefixWord ++ tailWord_4958177) baseStart_4958177 baseEnd_4958177 := by
    simpa [prefixWord, tailWord_4958177, baseEnd_4958177] using wordTrace_append hprefix tailTrace_4958177
  have hstable : (prefixWord ++ tailWord_4958177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958177).length < 2 ^ (prefixWord ++ tailWord_4958177).sum := by decide
  have hdescent : baseEnd_4958177 < baseStart_4958177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958180 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_4958180 : Nat := 118140960795 + 4958180 * 2 ^ 59
def prefixEnd_4958180 : Nat := 4983230072969 + 3 ^ 40 * 4958180 * 2
def baseEnd_4958180 : Nat := 2545929511509516331647751

theorem tailTrace_4958180 : CollatzResearch.WordTrace tailWord_4958180 prefixEnd_4958180 2545929511509516331647751 := by
  unfold tailWord_4958180
  simp only [CollatzResearch.WordTrace]
  refine ⟨90419840588684062286367997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120559787451578749715157329 90419840588684062286367997)
  ·
    refine ⟨33907440220756523357387999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90419840588684062286367997 33907440220756523357387999)
    ·
      refine ⟨50861160331134785036081999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33907440220756523357387999 50861160331134785036081999)
      ·
        refine ⟨76291740496702177554122999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50861160331134785036081999 76291740496702177554122999)
        ·
          refine ⟨114437610745053266331184499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76291740496702177554122999 114437610745053266331184499)
          ·
            refine ⟨171656416117579899496776749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114437610745053266331184499 171656416117579899496776749)
            ·
              refine ⟨64371156044092462311291281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171656416117579899496776749 64371156044092462311291281)
              ·
                refine ⟨48278367033069346733468461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64371156044092462311291281 48278367033069346733468461)
                ·
                  refine ⟨18104387637401005025050673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48278367033069346733468461 18104387637401005025050673)
                  ·
                    refine ⟨13578290728050753768788005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18104387637401005025050673 13578290728050753768788005)
                    ·
                      refine ⟨2545929511509516331647751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13578290728050753768788005 2545929511509516331647751)
                      ·
                        rfl

theorem cell23_4958180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_4958180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958180 prefixEnd_4958180 := by exact prefixLift 4958180
  have htrace : WordTrace (prefixWord ++ tailWord_4958180) baseStart_4958180 baseEnd_4958180 := by
    simpa [prefixWord, tailWord_4958180, baseEnd_4958180] using wordTrace_append hprefix tailTrace_4958180
  have hstable : (prefixWord ++ tailWord_4958180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958180).length < 2 ^ (prefixWord ++ tailWord_4958180).sum := by decide
  have hdescent : baseEnd_4958180 < baseStart_4958180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958184 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_4958184 : Nat := 118140960795 + 4958184 * 2 ^ 59
def prefixEnd_4958184 : Nat := 4983230072969 + 3 ^ 40 * 4958184 * 2
def baseEnd_4958184 : Nat := 2545931565432134315997733

theorem tailTrace_4958184 : CollatzResearch.WordTrace tailWord_4958184 prefixEnd_4958184 2545931565432134315997733 := by
  unfold tailWord_4958184
  simp only [CollatzResearch.WordTrace]
  refine ⟨90419913534676816627940803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120559884712902422170587737 90419913534676816627940803)
  ·
    refine ⟨135629870302015224941911205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90419913534676816627940803 135629870302015224941911205)
    ·
      refine ⟨25430600681627854676608351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135629870302015224941911205 25430600681627854676608351)
      ·
        refine ⟨38145901022441782014912527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25430600681627854676608351 38145901022441782014912527)
        ·
          refine ⟨57218851533662673022368791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38145901022441782014912527 57218851533662673022368791)
          ·
            refine ⟨85828277300494009533553187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57218851533662673022368791 85828277300494009533553187)
            ·
              refine ⟨128742415950741014300329781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85828277300494009533553187 128742415950741014300329781)
              ·
                refine ⟨12069601495381970090655917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128742415950741014300329781 12069601495381970090655917)
                ·
                  refine ⟨4526100560768238783995969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12069601495381970090655917 4526100560768238783995969)
                  ·
                    refine ⟨3394575420576179087996977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526100560768238783995969 3394575420576179087996977)
                    ·
                      refine ⟨2545931565432134315997733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394575420576179087996977 2545931565432134315997733)
                      ·
                        rfl

theorem cell23_4958184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_4958184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958184 prefixEnd_4958184 := by exact prefixLift 4958184
  have htrace : WordTrace (prefixWord ++ tailWord_4958184) baseStart_4958184 baseEnd_4958184 := by
    simpa [prefixWord, tailWord_4958184, baseEnd_4958184] using wordTrace_append hprefix tailTrace_4958184
  have hstable : (prefixWord ++ tailWord_4958184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958184).length < 2 ^ (prefixWord ++ tailWord_4958184).sum := by decide
  have hdescent : baseEnd_4958184 < baseStart_4958184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958218 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_4958218 : Nat := 118140960795 + 4958218 * 2 ^ 59
def prefixEnd_4958218 : Nat := 4983230072969 + 3 ^ 40 * 4958218 * 2
def baseEnd_4958218 : Nat := 2545949023774387182972577

theorem tailTrace_4958218 : CollatzResearch.WordTrace tailWord_4958218 prefixEnd_4958218 2545949023774387182972577 := by
  unfold tailWord_4958218
  simp only [CollatzResearch.WordTrace]
  refine ⟨45210266787807614265654827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120560711434153638041746205 45210266787807614265654827)
  ·
    refine ⟨67815400181711421398482241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45210266787807614265654827 67815400181711421398482241)
    ·
      refine ⟨50861550136283566048861681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67815400181711421398482241 50861550136283566048861681)
      ·
        refine ⟨38146162602212674536646261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50861550136283566048861681 38146162602212674536646261)
        ·
          refine ⟨3576202743957438237810587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38146162602212674536646261 3576202743957438237810587)
          ·
            refine ⟨5364304115936157356715881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576202743957438237810587 5364304115936157356715881)
            ·
              refine ⟨4023228086952118017536911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5364304115936157356715881 4023228086952118017536911)
              ·
                refine ⟨6034842130428177026305367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023228086952118017536911 6034842130428177026305367)
                ·
                  refine ⟨9052263195642265539458051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6034842130428177026305367 9052263195642265539458051)
                  ·
                    refine ⟨13578394793463398309187077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9052263195642265539458051 13578394793463398309187077)
                    ·
                      refine ⟨2545949023774387182972577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13578394793463398309187077 2545949023774387182972577)
                      ·
                        rfl

theorem cell23_4958218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_4958218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958218 prefixEnd_4958218 := by exact prefixLift 4958218
  have htrace : WordTrace (prefixWord ++ tailWord_4958218) baseStart_4958218 baseEnd_4958218 := by
    simpa [prefixWord, tailWord_4958218, baseEnd_4958218] using wordTrace_append hprefix tailTrace_4958218
  have hstable : (prefixWord ++ tailWord_4958218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958218).length < 2 ^ (prefixWord ++ tailWord_4958218).sum := by decide
  have hdescent : baseEnd_4958218 < baseStart_4958218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958234 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_4958234 : Nat := 118140960795 + 4958234 * 2 ^ 59
def prefixEnd_4958234 : Nat := 4983230072969 + 3 ^ 40 * 4958234 * 2
def baseEnd_4958234 : Nat := 2545957239464859120372503

theorem tailTrace_4958234 : CollatzResearch.WordTrace tailWord_4958234 prefixEnd_4958234 2545957239464859120372503 := by
  unfold tailWord_4958234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45210412679793122948800439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120561100479448327863467837 45210412679793122948800439)
  ·
    refine ⟨67815619019689684423200659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45210412679793122948800439 67815619019689684423200659)
    ·
      refine ⟨101723428529534526634800989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67815619019689684423200659 101723428529534526634800989)
      ·
        refine ⟨38146285698575447488050371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101723428529534526634800989 38146285698575447488050371)
        ·
          refine ⟨57219428547863171232075557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38146285698575447488050371 57219428547863171232075557)
          ·
            refine ⟨10728642852724344606014167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57219428547863171232075557 10728642852724344606014167)
            ·
              refine ⟨16092964279086516909021251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10728642852724344606014167 16092964279086516909021251)
              ·
                refine ⟨24139446418629775363531877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16092964279086516909021251 24139446418629775363531877)
                ·
                  refine ⟨4526146203493082880662227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24139446418629775363531877 4526146203493082880662227)
                  ·
                    refine ⟨6789219305239624320993341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4526146203493082880662227 6789219305239624320993341)
                    ·
                      refine ⟨2545957239464859120372503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6789219305239624320993341 2545957239464859120372503)
                      ·
                        rfl

theorem cell23_4958234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_4958234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958234 prefixEnd_4958234 := by exact prefixLift 4958234
  have htrace : WordTrace (prefixWord ++ tailWord_4958234) baseStart_4958234 baseEnd_4958234 := by
    simpa [prefixWord, tailWord_4958234, baseEnd_4958234] using wordTrace_append hprefix tailTrace_4958234
  have hstable : (prefixWord ++ tailWord_4958234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958234).length < 2 ^ (prefixWord ++ tailWord_4958234).sum := by decide
  have hdescent : baseEnd_4958234 < baseStart_4958234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958248 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4958248 : Nat := 118140960795 + 4958248 * 2 ^ 59
def prefixEnd_4958248 : Nat := 4983230072969 + 3 ^ 40 * 4958248 * 2
def baseEnd_4958248 : Nat := 2545964428194022065597439

theorem tailTrace_4958248 : CollatzResearch.WordTrace tailWord_4958248 prefixEnd_4958248 2545964428194022065597439 := by
  unfold tailWord_4958248
  simp only [CollatzResearch.WordTrace]
  refine ⟨90421080670560886093105699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120561440894081181457474265 90421080670560886093105699)
  ·
    refine ⟨135631621005841329139658549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90421080670560886093105699 135631621005841329139658549)
    ·
      refine ⟨12715464469297624606842989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135631621005841329139658549 12715464469297624606842989)
      ·
        refine ⟨4768299175986609227566121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12715464469297624606842989 4768299175986609227566121)
        ·
          refine ⟨3576224381989956920674591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4768299175986609227566121 3576224381989956920674591)
          ·
            refine ⟨5364336572984935381011887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576224381989956920674591 5364336572984935381011887)
            ·
              refine ⟨8046504859477403071517831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364336572984935381011887 8046504859477403071517831)
              ·
                refine ⟨12069757289216104607276747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8046504859477403071517831 12069757289216104607276747)
                ·
                  refine ⟨18104635933824156910915121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12069757289216104607276747 18104635933824156910915121)
                  ·
                    refine ⟨13578476950368117683186341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18104635933824156910915121 13578476950368117683186341)
                    ·
                      refine ⟨2545964428194022065597439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13578476950368117683186341 2545964428194022065597439)
                      ·
                        rfl

theorem cell23_4958248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4958248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958248 prefixEnd_4958248 := by exact prefixLift 4958248
  have htrace : WordTrace (prefixWord ++ tailWord_4958248) baseStart_4958248 baseEnd_4958248 := by
    simpa [prefixWord, tailWord_4958248, baseEnd_4958248] using wordTrace_append hprefix tailTrace_4958248
  have hstable : (prefixWord ++ tailWord_4958248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958248).length < 2 ^ (prefixWord ++ tailWord_4958248).sum := by decide
  have hdescent : baseEnd_4958248 < baseStart_4958248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958278 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_4958278 : Nat := 118140960795 + 4958278 * 2 ^ 59
def prefixEnd_4958278 : Nat := 4983230072969 + 3 ^ 40 * 4958278 * 2
def baseEnd_4958278 : Nat := 2545979832613656948222301

theorem tailTrace_4958278 : CollatzResearch.WordTrace tailWord_4958278 prefixEnd_4958278 2545979832613656948222301 := by
  unfold tailWord_4958278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5651351735344158978431359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120562170354008724873202325 5651351735344158978431359)
  ·
    refine ⟨8477027603016238467647039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5651351735344158978431359 8477027603016238467647039)
    ·
      refine ⟨12715541404524357701470559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8477027603016238467647039 12715541404524357701470559)
      ·
        refine ⟨19073312106786536552205839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12715541404524357701470559 19073312106786536552205839)
        ·
          refine ⟨28609968160179804828308759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19073312106786536552205839 28609968160179804828308759)
          ·
            refine ⟨42914952240269707242463139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28609968160179804828308759 42914952240269707242463139)
            ·
              refine ⟨64372428360404560863694709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42914952240269707242463139 64372428360404560863694709)
              ·
                refine ⟨6034915158787927580971379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64372428360404560863694709 6034915158787927580971379)
                ·
                  refine ⟨9052372738181891371457069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6034915158787927580971379 9052372738181891371457069)
                  ·
                    refine ⟨3394639776818209264296401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9052372738181891371457069 3394639776818209264296401)
                    ·
                      refine ⟨2545979832613656948222301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394639776818209264296401 2545979832613656948222301)
                      ·
                        rfl

theorem cell23_4958278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_4958278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958278 prefixEnd_4958278 := by exact prefixLift 4958278
  have htrace : WordTrace (prefixWord ++ tailWord_4958278) baseStart_4958278 baseEnd_4958278 := by
    simpa [prefixWord, tailWord_4958278, baseEnd_4958278] using wordTrace_append hprefix tailTrace_4958278
  have hstable : (prefixWord ++ tailWord_4958278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958278).length < 2 ^ (prefixWord ++ tailWord_4958278).sum := by decide
  have hdescent : baseEnd_4958278 < baseStart_4958278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958307 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 3]
def baseStart_4958307 : Nat := 118140960795 + 4958307 * 2 ^ 59
def prefixEnd_4958307 : Nat := 4983230072969 + 3 ^ 40 * 4958307 * 2
def baseEnd_4958307 : Nat := 2545994723552637334759667

theorem tailTrace_4958307 : CollatzResearch.WordTrace tailWord_4958307 prefixEnd_4958307 2545994723552637334759667 := by
  unfold tailWord_4958307
  simp only [CollatzResearch.WordTrace]
  refine ⟨180844313247908025262609175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120562875498605350175072783 180844313247908025262609175)
  ·
    refine ⟨271266469871862037893913763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180844313247908025262609175 271266469871862037893913763)
    ·
      refine ⟨406899704807793056840870645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271266469871862037893913763 406899704807793056840870645)
      ·
        refine ⟨38146847325730599078831623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 406899704807793056840870645 38146847325730599078831623)
        ·
          refine ⟨57220270988595898618247435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38146847325730599078831623 57220270988595898618247435)
          ·
            refine ⟨85830406482893847927371153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57220270988595898618247435 85830406482893847927371153)
            ·
              refine ⟨64372804862170385945528365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85830406482893847927371153 64372804862170385945528365)
              ·
                refine ⟨24139801823313894729573137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64372804862170385945528365 24139801823313894729573137)
                ·
                  refine ⟨18104851367485421047179853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24139801823313894729573137 18104851367485421047179853)
                  ·
                    refine ⟨6789319262807032892692445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18104851367485421047179853 6789319262807032892692445)
                    ·
                      refine ⟨2545994723552637334759667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6789319262807032892692445 2545994723552637334759667)
                      ·
                        rfl

theorem cell23_4958307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_4958307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958307 prefixEnd_4958307 := by exact prefixLift 4958307
  have htrace : WordTrace (prefixWord ++ tailWord_4958307) baseStart_4958307 baseEnd_4958307 := by
    simpa [prefixWord, tailWord_4958307, baseEnd_4958307] using wordTrace_append hprefix tailTrace_4958307
  have hstable : (prefixWord ++ tailWord_4958307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958307).length < 2 ^ (prefixWord ++ tailWord_4958307).sum := by decide
  have hdescent : baseEnd_4958307 < baseStart_4958307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958308 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_4958308 : Nat := 118140960795 + 4958308 * 2 ^ 59
def prefixEnd_4958308 : Nat := 4983230072969 + 3 ^ 40 * 4958308 * 2
def baseEnd_4958308 : Nat := 2545995237033291830847163

theorem tailTrace_4958308 : CollatzResearch.WordTrace tailWord_4958308 prefixEnd_4958308 2545995237033291830847163 := by
  unfold tailWord_4958308
  simp only [CollatzResearch.WordTrace]
  refine ⟨90422174860452201216697789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120562899813936268288930385 90422174860452201216697789)
  ·
    refine ⟨33908315572669575456261671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90422174860452201216697789 33908315572669575456261671)
    ·
      refine ⟨50862473359004363184392507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33908315572669575456261671 50862473359004363184392507)
      ·
        refine ⟨76293710038506544776588761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50862473359004363184392507 76293710038506544776588761)
        ·
          refine ⟨57220282528879908582441571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76293710038506544776588761 57220282528879908582441571)
          ·
            refine ⟨85830423793319862873662357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57220282528879908582441571 85830423793319862873662357)
            ·
              refine ⟨4023301115311868572202923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85830423793319862873662357 4023301115311868572202923)
              ·
                refine ⟨6034951672967802858304385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023301115311868572202923 6034951672967802858304385)
                ·
                  refine ⟨4526213754725852143728289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6034951672967802858304385 4526213754725852143728289)
                  ·
                    refine ⟨3394660316044389107796217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526213754725852143728289 3394660316044389107796217)
                    ·
                      refine ⟨2545995237033291830847163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394660316044389107796217 2545995237033291830847163)
                      ·
                        rfl

theorem cell23_4958308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_4958308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958308 prefixEnd_4958308 := by exact prefixLift 4958308
  have htrace : WordTrace (prefixWord ++ tailWord_4958308) baseStart_4958308 baseEnd_4958308 := by
    simpa [prefixWord, tailWord_4958308, baseEnd_4958308] using wordTrace_append hprefix tailTrace_4958308
  have hstable : (prefixWord ++ tailWord_4958308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958308).length < 2 ^ (prefixWord ++ tailWord_4958308).sum := by decide
  have hdescent : baseEnd_4958308 < baseStart_4958308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958327 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 2, 5]
def baseStart_4958327 : Nat := 118140960795 + 4958327 * 2 ^ 59
def prefixEnd_4958327 : Nat := 4983230072969 + 3 ^ 40 * 4958327 * 2
def baseEnd_4958327 : Nat := 848668331055242418836525

theorem tailTrace_4958327 : CollatzResearch.WordTrace tailWord_4958327 prefixEnd_4958327 848668331055242418836525 := by
  unfold tailWord_4958327
  simp only [CollatzResearch.WordTrace]
  refine ⟨180845042707835568678337235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120563361805223712452224823 180845042707835568678337235)
  ·
    refine ⟨271267564061753353017505853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180845042707835568678337235 271267564061753353017505853)
    ·
      refine ⟨101725336523157507381564695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271267564061753353017505853 101725336523157507381564695)
      ·
        refine ⟨152588004784736261072347043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101725336523157507381564695 152588004784736261072347043)
        ·
          refine ⟨228882007177104391608520565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152588004784736261072347043 228882007177104391608520565)
          ·
            refine ⟨21457688172853536713298803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228882007177104391608520565 21457688172853536713298803)
            ·
              refine ⟨32186532259280305069948205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21457688172853536713298803 32186532259280305069948205)
              ·
                refine ⟨12069949597230114401230577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32186532259280305069948205 12069949597230114401230577)
                ·
                  refine ⟨9052462197922585800922933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12069949597230114401230577 9052462197922585800922933)
                  ·
                    refine ⟨848668331055242418836525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9052462197922585800922933 848668331055242418836525)
                    ·
                      rfl

theorem cell23_4958327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_4958327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958327 prefixEnd_4958327 := by exact prefixLift 4958327
  have htrace : WordTrace (prefixWord ++ tailWord_4958327) baseStart_4958327 baseEnd_4958327 := by
    simpa [prefixWord, tailWord_4958327, baseEnd_4958327] using wordTrace_append hprefix tailTrace_4958327
  have hstable : (prefixWord ++ tailWord_4958327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958327).length < 2 ^ (prefixWord ++ tailWord_4958327).sum := by decide
  have hdescent : baseEnd_4958327 < baseStart_4958327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958344 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 2, 5]
def baseStart_4958344 : Nat := 118140960795 + 4958344 * 2 ^ 59
def prefixEnd_4958344 : Nat := 4983230072969 + 3 ^ 40 * 4958344 * 2
def baseEnd_4958344 : Nat := 848671240778951229998999

theorem tailTrace_4958344 : CollatzResearch.WordTrace tailWord_4958344 prefixEnd_4958344 848671240778951229998999 := by
  unfold tailWord_4958344
  simp only [CollatzResearch.WordTrace]
  refine ⟨90422831374386990290853043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120563775165849320387804057 90422831374386990290853043)
  ·
    refine ⟨135634247061580485436279565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90422831374386990290853043 135634247061580485436279565)
    ·
      refine ⟨50862842648092682038604837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135634247061580485436279565 50862842648092682038604837)
      ·
        refine ⟨9536782996517377882238407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50862842648092682038604837 9536782996517377882238407)
        ·
          refine ⟨14305174494776066823357611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9536782996517377882238407 14305174494776066823357611)
          ·
            refine ⟨21457761742164100235036417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14305174494776066823357611 21457761742164100235036417)
            ·
              refine ⟨16093321306623075176277313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21457761742164100235036417 16093321306623075176277313)
              ·
                refine ⟨12069990979967306382207985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16093321306623075176277313 12069990979967306382207985)
                ·
                  refine ⟨9052493234975479786655989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12069990979967306382207985 9052493234975479786655989)
                  ·
                    refine ⟨848671240778951229998999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9052493234975479786655989 848671240778951229998999)
                    ·
                      rfl

theorem cell23_4958344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_4958344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958344 prefixEnd_4958344 := by exact prefixLift 4958344
  have htrace : WordTrace (prefixWord ++ tailWord_4958344) baseStart_4958344 baseEnd_4958344 := by
    simpa [prefixWord, tailWord_4958344, baseEnd_4958344] using wordTrace_append hprefix tailTrace_4958344
  have hstable : (prefixWord ++ tailWord_4958344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958344).length < 2 ^ (prefixWord ++ tailWord_4958344).sum := by decide
  have hdescent : baseEnd_4958344 < baseStart_4958344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958378 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4958378 : Nat := 118140960795 + 4958378 * 2 ^ 59
def prefixEnd_4958378 : Nat := 4983230072969 + 3 ^ 40 * 4958378 * 2
def baseEnd_4958378 : Nat := 848677060226368852323947

theorem tailTrace_4958378 : CollatzResearch.WordTrace tailWord_4958378 prefixEnd_4958378 848677060226368852323947 := by
  unfold tailWord_4958378
  simp only [CollatzResearch.WordTrace]
  refine ⟨45211725707662701097110947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120564601887100536258962525 45211725707662701097110947)
  ·
    refine ⟨67817588561494051645666421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45211725707662701097110947 67817588561494051645666421)
    ·
      refine ⟨6357898927640067341781227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67817588561494051645666421 6357898927640067341781227)
      ·
        refine ⟨9536848391460101012671841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357898927640067341781227 9536848391460101012671841)
        ·
          refine ⟨7152636293595075759503881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9536848391460101012671841 7152636293595075759503881)
          ·
            refine ⟨5364477220196306819627911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7152636293595075759503881 5364477220196306819627911)
            ·
              refine ⟨8046715830294460229441867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364477220196306819627911 8046715830294460229441867)
              ·
                refine ⟨12070073745441690344162801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8046715830294460229441867 12070073745441690344162801)
                ·
                  refine ⟨9052555309081267758122101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12070073745441690344162801 9052555309081267758122101)
                  ·
                    refine ⟨848677060226368852323947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9052555309081267758122101 848677060226368852323947)
                    ·
                      rfl

theorem cell23_4958378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4958378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958378 prefixEnd_4958378 := by exact prefixLift 4958378
  have htrace : WordTrace (prefixWord ++ tailWord_4958378) baseStart_4958378 baseEnd_4958378 := by
    simpa [prefixWord, tailWord_4958378, baseEnd_4958378] using wordTrace_append hprefix tailTrace_4958378
  have hstable : (prefixWord ++ tailWord_4958378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958378).length < 2 ^ (prefixWord ++ tailWord_4958378).sum := by decide
  have hdescent : baseEnd_4958378 < baseStart_4958378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958381 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_4958381 : Nat := 118140960795 + 4958381 * 2 ^ 59
def prefixEnd_4958381 : Nat := 4983230072969 + 3 ^ 40 * 4958381 * 2
def baseEnd_4958381 : Nat := 2546032721121070045234327

theorem tailTrace_4958381 : CollatzResearch.WordTrace tailWord_4958381 prefixEnd_4958381 2546032721121070045234327 := by
  unfold tailWord_4958381
  simp only [CollatzResearch.WordTrace]
  refine ⟨180847012249639935900802997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120564674833093290600535331 180847012249639935900802997)
  ·
    refine ⟨16954407398403743990700281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 180847012249639935900802997 16954407398403743990700281)
    ·
      refine ⟨12715805548802807993025211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16954407398403743990700281 12715805548802807993025211)
      ·
        refine ⟨19073708323204211989537817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12715805548802807993025211 19073708323204211989537817)
        ·
          refine ⟨14305281242403158992153363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19073708323204211989537817 14305281242403158992153363)
          ·
            refine ⟨21457921863604738488230045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14305281242403158992153363 21457921863604738488230045)
            ·
              refine ⟨8046720698851776933086267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21457921863604738488230045 8046720698851776933086267)
              ·
                refine ⟨12070081048277665399629401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8046720698851776933086267 12070081048277665399629401)
                ·
                  refine ⟨9052560786208249049722051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12070081048277665399629401 9052560786208249049722051)
                  ·
                    refine ⟨13578841179312373574583077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9052560786208249049722051 13578841179312373574583077)
                    ·
                      refine ⟨2546032721121070045234327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13578841179312373574583077 2546032721121070045234327)
                      ·
                        rfl

theorem cell23_4958381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_4958381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958381 prefixEnd_4958381 := by exact prefixLift 4958381
  have htrace : WordTrace (prefixWord ++ tailWord_4958381) baseStart_4958381 baseEnd_4958381 := by
    simpa [prefixWord, tailWord_4958381, baseEnd_4958381] using wordTrace_append hprefix tailTrace_4958381
  have hstable : (prefixWord ++ tailWord_4958381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958381).length < 2 ^ (prefixWord ++ tailWord_4958381).sum := by decide
  have hdescent : baseEnd_4958381 < baseStart_4958381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958391 : List Nat := [1, 1, 3, 1, 4, 2, 1, 5, 1, 4]
def baseStart_4958391 : Nat := 118140960795 + 4958391 * 2 ^ 59
def prefixEnd_4958391 : Nat := 4983230072969 + 3 ^ 40 * 4958391 * 2
def baseEnd_4958391 : Nat := 848679285309205002036427

theorem tailTrace_4958391 : CollatzResearch.WordTrace tailWord_4958391 prefixEnd_4958391 848679285309205002036427 := by
  unfold tailWord_4958391
  simp only [CollatzResearch.WordTrace]
  refine ⟨180847376979603707608667027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120564917986402471739111351 180847376979603707608667027)
  ·
    refine ⟨271271065469405561413000541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180847376979603707608667027 271271065469405561413000541)
    ·
      refine ⟨101726649551027085529875203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271271065469405561413000541 101726649551027085529875203)
      ·
        refine ⟨152589974326540628294812805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101726649551027085529875203 152589974326540628294812805)
        ·
          refine ⟨28610620186226367805277401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152589974326540628294812805 28610620186226367805277401)
          ·
            refine ⟨21457965139669775853958051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28610620186226367805277401 21457965139669775853958051)
            ·
              refine ⟨32186947709504663780937077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21457965139669775853958051 32186947709504663780937077)
              ·
                refine ⟨3017526347766062229462851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32186947709504663780937077 3017526347766062229462851)
                ·
                  refine ⟨4526289521649093344194277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017526347766062229462851 4526289521649093344194277)
                  ·
                    refine ⟨848679285309205002036427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526289521649093344194277 848679285309205002036427)
                    ·
                      rfl

theorem cell23_4958391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_4958391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958391 prefixEnd_4958391 := by exact prefixLift 4958391
  have htrace : WordTrace (prefixWord ++ tailWord_4958391) baseStart_4958391 baseEnd_4958391 := by
    simpa [prefixWord, tailWord_4958391, baseEnd_4958391] using wordTrace_append hprefix tailTrace_4958391
  have hstable : (prefixWord ++ tailWord_4958391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958391).length < 2 ^ (prefixWord ++ tailWord_4958391).sum := by decide
  have hdescent : baseEnd_4958391 < baseStart_4958391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958404 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 8]
def baseStart_4958404 : Nat := 118140960795 + 4958404 * 2 ^ 59
def prefixEnd_4958404 : Nat := 4983230072969 + 3 ^ 40 * 4958404 * 2
def baseEnd_4958404 : Nat := 282893836797347050582969

theorem tailTrace_4958404 : CollatzResearch.WordTrace tailWord_4958404 prefixEnd_4958404 282893836797347050582969 := by
  unfold tailWord_4958404
  simp only [CollatzResearch.WordTrace]
  refine ⟨90423925564278305414445133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120565234085704407219260177 90423925564278305414445133)
  ·
    refine ⟨33908972086604364530416925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90423925564278305414445133 33908972086604364530416925)
    ·
      refine ⟨12715864532476636698906347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33908972086604364530416925 12715864532476636698906347)
      ·
        refine ⟨19073796798714955048359521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12715864532476636698906347 19073796798714955048359521)
        ·
          refine ⟨14305347599036216286269641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19073796798714955048359521 14305347599036216286269641)
          ·
            refine ⟨10729010699277162214702231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14305347599036216286269641 10729010699277162214702231)
            ·
              refine ⟨16093516048915743322053347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10729010699277162214702231 16093516048915743322053347)
              ·
                refine ⟨24140274073373614983080021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16093516048915743322053347 24140274073373614983080021)
                ·
                  refine ⟨282893836797347050582969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24140274073373614983080021 282893836797347050582969)
                  ·
                    rfl

theorem cell23_4958404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_4958404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958404 prefixEnd_4958404 := by exact prefixLift 4958404
  have htrace : WordTrace (prefixWord ++ tailWord_4958404) baseStart_4958404 baseEnd_4958404 := by
    simpa [prefixWord, tailWord_4958404, baseEnd_4958404] using wordTrace_append hprefix tailTrace_4958404
  have hstable : (prefixWord ++ tailWord_4958404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958404).length < 2 ^ (prefixWord ++ tailWord_4958404).sum := by decide
  have hdescent : baseEnd_4958404 < baseStart_4958404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958417 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 5, 5]
def baseStart_4958417 : Nat := 118140960795 + 4958417 * 2 ^ 59
def prefixEnd_4958417 : Nat := 4983230072969 + 3 ^ 40 * 4958417 * 2
def baseEnd_4958417 : Nat := 848683735474877301461387

theorem tailTrace_4958417 : CollatzResearch.WordTrace tailWord_4958417 prefixEnd_4958417 848683735474877301461387 := by
  unfold tailWord_4958417
  simp only [CollatzResearch.WordTrace]
  refine ⟨180848325277509514049113505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120565550185006342699409003 180848325277509514049113505)
  ·
    refine ⟨135636243958132135536835129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180848325277509514049113505 135636243958132135536835129)
    ·
      refine ⟨101727182968599101652626347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135636243958132135536835129 101727182968599101652626347)
      ·
        refine ⟨152590774452898652478939521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101727182968599101652626347 152590774452898652478939521)
        ·
          refine ⟨114443080839673989359204641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152590774452898652478939521 114443080839673989359204641)
          ·
            refine ⟨85832310629755492019403481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114443080839673989359204641 85832310629755492019403481)
            ·
              refine ⟨64374232972316619014552611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85832310629755492019403481 64374232972316619014552611)
              ·
                refine ⟨96561349458474928521828917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64374232972316619014552611 96561349458474928521828917)
                ·
                  refine ⟨9052626511732024548921461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96561349458474928521828917 9052626511732024548921461)
                  ·
                    refine ⟨848683735474877301461387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9052626511732024548921461 848683735474877301461387)
                    ·
                      rfl

theorem cell23_4958417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_4958417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958417 prefixEnd_4958417 := by exact prefixLift 4958417
  have htrace : WordTrace (prefixWord ++ tailWord_4958417) baseStart_4958417 baseEnd_4958417 := by
    simpa [prefixWord, tailWord_4958417, baseEnd_4958417] using wordTrace_append hprefix tailTrace_4958417
  have hstable : (prefixWord ++ tailWord_4958417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958417).length < 2 ^ (prefixWord ++ tailWord_4958417).sum := by decide
  have hdescent : baseEnd_4958417 < baseStart_4958417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958464 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 4, 4]
def baseStart_4958464 : Nat := 118140960795 + 4958464 * 2 ^ 59
def prefixEnd_4958464 : Nat := 4983230072969 + 3 ^ 40 * 4958464 * 2
def baseEnd_4958464 : Nat := 848691780005131073498815

theorem tailTrace_4958464 : CollatzResearch.WordTrace tailWord_4958464 prefixEnd_4958464 848691780005131073498815 := by
  unfold tailWord_4958464
  simp only [CollatzResearch.WordTrace]
  refine ⟨90425019754169620538037223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120566693005559494050716297 90425019754169620538037223)
  ·
    refine ⟨135637529631254430807055835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90425019754169620538037223 135637529631254430807055835)
    ·
      refine ⟨203456294446881646210583753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135637529631254430807055835 203456294446881646210583753)
      ·
        refine ⟨152592220835161234657937815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203456294446881646210583753 152592220835161234657937815)
        ·
          refine ⟨228888331252741851986906723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152592220835161234657937815 228888331252741851986906723)
          ·
            refine ⟨343332496879112777980360085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228888331252741851986906723 343332496879112777980360085)
            ·
              refine ⟨16093710791208411467829379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 343332496879112777980360085 16093710791208411467829379)
              ·
                refine ⟨24140566186812617201744069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16093710791208411467829379 24140566186812617201744069)
                ·
                  refine ⟨4526356160027365725327013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24140566186812617201744069 4526356160027365725327013)
                  ·
                    refine ⟨848691780005131073498815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526356160027365725327013 848691780005131073498815)
                    ·
                      rfl

theorem cell23_4958464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_4958464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958464 prefixEnd_4958464 := by exact prefixLift 4958464
  have htrace : WordTrace (prefixWord ++ tailWord_4958464) baseStart_4958464 baseEnd_4958464 := by
    simpa [prefixWord, tailWord_4958464, baseEnd_4958464] using wordTrace_append hprefix tailTrace_4958464
  have hstable : (prefixWord ++ tailWord_4958464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958464).length < 2 ^ (prefixWord ++ tailWord_4958464).sum := by decide
  have hdescent : baseEnd_4958464 < baseStart_4958464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958465 : List Nat := [1, 2, 4, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_4958465 : Nat := 118140960795 + 4958465 * 2 ^ 59
def prefixEnd_4958465 : Nat := 4983230072969 + 3 ^ 40 * 4958465 * 2
def baseEnd_4958465 : Nat := 2546075853496047716583941

theorem tailTrace_4958465 : CollatzResearch.WordTrace tailWord_4958465 prefixEnd_4958465 2546075853496047716583941 := by
  unfold tailWord_4958465
  simp only [CollatzResearch.WordTrace]
  refine ⟨180850075981335618246860849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120566717320890412164573899 180850075981335618246860849)
  ·
    refine ⟨135637556986001713685145637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180850075981335618246860849 135637556986001713685145637)
    ·
      refine ⟨25432041934875321315964807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135637556986001713685145637 25432041934875321315964807)
      ·
        refine ⟨38148062902312981973947211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25432041934875321315964807 38148062902312981973947211)
        ·
          refine ⟨57222094353469472960920817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38148062902312981973947211 57222094353469472960920817)
          ·
            refine ⟨42916570765102104720690613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57222094353469472960920817 42916570765102104720690613)
            ·
              refine ⟨4023428509228322317564745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42916570765102104720690613 4023428509228322317564745)
              ·
                refine ⟨3017571381921241738173559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4023428509228322317564745 3017571381921241738173559)
                ·
                  refine ⟨4526357072881862607260339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017571381921241738173559 4526357072881862607260339)
                  ·
                    refine ⟨6789535609322793910890509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4526357072881862607260339 6789535609322793910890509)
                    ·
                      refine ⟨2546075853496047716583941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6789535609322793910890509 2546075853496047716583941)
                      ·
                        rfl

theorem cell23_4958465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_4958465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958465 prefixEnd_4958465 := by exact prefixLift 4958465
  have htrace : WordTrace (prefixWord ++ tailWord_4958465) baseStart_4958465 baseEnd_4958465 := by
    simpa [prefixWord, tailWord_4958465, baseEnd_4958465] using wordTrace_append hprefix tailTrace_4958465
  have hstable : (prefixWord ++ tailWord_4958465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958465).length < 2 ^ (prefixWord ++ tailWord_4958465).sum := by decide
  have hdescent : baseEnd_4958465 < baseStart_4958465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958467 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6]
def baseStart_4958467 : Nat := 118140960795 + 4958467 * 2 ^ 59
def prefixEnd_4958467 : Nat := 4983230072969 + 3 ^ 40 * 4958467 * 2
def baseEnd_4958467 : Nat := 2546076880457356708758931

theorem tailTrace_4958467 : CollatzResearch.WordTrace tailWord_4958467 prefixEnd_4958467 2546076880457356708758931 := by
  unfold tailWord_4958467
  simp only [CollatzResearch.WordTrace]
  refine ⟨180850148927328372588433655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120566765951552248392289103 180850148927328372588433655)
  ·
    refine ⟨271275223390992558882650483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180850148927328372588433655 271275223390992558882650483)
    ·
      refine ⟨406912835086488838323975725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271275223390992558882650483 406912835086488838323975725)
      ·
        refine ⟨152592313157433314371490897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406912835086488838323975725 152592313157433314371490897)
        ·
          refine ⟨114444234868074985778618173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152592313157433314371490897 114444234868074985778618173)
          ·
            refine ⟨42916588075528119666981815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114444234868074985778618173 42916588075528119666981815)
            ·
              refine ⟨64374882113292179500472723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42916588075528119666981815 64374882113292179500472723)
              ·
                refine ⟨96562323169938269250709085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64374882113292179500472723 96562323169938269250709085)
                ·
                  refine ⟨36210871188726850969015907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96562323169938269250709085 36210871188726850969015907)
                  ·
                    refine ⟨54316306783090276453523861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36210871188726850969015907 54316306783090276453523861)
                    ·
                      refine ⟨2546076880457356708758931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54316306783090276453523861 2546076880457356708758931)
                      ·
                        rfl

theorem cell23_4958467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_4958467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958467 prefixEnd_4958467 := by exact prefixLift 4958467
  have htrace : WordTrace (prefixWord ++ tailWord_4958467) baseStart_4958467 baseEnd_4958467 := by
    simpa [prefixWord, tailWord_4958467, baseEnd_4958467] using wordTrace_append hprefix tailTrace_4958467
  have hstable : (prefixWord ++ tailWord_4958467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958467).length < 2 ^ (prefixWord ++ tailWord_4958467).sum := by decide
  have hdescent : baseEnd_4958467 < baseStart_4958467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958474 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_4958474 : Nat := 118140960795 + 4958474 * 2 ^ 59
def prefixEnd_4958474 : Nat := 4983230072969 + 3 ^ 40 * 4958474 * 2
def baseEnd_4958474 : Nat := 2546080474821938181371399

theorem tailTrace_4958474 : CollatzResearch.WordTrace tailWord_4958474 prefixEnd_4958474 2546080474821938181371399 := by
  unfold tailWord_4958474
  simp only [CollatzResearch.WordTrace]
  refine ⟨45212601059575753195984619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120566936158868675189292317 45212601059575753195984619)
  ·
    refine ⟨67818901589363629793976929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45212601059575753195984619 67818901589363629793976929)
    ·
      refine ⟨50864176192022722345482697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67818901589363629793976929 50864176192022722345482697)
      ·
        refine ⟨38148132144017041759112023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50864176192022722345482697 38148132144017041759112023)
        ·
          refine ⟨57222198216025562638668035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38148132144017041759112023 57222198216025562638668035)
          ·
            refine ⟨85833297324038343958002053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57222198216025562638668035 85833297324038343958002053)
            ·
              refine ⟨16093743248257189492125385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85833297324038343958002053 16093743248257189492125385)
              ·
                refine ⟨12070307436192892119094039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16093743248257189492125385 12070307436192892119094039)
                ·
                  refine ⟨18105461154289338178641059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12070307436192892119094039 18105461154289338178641059)
                  ·
                    refine ⟨27158191731434007267961589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18105461154289338178641059 27158191731434007267961589)
                    ·
                      refine ⟨2546080474821938181371399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27158191731434007267961589 2546080474821938181371399)
                      ·
                        rfl

theorem cell23_4958474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_4958474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958474 prefixEnd_4958474 := by exact prefixLift 4958474
  have htrace : WordTrace (prefixWord ++ tailWord_4958474) baseStart_4958474 baseEnd_4958474 := by
    simpa [prefixWord, tailWord_4958474, baseEnd_4958474] using wordTrace_append hprefix tailTrace_4958474
  have hstable : (prefixWord ++ tailWord_4958474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958474).length < 2 ^ (prefixWord ++ tailWord_4958474).sum := by decide
  have hdescent : baseEnd_4958474 < baseStart_4958474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958481 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 2, 4]
def baseStart_4958481 : Nat := 118140960795 + 4958481 * 2 ^ 59
def prefixEnd_4958481 : Nat := 4983230072969 + 3 ^ 40 * 4958481 * 2
def baseEnd_4958481 : Nat := 848694689728839884661289

theorem tailTrace_4958481 : CollatzResearch.WordTrace tailWord_4958481 prefixEnd_4958481 848694689728839884661289 := by
  unfold tailWord_4958481
  simp only [CollatzResearch.WordTrace]
  refine ⟨180850659549277652979443297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120567106366185101986295531 180850659549277652979443297)
  ·
    refine ⟨135637994661958239734582473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180850659549277652979443297 135637994661958239734582473)
    ·
      refine ⟨101728495996468679800936855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135637994661958239734582473 101728495996468679800936855)
      ·
        refine ⟨152592743994703019701405283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101728495996468679800936855 152592743994703019701405283)
        ·
          refine ⟨228889115992054529552107925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152592743994703019701405283 228889115992054529552107925)
          ·
            refine ⟨10729177312127556072755059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 228889115992054529552107925 10729177312127556072755059)
            ·
              refine ⟨16093765968191334109132589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10729177312127556072755059 16093765968191334109132589)
              ·
                refine ⟨6035162238071750290924721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16093765968191334109132589 6035162238071750290924721)
                ·
                  refine ⟨4526371678553812718193541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035162238071750290924721 4526371678553812718193541)
                  ·
                    refine ⟨848694689728839884661289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526371678553812718193541 848694689728839884661289)
                    ·
                      rfl

theorem cell23_4958481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_4958481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958481 prefixEnd_4958481 := by exact prefixLift 4958481
  have htrace : WordTrace (prefixWord ++ tailWord_4958481) baseStart_4958481 baseEnd_4958481 := by
    simpa [prefixWord, tailWord_4958481, baseEnd_4958481] using wordTrace_append hprefix tailTrace_4958481
  have hstable : (prefixWord ++ tailWord_4958481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958481).length < 2 ^ (prefixWord ++ tailWord_4958481).sum := by decide
  have hdescent : baseEnd_4958481 < baseStart_4958481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958491 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 3]
def baseStart_4958491 : Nat := 118140960795 + 4958491 * 2 ^ 59
def prefixEnd_4958491 : Nat := 4983230072969 + 3 ^ 40 * 4958491 * 2
def baseEnd_4958491 : Nat := 2546089203993064614858821

theorem tailTrace_4958491 : CollatzResearch.WordTrace tailWord_4958491 prefixEnd_4958491 2546089203993064614858821 := by
  unfold tailWord_4958491
  simp only [CollatzResearch.WordTrace]
  refine ⟨180851024279241424687307327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120567349519494283124871551 180851024279241424687307327)
  ·
    refine ⟨271276536418862137030960991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180851024279241424687307327 271276536418862137030960991)
    ·
      refine ⟨406914804628293205546441487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271276536418862137030960991 406914804628293205546441487)
      ·
        refine ⟨610372206942439808319662231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406914804628293205546441487 610372206942439808319662231)
        ·
          refine ⟨915558310413659712479493347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610372206942439808319662231 915558310413659712479493347)
          ·
            refine ⟨1373337465620489568719240021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915558310413659712479493347 1373337465620489568719240021)
            ·
              refine ⟨8046899212620056066714297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1373337465620489568719240021 8046899212620056066714297)
              ·
                refine ⟨6035174409465042050035723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8046899212620056066714297 6035174409465042050035723)
                ·
                  refine ⟨9052761614197563075053585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6035174409465042050035723 9052761614197563075053585)
                  ·
                    refine ⟨6789571210648172306290189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9052761614197563075053585 6789571210648172306290189)
                    ·
                      refine ⟨2546089203993064614858821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6789571210648172306290189 2546089203993064614858821)
                      ·
                        rfl

theorem cell23_4958491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 3].length) (baseStart_4958491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958491 prefixEnd_4958491 := by exact prefixLift 4958491
  have htrace : WordTrace (prefixWord ++ tailWord_4958491) baseStart_4958491 baseEnd_4958491 := by
    simpa [prefixWord, tailWord_4958491, baseEnd_4958491] using wordTrace_append hprefix tailTrace_4958491
  have hstable : (prefixWord ++ tailWord_4958491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958491).length < 2 ^ (prefixWord ++ tailWord_4958491).sum := by decide
  have hdescent : baseEnd_4958491 < baseStart_4958491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958501 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_4958501 : Nat := 118140960795 + 4958501 * 2 ^ 59
def prefixEnd_4958501 : Nat := 4983230072969 + 3 ^ 40 * 4958501 * 2
def baseEnd_4958501 : Nat := 2546094338799609575733775

theorem tailTrace_4958501 : CollatzResearch.WordTrace tailWord_4958501 prefixEnd_4958501 2546094338799609575733775 := by
  unfold tailWord_4958501
  simp only [CollatzResearch.WordTrace]
  refine ⟨180851389009205196395171357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120567592672803464263447571 180851389009205196395171357)
  ·
    refine ⟨67819270878451948648189259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180851389009205196395171357 67819270878451948648189259)
    ·
      refine ⟨101728906317677922972283889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67819270878451948648189259 101728906317677922972283889)
      ·
        refine ⟨76296679738258442229212917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101728906317677922972283889 76296679738258442229212917)
        ·
          refine ⟨7152813725461728958988711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76296679738258442229212917 7152813725461728958988711)
          ·
            refine ⟨10729220588192593438483067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152813725461728958988711 10729220588192593438483067)
            ·
              refine ⟨16093830882288890157724601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10729220588192593438483067 16093830882288890157724601)
              ·
                refine ⟨12070373161716667618293451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16093830882288890157724601 12070373161716667618293451)
                ·
                  refine ⟨18105559742575001427440177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12070373161716667618293451 18105559742575001427440177)
                  ·
                    refine ⟨13579169806931251070580133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18105559742575001427440177 13579169806931251070580133)
                    ·
                      refine ⟨2546094338799609575733775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13579169806931251070580133 2546094338799609575733775)
                      ·
                        rfl

theorem cell23_4958501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_4958501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958501 prefixEnd_4958501 := by exact prefixLift 4958501
  have htrace : WordTrace (prefixWord ++ tailWord_4958501) baseStart_4958501 baseEnd_4958501 := by
    simpa [prefixWord, tailWord_4958501, baseEnd_4958501] using wordTrace_append hprefix tailTrace_4958501
  have hstable : (prefixWord ++ tailWord_4958501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958501).length < 2 ^ (prefixWord ++ tailWord_4958501).sum := by decide
  have hdescent : baseEnd_4958501 < baseStart_4958501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958522 : List Nat := [3, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2]
def baseStart_4958522 : Nat := 118140960795 + 4958522 * 2 ^ 59
def prefixEnd_4958522 : Nat := 4983230072969 + 3 ^ 40 * 4958522 * 2
def baseEnd_4958522 : Nat := 2546105121893353993571179

theorem tailTrace_4958522 : CollatzResearch.WordTrace tailWord_4958522 prefixEnd_4958522 2546105121893353993571179 := by
  unfold tailWord_4958522
  simp only [CollatzResearch.WordTrace]
  refine ⟨45213038735532279245421455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120568103294752744654457213 45213038735532279245421455)
  ·
    refine ⟨67819558103298418868132183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45213038735532279245421455 67819558103298418868132183)
    ·
      refine ⟨101729337154947628302198275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67819558103298418868132183 101729337154947628302198275)
      ·
        refine ⟨152594005732421442453297413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101729337154947628302198275 152594005732421442453297413)
        ·
          refine ⟨28611376074829020459993265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152594005732421442453297413 28611376074829020459993265)
          ·
            refine ⟨21458532056121765344994949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28611376074829020459993265 21458532056121765344994949)
            ·
              refine ⟨4023474760522831002186553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21458532056121765344994949 4023474760522831002186553)
              ·
                refine ⟨3017606070392123251639915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4023474760522831002186553 3017606070392123251639915)
                ·
                  refine ⟨4526409105588184877459873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017606070392123251639915 4526409105588184877459873)
                  ·
                    refine ⟨3394806829191138658094905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526409105588184877459873 3394806829191138658094905)
                    ·
                      refine ⟨2546105121893353993571179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394806829191138658094905 2546105121893353993571179)
                      ·
                        rfl

theorem cell23_4958522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_4958522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958522 prefixEnd_4958522 := by exact prefixLift 4958522
  have htrace : WordTrace (prefixWord ++ tailWord_4958522) baseStart_4958522 baseEnd_4958522 := by
    simpa [prefixWord, tailWord_4958522, baseEnd_4958522] using wordTrace_append hprefix tailTrace_4958522
  have hstable : (prefixWord ++ tailWord_4958522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958522).length < 2 ^ (prefixWord ++ tailWord_4958522).sum := by decide
  have hdescent : baseEnd_4958522 < baseStart_4958522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958531 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 3, 3, 2]
def baseStart_4958531 : Nat := 118140960795 + 4958531 * 2 ^ 59
def prefixEnd_4958531 : Nat := 4983230072969 + 3 ^ 40 * 4958531 * 2
def baseEnd_4958531 : Nat := 2546109743219244458358637

theorem tailTrace_4958531 : CollatzResearch.WordTrace tailWord_4958531 prefixEnd_4958531 2546109743219244458358637 := by
  unfold tailWord_4958531
  simp only [CollatzResearch.WordTrace]
  refine ⟨180852483199096511518763447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120568322132731007679175631 180852483199096511518763447)
  ·
    refine ⟨271278724798644767278145171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180852483199096511518763447 271278724798644767278145171)
    ·
      refine ⟨406918087197967150917217757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271278724798644767278145171 406918087197967150917217757)
      ·
        refine ⟨152594282699237681593956659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406918087197967150917217757 152594282699237681593956659)
        ·
          refine ⟨228891424048856522390934989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152594282699237681593956659 228891424048856522390934989)
          ·
            refine ⟨85834284018321195896600621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228891424048856522390934989 85834284018321195896600621)
            ·
              refine ⟨32187856506870448461225233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85834284018321195896600621 32187856506870448461225233)
              ·
                refine ⟨24140892380152836345918925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32187856506870448461225233 24140892380152836345918925)
                ·
                  refine ⟨9052834642557313629719597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24140892380152836345918925 9052834642557313629719597)
                  ·
                    refine ⟨3394812990958992611144849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9052834642557313629719597 3394812990958992611144849)
                    ·
                      refine ⟨2546109743219244458358637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394812990958992611144849 2546109743219244458358637)
                      ·
                        rfl

theorem cell23_4958531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_4958531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958531 prefixEnd_4958531 := by exact prefixLift 4958531
  have htrace : WordTrace (prefixWord ++ tailWord_4958531) baseStart_4958531 baseEnd_4958531 := by
    simpa [prefixWord, tailWord_4958531, baseEnd_4958531] using wordTrace_append hprefix tailTrace_4958531
  have hstable : (prefixWord ++ tailWord_4958531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958531).length < 2 ^ (prefixWord ++ tailWord_4958531).sum := by decide
  have hdescent : baseEnd_4958531 < baseStart_4958531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958548 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_4958548 : Nat := 118140960795 + 4958548 * 2 ^ 59
def prefixEnd_4958548 : Nat := 4983230072969 + 3 ^ 40 * 4958548 * 2
def baseEnd_4958548 : Nat := 2546118472390370891846059

theorem tailTrace_4958548 : CollatzResearch.WordTrace tailWord_4958548 prefixEnd_4958548 2546118472390370891846059 := by
  unfold tailWord_4958548
  simp only [CollatzResearch.WordTrace]
  refine ⟨90426551620017461711066149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120568735493356615614754865 90426551620017461711066149)
  ·
    refine ⟨16954978428753274070824903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90426551620017461711066149 16954978428753274070824903)
    ·
      refine ⟨25432467643129911106237355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16954978428753274070824903 25432467643129911106237355)
      ·
        refine ⟨38148701464694866659356033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25432467643129911106237355 38148701464694866659356033)
        ·
          refine ⟨28611526098521149994517025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38148701464694866659356033 28611526098521149994517025)
          ·
            refine ⟨21458644573890862495887769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28611526098521149994517025 21458644573890862495887769)
            ·
              refine ⟨16093983430418146871915827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21458644573890862495887769 16093983430418146871915827)
              ·
                refine ⟨24140975145627220307873741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16093983430418146871915827 24140975145627220307873741)
                ·
                  refine ⟨9052865679610207615452653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24140975145627220307873741 9052865679610207615452653)
                  ·
                    refine ⟨3394824629853827855794745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9052865679610207615452653 3394824629853827855794745)
                    ·
                      refine ⟨2546118472390370891846059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394824629853827855794745 2546118472390370891846059)
                      ·
                        rfl

theorem cell23_4958548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_4958548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958548 prefixEnd_4958548 := by exact prefixLift 4958548
  have htrace : WordTrace (prefixWord ++ tailWord_4958548) baseStart_4958548 baseEnd_4958548 := by
    simpa [prefixWord, tailWord_4958548, baseEnd_4958548] using wordTrace_append hprefix tailTrace_4958548
  have hstable : (prefixWord ++ tailWord_4958548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958548).length < 2 ^ (prefixWord ++ tailWord_4958548).sum := by decide
  have hdescent : baseEnd_4958548 < baseStart_4958548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958564 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_4958564 : Nat := 118140960795 + 4958564 * 2 ^ 59
def prefixEnd_4958564 : Nat := 4983230072969 + 3 ^ 40 * 4958564 * 2
def baseEnd_4958564 : Nat := 2546126688080842829245985

theorem tailTrace_4958564 : CollatzResearch.WordTrace tailWord_4958564 prefixEnd_4958564 2546126688080842829245985 := by
  unfold tailWord_4958564
  simp only [CollatzResearch.WordTrace]
  refine ⟨90426843403988479077357373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120569124538651305436476497 90426843403988479077357373)
  ·
    refine ⟨33910066276495679654009015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90426843403988479077357373 33910066276495679654009015)
    ·
      refine ⟨50865099414743519481013523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33910066276495679654009015 50865099414743519481013523)
      ·
        refine ⟨76297649122115279221520285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50865099414743519481013523 76297649122115279221520285)
        ·
          refine ⟨28611618420793229708070107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76297649122115279221520285 28611618420793229708070107)
          ·
            refine ⟨42917427631189844562105161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28611618420793229708070107 42917427631189844562105161)
            ·
              refine ⟨32188070723392383421578871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42917427631189844562105161 32188070723392383421578871)
              ·
                refine ⟨48282106085088575132368307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32188070723392383421578871 48282106085088575132368307)
                ·
                  refine ⟨72423159127632862698552461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48282106085088575132368307 72423159127632862698552461)
                  ·
                    refine ⟨27158684672862323511957173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72423159127632862698552461 27158684672862323511957173)
                    ·
                      refine ⟨2546126688080842829245985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27158684672862323511957173 2546126688080842829245985)
                      ·
                        rfl

theorem cell23_4958564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_4958564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958564 prefixEnd_4958564 := by exact prefixLift 4958564
  have htrace : WordTrace (prefixWord ++ tailWord_4958564) baseStart_4958564 baseEnd_4958564 := by
    simpa [prefixWord, tailWord_4958564, baseEnd_4958564] using wordTrace_append hprefix tailTrace_4958564
  have hstable : (prefixWord ++ tailWord_4958564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958564).length < 2 ^ (prefixWord ++ tailWord_4958564).sum := by decide
  have hdescent : baseEnd_4958564 < baseStart_4958564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958565 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 1, 3, 2]
def baseStart_4958565 : Nat := 118140960795 + 4958565 * 2 ^ 59
def prefixEnd_4958565 : Nat := 4983230072969 + 3 ^ 40 * 4958565 * 2
def baseEnd_4958565 : Nat := 2546127201561497325333481

theorem tailTrace_4958565 : CollatzResearch.WordTrace tailWord_4958565 prefixEnd_4958565 2546127201561497325333481 := by
  unfold tailWord_4958565
  simp only [CollatzResearch.WordTrace]
  refine ⟨180853723280973335325501149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120569148853982223550334099 180853723280973335325501149)
  ·
    refine ⟨67820146230365000747062931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180853723280973335325501149 67820146230365000747062931)
    ·
      refine ⟨101730219345547501120594397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67820146230365000747062931 101730219345547501120594397)
      ·
        refine ⟨38148832254580312920222899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101730219345547501120594397 38148832254580312920222899)
        ·
          refine ⟨57223248381870469380334349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38148832254580312920222899 57223248381870469380334349)
          ·
            refine ⟨21458718143201426017625381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57223248381870469380334349 21458718143201426017625381)
            ·
              refine ⟨4023509651850267378304759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21458718143201426017625381 4023509651850267378304759)
              ·
                refine ⟨6035264477775401067457139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023509651850267378304759 6035264477775401067457139)
                ·
                  refine ⟨9052896716663101601185709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6035264477775401067457139 9052896716663101601185709)
                  ·
                    refine ⟨3394836268748663100444641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9052896716663101601185709 3394836268748663100444641)
                    ·
                      refine ⟨2546127201561497325333481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394836268748663100444641 2546127201561497325333481)
                      ·
                        rfl

theorem cell23_4958565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_4958565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958565 prefixEnd_4958565 := by exact prefixLift 4958565
  have htrace : WordTrace (prefixWord ++ tailWord_4958565) baseStart_4958565 baseEnd_4958565 := by
    simpa [prefixWord, tailWord_4958565, baseEnd_4958565] using wordTrace_append hprefix tailTrace_4958565
  have hstable : (prefixWord ++ tailWord_4958565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958565).length < 2 ^ (prefixWord ++ tailWord_4958565).sum := by decide
  have hdescent : baseEnd_4958565 < baseStart_4958565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958572 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 2, 1, 3]
def baseStart_4958572 : Nat := 118140960795 + 4958572 * 2 ^ 59
def prefixEnd_4958572 : Nat := 4983230072969 + 3 ^ 40 * 4958572 * 2
def baseEnd_4958572 : Nat := 2546130795926078797945949

theorem tailTrace_4958572 : CollatzResearch.WordTrace tailWord_4958572 prefixEnd_4958572 2546130795926078797945949 := by
  unfold tailWord_4958572
  simp only [CollatzResearch.WordTrace]
  refine ⟨90426989295973987760502985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120569319061298650347337313 90426989295973987760502985)
  ·
    refine ⟨67820241971980490820377239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90426989295973987760502985 67820241971980490820377239)
    ·
      refine ⟨101730362957970736230565859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67820241971980490820377239 101730362957970736230565859)
      ·
        refine ⟨152595544436956104345848789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101730362957970736230565859 152595544436956104345848789)
        ·
          refine ⟨3576458072741158695605831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 152595544436956104345848789 3576458072741158695605831)
          ·
            refine ⟨5364687109111738043408747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576458072741158695605831 5364687109111738043408747)
            ·
              refine ⟨8047030663667607065113121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364687109111738043408747 8047030663667607065113121)
              ·
                refine ⟨6035272997750705298834841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8047030663667607065113121 6035272997750705298834841)
                ·
                  refine ⟨4526454748313028974126131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035272997750705298834841 4526454748313028974126131)
                  ·
                    refine ⟨6789682122469543461189197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4526454748313028974126131 6789682122469543461189197)
                    ·
                      refine ⟨2546130795926078797945949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6789682122469543461189197 2546130795926078797945949)
                      ·
                        rfl

theorem cell23_4958572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_4958572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958572 prefixEnd_4958572 := by exact prefixLift 4958572
  have htrace : WordTrace (prefixWord ++ tailWord_4958572) baseStart_4958572 baseEnd_4958572 := by
    simpa [prefixWord, tailWord_4958572, baseEnd_4958572] using wordTrace_append hprefix tailTrace_4958572
  have hstable : (prefixWord ++ tailWord_4958572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958572).length < 2 ^ (prefixWord ++ tailWord_4958572).sum := by decide
  have hdescent : baseEnd_4958572 < baseStart_4958572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958595 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 1, 4, 2]
def baseStart_4958595 : Nat := 118140960795 + 4958595 * 2 ^ 59
def prefixEnd_4958595 : Nat := 4983230072969 + 3 ^ 40 * 4958595 * 2
def baseEnd_4958595 : Nat := 2546142605981132207958343

theorem tailTrace_4958595 : CollatzResearch.WordTrace tailWord_4958595 prefixEnd_4958595 2546142605981132207958343 := by
  unfold tailWord_4958595
  simp only [CollatzResearch.WordTrace]
  refine ⟨180854817470864650449093239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120569878313909766966062159 180854817470864650449093239)
  ·
    refine ⟨271282226206296975673639859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180854817470864650449093239 271282226206296975673639859)
    ·
      refine ⟨406923339309445463510459789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271282226206296975673639859 406923339309445463510459789)
      ·
        refine ⟨152596252241042048816422421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 406923339309445463510459789 152596252241042048816422421)
        ·
          refine ⟨7152949323798846038269801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152596252241042048816422421 7152949323798846038269801)
          ·
            refine ⟨5364711992849134528702351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7152949323798846038269801 5364711992849134528702351)
            ·
              refine ⟨8047067989273701793053527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364711992849134528702351 8047067989273701793053527)
              ·
                refine ⟨12070601983910552689580291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8047067989273701793053527 12070601983910552689580291)
                ·
                  refine ⟨18105902975865829034370437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12070601983910552689580291 18105902975865829034370437)
                  ·
                    refine ⟨3394856807974842943944457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18105902975865829034370437 3394856807974842943944457)
                    ·
                      refine ⟨2546142605981132207958343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394856807974842943944457 2546142605981132207958343)
                      ·
                        rfl

theorem cell23_4958595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_4958595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958595 prefixEnd_4958595 := by exact prefixLift 4958595
  have htrace : WordTrace (prefixWord ++ tailWord_4958595) baseStart_4958595 baseEnd_4958595 := by
    simpa [prefixWord, tailWord_4958595, baseEnd_4958595] using wordTrace_append hprefix tailTrace_4958595
  have hstable : (prefixWord ++ tailWord_4958595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958595).length < 2 ^ (prefixWord ++ tailWord_4958595).sum := by decide
  have hdescent : baseEnd_4958595 < baseStart_4958595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958618 : List Nat := [3, 1, 1, 4, 1, 2, 3, 3, 5]
def baseStart_4958618 : Nat := 118140960795 + 4958618 * 2 ^ 59
def prefixEnd_4958618 : Nat := 4983230072969 + 3 ^ 40 * 4958618 * 2
def baseEnd_4958618 : Nat := 282906046226242846441193

theorem tailTrace_4958618 : CollatzResearch.WordTrace tailWord_4958618 prefixEnd_4958618 282906046226242846441193 := by
  unfold tailWord_4958618
  simp only [CollatzResearch.WordTrace]
  refine ⟨45213914087445331344295127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120570437566520883584787005 45213914087445331344295127)
  ·
    refine ⟨67820871131167997016442691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45213914087445331344295127 67820871131167997016442691)
    ·
      refine ⟨101731306696751995524664037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67820871131167997016442691 101731306696751995524664037)
      ·
        refine ⟨19074620005640999160874507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101731306696751995524664037 19074620005640999160874507)
        ·
          refine ⟨28611930008461498741311761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19074620005640999160874507 28611930008461498741311761)
          ·
            refine ⟨21458947506346124055983821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28611930008461498741311761 21458947506346124055983821)
            ·
              refine ⟨8047105314879796520993933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21458947506346124055983821 8047105314879796520993933)
              ·
                refine ⟨3017664493079923695372725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8047105314879796520993933 3017664493079923695372725)
                ·
                  refine ⟨282906046226242846441193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3017664493079923695372725 282906046226242846441193)
                  ·
                    rfl

theorem cell23_4958618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_4958618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958618 prefixEnd_4958618 := by exact prefixLift 4958618
  have htrace : WordTrace (prefixWord ++ tailWord_4958618) baseStart_4958618 baseEnd_4958618 := by
    simpa [prefixWord, tailWord_4958618, baseEnd_4958618] using wordTrace_append hprefix tailTrace_4958618
  have hstable : (prefixWord ++ tailWord_4958618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958618).length < 2 ^ (prefixWord ++ tailWord_4958618).sum := by decide
  have hdescent : baseEnd_4958618 < baseStart_4958618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958631 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 4, 5]
def baseStart_4958631 : Nat := 118140960795 + 4958631 * 2 ^ 59
def prefixEnd_4958631 : Nat := 4983230072969 + 3 ^ 40 * 4958631 * 2
def baseEnd_4958631 : Nat := 848720363761564689036059

theorem tailTrace_4958631 : CollatzResearch.WordTrace tailWord_4958631 prefixEnd_4958631 848720363761564689036059 := by
  unfold tailWord_4958631
  simp only [CollatzResearch.WordTrace]
  refine ⟨180856130498734228597403747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120570753665822819064935831 180856130498734228597403747)
  ·
    refine ⟨271284195748101342896105621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180856130498734228597403747 271284195748101342896105621)
    ·
      refine ⟨12716446675692250448254951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 271284195748101342896105621 12716446675692250448254951)
      ·
        refine ⟨19074670013538375672382427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12716446675692250448254951 19074670013538375672382427)
        ·
          refine ⟨28612005020307563508573641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19074670013538375672382427 28612005020307563508573641)
          ·
            refine ⟨21459003765230672631430231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28612005020307563508573641 21459003765230672631430231)
            ·
              refine ⟨32188505647846008947145347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21459003765230672631430231 32188505647846008947145347)
              ·
                refine ⟨48282758471769013420718021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32188505647846008947145347 48282758471769013420718021)
                ·
                  refine ⟨9053017213456690016384629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48282758471769013420718021 9053017213456690016384629)
                  ·
                    refine ⟨848720363761564689036059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9053017213456690016384629 848720363761564689036059)
                    ·
                      rfl

theorem cell23_4958631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_4958631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958631 prefixEnd_4958631 := by exact prefixLift 4958631
  have htrace : WordTrace (prefixWord ++ tailWord_4958631) baseStart_4958631 baseEnd_4958631 := by
    simpa [prefixWord, tailWord_4958631, baseEnd_4958631] using wordTrace_append hprefix tailTrace_4958631
  have hstable : (prefixWord ++ tailWord_4958631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958631).length < 2 ^ (prefixWord ++ tailWord_4958631).sum := by decide
  have hdescent : baseEnd_4958631 < baseStart_4958631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958641 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_4958641 : Nat := 118140960795 + 4958641 * 2 ^ 59
def prefixEnd_4958641 : Nat := 4983230072969 + 3 ^ 40 * 4958641 * 2
def baseEnd_4958641 : Nat := 2546166226091239027983131

theorem tailTrace_4958641 : CollatzResearch.WordTrace tailWord_4958641 prefixEnd_4958641 2546166226091239027983131 := by
  unfold tailWord_4958641
  simp only [CollatzResearch.WordTrace]
  refine ⟨180856495228698000305267777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120570996819132000203511851 180856495228698000305267777)
  ·
    refine ⟨135642371421523500228950833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180856495228698000305267777 135642371421523500228950833)
    ·
      refine ⟨101731778566142625171713125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135642371421523500228950833 101731778566142625171713125)
      ·
        refine ⟨19074708481151742219696211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101731778566142625171713125 19074708481151742219696211)
        ·
          refine ⟨28612062721727613329544317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19074708481151742219696211 28612062721727613329544317)
          ·
            refine ⟨10729523520647854998579119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28612062721727613329544317 10729523520647854998579119)
            ·
              refine ⟨16094285280971782497868679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10729523520647854998579119 16094285280971782497868679)
              ·
                refine ⟨24141427921457673746803019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16094285280971782497868679 24141427921457673746803019)
                ·
                  refine ⟨36212141882186510620204529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24141427921457673746803019 36212141882186510620204529)
                  ·
                    refine ⟨27159106411639882965153397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36212141882186510620204529 27159106411639882965153397)
                    ·
                      refine ⟨2546166226091239027983131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27159106411639882965153397 2546166226091239027983131)
                      ·
                        rfl

theorem cell23_4958641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_4958641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958641 prefixEnd_4958641 := by exact prefixLift 4958641
  have htrace : WordTrace (prefixWord ++ tailWord_4958641) baseStart_4958641 baseEnd_4958641 := by
    simpa [prefixWord, tailWord_4958641, baseEnd_4958641] using wordTrace_append hprefix tailTrace_4958641
  have hstable : (prefixWord ++ tailWord_4958641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958641).length < 2 ^ (prefixWord ++ tailWord_4958641).sum := by decide
  have hdescent : baseEnd_4958641 < baseStart_4958641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958695 : List Nat := [1, 1, 5, 2, 1, 1, 3, 4, 1, 4]
def baseStart_4958695 : Nat := 118140960795 + 4958695 * 2 ^ 59
def prefixEnd_4958695 : Nat := 4983230072969 + 3 ^ 40 * 4958695 * 2
def baseEnd_4958695 : Nat := 848731318015527272235961

theorem tailTrace_4958695 : CollatzResearch.WordTrace tailWord_4958695 prefixEnd_4958695 848731318015527272235961 := by
  unfold tailWord_4958695
  simp only [CollatzResearch.WordTrace]
  refine ⟨180858464770502367527733539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120572309847001578351822359 180858464770502367527733539)
  ·
    refine ⟨271287697155753551291600309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180858464770502367527733539 271287697155753551291600309)
    ·
      refine ⟨25433221608351895433587529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271287697155753551291600309 25433221608351895433587529)
      ·
        refine ⟨19074916206263921575190647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25433221608351895433587529 19074916206263921575190647)
        ·
          refine ⟨28612374309395882362785971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19074916206263921575190647 28612374309395882362785971)
          ·
            refine ⟨42918561464093823544178957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28612374309395882362785971 42918561464093823544178957)
            ·
              refine ⟨16094460549035183829067109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42918561464093823544178957 16094460549035183829067109)
              ·
                refine ⟨3017711352944096967950083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16094460549035183829067109 3017711352944096967950083)
                ·
                  refine ⟨4526567029416145451925125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017711352944096967950083 4526567029416145451925125)
                  ·
                    refine ⟨848731318015527272235961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526567029416145451925125 848731318015527272235961)
                    ·
                      rfl

theorem cell23_4958695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_4958695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958695 prefixEnd_4958695 := by exact prefixLift 4958695
  have htrace : WordTrace (prefixWord ++ tailWord_4958695) baseStart_4958695 baseEnd_4958695 := by
    simpa [prefixWord, tailWord_4958695, baseEnd_4958695] using wordTrace_append hprefix tailTrace_4958695
  have hstable : (prefixWord ++ tailWord_4958695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958695).length < 2 ^ (prefixWord ++ tailWord_4958695).sum := by decide
  have hdescent : baseEnd_4958695 < baseStart_4958695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 9, 1, 1, 3]
def baseStart_4958735 : Nat := 118140960795 + 4958735 * 2 ^ 59
def prefixEnd_4958735 : Nat := 4983230072969 + 3 ^ 40 * 4958735 * 2
def baseEnd_4958735 : Nat := 2546214493272761660207699

theorem tailTrace_4958735 : CollatzResearch.WordTrace tailWord_4958735 prefixEnd_4958735 2546214493272761660207699 := by
  unfold tailWord_4958735
  simp only [CollatzResearch.WordTrace]
  refine ⟨180859923690357454359189659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120573282460238302906126439 180859923690357454359189659)
  ·
    refine ⟨271289885535536181538784489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180859923690357454359189659 271289885535536181538784489)
    ·
      refine ⟨203467414151652136154088367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271289885535536181538784489 203467414151652136154088367)
      ·
        refine ⟨305201121227478204231132551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203467414151652136154088367 305201121227478204231132551)
        ·
          refine ⟨457801681841217306346698827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305201121227478204231132551 457801681841217306346698827)
          ·
            refine ⟨686702522761825959520048241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457801681841217306346698827 686702522761825959520048241)
            ·
              refine ⟨515026892071369469640036181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686702522761825959520048241 515026892071369469640036181)
              ·
                refine ⟨3017735695730680486172087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 515026892071369469640036181 3017735695730680486172087)
                ·
                  refine ⟨4526603543596020729258131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017735695730680486172087 4526603543596020729258131)
                  ·
                    refine ⟨6789905315394031093887197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4526603543596020729258131 6789905315394031093887197)
                    ·
                      refine ⟨2546214493272761660207699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6789905315394031093887197 2546214493272761660207699)
                      ·
                        rfl

theorem cell23_4958735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 1, 3].length) (baseStart_4958735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958735 prefixEnd_4958735 := by exact prefixLift 4958735
  have htrace : WordTrace (prefixWord ++ tailWord_4958735) baseStart_4958735 baseEnd_4958735 := by
    simpa [prefixWord, tailWord_4958735, baseEnd_4958735] using wordTrace_append hprefix tailTrace_4958735
  have hstable : (prefixWord ++ tailWord_4958735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958735).length < 2 ^ (prefixWord ++ tailWord_4958735).sum := by decide
  have hdescent : baseEnd_4958735 < baseStart_4958735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958752 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4958752 : Nat := 118140960795 + 4958752 * 2 ^ 59
def prefixEnd_4958752 : Nat := 4983230072969 + 3 ^ 40 * 4958752 * 2
def baseEnd_4958752 : Nat := 2546223222443888093695121

theorem tailTrace_4958752 : CollatzResearch.WordTrace tailWord_4958752 prefixEnd_4958752 2546223222443888093695121 := by
  unfold tailWord_4958752
  simp only [CollatzResearch.WordTrace]
  refine ⟨90430271865647933131279255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120573695820863910841705673 90430271865647933131279255)
  ·
    refine ⟨135645407798471899696918883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90430271865647933131279255 135645407798471899696918883)
    ·
      refine ⟨203468111697707849545378325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135645407798471899696918883 203468111697707849545378325)
      ·
        refine ⟨9537567735830055447439609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 203468111697707849545378325 9537567735830055447439609)
        ·
          refine ⟨7153175801872541585579707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9537567735830055447439609 7153175801872541585579707)
          ·
            refine ⟨10729763702808812378369561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7153175801872541585579707 10729763702808812378369561)
            ·
              refine ⟨8047322777106609283777171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10729763702808812378369561 8047322777106609283777171)
              ·
                refine ⟨12070984165659913925665757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8047322777106609283777171 12070984165659913925665757)
                ·
                  refine ⟨4526619062122467722124659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12070984165659913925665757 4526619062122467722124659)
                  ·
                    refine ⟨6789928593183701583186989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4526619062122467722124659 6789928593183701583186989)
                    ·
                      refine ⟨2546223222443888093695121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6789928593183701583186989 2546223222443888093695121)
                      ·
                        rfl

theorem cell23_4958752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4958752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958752 prefixEnd_4958752 := by exact prefixLift 4958752
  have htrace : WordTrace (prefixWord ++ tailWord_4958752) baseStart_4958752 baseEnd_4958752 := by
    simpa [prefixWord, tailWord_4958752, baseEnd_4958752] using wordTrace_append hprefix tailTrace_4958752
  have hstable : (prefixWord ++ tailWord_4958752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958752).length < 2 ^ (prefixWord ++ tailWord_4958752).sum := by decide
  have hdescent : baseEnd_4958752 < baseStart_4958752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958768 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 2, 4]
def baseStart_4958768 : Nat := 118140960795 + 4958768 * 2 ^ 59
def prefixEnd_4958768 : Nat := 4983230072969 + 3 ^ 40 * 4958768 * 2
def baseEnd_4958768 : Nat := 848743812711453343698349

theorem tailTrace_4958768 : CollatzResearch.WordTrace tailWord_4958768 prefixEnd_4958768 848743812711453343698349 := by
  unfold tailWord_4958768
  simp only [CollatzResearch.WordTrace]
  refine ⟨90430563649618950497570479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120574084866158600663427305 90430563649618950497570479)
  ·
    refine ⟨135645845474428425746355719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90430563649618950497570479 135645845474428425746355719)
    ·
      refine ⟨203468768211642638619533579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135645845474428425746355719 203468768211642638619533579)
      ·
        refine ⟨305203152317463957929300369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203468768211642638619533579 305203152317463957929300369)
        ·
          refine ⟨228902364238097968446975277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305203152317463957929300369 228902364238097968446975277)
          ·
            refine ⟨85838386589286738167615729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228902364238097968446975277 85838386589286738167615729)
            ·
              refine ⟨64378789941965053625711797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85838386589286738167615729 64378789941965053625711797)
              ·
                refine ⟨6035511557059223777410481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64378789941965053625711797 6035511557059223777410481)
                ·
                  refine ⟨4526633667794417833057861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035511557059223777410481 4526633667794417833057861)
                  ·
                    refine ⟨848743812711453343698349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526633667794417833057861 848743812711453343698349)
                    ·
                      rfl

theorem cell23_4958768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_4958768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958768 prefixEnd_4958768 := by exact prefixLift 4958768
  have htrace : WordTrace (prefixWord ++ tailWord_4958768) baseStart_4958768 baseEnd_4958768 := by
    simpa [prefixWord, tailWord_4958768, baseEnd_4958768] using wordTrace_append hprefix tailTrace_4958768
  have hstable : (prefixWord ++ tailWord_4958768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958768).length < 2 ^ (prefixWord ++ tailWord_4958768).sum := by decide
  have hdescent : baseEnd_4958768 < baseStart_4958768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958771 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6]
def baseStart_4958771 : Nat := 118140960795 + 4958771 * 2 ^ 59
def prefixEnd_4958771 : Nat := 4983230072969 + 3 ^ 40 * 4958771 * 2
def baseEnd_4958771 : Nat := 2546232978576323519357533

theorem tailTrace_4958771 : CollatzResearch.WordTrace tailWord_4958771 prefixEnd_4958771 2546232978576323519357533 := by
  unfold tailWord_4958771
  simp only [CollatzResearch.WordTrace]
  refine ⟨180861236718227032507500167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120574157812151355005000111 180861236718227032507500167)
  ·
    refine ⟨271291855077340548761250251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180861236718227032507500167 271291855077340548761250251)
    ·
      refine ⟨406937782616010823141875377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271291855077340548761250251 406937782616010823141875377)
      ·
        refine ⟨305203336962008117356406533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406937782616010823141875377 305203336962008117356406533)
        ·
          refine ⟨57225625680376522004326225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305203336962008117356406533 57225625680376522004326225)
          ·
            refine ⟨42919219260282391503244669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57225625680376522004326225 42919219260282391503244669)
            ·
              refine ⟨16094707222605896813716751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42919219260282391503244669 16094707222605896813716751)
              ·
                refine ⟨24142060833908845220575127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16094707222605896813716751 24142060833908845220575127)
                ·
                  refine ⟨36213091250863267830862691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24142060833908845220575127 36213091250863267830862691)
                  ·
                    refine ⟨54319636876294901746294037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36213091250863267830862691 54319636876294901746294037)
                    ·
                      refine ⟨2546232978576323519357533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54319636876294901746294037 2546232978576323519357533)
                      ·
                        rfl

theorem cell23_4958771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_4958771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958771 prefixEnd_4958771 := by exact prefixLift 4958771
  have htrace : WordTrace (prefixWord ++ tailWord_4958771) baseStart_4958771 baseEnd_4958771 := by
    simpa [prefixWord, tailWord_4958771, baseEnd_4958771] using wordTrace_append hprefix tailTrace_4958771
  have hstable : (prefixWord ++ tailWord_4958771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958771).length < 2 ^ (prefixWord ++ tailWord_4958771).sum := by decide
  have hdescent : baseEnd_4958771 < baseStart_4958771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958775 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 3, 2, 2]
def baseStart_4958775 : Nat := 118140960795 + 4958775 * 2 ^ 59
def prefixEnd_4958775 : Nat := 4983230072969 + 3 ^ 40 * 4958775 * 2
def baseEnd_4958775 : Nat := 2546235032498941503707515

theorem tailTrace_4958775 : CollatzResearch.WordTrace tailWord_4958775 prefixEnd_4958775 2546235032498941503707515 := by
  unfold tailWord_4958775
  simp only [CollatzResearch.WordTrace]
  refine ⟨180861382610212541190645779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120574255073475027460430519 180861382610212541190645779)
  ·
    refine ⟨271292073915318811785968669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180861382610212541190645779 271292073915318811785968669)
    ·
      refine ⟨101734527718244554419738251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271292073915318811785968669 101734527718244554419738251)
      ·
        refine ⟨152601791577366831629607377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101734527718244554419738251 152601791577366831629607377)
        ·
          refine ⟨114451343683025123722205533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152601791577366831629607377 114451343683025123722205533)
          ·
            refine ⟨42919253881134421395827075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114451343683025123722205533 42919253881134421395827075)
            ·
              refine ⟨64378880821701632093740613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42919253881134421395827075 64378880821701632093740613)
              ·
                refine ⟨12071040154069056017576365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64378880821701632093740613 12071040154069056017576365)
                ·
                  refine ⟨4526640057775896006591137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12071040154069056017576365 4526640057775896006591137)
                  ·
                    refine ⟨3394980043331922004943353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526640057775896006591137 3394980043331922004943353)
                    ·
                      refine ⟨2546235032498941503707515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3394980043331922004943353 2546235032498941503707515)
                      ·
                        rfl

theorem cell23_4958775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_4958775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958775 prefixEnd_4958775 := by exact prefixLift 4958775
  have htrace : WordTrace (prefixWord ++ tailWord_4958775) baseStart_4958775 baseEnd_4958775 := by
    simpa [prefixWord, tailWord_4958775, baseEnd_4958775] using wordTrace_append hprefix tailTrace_4958775
  have hstable : (prefixWord ++ tailWord_4958775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958775).length < 2 ^ (prefixWord ++ tailWord_4958775).sum := by decide
  have hdescent : baseEnd_4958775 < baseStart_4958775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958835 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 1, 3, 2]
def baseStart_4958835 : Nat := 118140960795 + 4958835 * 2 ^ 59
def prefixEnd_4958835 : Nat := 4983230072969 + 3 ^ 40 * 4958835 * 2
def baseEnd_4958835 : Nat := 2546265841338211268957239

theorem tailTrace_4958835 : CollatzResearch.WordTrace tailWord_4958835 prefixEnd_4958835 2546265841338211268957239 := by
  unfold tailWord_4958835
  simp only [CollatzResearch.WordTrace]
  refine ⟨180863570989995171437829959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120575713993330114291886639 180863570989995171437829959)
  ·
    refine ⟨271295356484992757156744939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180863570989995171437829959 271295356484992757156744939)
    ·
      refine ⟨406943034727489135735117409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271295356484992757156744939 406943034727489135735117409)
      ·
        refine ⟨305207276045616851801338057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406943034727489135735117409 305207276045616851801338057)
        ·
          refine ⟨228905457034212638851003543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305207276045616851801338057 228905457034212638851003543)
          ·
            refine ⟨343358185551318958276505315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228905457034212638851003543 343358185551318958276505315)
            ·
              refine ⟨515037278326978437414757973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343358185551318958276505315 515037278326978437414757973)
              ·
                refine ⟨6035593105394278563454195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 515037278326978437414757973 6035593105394278563454195)
                ·
                  refine ⟨9053389658091417845181293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6035593105394278563454195 9053389658091417845181293)
                  ·
                    refine ⟨3395021121784281691942985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9053389658091417845181293 3395021121784281691942985)
                    ·
                      refine ⟨2546265841338211268957239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395021121784281691942985 2546265841338211268957239)
                      ·
                        rfl

theorem cell23_4958835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 3, 2].length) (baseStart_4958835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958835 prefixEnd_4958835 := by exact prefixLift 4958835
  have htrace : WordTrace (prefixWord ++ tailWord_4958835) baseStart_4958835 baseEnd_4958835 := by
    simpa [prefixWord, tailWord_4958835, baseEnd_4958835] using wordTrace_append hprefix tailTrace_4958835
  have hstable : (prefixWord ++ tailWord_4958835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958835).length < 2 ^ (prefixWord ++ tailWord_4958835).sum := by decide
  have hdescent : baseEnd_4958835 < baseStart_4958835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958865 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 8, 2, 2]
def baseStart_4958865 : Nat := 118140960795 + 4958865 * 2 ^ 59
def prefixEnd_4958865 : Nat := 4983230072969 + 3 ^ 40 * 4958865 * 2
def baseEnd_4958865 : Nat := 2546281245757846151582101

theorem tailTrace_4958865 : CollatzResearch.WordTrace tailWord_4958865 prefixEnd_4958865 2546281245757846151582101 := by
  unfold tailWord_4958865
  simp only [CollatzResearch.WordTrace]
  refine ⟨180864665179886486561422049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120576443453257657707614699 180864665179886486561422049)
  ·
    refine ⟨135648498884914864921066537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180864665179886486561422049 135648498884914864921066537)
    ·
      refine ⟨101736374163686148690799903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135648498884914864921066537 101736374163686148690799903)
      ·
        refine ⟨152604561245529223036199855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101736374163686148690799903 152604561245529223036199855)
        ·
          refine ⟨228906841868293834554299783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152604561245529223036199855 228906841868293834554299783)
          ·
            refine ⟨343360262802440751831449675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228906841868293834554299783 343360262802440751831449675)
            ·
              refine ⟨515040394203661127747174513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343360262802440751831449675 515040394203661127747174513)
              ·
                refine ⟨386280295652745845810380885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515040394203661127747174513 386280295652745845810380885)
                ·
                  refine ⟨4526722214680615380590401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 386280295652745845810380885 4526722214680615380590401)
                  ·
                    refine ⟨3395041661010461535442801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526722214680615380590401 3395041661010461535442801)
                    ·
                      refine ⟨2546281245757846151582101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395041661010461535442801 2546281245757846151582101)
                      ·
                        rfl

theorem cell23_4958865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_4958865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958865 prefixEnd_4958865 := by exact prefixLift 4958865
  have htrace : WordTrace (prefixWord ++ tailWord_4958865) baseStart_4958865 baseEnd_4958865 := by
    simpa [prefixWord, tailWord_4958865, baseEnd_4958865] using wordTrace_append hprefix tailTrace_4958865
  have hstable : (prefixWord ++ tailWord_4958865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958865).length < 2 ^ (prefixWord ++ tailWord_4958865).sum := by decide
  have hdescent : baseEnd_4958865 < baseStart_4958865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958898 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_4958898 : Nat := 118140960795 + 4958898 * 2 ^ 59
def prefixEnd_4958898 : Nat := 4983230072969 + 3 ^ 40 * 4958898 * 2
def baseEnd_4958898 : Nat := 2546298190619444522469449

theorem tailTrace_4958898 : CollatzResearch.WordTrace tailWord_4958898 prefixEnd_4958898 2546298190619444522469449 := by
  unfold tailWord_4958898
  simp only [CollatzResearch.WordTrace]
  refine ⟨45216467197191733299343337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120577245859177955464915565 45216467197191733299343337)
  ·
    refine ⟨33912350397893799974507503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45216467197191733299343337 33912350397893799974507503)
    ·
      refine ⟨50868525596840699961761255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33912350397893799974507503 50868525596840699961761255)
      ·
        refine ⟨76302788395261049942641883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50868525596840699961761255 76302788395261049942641883)
        ·
          refine ⟨114454182592891574913962825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76302788395261049942641883 114454182592891574913962825)
          ·
            refine ⟨85840636944668681185472119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114454182592891574913962825 85840636944668681185472119)
            ·
              refine ⟨128760955417003021778208179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85840636944668681185472119 128760955417003021778208179)
              ·
                refine ⟨193141433125504532667312269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128760955417003021778208179 193141433125504532667312269)
                ·
                  refine ⟨72428037422064199750242101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193141433125504532667312269 72428037422064199750242101)
                  ·
                    refine ⟨6790128508318518726585197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72428037422064199750242101 6790128508318518726585197)
                    ·
                      refine ⟨2546298190619444522469449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6790128508318518726585197 2546298190619444522469449)
                      ·
                        rfl

theorem cell23_4958898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_4958898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958898 prefixEnd_4958898 := by exact prefixLift 4958898
  have htrace : WordTrace (prefixWord ++ tailWord_4958898) baseStart_4958898 baseEnd_4958898 := by
    simpa [prefixWord, tailWord_4958898, baseEnd_4958898] using wordTrace_append hprefix tailTrace_4958898
  have hstable : (prefixWord ++ tailWord_4958898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958898).length < 2 ^ (prefixWord ++ tailWord_4958898).sum := by decide
  have hdescent : baseEnd_4958898 < baseStart_4958898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958916 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_4958916 : Nat := 118140960795 + 4958916 * 2 ^ 59
def prefixEnd_4958916 : Nat := 4983230072969 + 3 ^ 40 * 4958916 * 2
def baseEnd_4958916 : Nat := 2546307433271225452044367

theorem tailTrace_4958916 : CollatzResearch.WordTrace tailWord_4958916 prefixEnd_4958916 2546307433271225452044367 := by
  unfold tailWord_4958916
  simp only [CollatzResearch.WordTrace]
  refine ⟨90433262651350861135764301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120577683535134481514352401 90433262651350861135764301)
  ·
    refine ⟨33912473494256572925911613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90433262651350861135764301 33912473494256572925911613)
    ·
      refine ⟨12717177560346214847216855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33912473494256572925911613 12717177560346214847216855)
      ·
        refine ⟨19075766340519322270825283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12717177560346214847216855 19075766340519322270825283)
        ·
          refine ⟨28613649510778983406237925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19075766340519322270825283 28613649510778983406237925)
          ·
            refine ⟨5365059283271059388669611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28613649510778983406237925 5365059283271059388669611)
            ·
              refine ⟨8047588924906589083004417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365059283271059388669611 8047588924906589083004417)
              ·
                refine ⟨6035691693679941812253313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8047588924906589083004417 6035691693679941812253313)
                ·
                  refine ⟨4526768770259956359189985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035691693679941812253313 4526768770259956359189985)
                  ·
                    refine ⟨3395076577694967269392489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526768770259956359189985 3395076577694967269392489)
                    ·
                      refine ⟨2546307433271225452044367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395076577694967269392489 2546307433271225452044367)
                      ·
                        rfl

theorem cell23_4958916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_4958916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958916 prefixEnd_4958916 := by exact prefixLift 4958916
  have htrace : WordTrace (prefixWord ++ tailWord_4958916) baseStart_4958916 baseEnd_4958916 := by
    simpa [prefixWord, tailWord_4958916, baseEnd_4958916] using wordTrace_append hprefix tailTrace_4958916
  have hstable : (prefixWord ++ tailWord_4958916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958916).length < 2 ^ (prefixWord ++ tailWord_4958916).sum := by decide
  have hdescent : baseEnd_4958916 < baseStart_4958916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958933 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4958933 : Nat := 118140960795 + 4958933 * 2 ^ 59
def prefixEnd_4958933 : Nat := 4983230072969 + 3 ^ 40 * 4958933 * 2
def baseEnd_4958933 : Nat := 2546316162442351885531789

theorem tailTrace_4958933 : CollatzResearch.WordTrace tailWord_4958933 prefixEnd_4958933 2546316162442351885531789 := by
  unfold tailWord_4958933
  simp only [CollatzResearch.WordTrace]
  refine ⟨180867145343640134174897453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120578096895760089449931635 180867145343640134174897453)
  ·
    refine ⟨67825179503865050315586545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180867145343640134174897453 67825179503865050315586545)
    ·
      refine ⟨50868884627898787736689909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67825179503865050315586545 50868884627898787736689909)
      ·
        refine ⟨4768957933865511350314679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50868884627898787736689909 4768957933865511350314679)
        ·
          refine ⟨7153436900798267025472019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4768957933865511350314679 7153436900798267025472019)
          ·
            refine ⟨10730155351197400538208029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7153436900798267025472019 10730155351197400538208029)
            ·
              refine ⟨4023808256699025201828011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10730155351197400538208029 4023808256699025201828011)
              ·
                refine ⟨6035712385048537802742017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023808256699025201828011 6035712385048537802742017)
                ·
                  refine ⟨4526784288786403352056513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035712385048537802742017 4526784288786403352056513)
                  ·
                    refine ⟨3395088216589802514042385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526784288786403352056513 3395088216589802514042385)
                    ·
                      refine ⟨2546316162442351885531789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395088216589802514042385 2546316162442351885531789)
                      ·
                        rfl

theorem cell23_4958933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4958933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958933 prefixEnd_4958933 := by exact prefixLift 4958933
  have htrace : WordTrace (prefixWord ++ tailWord_4958933) baseStart_4958933 baseEnd_4958933 := by
    simpa [prefixWord, tailWord_4958933, baseEnd_4958933] using wordTrace_append hprefix tailTrace_4958933
  have hstable : (prefixWord ++ tailWord_4958933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958933).length < 2 ^ (prefixWord ++ tailWord_4958933).sum := by decide
  have hdescent : baseEnd_4958933 < baseStart_4958933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4958938 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_4958938 : Nat := 118140960795 + 4958938 * 2 ^ 59
def prefixEnd_4958938 : Nat := 4983230072969 + 3 ^ 40 * 4958938 * 2
def baseEnd_4958938 : Nat := 2546318729845624365969265

theorem tailTrace_4958938 : CollatzResearch.WordTrace tailWord_4958938 prefixEnd_4958938 2546318729845624365969265 := by
  unfold tailWord_4958938
  simp only [CollatzResearch.WordTrace]
  refine ⟨45216831927155505007207367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120578218472414680019219645 45216831927155505007207367)
  ·
    refine ⟨67825247890733257510811051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45216831927155505007207367 67825247890733257510811051)
    ·
      refine ⟨101737871836099886266216577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67825247890733257510811051 101737871836099886266216577)
      ·
        refine ⟨76303403877074914699662433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101737871836099886266216577 76303403877074914699662433)
        ·
          refine ⟨57227552907806186024746825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76303403877074914699662433 57227552907806186024746825)
          ·
            refine ⟨42920664680854639518560119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57227552907806186024746825 42920664680854639518560119)
            ·
              refine ⟨64380997021281959277840179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42920664680854639518560119 64380997021281959277840179)
              ·
                refine ⟨96571495531922938916760269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64380997021281959277840179 96571495531922938916760269)
                ·
                  refine ⟨36214310824471102093785101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96571495531922938916760269 36214310824471102093785101)
                  ·
                    refine ⟨13580366559176663285169413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36214310824471102093785101 13580366559176663285169413)
                    ·
                      refine ⟨2546318729845624365969265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13580366559176663285169413 2546318729845624365969265)
                      ·
                        rfl

theorem cell23_4958938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_4958938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4958938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4958938 prefixEnd_4958938 := by exact prefixLift 4958938
  have htrace : WordTrace (prefixWord ++ tailWord_4958938) baseStart_4958938 baseEnd_4958938 := by
    simpa [prefixWord, tailWord_4958938, baseEnd_4958938] using wordTrace_append hprefix tailTrace_4958938
  have hstable : (prefixWord ++ tailWord_4958938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4958938).length < 2 ^ (prefixWord ++ tailWord_4958938).sum := by decide
  have hdescent : baseEnd_4958938 < baseStart_4958938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4958938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959032 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 2, 3, 2]
def baseStart_4959032 : Nat := 118140960795 + 4959032 * 2 ^ 59
def prefixEnd_4959032 : Nat := 4983230072969 + 3 ^ 40 * 4959032 * 2
def baseEnd_4959032 : Nat := 2546366997027146998193833

theorem tailTrace_4959032 : CollatzResearch.WordTrace tailWord_4959032 prefixEnd_4959032 2546366997027146998193833 := by
  unfold tailWord_4959032
  simp only [CollatzResearch.WordTrace]
  refine ⟨90435378085140737041375675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120580504113520982721834233 90435378085140737041375675)
  ·
    refine ⟨135653067127711105562063513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90435378085140737041375675 135653067127711105562063513)
    ·
      refine ⟨101739800345783329171547635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135653067127711105562063513 101739800345783329171547635)
      ·
        refine ⟨152609700518674993757321453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101739800345783329171547635 152609700518674993757321453)
        ·
          refine ⟨57228637694503122658995545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152609700518674993757321453 57228637694503122658995545)
          ·
            refine ⟨42921478270877341994246659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57228637694503122658995545 42921478270877341994246659)
            ·
              refine ⟨64382217406316012991369989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42921478270877341994246659 64382217406316012991369989)
              ·
                refine ⟨12071665763684252435881873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64382217406316012991369989 12071665763684252435881873)
                ·
                  refine ⟨9053749322763189326911405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12071665763684252435881873 9053749322763189326911405)
                  ·
                    refine ⟨3395155996036195997591777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9053749322763189326911405 3395155996036195997591777)
                    ·
                      refine ⟨2546366997027146998193833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395155996036195997591777 2546366997027146998193833)
                      ·
                        rfl

theorem cell23_4959032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_4959032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959032 prefixEnd_4959032 := by exact prefixLift 4959032
  have htrace : WordTrace (prefixWord ++ tailWord_4959032) baseStart_4959032 baseEnd_4959032 := by
    simpa [prefixWord, tailWord_4959032, baseEnd_4959032] using wordTrace_append hprefix tailTrace_4959032
  have hstable : (prefixWord ++ tailWord_4959032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959032).length < 2 ^ (prefixWord ++ tailWord_4959032).sum := by decide
  have hdescent : baseEnd_4959032 < baseStart_4959032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959079 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_4959079 : Nat := 118140960795 + 4959079 * 2 ^ 59
def prefixEnd_4959079 : Nat := 4983230072969 + 3 ^ 40 * 4959079 * 2
def baseEnd_4959079 : Nat := 2546391130617908314306117

theorem tailTrace_4959079 : CollatzResearch.WordTrace tailWord_4959079 prefixEnd_4959079 2546391130617908314306117 := by
  unfold tailWord_4959079
  simp only [CollatzResearch.WordTrace]
  refine ⟨180872470401111201109712291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120581646934074134073141527 180872470401111201109712291)
  ·
    refine ⟨271308705601666801664568437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180872470401111201109712291 271308705601666801664568437)
    ·
      refine ⟨25435191150156262656053291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271308705601666801664568437 25435191150156262656053291)
      ·
        refine ⟨38152786725234393984079937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25435191150156262656053291 38152786725234393984079937)
        ·
          refine ⟨28614590043925795488059953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38152786725234393984079937 28614590043925795488059953)
          ·
            refine ⟨21460942532944346616044965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28614590043925795488059953 21460942532944346616044965)
            ·
              refine ⟨4023926724927064990508431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21460942532944346616044965 4023926724927064990508431)
              ·
                refine ⟨6035890087390597485762647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023926724927064990508431 6035890087390597485762647)
                ·
                  refine ⟨9053835131085896228643971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6035890087390597485762647 9053835131085896228643971)
                  ·
                    refine ⟨13580752696628844342965957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9053835131085896228643971 13580752696628844342965957)
                    ·
                      refine ⟨2546391130617908314306117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13580752696628844342965957 2546391130617908314306117)
                      ·
                        rfl

theorem cell23_4959079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_4959079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959079 prefixEnd_4959079 := by exact prefixLift 4959079
  have htrace : WordTrace (prefixWord ++ tailWord_4959079) baseStart_4959079 baseEnd_4959079 := by
    simpa [prefixWord, tailWord_4959079, baseEnd_4959079] using wordTrace_append hprefix tailTrace_4959079
  have hstable : (prefixWord ++ tailWord_4959079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959079).length < 2 ^ (prefixWord ++ tailWord_4959079).sum := by decide
  have hdescent : baseEnd_4959079 < baseStart_4959079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959089 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 2, 4]
def baseStart_4959089 : Nat := 118140960795 + 4959089 * 2 ^ 59
def prefixEnd_4959089 : Nat := 4983230072969 + 3 ^ 40 * 4959089 * 2
def baseEnd_4959089 : Nat := 848798755141484425060357

theorem tailTrace_4959089 : CollatzResearch.WordTrace tailWord_4959089 prefixEnd_4959089 848798755141484425060357 := by
  unfold tailWord_4959089
  simp only [CollatzResearch.WordTrace]
  refine ⟨180872835131074972817576321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120581890087383315211717547 180872835131074972817576321)
  ·
    refine ⟨135654626348306229613182241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180872835131074972817576321 135654626348306229613182241)
    ·
      refine ⟨101740969761229672209886681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135654626348306229613182241 101740969761229672209886681)
      ·
        refine ⟨76305727320922254157415011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101740969761229672209886681 76305727320922254157415011)
        ·
          refine ⟨114458590981383381236122517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76305727320922254157415011 114458590981383381236122517)
          ·
            refine ⟨5365246452252345995443243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114458590981383381236122517 5365246452252345995443243)
            ·
              refine ⟨8047869678378518993164865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365246452252345995443243 8047869678378518993164865)
              ·
                refine ⟨6035902258783889244873649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8047869678378518993164865 6035902258783889244873649)
                ·
                  refine ⟨4526926694087916933655237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035902258783889244873649 4526926694087916933655237)
                  ·
                    refine ⟨848798755141484425060357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4526926694087916933655237 848798755141484425060357)
                    ·
                      rfl

theorem cell23_4959089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_4959089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959089 prefixEnd_4959089 := by exact prefixLift 4959089
  have htrace : WordTrace (prefixWord ++ tailWord_4959089) baseStart_4959089 baseEnd_4959089 := by
    simpa [prefixWord, tailWord_4959089, baseEnd_4959089] using wordTrace_append hprefix tailTrace_4959089
  have hstable : (prefixWord ++ tailWord_4959089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959089).length < 2 ^ (prefixWord ++ tailWord_4959089).sum := by decide
  have hdescent : baseEnd_4959089 < baseStart_4959089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959095 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_4959095 : Nat := 118140960795 + 4959095 * 2 ^ 59
def prefixEnd_4959095 : Nat := 4983230072969 + 3 ^ 40 * 4959095 * 2
def baseEnd_4959095 : Nat := 2546399346308380251706043

theorem tailTrace_4959095 : CollatzResearch.WordTrace tailWord_4959095 prefixEnd_4959095 2546399346308380251706043 := by
  unfold tailWord_4959095
  simp only [CollatzResearch.WordTrace]
  refine ⟨180873053969053235842294739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120582035979368823894863159 180873053969053235842294739)
  ·
    refine ⟨271309580953579853763442109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180873053969053235842294739 271309580953579853763442109)
    ·
      refine ⟨101741092857592445161290791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271309580953579853763442109 101741092857592445161290791)
      ·
        refine ⟨152611639286388667741936187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101741092857592445161290791 152611639286388667741936187)
        ·
          refine ⟨228917458929583001612904281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152611639286388667741936187 228917458929583001612904281)
          ·
            refine ⟨171688094197187251209678211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228917458929583001612904281 171688094197187251209678211)
            ·
              refine ⟨257532141295780876814517317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171688094197187251209678211 257532141295780876814517317)
              ·
                refine ⟨48287276492958914402721997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257532141295780876814517317 48287276492958914402721997)
                ·
                  refine ⟨18107728684859592901020749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48287276492958914402721997 18107728684859592901020749)
                  ·
                    refine ⟨6790398256822347337882781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18107728684859592901020749 6790398256822347337882781)
                    ·
                      refine ⟨2546399346308380251706043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6790398256822347337882781 2546399346308380251706043)
                      ·
                        rfl

theorem cell23_4959095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_4959095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959095 prefixEnd_4959095 := by exact prefixLift 4959095
  have htrace : WordTrace (prefixWord ++ tailWord_4959095) baseStart_4959095 baseEnd_4959095 := by
    simpa [prefixWord, tailWord_4959095, baseEnd_4959095] using wordTrace_append hprefix tailTrace_4959095
  have hstable : (prefixWord ++ tailWord_4959095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959095).length < 2 ^ (prefixWord ++ tailWord_4959095).sum := by decide
  have hdescent : baseEnd_4959095 < baseStart_4959095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959125 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_4959125 : Nat := 118140960795 + 4959125 * 2 ^ 59
def prefixEnd_4959125 : Nat := 4983230072969 + 3 ^ 40 * 4959125 * 2
def baseEnd_4959125 : Nat := 2546414750728015134330905

theorem tailTrace_4959125 : CollatzResearch.WordTrace tailWord_4959125 prefixEnd_4959125 2546414750728015134330905 := by
  unfold tailWord_4959125
  simp only [CollatzResearch.WordTrace]
  refine ⟨180874148158944550965886829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120582765439296367310591219 180874148158944550965886829)
  ·
    refine ⟨67827805559604206612207561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180874148158944550965886829 67827805559604206612207561)
    ·
      refine ⟨50870854169703154959155671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67827805559604206612207561 50870854169703154959155671)
      ·
        refine ⟨76306281254554732438733507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50870854169703154959155671 76306281254554732438733507)
        ·
          refine ⟨114459421881832098658100261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76306281254554732438733507 114459421881832098658100261)
          ·
            refine ⟨21461141602843518498393799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114459421881832098658100261 21461141602843518498393799)
            ·
              refine ⟨32191712404265277747590699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21461141602843518498393799 32191712404265277747590699)
              ·
                refine ⟨48287568606397916621386049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32191712404265277747590699 48287568606397916621386049)
                ·
                  refine ⟨36215676454798437466039537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48287568606397916621386049 36215676454798437466039537)
                  ·
                    refine ⟨27161757341098828099529653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36215676454798437466039537 27161757341098828099529653)
                    ·
                      refine ⟨2546414750728015134330905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27161757341098828099529653 2546414750728015134330905)
                      ·
                        rfl

theorem cell23_4959125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_4959125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959125 prefixEnd_4959125 := by exact prefixLift 4959125
  have htrace : WordTrace (prefixWord ++ tailWord_4959125) baseStart_4959125 baseEnd_4959125 := by
    simpa [prefixWord, tailWord_4959125, baseEnd_4959125] using wordTrace_append hprefix tailTrace_4959125
  have hstable : (prefixWord ++ tailWord_4959125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959125).length < 2 ^ (prefixWord ++ tailWord_4959125).sum := by decide
  have hdescent : baseEnd_4959125 < baseStart_4959125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959130 : List Nat := [3, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2]
def baseStart_4959130 : Nat := 118140960795 + 4959130 * 2 ^ 59
def prefixEnd_4959130 : Nat := 4983230072969 + 3 ^ 40 * 4959130 * 2
def baseEnd_4959130 : Nat := 2546417318131287614768383

theorem tailTrace_4959130 : CollatzResearch.WordTrace tailWord_4959130 prefixEnd_4959130 2546417318131287614768383 := by
  unfold tailWord_4959130
  simp only [CollatzResearch.WordTrace]
  refine ⟨45218582630981609204954711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120582887015950957879879229 45218582630981609204954711)
  ·
    refine ⟨67827873946472413807432067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45218582630981609204954711 67827873946472413807432067)
    ·
      refine ⟨101741810919708620711148101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67827873946472413807432067 101741810919708620711148101)
      ·
        refine ⟨19076589547445366383340269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101741810919708620711148101 19076589547445366383340269)
        ·
          refine ⟨7153721080292012393752601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19076589547445366383340269 7153721080292012393752601)
          ·
            refine ⟨5365290810219009295314451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7153721080292012393752601 5365290810219009295314451)
            ·
              refine ⟨8047936215328513942971677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365290810219009295314451 8047936215328513942971677)
              ·
                refine ⟨3017976080748192728614379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8047936215328513942971677 3017976080748192728614379)
                ·
                  refine ⟨4526964121122289092921569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017976080748192728614379 4526964121122289092921569)
                  ·
                    refine ⟨3395223090841716819691177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4526964121122289092921569 3395223090841716819691177)
                    ·
                      refine ⟨2546417318131287614768383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395223090841716819691177 2546417318131287614768383)
                      ·
                        rfl

theorem cell23_4959130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_4959130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959130 prefixEnd_4959130 := by exact prefixLift 4959130
  have htrace : WordTrace (prefixWord ++ tailWord_4959130) baseStart_4959130 baseEnd_4959130 := by
    simpa [prefixWord, tailWord_4959130, baseEnd_4959130] using wordTrace_append hprefix tailTrace_4959130
  have hstable : (prefixWord ++ tailWord_4959130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959130).length < 2 ^ (prefixWord ++ tailWord_4959130).sum := by decide
  have hdescent : baseEnd_4959130 < baseStart_4959130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959139 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 1, 3, 2]
def baseStart_4959139 : Nat := 118140960795 + 4959139 * 2 ^ 59
def prefixEnd_4959139 : Nat := 4983230072969 + 3 ^ 40 * 4959139 * 2
def baseEnd_4959139 : Nat := 2546421939457178079555841

theorem tailTrace_4959139 : CollatzResearch.WordTrace tailWord_4959139 prefixEnd_4959139 2546421939457178079555841 := by
  unfold tailWord_4959139
  simp only [CollatzResearch.WordTrace]
  refine ⟨180874658780893831356896471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120583105853929220904597647 180874658780893831356896471)
  ·
    refine ⟨271311988171340747035344707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180874658780893831356896471 271311988171340747035344707)
    ·
      refine ⟨406967982257011120553017061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271311988171340747035344707 406967982257011120553017061)
      ·
        refine ⟨76306496673189585103690699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 406967982257011120553017061 76306496673189585103690699)
        ·
          refine ⟨114459745009784377655536049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76306496673189585103690699 114459745009784377655536049)
          ·
            refine ⟨85844808757338283241652037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114459745009784377655536049 85844808757338283241652037)
            ·
              refine ⟨16095901642000928107809757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85844808757338283241652037 16095901642000928107809757)
              ·
                refine ⟨6035963115750348040428659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16095901642000928107809757 6035963115750348040428659)
                ·
                  refine ⟨9053944673625522060642989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6035963115750348040428659 9053944673625522060642989)
                  ·
                    refine ⟨3395229252609570772741121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9053944673625522060642989 3395229252609570772741121)
                    ·
                      refine ⟨2546421939457178079555841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395229252609570772741121 2546421939457178079555841)
                      ·
                        rfl

theorem cell23_4959139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_4959139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959139 prefixEnd_4959139 := by exact prefixLift 4959139
  have htrace : WordTrace (prefixWord ++ tailWord_4959139) baseStart_4959139 baseEnd_4959139 := by
    simpa [prefixWord, tailWord_4959139, baseEnd_4959139] using wordTrace_append hprefix tailTrace_4959139
  have hstable : (prefixWord ++ tailWord_4959139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959139).length < 2 ^ (prefixWord ++ tailWord_4959139).sum := by decide
  have hdescent : baseEnd_4959139 < baseStart_4959139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959175 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 7]
def baseStart_4959175 : Nat := 118140960795 + 4959175 * 2 ^ 59
def prefixEnd_4959175 : Nat := 4983230072969 + 3 ^ 40 * 4959175 * 2
def baseEnd_4959175 : Nat := 282937824973415548745075

theorem tailTrace_4959175 : CollatzResearch.WordTrace tailWord_4959175 prefixEnd_4959175 282937824973415548745075 := by
  unfold tailWord_4959175
  simp only [CollatzResearch.WordTrace]
  refine ⟨180875971808763409505206979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120583981205842273003471319 180875971808763409505206979)
  ·
    refine ⟨271313957713145114257810469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180875971808763409505206979 271313957713145114257810469)
    ·
      refine ⟨50871367071214708923339463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271313957713145114257810469 50871367071214708923339463)
      ·
        refine ⟨76307050606822063385009195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50871367071214708923339463 76307050606822063385009195)
        ·
          refine ⟨114460575910233095077513793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76307050606822063385009195 114460575910233095077513793)
          ·
            refine ⟨85845431932674821308135345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114460575910233095077513793 85845431932674821308135345)
            ·
              refine ⟨64384073949506115981101509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85845431932674821308135345 64384073949506115981101509)
              ·
                refine ⟨12072013865532396746456533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64384073949506115981101509 12072013865532396746456533)
                ·
                  refine ⟨282937824973415548745075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12072013865532396746456533 282937824973415548745075)
                  ·
                    rfl

theorem cell23_4959175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 7].length) (baseStart_4959175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959175 prefixEnd_4959175 := by exact prefixLift 4959175
  have htrace : WordTrace (prefixWord ++ tailWord_4959175) baseStart_4959175 baseEnd_4959175 := by
    simpa [prefixWord, tailWord_4959175, baseEnd_4959175] using wordTrace_append hprefix tailTrace_4959175
  have hstable : (prefixWord ++ tailWord_4959175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959175).length < 2 ^ (prefixWord ++ tailWord_4959175).sum := by decide
  have hdescent : baseEnd_4959175 < baseStart_4959175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959186 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_4959186 : Nat := 118140960795 + 4959186 * 2 ^ 59
def prefixEnd_4959186 : Nat := 4983230072969 + 3 ^ 40 * 4959186 * 2
def baseEnd_4959186 : Nat := 2546446073047939395668125

theorem tailTrace_4959186 : CollatzResearch.WordTrace tailWord_4959186 prefixEnd_4959186 2546446073047939395668125 := by
  unfold tailWord_4959186
  simp only [CollatzResearch.WordTrace]
  refine ⟨45219093252930889595964353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120584248674482372255904941 45219093252930889595964353)
  ·
    refine ⟨33914319939698167196973265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45219093252930889595964353 33914319939698167196973265)
    ·
      refine ⟨25435739954773625397729949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33914319939698167196973265 25435739954773625397729949)
      ·
        refine ⟨9538402483040109524148731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25435739954773625397729949 9538402483040109524148731)
        ·
          refine ⟨14307603724560164286223097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538402483040109524148731 14307603724560164286223097)
          ·
            refine ⟨10730702793420123214667323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14307603724560164286223097 10730702793420123214667323)
            ·
              refine ⟨16096054190130184822000985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10730702793420123214667323 16096054190130184822000985)
              ·
                refine ⟨12072040642597638616500739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16096054190130184822000985 12072040642597638616500739)
                ·
                  refine ⟨18108060963896457924751109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12072040642597638616500739 18108060963896457924751109)
                  ·
                    refine ⟨3395261430730585860890833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18108060963896457924751109 3395261430730585860890833)
                    ·
                      refine ⟨2546446073047939395668125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395261430730585860890833 2546446073047939395668125)
                      ·
                        rfl

theorem cell23_4959186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_4959186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959186 prefixEnd_4959186 := by exact prefixLift 4959186
  have htrace : WordTrace (prefixWord ++ tailWord_4959186) baseStart_4959186 baseEnd_4959186 := by
    simpa [prefixWord, tailWord_4959186, baseEnd_4959186] using wordTrace_append hprefix tailTrace_4959186
  have hstable : (prefixWord ++ tailWord_4959186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959186).length < 2 ^ (prefixWord ++ tailWord_4959186).sum := by decide
  have hdescent : baseEnd_4959186 < baseStart_4959186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959190 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_4959190 : Nat := 118140960795 + 4959190 * 2 ^ 59
def prefixEnd_4959190 : Nat := 4983230072969 + 3 ^ 40 * 4959190 * 2
def baseEnd_4959190 : Nat := 2546448126970557380018107

theorem tailTrace_4959190 : CollatzResearch.WordTrace tailWord_4959190 prefixEnd_4959190 2546448126970557380018107 := by
  unfold tailWord_4959190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11304782431481816691687689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120584345935806044711335349 11304782431481816691687689)
  ·
    refine ⟨8478586823611362518765767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11304782431481816691687689 8478586823611362518765767)
    ·
      refine ⟨12717880235417043778148651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8478586823611362518765767 12717880235417043778148651)
      ·
        refine ⟨19076820353125565667222977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12717880235417043778148651 19076820353125565667222977)
        ·
          refine ⟨14307615264844174250417233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19076820353125565667222977 14307615264844174250417233)
          ·
            refine ⟨10730711448633130687812925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14307615264844174250417233 10730711448633130687812925)
            ·
              refine ⟨4024016793237424007929847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10730711448633130687812925 4024016793237424007929847)
              ·
                refine ⟨6036025189856136011894771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024016793237424007929847 6036025189856136011894771)
                ·
                  refine ⟨9054037784784204017842157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6036025189856136011894771 9054037784784204017842157)
                  ·
                    refine ⟨3395264169294076506690809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9054037784784204017842157 3395264169294076506690809)
                    ·
                      refine ⟨2546448126970557380018107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395264169294076506690809 2546448126970557380018107)
                      ·
                        rfl

theorem cell23_4959190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_4959190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959190 prefixEnd_4959190 := by exact prefixLift 4959190
  have htrace : WordTrace (prefixWord ++ tailWord_4959190) baseStart_4959190 baseEnd_4959190 := by
    simpa [prefixWord, tailWord_4959190, baseEnd_4959190] using wordTrace_append hprefix tailTrace_4959190
  have hstable : (prefixWord ++ tailWord_4959190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959190).length < 2 ^ (prefixWord ++ tailWord_4959190).sum := by decide
  have hdescent : baseEnd_4959190 < baseStart_4959190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959269 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_4959269 : Nat := 118140960795 + 4959269 * 2 ^ 59
def prefixEnd_4959269 : Nat := 4983230072969 + 3 ^ 40 * 4959269 * 2
def baseEnd_4959269 : Nat := 848829563980754190310081

theorem tailTrace_4959269 : CollatzResearch.WordTrace tailWord_4959269 prefixEnd_4959269 848829563980754190310081 := by
  unfold tailWord_4959269
  simp only [CollatzResearch.WordTrace]
  refine ⟨180879400270422863559128861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120586266846948575706085907 180879400270422863559128861)
  ·
    refine ⟨67829775101408573834673323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180879400270422863559128861 67829775101408573834673323)
    ·
      refine ⟨101744662652112860752009985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67829775101408573834673323 101744662652112860752009985)
      ·
        refine ⟨76308496989084645564007489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101744662652112860752009985 76308496989084645564007489)
        ·
          refine ⟨57231372741813484173005617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76308496989084645564007489 57231372741813484173005617)
          ·
            refine ⟨42923529556360113129754213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57231372741813484173005617 42923529556360113129754213)
            ·
              refine ⟨8048161791817521211828915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42923529556360113129754213 8048161791817521211828915)
              ·
                refine ⟨12072242687726281817743373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048161791817521211828915 12072242687726281817743373)
                ·
                  refine ⟨4527091007897355681653765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12072242687726281817743373 4527091007897355681653765)
                  ·
                    refine ⟨848829563980754190310081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527091007897355681653765 848829563980754190310081)
                    ·
                      rfl

theorem cell23_4959269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_4959269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959269 prefixEnd_4959269 := by exact prefixLift 4959269
  have htrace : WordTrace (prefixWord ++ tailWord_4959269) baseStart_4959269 baseEnd_4959269 := by
    simpa [prefixWord, tailWord_4959269, baseEnd_4959269] using wordTrace_append hprefix tailTrace_4959269
  have hstable : (prefixWord ++ tailWord_4959269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959269).length < 2 ^ (prefixWord ++ tailWord_4959269).sum := by decide
  have hdescent : baseEnd_4959269 < baseStart_4959269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959286 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_4959286 : Nat := 118140960795 + 4959286 * 2 ^ 59
def prefixEnd_4959286 : Nat := 4983230072969 + 3 ^ 40 * 4959286 * 2
def baseEnd_4959286 : Nat := 848832473704463001472555

theorem tailTrace_4959286 : CollatzResearch.WordTrace tailWord_4959286 prefixEnd_4959286 848832473704463001472555 := by
  unfold tailWord_4959286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305001269460079716406107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120586680207574183641665141 11305001269460079716406107)
  ·
    refine ⟨16957501904190119574609161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11305001269460079716406107 16957501904190119574609161)
    ·
      refine ⟨12718126428142589680956871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16957501904190119574609161 12718126428142589680956871)
      ·
        refine ⟨19077189642213884521435307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12718126428142589680956871 19077189642213884521435307)
        ·
          refine ⟨28615784463320826782152961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19077189642213884521435307 28615784463320826782152961)
          ·
            refine ⟨21461838347490620086614721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28615784463320826782152961 21461838347490620086614721)
            ·
              refine ⟨16096378760617965064961041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21461838347490620086614721 16096378760617965064961041)
              ·
                refine ⟨12072284070463473798720781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16096378760617965064961041 12072284070463473798720781)
                ·
                  refine ⟨4527106526423802674520293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12072284070463473798720781 4527106526423802674520293)
                  ·
                    refine ⟨848832473704463001472555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527106526423802674520293 848832473704463001472555)
                    ·
                      rfl

theorem cell23_4959286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_4959286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959286 prefixEnd_4959286 := by exact prefixLift 4959286
  have htrace : WordTrace (prefixWord ++ tailWord_4959286) baseStart_4959286 baseEnd_4959286 := by
    simpa [prefixWord, tailWord_4959286, baseEnd_4959286] using wordTrace_append hprefix tailTrace_4959286
  have hstable : (prefixWord ++ tailWord_4959286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959286).length < 2 ^ (prefixWord ++ tailWord_4959286).sum := by decide
  have hdescent : baseEnd_4959286 < baseStart_4959286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959303 : List Nat := [1, 1, 4, 1, 3, 4, 1, 3, 1, 4]
def baseStart_4959303 : Nat := 118140960795 + 4959303 * 2 ^ 59
def prefixEnd_4959303 : Nat := 4983230072969 + 3 ^ 40 * 4959303 * 2
def baseEnd_4959303 : Nat := 848835383428171812635029

theorem tailTrace_4959303 : CollatzResearch.WordTrace tailWord_4959303 prefixEnd_4959303 848835383428171812635029 := by
  unfold tailWord_4959303
  simp only [CollatzResearch.WordTrace]
  refine ⟨180880640352299687365866563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120587093568199791577244375 180880640352299687365866563)
  ·
    refine ⟨271320960528449531048799845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180880640352299687365866563 271320960528449531048799845)
    ·
      refine ⟨50872680099084287071649971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271320960528449531048799845 50872680099084287071649971)
      ·
        refine ⟨76309020148626430607474957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50872680099084287071649971 76309020148626430607474957)
        ·
          refine ⟨28615882555734911477803109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76309020148626430607474957 28615882555734911477803109)
          ·
            refine ⟨5365477979200295902088083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28615882555734911477803109 5365477979200295902088083)
            ·
              refine ⟨8048216968800443853132125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365477979200295902088083 8048216968800443853132125)
              ·
                refine ⟨3018081363300166444924547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8048216968800443853132125 3018081363300166444924547)
                ·
                  refine ⟨4527122044950249667386821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018081363300166444924547 4527122044950249667386821)
                  ·
                    refine ⟨848835383428171812635029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527122044950249667386821 848835383428171812635029)
                    ·
                      rfl

theorem cell23_4959303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_4959303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959303 prefixEnd_4959303 := by exact prefixLift 4959303
  have htrace : WordTrace (prefixWord ++ tailWord_4959303) baseStart_4959303 baseEnd_4959303 := by
    simpa [prefixWord, tailWord_4959303, baseEnd_4959303] using wordTrace_append hprefix tailTrace_4959303
  have hstable : (prefixWord ++ tailWord_4959303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959303).length < 2 ^ (prefixWord ++ tailWord_4959303).sum := by decide
  have hdescent : baseEnd_4959303 < baseStart_4959303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959332 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_4959332 : Nat := 118140960795 + 4959332 * 2 ^ 59
def prefixEnd_4959332 : Nat := 4983230072969 + 3 ^ 40 * 4959332 * 2
def baseEnd_4959332 : Nat := 2546521041223495824442453

theorem tailTrace_4959332 : CollatzResearch.WordTrace tailWord_4959332 prefixEnd_4959332 2546521041223495824442453 := by
  unfold tailWord_4959332
  simp only [CollatzResearch.WordTrace]
  refine ⟨90440849034597312659336125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120587798712796416879114833 90440849034597312659336125)
  ·
    refine ⟨33915318387973992247251047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90440849034597312659336125 33915318387973992247251047)
    ·
      refine ⟨50872977581960988370876571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33915318387973992247251047 50872977581960988370876571)
      ·
        refine ⟨76309466372941482556314857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50872977581960988370876571 76309466372941482556314857)
        ·
          refine ⟨57232099779706111917236143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76309466372941482556314857 57232099779706111917236143)
          ·
            refine ⟨85848149669559167875854215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57232099779706111917236143 85848149669559167875854215)
            ·
              refine ⟨128772224504338751813781323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85848149669559167875854215 128772224504338751813781323)
              ·
                refine ⟨193158336756508127720671985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128772224504338751813781323 193158336756508127720671985)
                ·
                  refine ⟨144868752567381095790503989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193158336756508127720671985 144868752567381095790503989)
                  ·
                    refine ⟨13581445553191977730359749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144868752567381095790503989 13581445553191977730359749)
                    ·
                      refine ⟨2546521041223495824442453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13581445553191977730359749 2546521041223495824442453)
                      ·
                        rfl

theorem cell23_4959332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_4959332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959332 prefixEnd_4959332 := by exact prefixLift 4959332
  have htrace : WordTrace (prefixWord ++ tailWord_4959332) baseStart_4959332 baseEnd_4959332 := by
    simpa [prefixWord, tailWord_4959332, baseEnd_4959332] using wordTrace_append hprefix tailTrace_4959332
  have hstable : (prefixWord ++ tailWord_4959332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959332).length < 2 ^ (prefixWord ++ tailWord_4959332).sum := by decide
  have hdescent : baseEnd_4959332 < baseStart_4959332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
