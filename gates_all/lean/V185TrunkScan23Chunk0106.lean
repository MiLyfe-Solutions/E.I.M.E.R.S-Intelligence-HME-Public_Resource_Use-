import V185TrunkScan23Chunk0105

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_627559 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_627559 : Nat := 118140960795 + 627559 * 2 ^ 59
def prefixEnd_627559 : Nat := 4983230072969 + 3 ^ 40 * 627559 * 2
def baseEnd_627559 : Nat := 322239406055015406226415

theorem tailTrace_627559 : CollatzResearch.WordTrace tailWord_627559 prefixEnd_627559 322239406055015406226415 := by
  unfold tailWord_627559
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888957133468396389389731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15259304755645597592926487 22888957133468396389389731)
  ·
    refine ⟨34333435700202594584084597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22888957133468396389389731 34333435700202594584084597)
    ·
      refine ⟨3218759596893993242257931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34333435700202594584084597 3218759596893993242257931)
      ·
        refine ⟨4828139395340989863386897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218759596893993242257931 4828139395340989863386897)
        ·
          refine ⟨3621104546505742397540173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4828139395340989863386897 3621104546505742397540173)
          ·
            refine ⟨1357914204939653399077565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3621104546505742397540173 1357914204939653399077565)
            ·
              refine ⟨509217826852370024654087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1357914204939653399077565 509217826852370024654087)
              ·
                refine ⟨763826740278555036981131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509217826852370024654087 763826740278555036981131)
                ·
                  refine ⟨1145740110417832555471697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763826740278555036981131 1145740110417832555471697)
                  ·
                    refine ⟨859305082813374416603773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1145740110417832555471697 859305082813374416603773)
                    ·
                      refine ⟨322239406055015406226415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859305082813374416603773 322239406055015406226415)
                      ·
                        rfl

theorem cell23_627559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_627559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627559 prefixEnd_627559 := by exact prefixLift 627559
  have htrace : WordTrace (prefixWord ++ tailWord_627559) baseStart_627559 baseEnd_627559 := by
    simpa [prefixWord, tailWord_627559, baseEnd_627559] using wordTrace_append hprefix tailTrace_627559
  have hstable : (prefixWord ++ tailWord_627559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627559).length < 2 ^ (prefixWord ++ tailWord_627559).sum := by decide
  have hdescent : baseEnd_627559 < baseStart_627559 := by decide
  rcases family_descends (prefixWord ++ tailWord_627559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627568 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_627568 : Nat := 118140960795 + 627568 * 2 ^ 59
def prefixEnd_627568 : Nat := 4983230072969 + 3 ^ 40 * 627568 * 2
def baseEnd_627568 : Nat := 322244027380905871013873

theorem tailTrace_627568 : CollatzResearch.WordTrace tailWord_627568 prefixEnd_627568 322244027380905871013873 := by
  unfold tailWord_627568
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444642695217895463233679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15259523593623860617644905 11444642695217895463233679)
  ·
    refine ⟨17166964042826843194850519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11444642695217895463233679 17166964042826843194850519)
    ·
      refine ⟨25750446064240264792275779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17166964042826843194850519 25750446064240264792275779)
      ·
        refine ⟨38625669096360397188413669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25750446064240264792275779 38625669096360397188413669)
        ·
          refine ⟨7242312955567574472827563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38625669096360397188413669 7242312955567574472827563)
          ·
            refine ⟨10863469433351361709241345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7242312955567574472827563 10863469433351361709241345)
            ·
              refine ⟨8147602075013521281931009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10863469433351361709241345 8147602075013521281931009)
              ·
                refine ⟨6110701556260140961448257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8147602075013521281931009 6110701556260140961448257)
                ·
                  refine ⟨4583026167195105721086193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6110701556260140961448257 4583026167195105721086193)
                  ·
                    refine ⟨3437269625396329290814645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4583026167195105721086193 3437269625396329290814645)
                    ·
                      refine ⟨322244027380905871013873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3437269625396329290814645 322244027380905871013873)
                      ·
                        rfl

theorem cell23_627568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_627568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627568 prefixEnd_627568 := by exact prefixLift 627568
  have htrace : WordTrace (prefixWord ++ tailWord_627568) baseStart_627568 baseEnd_627568 := by
    simpa [prefixWord, tailWord_627568, baseEnd_627568] using wordTrace_append hprefix tailTrace_627568
  have hstable : (prefixWord ++ tailWord_627568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627568).length < 2 ^ (prefixWord ++ tailWord_627568).sum := by decide
  have hdescent : baseEnd_627568 < baseStart_627568 := by decide
  rcases family_descends (prefixWord ++ tailWord_627568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627573 : List Nat := [1, 3, 4, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_627573 : Nat := 118140960795 + 627573 * 2 ^ 59
def prefixEnd_627573 : Nat := 4983230072969 + 3 ^ 40 * 627573 * 2
def baseEnd_627573 : Nat := 322246594784178351451351

theorem tailTrace_627573 : CollatzResearch.WordTrace tailWord_627573 prefixEnd_627573 322246594784178351451351 := by
  unfold tailWord_627573
  simp only [CollatzResearch.WordTrace]
  refine ⟨22889467755417676780399373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15259645170278451186932915 22889467755417676780399373)
  ·
    refine ⟨8583550408281628792649765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22889467755417676780399373 8583550408281628792649765)
    ·
      refine ⟨1609415701552805398621831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8583550408281628792649765 1609415701552805398621831)
      ·
        refine ⟨2414123552329208097932747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609415701552805398621831 2414123552329208097932747)
        ·
          refine ⟨3621185328493812146899121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414123552329208097932747 3621185328493812146899121)
          ·
            refine ⟨2715888996370359110174341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3621185328493812146899121 2715888996370359110174341)
            ·
              refine ⟨509229186819442333157689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2715888996370359110174341 509229186819442333157689)
              ·
                refine ⟨381921890114581749868267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509229186819442333157689 381921890114581749868267)
                ·
                  refine ⟨572882835171872624802401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381921890114581749868267 572882835171872624802401)
                  ·
                    refine ⟨429662126378904468601801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 572882835171872624802401 429662126378904468601801)
                    ·
                      refine ⟨322246594784178351451351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429662126378904468601801 322246594784178351451351)
                      ·
                        rfl

theorem cell23_627573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_627573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627573 prefixEnd_627573 := by exact prefixLift 627573
  have htrace : WordTrace (prefixWord ++ tailWord_627573) baseStart_627573 baseEnd_627573 := by
    simpa [prefixWord, tailWord_627573, baseEnd_627573] using wordTrace_append hprefix tailTrace_627573
  have hstable : (prefixWord ++ tailWord_627573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627573).length < 2 ^ (prefixWord ++ tailWord_627573).sum := by decide
  have hdescent : baseEnd_627573 < baseStart_627573 := by decide
  rcases family_descends (prefixWord ++ tailWord_627573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627586 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_627586 : Nat := 118140960795 + 627586 * 2 ^ 59
def prefixEnd_627586 : Nat := 4983230072969 + 3 ^ 40 * 627586 * 2
def baseEnd_627586 : Nat := 322253270032686800588791

theorem tailTrace_627586 : CollatzResearch.WordTrace tailWord_627586 prefixEnd_627586 322253270032686800588791 := by
  unfold tailWord_627586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5722485476092645000155653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15259961269580386667081741 5722485476092645000155653)
  ·
    refine ⟨1072966026767370937529185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5722485476092645000155653 1072966026767370937529185)
    ·
      refine ⟨804724520075528203146889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1072966026767370937529185 804724520075528203146889)
      ·
        refine ⟨603543390056646152360167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804724520075528203146889 603543390056646152360167)
        ·
          refine ⟨905315085084969228540251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603543390056646152360167 905315085084969228540251)
          ·
            refine ⟨1357972627627453842810377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905315085084969228540251 1357972627627453842810377)
            ·
              refine ⟨1018479470720590382107783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357972627627453842810377 1018479470720590382107783)
              ·
                refine ⟨1527719206080885573161675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018479470720590382107783 1527719206080885573161675)
                ·
                  refine ⟨2291578809121328359742513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527719206080885573161675 2291578809121328359742513)
                  ·
                    refine ⟨1718684106840996269806885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291578809121328359742513 1718684106840996269806885)
                    ·
                      refine ⟨322253270032686800588791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1718684106840996269806885 322253270032686800588791)
                      ·
                        rfl

theorem cell23_627586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_627586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627586 prefixEnd_627586 := by exact prefixLift 627586
  have htrace : WordTrace (prefixWord ++ tailWord_627586) baseStart_627586 baseEnd_627586 := by
    simpa [prefixWord, tailWord_627586, baseEnd_627586] using wordTrace_append hprefix tailTrace_627586
  have hstable : (prefixWord ++ tailWord_627586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627586).length < 2 ^ (prefixWord ++ tailWord_627586).sum := by decide
  have hdescent : baseEnd_627586 < baseStart_627586 := by decide
  rcases family_descends (prefixWord ++ tailWord_627586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627606 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_627606 : Nat := 118140960795 + 627606 * 2 ^ 59
def prefixEnd_627606 : Nat := 4983230072969 + 3 ^ 40 * 627606 * 2
def baseEnd_627606 : Nat := 322263539645776722338699

theorem tailTrace_627606 : CollatzResearch.WordTrace tailWord_627606 prefixEnd_627606 322263539645776722338699 := by
  unfold tailWord_627606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430666960268632713521917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15260447576198748944233781 1430666960268632713521917)
  ·
    refine ⟨536500110100737267570719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1430666960268632713521917 536500110100737267570719)
    ·
      refine ⟨804750165151105901356079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 536500110100737267570719 804750165151105901356079)
      ·
        refine ⟨1207125247726658852034119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804750165151105901356079 1207125247726658852034119)
        ·
          refine ⟨1810687871589988278051179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207125247726658852034119 1810687871589988278051179)
          ·
            refine ⟨2716031807384982417076769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810687871589988278051179 2716031807384982417076769)
            ·
              refine ⟨2037023855538736812807577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2716031807384982417076769 2037023855538736812807577)
              ·
                refine ⟨1527767891654052609605683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037023855538736812807577 1527767891654052609605683)
                ·
                  refine ⟨2291651837481078914408525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527767891654052609605683 2291651837481078914408525)
                  ·
                    refine ⟨859369439055404592903197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291651837481078914408525 859369439055404592903197)
                    ·
                      refine ⟨322263539645776722338699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859369439055404592903197 322263539645776722338699)
                      ·
                        rfl

theorem cell23_627606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_627606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627606 prefixEnd_627606 := by exact prefixLift 627606
  have htrace : WordTrace (prefixWord ++ tailWord_627606) baseStart_627606 baseEnd_627606 := by
    simpa [prefixWord, tailWord_627606, baseEnd_627606] using wordTrace_append hprefix tailTrace_627606
  have hstable : (prefixWord ++ tailWord_627606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627606).length < 2 ^ (prefixWord ++ tailWord_627606).sum := by decide
  have hdescent : baseEnd_627606 < baseStart_627606 := by decide
  rcases family_descends (prefixWord ++ tailWord_627606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627623 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_627623 : Nat := 118140960795 + 627623 * 2 ^ 59
def prefixEnd_627623 : Nat := 4983230072969 + 3 ^ 40 * 627623 * 2
def baseEnd_627623 : Nat := 322272268816903155826121

theorem tailTrace_627623 : CollatzResearch.WordTrace tailWord_627623 prefixEnd_627623 322272268816903155826121 := by
  unfold tailWord_627623
  simp only [CollatzResearch.WordTrace]
  refine ⟨22891291405236535319719523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15260860936824356879813015 22891291405236535319719523)
  ·
    refine ⟨34336937107854802979579285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22891291405236535319719523 34336937107854802979579285)
    ·
      refine ⟨1609543926930693889667779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34336937107854802979579285 1609543926930693889667779)
      ·
        refine ⟨2414315890396040834501669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609543926930693889667779 2414315890396040834501669)
        ·
          refine ⟨452684229449257656469063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2414315890396040834501669 452684229449257656469063)
          ·
            refine ⟨679026344173886484703595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452684229449257656469063 679026344173886484703595)
            ·
              refine ⟨1018539516260829727055393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679026344173886484703595 1018539516260829727055393)
              ·
                refine ⟨763904637195622295291545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018539516260829727055393 763904637195622295291545)
                ·
                  refine ⟨572928477896716721468659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 763904637195622295291545 572928477896716721468659)
                  ·
                    refine ⟨859392716845075082202989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 572928477896716721468659 859392716845075082202989)
                    ·
                      refine ⟨322272268816903155826121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859392716845075082202989 322272268816903155826121)
                      ·
                        rfl

theorem cell23_627623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_627623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627623 prefixEnd_627623 := by exact prefixLift 627623
  have htrace : WordTrace (prefixWord ++ tailWord_627623) baseStart_627623 baseEnd_627623 := by
    simpa [prefixWord, tailWord_627623, baseEnd_627623] using wordTrace_append hprefix tailTrace_627623
  have hstable : (prefixWord ++ tailWord_627623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627623).length < 2 ^ (prefixWord ++ tailWord_627623).sum := by decide
  have hdescent : baseEnd_627623 < baseStart_627623 := by decide
  rcases family_descends (prefixWord ++ tailWord_627623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627628 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_627628 : Nat := 118140960795 + 627628 * 2 ^ 59
def prefixEnd_627628 : Nat := 4983230072969 + 3 ^ 40 * 627628 * 2
def baseEnd_627628 : Nat := 322274836220175636263597

theorem tailTrace_627628 : CollatzResearch.WordTrace tailWord_627628 prefixEnd_627628 322274836220175636263597 := by
  unfold tailWord_627628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445736885109210586825769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15260982513478947449101025 11445736885109210586825769)
  ·
    refine ⟨8584302663831907940119327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11445736885109210586825769 8584302663831907940119327)
    ·
      refine ⟨12876453995747861910178991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8584302663831907940119327 12876453995747861910178991)
      ·
        refine ⟨19314680993621792865268487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12876453995747861910178991 19314680993621792865268487)
        ·
          refine ⟨28972021490432689297902731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19314680993621792865268487 28972021490432689297902731)
          ·
            refine ⟨43458032235649033946854097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28972021490432689297902731 43458032235649033946854097)
            ·
              refine ⟨32593524176736775460140573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43458032235649033946854097 32593524176736775460140573)
              ·
                refine ⟨12222571566276290797552715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32593524176736775460140573 12222571566276290797552715)
                ·
                  refine ⟨18333857349414436196329073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12222571566276290797552715 18333857349414436196329073)
                  ·
                    refine ⟨13750393012060827147246805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18333857349414436196329073 13750393012060827147246805)
                    ·
                      refine ⟨322274836220175636263597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13750393012060827147246805 322274836220175636263597)
                      ·
                        rfl

theorem cell23_627628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_627628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627628 prefixEnd_627628 := by exact prefixLift 627628
  have htrace : WordTrace (prefixWord ++ tailWord_627628) baseStart_627628 baseEnd_627628 := by
    simpa [prefixWord, tailWord_627628, baseEnd_627628] using wordTrace_append hprefix tailTrace_627628
  have hstable : (prefixWord ++ tailWord_627628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627628).length < 2 ^ (prefixWord ++ tailWord_627628).sum := by decide
  have hdescent : baseEnd_627628 < baseStart_627628 := by decide
  rcases family_descends (prefixWord ++ tailWord_627628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627665 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 2, 5]
def baseStart_627665 : Nat := 118140960795 + 627665 * 2 ^ 59
def prefixEnd_627665 : Nat := 4983230072969 + 3 ^ 40 * 627665 * 2
def baseEnd_627665 : Nat := 107431278334797330500309

theorem tailTrace_627665 : CollatzResearch.WordTrace tailWord_627665 prefixEnd_627665 107431278334797330500309 := by
  unfold tailWord_627665
  simp only [CollatzResearch.WordTrace]
  refine ⟨22892823271084376492748449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15261882180722917661832299 22892823271084376492748449)
  ·
    refine ⟨17169617453313282369561337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22892823271084376492748449 17169617453313282369561337)
    ·
      refine ⟨12877213089984961777171003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17169617453313282369561337 12877213089984961777171003)
      ·
        refine ⟨19315819634977442665756505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12877213089984961777171003 19315819634977442665756505)
        ·
          refine ⟨14486864726233081999317379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19315819634977442665756505 14486864726233081999317379)
          ·
            refine ⟨21730297089349622998976069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14486864726233081999317379 21730297089349622998976069)
            ·
              refine ⟨4074430704253054312308013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21730297089349622998976069 4074430704253054312308013)
              ·
                refine ⟨1527911514094895367115505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4074430704253054312308013 1527911514094895367115505)
                ·
                  refine ⟨1145933635571171525336629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1527911514094895367115505 1145933635571171525336629)
                  ·
                    refine ⟨107431278334797330500309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1145933635571171525336629 107431278334797330500309)
                    ·
                      rfl

theorem cell23_627665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_627665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627665 prefixEnd_627665 := by exact prefixLift 627665
  have htrace : WordTrace (prefixWord ++ tailWord_627665) baseStart_627665 baseEnd_627665 := by
    simpa [prefixWord, tailWord_627665, baseEnd_627665] using wordTrace_append hprefix tailTrace_627665
  have hstable : (prefixWord ++ tailWord_627665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627665).length < 2 ^ (prefixWord ++ tailWord_627665).sum := by decide
  have hdescent : baseEnd_627665 < baseStart_627665 := by decide
  rcases family_descends (prefixWord ++ tailWord_627665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627746 : List Nat := [3, 3, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_627746 : Nat := 118140960795 + 627746 * 2 ^ 59
def prefixEnd_627746 : Nat := 4983230072969 + 3 ^ 40 * 627746 * 2
def baseEnd_627746 : Nat := 107445142312468724862685

theorem tailTrace_627746 : CollatzResearch.WordTrace tailWord_627746 prefixEnd_627746 107445142312468724862685 := by
  unfold tailWord_627746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723944395947731831611773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15263851722527284884298061 5723944395947731831611773)
  ·
    refine ⟨2146479148480399436854415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5723944395947731831611773 2146479148480399436854415)
    ·
      refine ⟨3219718722720599155281623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146479148480399436854415 3219718722720599155281623)
      ·
        refine ⟨4829578084080898732922435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219718722720599155281623 4829578084080898732922435)
        ·
          refine ⟨7244367126121348099383653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829578084080898732922435 7244367126121348099383653)
          ·
            refine ⟨1358318836147752768634435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7244367126121348099383653 1358318836147752768634435)
            ·
              refine ⟨2037478254221629152951653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358318836147752768634435 2037478254221629152951653)
              ·
                refine ⟨382027172666555466178435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2037478254221629152951653 382027172666555466178435)
                ·
                  refine ⟨573040758999833199267653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382027172666555466178435 573040758999833199267653)
                  ·
                    refine ⟨107445142312468724862685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573040758999833199267653 107445142312468724862685)
                    ·
                      rfl

theorem cell23_627746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_627746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627746 prefixEnd_627746 := by exact prefixLift 627746
  have htrace : WordTrace (prefixWord ++ tailWord_627746) baseStart_627746 baseEnd_627746 := by
    simpa [prefixWord, tailWord_627746, baseEnd_627746] using wordTrace_append hprefix tailTrace_627746
  have hstable : (prefixWord ++ tailWord_627746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627746).length < 2 ^ (prefixWord ++ tailWord_627746).sum := by decide
  have hdescent : baseEnd_627746 < baseStart_627746 := by decide
  rcases family_descends (prefixWord ++ tailWord_627746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627755 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 5, 5]
def baseStart_627755 : Nat := 118140960795 + 627755 * 2 ^ 59
def prefixEnd_627755 : Nat := 4983230072969 + 3 ^ 40 * 627755 * 2
def baseEnd_627755 : Nat := 107446682754432213125171

theorem tailTrace_627755 : CollatzResearch.WordTrace tailWord_627755 prefixEnd_627755 107446682754432213125171 := by
  unfold tailWord_627755
  simp only [CollatzResearch.WordTrace]
  refine ⟨22896105840758321863524719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15264070560505547909016479 22896105840758321863524719)
  ·
    refine ⟨34344158761137482795287079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22896105840758321863524719 34344158761137482795287079)
    ·
      refine ⟨51516238141706224192930619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34344158761137482795287079 51516238141706224192930619)
      ·
        refine ⟨77274357212559336289395929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51516238141706224192930619 77274357212559336289395929)
        ·
          refine ⟨57955767909419502217046947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77274357212559336289395929 57955767909419502217046947)
          ·
            refine ⟨86933651864129253325570421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57955767909419502217046947 86933651864129253325570421)
            ·
              refine ⟨8150029862262117499272227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86933651864129253325570421 8150029862262117499272227)
              ·
                refine ⟨12225044793393176248908341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8150029862262117499272227 12225044793393176248908341)
                ·
                  refine ⟨1146097949380610273335157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12225044793393176248908341 1146097949380610273335157)
                  ·
                    refine ⟨107446682754432213125171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1146097949380610273335157 107446682754432213125171)
                    ·
                      rfl

theorem cell23_627755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 5].length) (baseStart_627755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627755 prefixEnd_627755 := by exact prefixLift 627755
  have htrace : WordTrace (prefixWord ++ tailWord_627755) baseStart_627755 baseEnd_627755 := by
    simpa [prefixWord, tailWord_627755, baseEnd_627755] using wordTrace_append hprefix tailTrace_627755
  have hstable : (prefixWord ++ tailWord_627755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627755).length < 2 ^ (prefixWord ++ tailWord_627755).sum := by decide
  have hdescent : baseEnd_627755 < baseStart_627755 := by decide
  rcases family_descends (prefixWord ++ tailWord_627755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627765 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_627765 : Nat := 118140960795 + 627765 * 2 ^ 59
def prefixEnd_627765 : Nat := 4983230072969 + 3 ^ 40 * 627765 * 2
def baseEnd_627765 : Nat := 322345183069841600250467

theorem tailTrace_627765 : CollatzResearch.WordTrace tailWord_627765 prefixEnd_627765 322345183069841600250467 := by
  unfold tailWord_627765
  simp only [CollatzResearch.WordTrace]
  refine ⟨22896470570722093571388749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15264313713814729047592499 22896470570722093571388749)
  ·
    refine ⟨8586176464020785089270781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22896470570722093571388749 8586176464020785089270781)
    ·
      refine ⟨3219816174007794408476543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8586176464020785089270781 3219816174007794408476543)
      ·
        refine ⟨4829724261011691612714815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219816174007794408476543 4829724261011691612714815)
        ·
          refine ⟨7244586391517537419072223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829724261011691612714815 7244586391517537419072223)
          ·
            refine ⟨10866879587276306128608335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244586391517537419072223 10866879587276306128608335)
            ·
              refine ⟨16300319380914459192912503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10866879587276306128608335 16300319380914459192912503)
              ·
                refine ⟨24450479071371688789368755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16300319380914459192912503 24450479071371688789368755)
                ·
                  refine ⟨36675718607057533184053133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24450479071371688789368755 36675718607057533184053133)
                  ·
                    refine ⟨13753394477646574944019925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36675718607057533184053133 13753394477646574944019925)
                    ·
                      refine ⟨322345183069841600250467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13753394477646574944019925 322345183069841600250467)
                      ·
                        rfl

theorem cell23_627765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_627765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627765 prefixEnd_627765 := by exact prefixLift 627765
  have htrace : WordTrace (prefixWord ++ tailWord_627765) baseStart_627765 baseEnd_627765 := by
    simpa [prefixWord, tailWord_627765, baseEnd_627765] using wordTrace_append hprefix tailTrace_627765
  have hstable : (prefixWord ++ tailWord_627765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627765).length < 2 ^ (prefixWord ++ tailWord_627765).sum := by decide
  have hdescent : baseEnd_627765 < baseStart_627765 := by decide
  rcases family_descends (prefixWord ++ tailWord_627765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627769 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 3]
def baseStart_627769 : Nat := 118140960795 + 627769 * 2 ^ 59
def prefixEnd_627769 : Nat := 4983230072969 + 3 ^ 40 * 627769 * 2
def baseEnd_627769 : Nat := 322347236992459584600449

theorem tailTrace_627769 : CollatzResearch.WordTrace tailWord_627769 prefixEnd_627769 322347236992459584600449 := by
  unfold tailWord_627769
  simp only [CollatzResearch.WordTrace]
  refine ⟨22896616462707602254534361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15264410975138401503022907 22896616462707602254534361)
  ·
    refine ⟨17172462347030701690900771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22896616462707602254534361 17172462347030701690900771)
    ·
      refine ⟨25758693520546052536351157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17172462347030701690900771 25758693520546052536351157)
      ·
        refine ⟨2414877517551192425282921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25758693520546052536351157 2414877517551192425282921)
        ·
          refine ⟨1811158138163394318962191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2414877517551192425282921 1811158138163394318962191)
          ·
            refine ⟨2716737207245091478443287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811158138163394318962191 2716737207245091478443287)
            ·
              refine ⟨4075105810867637217664931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716737207245091478443287 4075105810867637217664931)
              ·
                refine ⟨6112658716301455826497397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4075105810867637217664931 6112658716301455826497397)
                ·
                  refine ⟨573061754653261483734131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6112658716301455826497397 573061754653261483734131)
                  ·
                    refine ⟨859592631979892225601197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573061754653261483734131 859592631979892225601197)
                    ·
                      refine ⟨322347236992459584600449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859592631979892225601197 322347236992459584600449)
                      ·
                        rfl

theorem cell23_627769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_627769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627769 prefixEnd_627769 := by exact prefixLift 627769
  have htrace : WordTrace (prefixWord ++ tailWord_627769) baseStart_627769 baseEnd_627769 := by
    simpa [prefixWord, tailWord_627769, baseEnd_627769] using wordTrace_append hprefix tailTrace_627769
  have hstable : (prefixWord ++ tailWord_627769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627769).length < 2 ^ (prefixWord ++ tailWord_627769).sum := by decide
  have hdescent : baseEnd_627769 < baseStart_627769 := by decide
  rcases family_descends (prefixWord ++ tailWord_627769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627772 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_627772 : Nat := 118140960795 + 627772 * 2 ^ 59
def prefixEnd_627772 : Nat := 4983230072969 + 3 ^ 40 * 627772 * 2
def baseEnd_627772 : Nat := 107449592478141024287645

theorem tailTrace_627772 : CollatzResearch.WordTrace tailWord_627772 prefixEnd_627772 107449592478141024287645 := by
  unfold tailWord_627772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448362940848366883446785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15264483921131155844595713 11448362940848366883446785)
  ·
    refine ⟨8586272205636275162585089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11448362940848366883446785 8586272205636275162585089)
    ·
      refine ⟨6439704154227206371938817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8586272205636275162585089 6439704154227206371938817)
      ·
        refine ⟨4829778115670404778954113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6439704154227206371938817 4829778115670404778954113)
        ·
          refine ⟨3622333586752803584215585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829778115670404778954113 3622333586752803584215585)
          ·
            refine ⟨2716750190064602688161689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3622333586752803584215585 2716750190064602688161689)
            ·
              refine ⟨2037562642548452016121267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2716750190064602688161689 2037562642548452016121267)
              ·
                refine ⟨3056343963822678024181901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037562642548452016121267 3056343963822678024181901)
                ·
                  refine ⟨1146128986433504259068213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3056343963822678024181901 1146128986433504259068213)
                  ·
                    refine ⟨107449592478141024287645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1146128986433504259068213 107449592478141024287645)
                    ·
                      rfl

theorem cell23_627772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_627772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627772 prefixEnd_627772 := by exact prefixLift 627772
  have htrace : WordTrace (prefixWord ++ tailWord_627772) baseStart_627772 baseEnd_627772 := by
    simpa [prefixWord, tailWord_627772, baseEnd_627772] using wordTrace_append hprefix tailTrace_627772
  have hstable : (prefixWord ++ tailWord_627772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627772).length < 2 ^ (prefixWord ++ tailWord_627772).sum := by decide
  have hdescent : baseEnd_627772 < baseStart_627772 := by decide
  rcases family_descends (prefixWord ++ tailWord_627772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627785 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 3, 6]
def baseStart_627785 : Nat := 118140960795 + 627785 * 2 ^ 59
def prefixEnd_627785 : Nat := 4983230072969 + 3 ^ 40 * 627785 * 2
def baseEnd_627785 : Nat := 107451817560977174000125

theorem tailTrace_627785 : CollatzResearch.WordTrace tailWord_627785 prefixEnd_627785 107451817560977174000125 := by
  unfold tailWord_627785
  simp only [CollatzResearch.WordTrace]
  refine ⟨22897200030649636987116809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15264800020433091324744539 22897200030649636987116809)
  ·
    refine ⟨17172900022987227740337607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22897200030649636987116809 17172900022987227740337607)
    ·
      refine ⟨25759350034480841610506411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17172900022987227740337607 25759350034480841610506411)
      ·
        refine ⟨38639025051721262415759617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25759350034480841610506411 38639025051721262415759617)
        ·
          refine ⟨28979268788790946811819713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38639025051721262415759617 28979268788790946811819713)
          ·
            refine ⟨21734451591593210108864785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28979268788790946811819713 21734451591593210108864785)
            ·
              refine ⟨16300838693694907581648589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21734451591593210108864785 16300838693694907581648589)
              ·
                refine ⟨6112814510135590343118221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16300838693694907581648589 6112814510135590343118221)
                ·
                  refine ⟨2292305441300846378669333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6112814510135590343118221 2292305441300846378669333)
                  ·
                    refine ⟨107451817560977174000125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2292305441300846378669333 107451817560977174000125)
                    ·
                      rfl

theorem cell23_627785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_627785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627785 prefixEnd_627785 := by exact prefixLift 627785
  have htrace : WordTrace (prefixWord ++ tailWord_627785) baseStart_627785 baseEnd_627785 := by
    simpa [prefixWord, tailWord_627785, baseEnd_627785] using wordTrace_append hprefix tailTrace_627785
  have hstable : (prefixWord ++ tailWord_627785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627785).length < 2 ^ (prefixWord ++ tailWord_627785).sum := by decide
  have hdescent : baseEnd_627785 < baseStart_627785 := by decide
  rcases family_descends (prefixWord ++ tailWord_627785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627786 : List Nat := [3, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_627786 : Nat := 118140960795 + 627786 * 2 ^ 59
def prefixEnd_627786 : Nat := 4983230072969 + 3 ^ 40 * 627786 * 2
def baseEnd_627786 : Nat := 322355966163586018087871

theorem tailTrace_627786 : CollatzResearch.WordTrace tailWord_627786 prefixEnd_627786 322355966163586018087871 := by
  unfold tailWord_627786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724309125911503539475803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15264824335764009438602141 5724309125911503539475803)
  ·
    refine ⟨8586463688867255309213705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5724309125911503539475803 8586463688867255309213705)
    ·
      refine ⟨6439847766650441481910279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8586463688867255309213705 6439847766650441481910279)
      ·
        refine ⟨9659771649975662222865419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6439847766650441481910279 9659771649975662222865419)
        ·
          refine ⟨14489657474963493334298129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9659771649975662222865419 14489657474963493334298129)
          ·
            refine ⟨10867243106222620000723597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14489657474963493334298129 10867243106222620000723597)
            ·
              refine ⟨4075216164833482500271349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10867243106222620000723597 4075216164833482500271349)
              ·
                refine ⟨382051515453138984400439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4075216164833482500271349 382051515453138984400439)
                ·
                  refine ⟨573077273179708476600659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382051515453138984400439 573077273179708476600659)
                  ·
                    refine ⟨859615909769562714900989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573077273179708476600659 859615909769562714900989)
                    ·
                      refine ⟨322355966163586018087871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859615909769562714900989 322355966163586018087871)
                      ·
                        rfl

theorem cell23_627786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_627786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627786 prefixEnd_627786 := by exact prefixLift 627786
  have htrace : WordTrace (prefixWord ++ tailWord_627786) baseStart_627786 baseEnd_627786 := by
    simpa [prefixWord, tailWord_627786, baseEnd_627786] using wordTrace_append hprefix tailTrace_627786
  have hstable : (prefixWord ++ tailWord_627786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627786).length < 2 ^ (prefixWord ++ tailWord_627786).sum := by decide
  have hdescent : baseEnd_627786 < baseStart_627786 := by decide
  rcases family_descends (prefixWord ++ tailWord_627786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627792 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 8, 2]
def baseStart_627792 : Nat := 118140960795 + 627792 * 2 ^ 59
def prefixEnd_627792 : Nat := 4983230072969 + 3 ^ 40 * 627792 * 2
def baseEnd_627792 : Nat := 322359047047512994612843

theorem tailTrace_627792 : CollatzResearch.WordTrace tailWord_627792 prefixEnd_627792 322359047047512994612843 := by
  unfold tailWord_627792
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448727670812138591310815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15264970227749518121747753 11448727670812138591310815)
  ·
    refine ⟨17173091506218207886966223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11448727670812138591310815 17173091506218207886966223)
    ·
      refine ⟨25759637259327311830449335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17173091506218207886966223 25759637259327311830449335)
      ·
        refine ⟨38639455888990967745674003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25759637259327311830449335 38639455888990967745674003)
        ·
          refine ⟨57959183833486451618511005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38639455888990967745674003 57959183833486451618511005)
          ·
            refine ⟨21734693937557419356941627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57959183833486451618511005 21734693937557419356941627)
            ·
              refine ⟨32602040906336129035412441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21734693937557419356941627 32602040906336129035412441)
              ·
                refine ⟨24451530679752096776559331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32602040906336129035412441 24451530679752096776559331)
                ·
                  refine ⟨36677296019628145164838997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24451530679752096776559331 36677296019628145164838997)
                  ·
                    refine ⟨429812062730017326150457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36677296019628145164838997 429812062730017326150457)
                    ·
                      refine ⟨322359047047512994612843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429812062730017326150457 322359047047512994612843)
                      ·
                        rfl

theorem cell23_627792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 8, 2].length) (baseStart_627792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627792 prefixEnd_627792 := by exact prefixLift 627792
  have htrace : WordTrace (prefixWord ++ tailWord_627792) baseStart_627792 baseEnd_627792 := by
    simpa [prefixWord, tailWord_627792, baseEnd_627792] using wordTrace_append hprefix tailTrace_627792
  have hstable : (prefixWord ++ tailWord_627792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627792).length < 2 ^ (prefixWord ++ tailWord_627792).sum := by decide
  have hdescent : baseEnd_627792 < baseStart_627792 := by decide
  rcases family_descends (prefixWord ++ tailWord_627792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627826 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_627826 : Nat := 118140960795 + 627826 * 2 ^ 59
def prefixEnd_627826 : Nat := 4983230072969 + 3 ^ 40 * 627826 * 2
def baseEnd_627826 : Nat := 322376505389765861587687

theorem tailTrace_627826 : CollatzResearch.WordTrace tailWord_627826 prefixEnd_627826 322376505389765861587687 := by
  unfold tailWord_627826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724673855875275247339833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15265796949000733992906221 5724673855875275247339833)
  ·
    refine ⟨4293505391906456435504875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5724673855875275247339833 4293505391906456435504875)
    ·
      refine ⟨6440258087859684653257313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4293505391906456435504875 6440258087859684653257313)
      ·
        refine ⟨4830193565894763489942985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6440258087859684653257313 4830193565894763489942985)
        ·
          refine ⟨3622645174421072617457239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4830193565894763489942985 3622645174421072617457239)
          ·
            refine ⟨5433967761631608926185859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622645174421072617457239 5433967761631608926185859)
            ·
              refine ⟨8150951642447413389278789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433967761631608926185859 8150951642447413389278789)
              ·
                refine ⟨1528303432958890010489773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8150951642447413389278789 1528303432958890010489773)
                ·
                  refine ⟨573113787359583753933665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1528303432958890010489773 573113787359583753933665)
                  ·
                    refine ⟨429835340519687815450249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 573113787359583753933665 429835340519687815450249)
                    ·
                      refine ⟨322376505389765861587687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429835340519687815450249 322376505389765861587687)
                      ·
                        rfl

theorem cell23_627826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_627826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627826 prefixEnd_627826 := by exact prefixLift 627826
  have htrace : WordTrace (prefixWord ++ tailWord_627826) baseStart_627826 baseEnd_627826 := by
    simpa [prefixWord, tailWord_627826, baseEnd_627826] using wordTrace_append hprefix tailTrace_627826
  have hstable : (prefixWord ++ tailWord_627826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627826).length < 2 ^ (prefixWord ++ tailWord_627826).sum := by decide
  have hdescent : baseEnd_627826 < baseStart_627826 := by decide
  rcases family_descends (prefixWord ++ tailWord_627826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627832 : List Nat := [2, 1, 2, 1, 1, 1, 8, 7]
def baseStart_627832 : Nat := 118140960795 + 627832 * 2 ^ 59
def prefixEnd_627832 : Nat := 4983230072969 + 3 ^ 40 * 627832 * 2
def baseEnd_627832 : Nat := 11939984676803438448617

theorem tailTrace_627832 : CollatzResearch.WordTrace tailWord_627832 prefixEnd_627832 11939984676803438448617 := by
  unfold tailWord_627832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11449457130739682007038875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15265942840986242676051833 11449457130739682007038875)
  ·
    refine ⟨17174185696109523010558313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11449457130739682007038875 17174185696109523010558313)
    ·
      refine ⟨12880639272082142257918735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17174185696109523010558313 12880639272082142257918735)
      ·
        refine ⟨19320958908123213386878103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12880639272082142257918735 19320958908123213386878103)
        ·
          refine ⟨28981438362184820080317155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19320958908123213386878103 28981438362184820080317155)
          ·
            refine ⟨43472157543277230120475733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28981438362184820080317155 43472157543277230120475733)
            ·
              refine ⟨509439346210280040474325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 43472157543277230120475733 509439346210280040474325)
              ·
                refine ⟨11939984676803438448617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 509439346210280040474325 11939984676803438448617)
                ·
                  rfl

theorem cell23_627832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 7].length) (baseStart_627832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627832 prefixEnd_627832 := by exact prefixLift 627832
  have htrace : WordTrace (prefixWord ++ tailWord_627832) baseStart_627832 baseEnd_627832 := by
    simpa [prefixWord, tailWord_627832, baseEnd_627832] using wordTrace_append hprefix tailTrace_627832
  have hstable : (prefixWord ++ tailWord_627832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627832).length < 2 ^ (prefixWord ++ tailWord_627832).sum := by decide
  have hdescent : baseEnd_627832 < baseStart_627832 := by decide
  rcases family_descends (prefixWord ++ tailWord_627832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627835 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6]
def baseStart_627835 : Nat := 118140960795 + 627835 * 2 ^ 59
def prefixEnd_627835 : Nat := 4983230072969 + 3 ^ 40 * 627835 * 2
def baseEnd_627835 : Nat := 322381126715656326375145

theorem tailTrace_627835 : CollatzResearch.WordTrace tailWord_627835 prefixEnd_627835 322381126715656326375145 := by
  unfold tailWord_627835
  simp only [CollatzResearch.WordTrace]
  refine ⟨22899023680468495526436959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15266015786978997017624639 22899023680468495526436959)
  ·
    refine ⟨34348535520702743289655439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22899023680468495526436959 34348535520702743289655439)
    ·
      refine ⟨51522803281054114934483159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34348535520702743289655439 51522803281054114934483159)
      ·
        refine ⟨77284204921581172401724739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51522803281054114934483159 77284204921581172401724739)
        ·
          refine ⟨115926307382371758602587109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77284204921581172401724739 115926307382371758602587109)
          ·
            refine ⟨21736182634194704737985083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115926307382371758602587109 21736182634194704737985083)
            ·
              refine ⟨32604273951292057106977625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21736182634194704737985083 32604273951292057106977625)
              ·
                refine ⟨24453205463469042830233219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32604273951292057106977625 24453205463469042830233219)
                ·
                  refine ⟨36679808195203564245349829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24453205463469042830233219 36679808195203564245349829)
                  ·
                    refine ⟨6877464036600668296003093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36679808195203564245349829 6877464036600668296003093)
                    ·
                      refine ⟨322381126715656326375145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6877464036600668296003093 322381126715656326375145)
                      ·
                        rfl

theorem cell23_627835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_627835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627835 prefixEnd_627835 := by exact prefixLift 627835
  have htrace : WordTrace (prefixWord ++ tailWord_627835) baseStart_627835 baseEnd_627835 := by
    simpa [prefixWord, tailWord_627835, baseEnd_627835] using wordTrace_append hprefix tailTrace_627835
  have hstable : (prefixWord ++ tailWord_627835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627835).length < 2 ^ (prefixWord ++ tailWord_627835).sum := by decide
  have hdescent : baseEnd_627835 < baseStart_627835 := by decide
  rcases family_descends (prefixWord ++ tailWord_627835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627859 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 3]
def baseStart_627859 : Nat := 118140960795 + 627859 * 2 ^ 59
def prefixEnd_627859 : Nat := 4983230072969 + 3 ^ 40 * 627859 * 2
def baseEnd_627859 : Nat := 322393450251364232475035

theorem tailTrace_627859 : CollatzResearch.WordTrace tailWord_627859 prefixEnd_627859 322393450251364232475035 := by
  unfold tailWord_627859
  simp only [CollatzResearch.WordTrace]
  refine ⟨22899899032381547625310631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15266599354921031750207087 22899899032381547625310631)
  ·
    refine ⟨34349848548572321437965947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22899899032381547625310631 34349848548572321437965947)
    ·
      refine ⟨51524772822858482156948921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34349848548572321437965947 51524772822858482156948921)
      ·
        refine ⟨38643579617143861617711691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51524772822858482156948921 38643579617143861617711691)
        ·
          refine ⟨57965369425715792426567537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38643579617143861617711691 57965369425715792426567537)
          ·
            refine ⟨43474027069286844319925653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57965369425715792426567537 43474027069286844319925653)
            ·
              refine ⟨2037845018872820827496515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43474027069286844319925653 2037845018872820827496515)
              ·
                refine ⟨3056767528309231241244773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037845018872820827496515 3056767528309231241244773)
                ·
                  refine ⟨573143911557980857733395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3056767528309231241244773 573143911557980857733395)
                  ·
                    refine ⟨859715867336971286600093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573143911557980857733395 859715867336971286600093)
                    ·
                      refine ⟨322393450251364232475035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859715867336971286600093 322393450251364232475035)
                      ·
                        rfl

theorem cell23_627859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 3].length) (baseStart_627859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627859 prefixEnd_627859 := by exact prefixLift 627859
  have htrace : WordTrace (prefixWord ++ tailWord_627859) baseStart_627859 baseEnd_627859 := by
    simpa [prefixWord, tailWord_627859, baseEnd_627859] using wordTrace_append hprefix tailTrace_627859
  have hstable : (prefixWord ++ tailWord_627859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627859).length < 2 ^ (prefixWord ++ tailWord_627859).sum := by decide
  have hdescent : baseEnd_627859 < baseStart_627859 := by decide
  rcases family_descends (prefixWord ++ tailWord_627859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627870 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_627870 : Nat := 118140960795 + 627870 * 2 ^ 59
def prefixEnd_627870 : Nat := 4983230072969 + 3 ^ 40 * 627870 * 2
def baseEnd_627870 : Nat := 107466366179521229812495

theorem tailTrace_627870 : CollatzResearch.WordTrace tailWord_627870 prefixEnd_627870 107466366179521229812495 := by
  unfold tailWord_627870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862537529417712062995133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15266866823561131002640709 2862537529417712062995133)
  ·
    refine ⟨1073451573531642023623175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2862537529417712062995133 1073451573531642023623175)
    ·
      refine ⟨1610177360297463035434763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073451573531642023623175 1610177360297463035434763)
      ·
        refine ⟨2415266040446194553152145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610177360297463035434763 2415266040446194553152145)
        ·
          refine ⟨1811449530334645914864109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2415266040446194553152145 1811449530334645914864109)
          ·
            refine ⟨679293573875492218074041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1811449530334645914864109 679293573875492218074041)
            ·
              refine ⟨509470180406619163555531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679293573875492218074041 509470180406619163555531)
              ·
                refine ⟨764205270609928745333297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509470180406619163555531 764205270609928745333297)
                ·
                  refine ⟨573153952957446558999973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764205270609928745333297 573153952957446558999973)
                  ·
                    refine ⟨107466366179521229812495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573153952957446558999973 107466366179521229812495)
                    ·
                      rfl

theorem cell23_627870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_627870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627870 prefixEnd_627870 := by exact prefixLift 627870
  have htrace : WordTrace (prefixWord ++ tailWord_627870) baseStart_627870 baseEnd_627870 := by
    simpa [prefixWord, tailWord_627870, baseEnd_627870] using wordTrace_append hprefix tailTrace_627870
  have hstable : (prefixWord ++ tailWord_627870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627870).length < 2 ^ (prefixWord ++ tailWord_627870).sum := by decide
  have hdescent : baseEnd_627870 < baseStart_627870 := by decide
  rcases family_descends (prefixWord ++ tailWord_627870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627959 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 4, 5, 2]
def baseStart_627959 : Nat := 118140960795 + 627959 * 2 ^ 59
def prefixEnd_627959 : Nat := 4983230072969 + 3 ^ 40 * 627959 * 2
def baseEnd_627959 : Nat := 322444798316813841224575

theorem tailTrace_627959 : CollatzResearch.WordTrace tailWord_627959 prefixEnd_627959 322444798316813841224575 := by
  unfold tailWord_627959
  simp only [CollatzResearch.WordTrace]
  refine ⟨22903546332019264703950931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15269030888012843135967287 22903546332019264703950931)
  ·
    refine ⟨34355319498028897055926397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22903546332019264703950931 34355319498028897055926397)
    ·
      refine ⟨12883244811760836395972399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34355319498028897055926397 12883244811760836395972399)
      ·
        refine ⟨19324867217641254593958599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12883244811760836395972399 19324867217641254593958599)
        ·
          refine ⟨28987300826461881890937899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19324867217641254593958599 28987300826461881890937899)
          ·
            refine ⟨43480951239692822836406849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28987300826461881890937899 43480951239692822836406849)
            ·
              refine ⟨32610713429769617127305137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43480951239692822836406849 32610713429769617127305137)
              ·
                refine ⟨24458035072327212845478853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32610713429769617127305137 24458035072327212845478853)
                ·
                  refine ⟨4585881576061352408527285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24458035072327212845478853 4585881576061352408527285)
                  ·
                    refine ⟨429926397755751788299433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4585881576061352408527285 429926397755751788299433)
                    ·
                      refine ⟨322444798316813841224575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429926397755751788299433 322444798316813841224575)
                      ·
                        rfl

theorem cell23_627959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_627959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627959 prefixEnd_627959 := by exact prefixLift 627959
  have htrace : WordTrace (prefixWord ++ tailWord_627959) baseStart_627959 baseEnd_627959 := by
    simpa [prefixWord, tailWord_627959, baseEnd_627959] using wordTrace_append hprefix tailTrace_627959
  have hstable : (prefixWord ++ tailWord_627959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627959).length < 2 ^ (prefixWord ++ tailWord_627959).sum := by decide
  have hdescent : baseEnd_627959 < baseStart_627959 := by decide
  rcases family_descends (prefixWord ++ tailWord_627959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627966 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_627966 : Nat := 118140960795 + 627966 * 2 ^ 59
def prefixEnd_627966 : Nat := 4983230072969 + 3 ^ 40 * 627966 * 2
def baseEnd_627966 : Nat := 322448392681395313837043

theorem tailTrace_627966 : CollatzResearch.WordTrace tailWord_627966 prefixEnd_627966 322448392681395313837043 := by
  unfold tailWord_627966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862975205374238112431969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15269201095329269932970501 2862975205374238112431969)
  ·
    refine ⟨2147231404030678584323977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2862975205374238112431969 2147231404030678584323977)
    ·
      refine ⟨1610423553023008938242983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2147231404030678584323977 1610423553023008938242983)
      ·
        refine ⟨2415635329534513407364475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610423553023008938242983 2415635329534513407364475)
        ·
          refine ⟨3623452994301770111046713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415635329534513407364475 3623452994301770111046713)
          ·
            refine ⟨2717589745726327583285035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3623452994301770111046713 2717589745726327583285035)
            ·
              refine ⟨4076384618589491374927553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717589745726327583285035 4076384618589491374927553)
              ·
                refine ⟨3057288463942118531195665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4076384618589491374927553 3057288463942118531195665)
                ·
                  refine ⟨2292966347956588898396749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3057288463942118531195665 2292966347956588898396749)
                  ·
                    refine ⟨859862380483720836898781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2292966347956588898396749 859862380483720836898781)
                    ·
                      refine ⟨322448392681395313837043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859862380483720836898781 322448392681395313837043)
                      ·
                        rfl

theorem cell23_627966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_627966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627966 prefixEnd_627966 := by exact prefixLift 627966
  have htrace : WordTrace (prefixWord ++ tailWord_627966) baseStart_627966 baseEnd_627966 := by
    simpa [prefixWord, tailWord_627966, baseEnd_627966] using wordTrace_append hprefix tailTrace_627966
  have hstable : (prefixWord ++ tailWord_627966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627966).length < 2 ^ (prefixWord ++ tailWord_627966).sum := by decide
  have hdescent : baseEnd_627966 < baseStart_627966 := by decide
  rcases family_descends (prefixWord ++ tailWord_627966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628026 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_628026 : Nat := 118140960795 + 628026 * 2 ^ 59
def prefixEnd_628026 : Nat := 4983230072969 + 3 ^ 40 * 628026 * 2
def baseEnd_628026 : Nat := 322479201520665079086767

theorem tailTrace_628026 : CollatzResearch.WordTrace tailWord_628026 prefixEnd_628026 322479201520665079086767 := by
  unfold tailWord_628026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5726497505694133786659983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15270660015184356764426621 5726497505694133786659983)
  ·
    refine ⟨8589746258541200679989975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5726497505694133786659983 8589746258541200679989975)
    ·
      refine ⟨12884619387811801019984963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8589746258541200679989975 12884619387811801019984963)
      ·
        refine ⟨19326929081717701529977445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12884619387811801019984963 19326929081717701529977445)
        ·
          refine ⟨3623799202822069036870771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19326929081717701529977445 3623799202822069036870771)
          ·
            refine ⟨5435698804233103555306157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623799202822069036870771 5435698804233103555306157)
            ·
              refine ⟨2038387051587413833239809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5435698804233103555306157 2038387051587413833239809)
              ·
                refine ⟨1528790288690560374929857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038387051587413833239809 1528790288690560374929857)
                ·
                  refine ⟨1146592716517920281197393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528790288690560374929857 1146592716517920281197393)
                  ·
                    refine ⟨859944537388440210898045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1146592716517920281197393 859944537388440210898045)
                    ·
                      refine ⟨322479201520665079086767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859944537388440210898045 322479201520665079086767)
                      ·
                        rfl

theorem cell23_628026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_628026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628026 prefixEnd_628026 := by exact prefixLift 628026
  have htrace : WordTrace (prefixWord ++ tailWord_628026) baseStart_628026 baseEnd_628026 := by
    simpa [prefixWord, tailWord_628026, baseEnd_628026] using wordTrace_append hprefix tailTrace_628026
  have hstable : (prefixWord ++ tailWord_628026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628026).length < 2 ^ (prefixWord ++ tailWord_628026).sum := by decide
  have hdescent : baseEnd_628026 < baseStart_628026 := by decide
  rcases family_descends (prefixWord ++ tailWord_628026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628033 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 3, 4]
def baseStart_628033 : Nat := 118140960795 + 628033 * 2 ^ 59
def prefixEnd_628033 : Nat := 4983230072969 + 3 ^ 40 * 628033 * 2
def baseEnd_628033 : Nat := 107494265295082183899745

theorem tailTrace_628033 : CollatzResearch.WordTrace tailWord_628033 prefixEnd_628033 107494265295082183899745 := by
  unfold tailWord_628033
  simp only [CollatzResearch.WordTrace]
  refine ⟨22906245333751175342144753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15270830222500783561429835 22906245333751175342144753)
  ·
    refine ⟨17179684000313381506608565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22906245333751175342144753 17179684000313381506608565)
    ·
      refine ⟨1610595375029379516244553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17179684000313381506608565 1610595375029379516244553)
      ·
        refine ⟨1207946531272034637183415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1610595375029379516244553 1207946531272034637183415)
        ·
          refine ⟨1811919796908051955775123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207946531272034637183415 1811919796908051955775123)
          ·
            refine ⟨2717879695362077933662685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811919796908051955775123 2717879695362077933662685)
            ·
              refine ⟨1019204885760779225123507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2717879695362077933662685 1019204885760779225123507)
              ·
                refine ⟨1528807328641168837685261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019204885760779225123507 1528807328641168837685261)
                ·
                  refine ⟨573302748240438314131973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1528807328641168837685261 573302748240438314131973)
                  ·
                    refine ⟨107494265295082183899745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573302748240438314131973 107494265295082183899745)
                    ·
                      rfl

theorem cell23_628033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_628033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628033 prefixEnd_628033 := by exact prefixLift 628033
  have htrace : WordTrace (prefixWord ++ tailWord_628033) baseStart_628033 baseEnd_628033 := by
    simpa [prefixWord, tailWord_628033, baseEnd_628033] using wordTrace_append hprefix tailTrace_628033
  have hstable : (prefixWord ++ tailWord_628033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628033).length < 2 ^ (prefixWord ++ tailWord_628033).sum := by decide
  have hdescent : baseEnd_628033 < baseStart_628033 := by decide
  rcases family_descends (prefixWord ++ tailWord_628033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628056 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_628056 : Nat := 118140960795 + 628056 * 2 ^ 59
def prefixEnd_628056 : Nat := 4983230072969 + 3 ^ 40 * 628056 * 2
def baseEnd_628056 : Nat := 322494605940299961711629

theorem tailTrace_628056 : CollatzResearch.WordTrace tailWord_628056 prefixEnd_628056 322494605940299961711629 := by
  unfold tailWord_628056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11453542106333925135116011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15271389475111900180154681 11453542106333925135116011)
  ·
    refine ⟨17180313159500887702674017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11453542106333925135116011 17180313159500887702674017)
    ·
      refine ⟨12885234869625665777005513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17180313159500887702674017 12885234869625665777005513)
      ·
        refine ⟨9663926152219249332754135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12885234869625665777005513 9663926152219249332754135)
        ·
          refine ⟨14495889228328873999131203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663926152219249332754135 14495889228328873999131203)
          ·
            refine ⟨21743833842493310998696805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14495889228328873999131203 21743833842493310998696805)
            ·
              refine ⟨4076968845467495812255651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21743833842493310998696805 4076968845467495812255651)
              ·
                refine ⟨6115453268201243718383477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4076968845467495812255651 6115453268201243718383477)
                ·
                  refine ⟨573323743893866598598451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6115453268201243718383477 573323743893866598598451)
                  ·
                    refine ⟨859985615840799897897677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573323743893866598598451 859985615840799897897677)
                    ·
                      refine ⟨322494605940299961711629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859985615840799897897677 322494605940299961711629)
                      ·
                        rfl

theorem cell23_628056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_628056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628056 prefixEnd_628056 := by exact prefixLift 628056
  have htrace : WordTrace (prefixWord ++ tailWord_628056) baseStart_628056 baseEnd_628056 := by
    simpa [prefixWord, tailWord_628056, baseEnd_628056] using wordTrace_append hprefix tailTrace_628056
  have hstable : (prefixWord ++ tailWord_628056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628056).length < 2 ^ (prefixWord ++ tailWord_628056).sum := by decide
  have hdescent : baseEnd_628056 < baseStart_628056 := by decide
  rcases family_descends (prefixWord ++ tailWord_628056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628113 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 3, 2, 2]
def baseStart_628113 : Nat := 118140960795 + 628113 * 2 ^ 59
def prefixEnd_628113 : Nat := 4983230072969 + 3 ^ 40 * 628113 * 2
def baseEnd_628113 : Nat := 322523874337606238698867

theorem tailTrace_628113 : CollatzResearch.WordTrace tailWord_628113 prefixEnd_628113 322523874337606238698867 := by
  unfold tailWord_628113
  simp only [CollatzResearch.WordTrace]
  refine ⟨22909163173461349005056993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15272775448974232670037995 22909163173461349005056993)
  ·
    refine ⟨17181872380096011753792745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22909163173461349005056993 17181872380096011753792745)
    ·
      refine ⟨12886404285072008815344559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17181872380096011753792745 12886404285072008815344559)
      ·
        refine ⟨19329606427608013223016839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12886404285072008815344559 19329606427608013223016839)
        ·
          refine ⟨28994409641412019834525259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19329606427608013223016839 28994409641412019834525259)
          ·
            refine ⟨43491614462118029751787889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28994409641412019834525259 43491614462118029751787889)
            ·
              refine ⟨32618710846588522313840917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43491614462118029751787889 32618710846588522313840917)
              ·
                refine ⟨1529002070933836983461293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32618710846588522313840917 1529002070933836983461293)
                ·
                  refine ⟨573375776600188868797985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1529002070933836983461293 573375776600188868797985)
                  ·
                    refine ⟨430031832450141651598489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 573375776600188868797985 430031832450141651598489)
                    ·
                      refine ⟨322523874337606238698867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430031832450141651598489 322523874337606238698867)
                      ·
                        rfl

theorem cell23_628113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_628113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628113 prefixEnd_628113 := by exact prefixLift 628113
  have htrace : WordTrace (prefixWord ++ tailWord_628113) baseStart_628113 baseEnd_628113 := by
    simpa [prefixWord, tailWord_628113, baseEnd_628113] using wordTrace_append hprefix tailTrace_628113
  have hstable : (prefixWord ++ tailWord_628113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628113).length < 2 ^ (prefixWord ++ tailWord_628113).sum := by decide
  have hdescent : baseEnd_628113 < baseStart_628113 := by decide
  rcases family_descends (prefixWord ++ tailWord_628113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628124 : List Nat := [2, 2, 3, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_628124 : Nat := 118140960795 + 628124 * 2 ^ 59
def prefixEnd_628124 : Nat := 4983230072969 + 3 ^ 40 * 628124 * 2
def baseEnd_628124 : Nat := 322529522624805695661317

theorem tailTrace_628124 : CollatzResearch.WordTrace tailWord_628124 prefixEnd_628124 322529522624805695661317 := by
  unfold tailWord_628124
  simp only [CollatzResearch.WordTrace]
  refine ⟨11454782188210748941853713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15273042917614331922471617 11454782188210748941853713)
  ·
    refine ⟨8591086641158061706390285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11454782188210748941853713 8591086641158061706390285)
    ·
      refine ⟨3221657490434273139896357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8591086641158061706390285 3221657490434273139896357)
      ·
        refine ⟨604060779456426213730567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3221657490434273139896357 604060779456426213730567)
        ·
          refine ⟨906091169184639320595851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604060779456426213730567 906091169184639320595851)
          ·
            refine ⟨1359136753776958980893777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906091169184639320595851 1359136753776958980893777)
            ·
              refine ⟨1019352565332719235670333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359136753776958980893777 1019352565332719235670333)
              ·
                refine ⟨382257211999769713376375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019352565332719235670333 382257211999769713376375)
                ·
                  refine ⟨573385817999654570064563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382257211999769713376375 573385817999654570064563)
                  ·
                    refine ⟨860078726999481855096845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573385817999654570064563 860078726999481855096845)
                    ·
                      refine ⟨322529522624805695661317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860078726999481855096845 322529522624805695661317)
                      ·
                        rfl

theorem cell23_628124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_628124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628124 prefixEnd_628124 := by exact prefixLift 628124
  have htrace : WordTrace (prefixWord ++ tailWord_628124) baseStart_628124 baseEnd_628124 := by
    simpa [prefixWord, tailWord_628124, baseEnd_628124] using wordTrace_append hprefix tailTrace_628124
  have hstable : (prefixWord ++ tailWord_628124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628124).length < 2 ^ (prefixWord ++ tailWord_628124).sum := by decide
  have hdescent : baseEnd_628124 < baseStart_628124 := by decide
  rcases family_descends (prefixWord ++ tailWord_628124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628130 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_628130 : Nat := 118140960795 + 628130 * 2 ^ 59
def prefixEnd_628130 : Nat := 4983230072969 + 3 ^ 40 * 628130 * 2
def baseEnd_628130 : Nat := 322532603508732672186289

theorem tailTrace_628130 : CollatzResearch.WordTrace tailWord_628130 prefixEnd_628130 322532603508732672186289 := by
  unfold tailWord_628130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727445803599940227106461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15273188809599840605617229 5727445803599940227106461)
  ·
    refine ⟨2147792176349977585164923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5727445803599940227106461 2147792176349977585164923)
    ·
      refine ⟨3221688264524966377747385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147792176349977585164923 3221688264524966377747385)
      ·
        refine ⟨2416266198393724783310539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3221688264524966377747385 2416266198393724783310539)
        ·
          refine ⟨3624399297590587174965809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416266198393724783310539 3624399297590587174965809)
          ·
            refine ⟨2718299473192940381224357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3624399297590587174965809 2718299473192940381224357)
            ·
              refine ⟨509681151223676321479567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2718299473192940381224357 509681151223676321479567)
              ·
                refine ⟨764521726835514482219351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509681151223676321479567 764521726835514482219351)
                ·
                  refine ⟨1146782590253271723329027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764521726835514482219351 1146782590253271723329027)
                  ·
                    refine ⟨1720173885379907584993541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1146782590253271723329027 1720173885379907584993541)
                    ·
                      refine ⟨322532603508732672186289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1720173885379907584993541 322532603508732672186289)
                      ·
                        rfl

theorem cell23_628130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_628130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628130 prefixEnd_628130 := by exact prefixLift 628130
  have htrace : WordTrace (prefixWord ++ tailWord_628130) baseStart_628130 baseEnd_628130 := by
    simpa [prefixWord, tailWord_628130, baseEnd_628130] using wordTrace_append hprefix tailTrace_628130
  have hstable : (prefixWord ++ tailWord_628130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628130).length < 2 ^ (prefixWord ++ tailWord_628130).sum := by decide
  have hdescent : baseEnd_628130 < baseStart_628130 := by decide
  rcases family_descends (prefixWord ++ tailWord_628130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628159 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_628159 : Nat := 118140960795 + 628159 * 2 ^ 59
def prefixEnd_628159 : Nat := 4983230072969 + 3 ^ 40 * 628159 * 2
def baseEnd_628159 : Nat := 322547494447713058723655

theorem tailTrace_628159 : CollatzResearch.WordTrace tailWord_628159 prefixEnd_628159 322547494447713058723655 := by
  unfold tailWord_628159
  simp only [CollatzResearch.WordTrace]
  refine ⟨22910840931294698861231531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15273893954196465907487687 22910840931294698861231531)
  ·
    refine ⟨34366261396942048291847297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22910840931294698861231531 34366261396942048291847297)
    ·
      refine ⟨25774696047706536218885473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34366261396942048291847297 25774696047706536218885473)
      ·
        refine ⟨19331022035779902164164105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25774696047706536218885473 19331022035779902164164105)
        ·
          refine ⟨14498266526834926623123079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19331022035779902164164105 14498266526834926623123079)
          ·
            refine ⟨21747399790252389934684619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14498266526834926623123079 21747399790252389934684619)
            ·
              refine ⟨32621099685378584902026929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21747399790252389934684619 32621099685378584902026929)
              ·
                refine ⟨24465824764033938676520197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32621099685378584902026929 24465824764033938676520197)
                ·
                  refine ⟨4587342143256363501847537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24465824764033938676520197 4587342143256363501847537)
                  ·
                    refine ⟨3440506607442272626385653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4587342143256363501847537 3440506607442272626385653)
                    ·
                      refine ⟨322547494447713058723655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3440506607442272626385653 322547494447713058723655)
                      ·
                        rfl

theorem cell23_628159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_628159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628159 prefixEnd_628159 := by exact prefixLift 628159
  have htrace : WordTrace (prefixWord ++ tailWord_628159) baseStart_628159 baseEnd_628159 := by
    simpa [prefixWord, tailWord_628159, baseEnd_628159] using wordTrace_append hprefix tailTrace_628159
  have hstable : (prefixWord ++ tailWord_628159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628159).length < 2 ^ (prefixWord ++ tailWord_628159).sum := by decide
  have hdescent : baseEnd_628159 < baseStart_628159 := by decide
  rcases family_descends (prefixWord ++ tailWord_628159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628163 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 3]
def baseStart_628163 : Nat := 118140960795 + 628163 * 2 ^ 59
def prefixEnd_628163 : Nat := 4983230072969 + 3 ^ 40 * 628163 * 2
def baseEnd_628163 : Nat := 322549548370331043073637

theorem tailTrace_628163 : CollatzResearch.WordTrace tailWord_628163 prefixEnd_628163 322549548370331043073637 := by
  unfold tailWord_628163
  simp only [CollatzResearch.WordTrace]
  refine ⟨22910986823280207544377143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15273991215520138362918095 22910986823280207544377143)
  ·
    refine ⟨34366480234920311316565715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22910986823280207544377143 34366480234920311316565715)
    ·
      refine ⟨51549720352380466974848573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34366480234920311316565715 51549720352380466974848573)
      ·
        refine ⟨19331145132142675115568215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51549720352380466974848573 19331145132142675115568215)
        ·
          refine ⟨28996717698214012673352323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19331145132142675115568215 28996717698214012673352323)
          ·
            refine ⟨43495076547321019010028485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28996717698214012673352323 43495076547321019010028485)
            ·
              refine ⟨8155326852622691064380341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43495076547321019010028485 8155326852622691064380341)
              ·
                refine ⟨764561892433377287285657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8155326852622691064380341 764561892433377287285657)
                ·
                  refine ⟨573421419325032965464243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764561892433377287285657 573421419325032965464243)
                  ·
                    refine ⟨860132128987549448196365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573421419325032965464243 860132128987549448196365)
                    ·
                      refine ⟨322549548370331043073637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860132128987549448196365 322549548370331043073637)
                      ·
                        rfl

theorem cell23_628163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_628163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628163 prefixEnd_628163 := by exact prefixLift 628163
  have htrace : WordTrace (prefixWord ++ tailWord_628163) baseStart_628163 baseEnd_628163 := by
    simpa [prefixWord, tailWord_628163, baseEnd_628163] using wordTrace_append hprefix tailTrace_628163
  have hstable : (prefixWord ++ tailWord_628163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628163).length < 2 ^ (prefixWord ++ tailWord_628163).sum := by decide
  have hdescent : baseEnd_628163 < baseStart_628163 := by decide
  rcases family_descends (prefixWord ++ tailWord_628163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628206 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_628206 : Nat := 118140960795 + 628206 * 2 ^ 59
def prefixEnd_628206 : Nat := 4983230072969 + 3 ^ 40 * 628206 * 2
def baseEnd_628206 : Nat := 322571628038474374835939

theorem tailTrace_628206 : CollatzResearch.WordTrace tailWord_628206 prefixEnd_628206 322571628038474374835939 := by
  unfold tailWord_628206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864069395265553236024059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15275036774749617258794981 2864069395265553236024059)
  ·
    refine ⟨4296104092898329854036089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2864069395265553236024059 4296104092898329854036089)
    ·
      refine ⟨3222078069673747390527067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4296104092898329854036089 3222078069673747390527067)
      ·
        refine ⟨4833117104510621085790601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222078069673747390527067 4833117104510621085790601)
        ·
          refine ⟨3624837828382965814342951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4833117104510621085790601 3624837828382965814342951)
          ·
            refine ⟨5437256742574448721514427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624837828382965814342951 5437256742574448721514427)
            ·
              refine ⟨8155885113861673082271641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437256742574448721514427 8155885113861673082271641)
              ·
                refine ⟨6116913835396254811703731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8155885113861673082271641 6116913835396254811703731)
                ·
                  refine ⟨9175370753094382217555597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6116913835396254811703731 9175370753094382217555597)
                  ·
                    refine ⟨3440764032410393331583349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9175370753094382217555597 3440764032410393331583349)
                    ·
                      refine ⟨322571628038474374835939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3440764032410393331583349 322571628038474374835939)
                      ·
                        rfl

theorem cell23_628206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_628206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628206 prefixEnd_628206 := by exact prefixLift 628206
  have htrace : WordTrace (prefixWord ++ tailWord_628206) baseStart_628206 baseEnd_628206 := by
    simpa [prefixWord, tailWord_628206, baseEnd_628206] using wordTrace_append hprefix tailTrace_628206
  have hstable : (prefixWord ++ tailWord_628206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628206).length < 2 ^ (prefixWord ++ tailWord_628206).sum := by decide
  have hdescent : baseEnd_628206 < baseStart_628206 := by decide
  rcases family_descends (prefixWord ++ tailWord_628206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628214 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_628214 : Nat := 118140960795 + 628214 * 2 ^ 59
def prefixEnd_628214 : Nat := 4983230072969 + 3 ^ 40 * 628214 * 2
def baseEnd_628214 : Nat := 322575735883710343535903

theorem tailTrace_628214 : CollatzResearch.WordTrace tailWord_628214 prefixEnd_628214 322575735883710343535903 := by
  unfold tailWord_628214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432052934130965203405231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15275231297396962169655797 1432052934130965203405231)
  ·
    refine ⟨2148079401196447805107847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1432052934130965203405231 2148079401196447805107847)
    ·
      refine ⟨3222119101794671707661771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148079401196447805107847 3222119101794671707661771)
      ·
        refine ⟨4833178652692007561492657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222119101794671707661771 4833178652692007561492657)
        ·
          refine ⟨3624883989519005671119493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4833178652692007561492657 3624883989519005671119493)
          ·
            refine ⟨679665748034813563334905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3624883989519005671119493 679665748034813563334905)
            ·
              refine ⟨509749311026110172501179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679665748034813563334905 509749311026110172501179)
              ·
                refine ⟨764623966539165258751769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509749311026110172501179 764623966539165258751769)
                ·
                  refine ⟨573467974904373944063827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764623966539165258751769 573467974904373944063827)
                  ·
                    refine ⟨860201962356560916095741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573467974904373944063827 860201962356560916095741)
                    ·
                      refine ⟨322575735883710343535903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860201962356560916095741 322575735883710343535903)
                      ·
                        rfl

theorem cell23_628214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_628214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628214 prefixEnd_628214 := by exact prefixLift 628214
  have htrace : WordTrace (prefixWord ++ tailWord_628214) baseStart_628214 baseEnd_628214 := by
    simpa [prefixWord, tailWord_628214, baseEnd_628214] using wordTrace_append hprefix tailTrace_628214
  have hstable : (prefixWord ++ tailWord_628214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628214).length < 2 ^ (prefixWord ++ tailWord_628214).sum := by decide
  have hdescent : baseEnd_628214 < baseStart_628214 := by decide
  rcases family_descends (prefixWord ++ tailWord_628214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628219 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9]
def baseStart_628219 : Nat := 118140960795 + 628219 * 2 ^ 59
def prefixEnd_628219 : Nat := 4983230072969 + 3 ^ 40 * 628219 * 2
def baseEnd_628219 : Nat := 322578303286982823973379

theorem tailTrace_628219 : CollatzResearch.WordTrace tailWord_628219 prefixEnd_628219 322578303286982823973379 := by
  unfold tailWord_628219
  simp only [CollatzResearch.WordTrace]
  refine ⟨22913029311077329108415711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15275352874051552738943807 22913029311077329108415711)
  ·
    refine ⟨34369543966615993662623567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22913029311077329108415711 34369543966615993662623567)
    ·
      refine ⟨51554315949923990493935351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34369543966615993662623567 51554315949923990493935351)
      ·
        refine ⟨77331473924885985740903027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51554315949923990493935351 77331473924885985740903027)
        ·
          refine ⟨115997210887328978611354541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77331473924885985740903027 115997210887328978611354541)
          ·
            refine ⟨43498954082748366979257953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115997210887328978611354541 43498954082748366979257953)
            ·
              refine ⟨32624215562061275234443465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43498954082748366979257953 32624215562061275234443465)
              ·
                refine ⟨24468161671545956425832599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32624215562061275234443465 24468161671545956425832599)
                ·
                  refine ⟨36702242507318934638748899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24468161671545956425832599 36702242507318934638748899)
                  ·
                    refine ⟨55053363760978401958123349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36702242507318934638748899 55053363760978401958123349)
                    ·
                      refine ⟨322578303286982823973379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 55053363760978401958123349 322578303286982823973379)
                      ·
                        rfl

theorem cell23_628219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_628219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628219 prefixEnd_628219 := by exact prefixLift 628219
  have htrace : WordTrace (prefixWord ++ tailWord_628219) baseStart_628219 baseEnd_628219 := by
    simpa [prefixWord, tailWord_628219, baseEnd_628219] using wordTrace_append hprefix tailTrace_628219
  have hstable : (prefixWord ++ tailWord_628219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628219).length < 2 ^ (prefixWord ++ tailWord_628219).sum := by decide
  have hdescent : baseEnd_628219 < baseStart_628219 := by decide
  rcases family_descends (prefixWord ++ tailWord_628219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628253 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_628253 : Nat := 118140960795 + 628253 * 2 ^ 59
def prefixEnd_628253 : Nat := 4983230072969 + 3 ^ 40 * 628253 * 2
def baseEnd_628253 : Nat := 322595761629235690948223

theorem tailTrace_628253 : CollatzResearch.WordTrace tailWord_628253 prefixEnd_628253 322595761629235690948223 := by
  unfold tailWord_628253
  simp only [CollatzResearch.WordTrace]
  refine ⟨22914269392954152915153413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15276179595302768610102275 22914269392954152915153413)
  ·
    refine ⟨4296425511178903671591265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22914269392954152915153413 4296425511178903671591265)
    ·
      refine ⟨3222319133384177753693449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4296425511178903671591265 3222319133384177753693449)
      ·
        refine ⟨2416739350038133315270087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3222319133384177753693449 2416739350038133315270087)
        ·
          refine ⟨3625109025057199972905131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416739350038133315270087 3625109025057199972905131)
          ·
            refine ⟨5437663537585799959357697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625109025057199972905131 5437663537585799959357697)
            ·
              refine ⟨4078247653189349969518273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437663537585799959357697 4078247653189349969518273)
              ·
                refine ⟨3058685739892012477138705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4078247653189349969518273 3058685739892012477138705)
                ·
                  refine ⟨2294014304919009357854029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058685739892012477138705 2294014304919009357854029)
                  ·
                    refine ⟨860255364344628509195261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294014304919009357854029 860255364344628509195261)
                    ·
                      refine ⟨322595761629235690948223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860255364344628509195261 322595761629235690948223)
                      ·
                        rfl

theorem cell23_628253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_628253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628253 prefixEnd_628253 := by exact prefixLift 628253
  have htrace : WordTrace (prefixWord ++ tailWord_628253) baseStart_628253 baseEnd_628253 := by
    simpa [prefixWord, tailWord_628253, baseEnd_628253] using wordTrace_append hprefix tailTrace_628253
  have hstable : (prefixWord ++ tailWord_628253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628253).length < 2 ^ (prefixWord ++ tailWord_628253).sum := by decide
  have hdescent : baseEnd_628253 < baseStart_628253 := by decide
  rcases family_descends (prefixWord ++ tailWord_628253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628270 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_628270 : Nat := 118140960795 + 628270 * 2 ^ 59
def prefixEnd_628270 : Nat := 4983230072969 + 3 ^ 40 * 628270 * 2
def baseEnd_628270 : Nat := 322604490800362124435645

theorem tailTrace_628270 : CollatzResearch.WordTrace tailWord_628270 prefixEnd_628270 322604490800362124435645 := by
  unfold tailWord_628270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864361179236570602315283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15276592955928376545681509 2864361179236570602315283)
  ·
    refine ⟨4296541768854855903472925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2864361179236570602315283 4296541768854855903472925)
    ·
      refine ⟨1611203163320570963802347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4296541768854855903472925 1611203163320570963802347)
      ·
        refine ⟨2416804744980856445703521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611203163320570963802347 2416804744980856445703521)
        ·
          refine ⟨1812603558735642334277641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2416804744980856445703521 1812603558735642334277641)
          ·
            refine ⟨1359452669051731750708231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812603558735642334277641 1359452669051731750708231)
            ·
              refine ⟨2039179003577597626062347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359452669051731750708231 2039179003577597626062347)
              ·
                refine ⟨3058768505366396439093521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039179003577597626062347 3058768505366396439093521)
                ·
                  refine ⟨2294076379024797329320141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058768505366396439093521 2294076379024797329320141)
                  ·
                    refine ⟨860278642134298998495053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2294076379024797329320141 860278642134298998495053)
                    ·
                      refine ⟨322604490800362124435645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860278642134298998495053 322604490800362124435645)
                      ·
                        rfl

theorem cell23_628270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_628270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628270 prefixEnd_628270 := by exact prefixLift 628270
  have htrace : WordTrace (prefixWord ++ tailWord_628270) baseStart_628270 baseEnd_628270 := by
    simpa [prefixWord, tailWord_628270, baseEnd_628270] using wordTrace_append hprefix tailTrace_628270
  have hstable : (prefixWord ++ tailWord_628270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628270).length < 2 ^ (prefixWord ++ tailWord_628270).sum := by decide
  have hdescent : baseEnd_628270 < baseStart_628270 := by decide
  rcases family_descends (prefixWord ++ tailWord_628270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628293 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 1, 6, 2]
def baseStart_628293 : Nat := 118140960795 + 628293 * 2 ^ 59
def prefixEnd_628293 : Nat := 4983230072969 + 3 ^ 40 * 628293 * 2
def baseEnd_628293 : Nat := 322616300855415534448039

theorem tailTrace_628293 : CollatzResearch.WordTrace tailWord_628293 prefixEnd_628293 322616300855415534448039 := by
  unfold tailWord_628293
  simp only [CollatzResearch.WordTrace]
  refine ⟨22915728312809239746609533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15277152208539493164406355 22915728312809239746609533)
  ·
    refine ⟨8593398117303464904978575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22915728312809239746609533 8593398117303464904978575)
    ·
      refine ⟨12890097175955197357467863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8593398117303464904978575 12890097175955197357467863)
      ·
        refine ⟨19335145763932796036201795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12890097175955197357467863 19335145763932796036201795)
        ·
          refine ⟨29002718645899194054302693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19335145763932796036201795 29002718645899194054302693)
          ·
            refine ⟨5438009746106098885181755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29002718645899194054302693 5438009746106098885181755)
            ·
              refine ⟨8157014619159148327772633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438009746106098885181755 8157014619159148327772633)
              ·
                refine ⟨6117760964369361245829475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8157014619159148327772633 6117760964369361245829475)
                ·
                  refine ⟨9176641446554041868744213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6117760964369361245829475 9176641446554041868744213)
                  ·
                    refine ⟨430155067807220712597385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9176641446554041868744213 430155067807220712597385)
                    ·
                      refine ⟨322616300855415534448039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430155067807220712597385 322616300855415534448039)
                      ·
                        rfl

theorem cell23_628293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_628293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628293 prefixEnd_628293 := by exact prefixLift 628293
  have htrace : WordTrace (prefixWord ++ tailWord_628293) baseStart_628293 baseEnd_628293 := by
    simpa [prefixWord, tailWord_628293, baseEnd_628293] using wordTrace_append hprefix tailTrace_628293
  have hstable : (prefixWord ++ tailWord_628293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628293).length < 2 ^ (prefixWord ++ tailWord_628293).sum := by decide
  have hdescent : baseEnd_628293 < baseStart_628293 := by decide
  rcases family_descends (prefixWord ++ tailWord_628293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628294 : List Nat := [6, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_628294 : Nat := 118140960795 + 628294 * 2 ^ 59
def prefixEnd_628294 : Nat := 4983230072969 + 3 ^ 40 * 628294 * 2
def baseEnd_628294 : Nat := 35846312704007781170615

theorem tailTrace_628294 : CollatzResearch.WordTrace tailWord_628294 prefixEnd_628294 35846312704007781170615 := by
  unfold tailWord_628294
  simp only [CollatzResearch.WordTrace]
  refine ⟨716117649556425528668623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15277176523870411278263957 716117649556425528668623)
  ·
    refine ⟨1074176474334638293002935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 716117649556425528668623 1074176474334638293002935)
    ·
      refine ⟨1611264711501957439504403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1074176474334638293002935 1611264711501957439504403)
      ·
        refine ⟨2416897067252936159256605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611264711501957439504403 2416897067252936159256605)
        ·
          refine ⟨906336400219851059721227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2416897067252936159256605 906336400219851059721227)
          ·
            refine ⟨1359504600329776589581841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906336400219851059721227 1359504600329776589581841)
            ·
              refine ⟨1019628450247332442186381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359504600329776589581841 1019628450247332442186381)
              ·
                refine ⟨382360668842749665819893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019628450247332442186381 382360668842749665819893)
                ·
                  refine ⟨35846312704007781170615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382360668842749665819893 35846312704007781170615)
                  ·
                    rfl

theorem cell23_628294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_628294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628294 prefixEnd_628294 := by exact prefixLift 628294
  have htrace : WordTrace (prefixWord ++ tailWord_628294) baseStart_628294 baseEnd_628294 := by
    simpa [prefixWord, tailWord_628294, baseEnd_628294] using wordTrace_append hprefix tailTrace_628294
  have hstable : (prefixWord ++ tailWord_628294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628294).length < 2 ^ (prefixWord ++ tailWord_628294).sum := by decide
  have hdescent : baseEnd_628294 < baseStart_628294 := by decide
  rcases family_descends (prefixWord ++ tailWord_628294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628313 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 3]
def baseStart_628313 : Nat := 118140960795 + 628313 * 2 ^ 59
def prefixEnd_628313 : Nat := 4983230072969 + 3 ^ 40 * 628313 * 2
def baseEnd_628313 : Nat := 322626570468505456197947

theorem tailTrace_628313 : CollatzResearch.WordTrace tailWord_628313 prefixEnd_628313 322626570468505456197947 := by
  unfold tailWord_628313
  simp only [CollatzResearch.WordTrace]
  refine ⟨22916457772736783162337593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15277638515157855441558395 22916457772736783162337593)
  ·
    refine ⟨17187343329552587371753195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22916457772736783162337593 17187343329552587371753195)
    ·
      refine ⟨25781014994328881057629793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17187343329552587371753195 25781014994328881057629793)
      ·
        refine ⟨19335761245746660793222345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25781014994328881057629793 19335761245746660793222345)
        ·
          refine ⟨14501820934309995594916759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19335761245746660793222345 14501820934309995594916759)
          ·
            refine ⟨21752731401464993392375139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14501820934309995594916759 21752731401464993392375139)
            ·
              refine ⟨32629097102197490088562709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21752731401464993392375139 32629097102197490088562709)
              ·
                refine ⟨1529488926665507347901377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32629097102197490088562709 1529488926665507347901377)
                ·
                  refine ⟨1147116694999130510926033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1529488926665507347901377 1147116694999130510926033)
                  ·
                    refine ⟨860337521249347883194525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147116694999130510926033 860337521249347883194525)
                    ·
                      refine ⟨322626570468505456197947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860337521249347883194525 322626570468505456197947)
                      ·
                        rfl

theorem cell23_628313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_628313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628313 prefixEnd_628313 := by exact prefixLift 628313
  have htrace : WordTrace (prefixWord ++ tailWord_628313) baseStart_628313 baseEnd_628313 := by
    simpa [prefixWord, tailWord_628313, baseEnd_628313] using wordTrace_append hprefix tailTrace_628313
  have hstable : (prefixWord ++ tailWord_628313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628313).length < 2 ^ (prefixWord ++ tailWord_628313).sum := by decide
  have hdescent : baseEnd_628313 < baseStart_628313 := by decide
  rcases family_descends (prefixWord ++ tailWord_628313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628363 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 1, 5]
def baseStart_628363 : Nat := 118140960795 + 628363 * 2 ^ 59
def prefixEnd_628363 : Nat := 4983230072969 + 3 ^ 40 * 628363 * 2
def baseEnd_628363 : Nat := 107550748167076753524239

theorem tailTrace_628363 : CollatzResearch.WordTrace tailWord_628363 prefixEnd_628363 107550748167076753524239 := by
  unfold tailWord_628363
  simp only [CollatzResearch.WordTrace]
  refine ⟨22918281422555641701657743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15278854281703761134438495 22918281422555641701657743)
  ·
    refine ⟨34377422133833462552486615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22918281422555641701657743 34377422133833462552486615)
    ·
      refine ⟨51566133200750193828729923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34377422133833462552486615 51566133200750193828729923)
      ·
        refine ⟨77349199801125290743094885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51566133200750193828729923 77349199801125290743094885)
        ·
          refine ⟨14502974962710992014330291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77349199801125290743094885 14502974962710992014330291)
          ·
            refine ⟨21754462444066488021495437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14502974962710992014330291 21754462444066488021495437)
            ·
              refine ⟨8157923416524933008060789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21754462444066488021495437 8157923416524933008060789)
              ·
                refine ⟨764805320299212469505699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8157923416524933008060789 764805320299212469505699)
                ·
                  refine ⟨1147207980448818704258549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764805320299212469505699 1147207980448818704258549)
                  ·
                    refine ⟨107550748167076753524239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1147207980448818704258549 107550748167076753524239)
                    ·
                      rfl

theorem cell23_628363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 5].length) (baseStart_628363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628363 prefixEnd_628363 := by exact prefixLift 628363
  have htrace : WordTrace (prefixWord ++ tailWord_628363) baseStart_628363 baseEnd_628363 := by
    simpa [prefixWord, tailWord_628363, baseEnd_628363] using wordTrace_append hprefix tailTrace_628363
  have hstable : (prefixWord ++ tailWord_628363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628363).length < 2 ^ (prefixWord ++ tailWord_628363).sum := by decide
  have hdescent : baseEnd_628363 < baseStart_628363 := by decide
  rcases family_descends (prefixWord ++ tailWord_628363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628400 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4]
def baseStart_628400 : Nat := 118140960795 + 628400 * 2 ^ 59
def prefixEnd_628400 : Nat := 4983230072969 + 3 ^ 40 * 628400 * 2
def baseEnd_628400 : Nat := 322671243285446615810047

theorem tailTrace_628400 : CollatzResearch.WordTrace tailWord_628400 prefixEnd_628400 322671243285446615810047 := by
  unfold tailWord_628400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11459815461710798510377327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15279753948947731347169769 11459815461710798510377327)
  ·
    refine ⟨17189723192566197765565991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11459815461710798510377327 17189723192566197765565991)
    ·
      refine ⟨25784584788849296648348987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17189723192566197765565991 25784584788849296648348987)
      ·
        refine ⟨38676877183273944972523481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25784584788849296648348987 38676877183273944972523481)
        ·
          refine ⟨29007657887455458729392611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38676877183273944972523481 29007657887455458729392611)
          ·
            refine ⟨43511486831183188094088917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29007657887455458729392611 43511486831183188094088917)
            ·
              refine ⟨1019800472605855970955209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43511486831183188094088917 1019800472605855970955209)
              ·
                refine ⟨764850354454391978216407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019800472605855970955209 764850354454391978216407)
                ·
                  refine ⟨1147275531681587967324611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764850354454391978216407 1147275531681587967324611)
                  ·
                    refine ⟨1720913297522381950986917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1147275531681587967324611 1720913297522381950986917)
                    ·
                      refine ⟨322671243285446615810047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1720913297522381950986917 322671243285446615810047)
                      ·
                        rfl

theorem cell23_628400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_628400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628400 prefixEnd_628400 := by exact prefixLift 628400
  have htrace : WordTrace (prefixWord ++ tailWord_628400) baseStart_628400 baseEnd_628400 := by
    simpa [prefixWord, tailWord_628400, baseEnd_628400] using wordTrace_append hprefix tailTrace_628400
  have hstable : (prefixWord ++ tailWord_628400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628400).length < 2 ^ (prefixWord ++ tailWord_628400).sum := by decide
  have hdescent : baseEnd_628400 < baseStart_628400 := by decide
  rcases family_descends (prefixWord ++ tailWord_628400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628428 : List Nat := [2, 2, 1, 5, 2, 2, 2, 2, 1, 1, 3]
def baseStart_628428 : Nat := 118140960795 + 628428 * 2 ^ 59
def prefixEnd_628428 : Nat := 4983230072969 + 3 ^ 40 * 628428 * 2
def baseEnd_628428 : Nat := 322685620743772506259919

theorem tailTrace_628428 : CollatzResearch.WordTrace tailWord_628428 prefixEnd_628428 322685620743772506259919 := by
  unfold tailWord_628428
  simp only [CollatzResearch.WordTrace]
  refine ⟨11460326083660078901386969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15280434778213438535182625 11460326083660078901386969)
  ·
    refine ⟨8595244562745059176040227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11460326083660078901386969 8595244562745059176040227)
    ·
      refine ⟨12892866844117588764060341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8595244562745059176040227 12892866844117588764060341)
      ·
        refine ⟨1208706266636023946630657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12892866844117588764060341 1208706266636023946630657)
        ·
          refine ⟨906529699977017959972993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1208706266636023946630657 906529699977017959972993)
          ·
            refine ⟨679897274982763469979745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906529699977017959972993 679897274982763469979745)
            ·
              refine ⟨509922956237072602484809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679897274982763469979745 509922956237072602484809)
              ·
                refine ⟨382442217177804451863607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509922956237072602484809 382442217177804451863607)
                ·
                  refine ⟨573663325766706677795411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382442217177804451863607 573663325766706677795411)
                  ·
                    refine ⟨860494988650060016693117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573663325766706677795411 860494988650060016693117)
                    ·
                      refine ⟨322685620743772506259919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860494988650060016693117 322685620743772506259919)
                      ·
                        rfl

theorem cell23_628428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_628428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628428 prefixEnd_628428 := by exact prefixLift 628428
  have htrace : WordTrace (prefixWord ++ tailWord_628428) baseStart_628428 baseEnd_628428 := by
    simpa [prefixWord, tailWord_628428, baseEnd_628428] using wordTrace_append hprefix tailTrace_628428
  have hstable : (prefixWord ++ tailWord_628428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628428).length < 2 ^ (prefixWord ++ tailWord_628428).sum := by decide
  have hdescent : baseEnd_628428 < baseStart_628428 := by decide
  rcases family_descends (prefixWord ++ tailWord_628428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628453 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_628453 : Nat := 118140960795 + 628453 * 2 ^ 59
def prefixEnd_628453 : Nat := 4983230072969 + 3 ^ 40 * 628453 * 2
def baseEnd_628453 : Nat := 107566152586711636149101

theorem tailTrace_628453 : CollatzResearch.WordTrace tailWord_628453 prefixEnd_628453 107566152586711636149101 := by
  unfold tailWord_628453
  simp only [CollatzResearch.WordTrace]
  refine ⟨22921563992229587072434013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15281042661486391381622675 22921563992229587072434013)
  ·
    refine ⟨8595586497086095152162755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22921563992229587072434013 8595586497086095152162755)
    ·
      refine ⟨12893379745629142728244133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8595586497086095152162755 12893379745629142728244133)
      ·
        refine ⟨2417508702305464261545775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12893379745629142728244133 2417508702305464261545775)
        ·
          refine ⟨3626263053458196392318663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417508702305464261545775 3626263053458196392318663)
          ·
            refine ⟨5439394580187294588477995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3626263053458196392318663 5439394580187294588477995)
            ·
              refine ⟨8159091870280941882716993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5439394580187294588477995 8159091870280941882716993)
              ·
                refine ⟨6119318902710706412037745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8159091870280941882716993 6119318902710706412037745)
                ·
                  refine ⟨4589489177033029809028309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6119318902710706412037745 4589489177033029809028309)
                  ·
                    refine ⟨107566152586711636149101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4589489177033029809028309 107566152586711636149101)
                    ·
                      rfl

theorem cell23_628453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_628453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628453 prefixEnd_628453 := by exact prefixLift 628453
  have htrace : WordTrace (prefixWord ++ tailWord_628453) baseStart_628453 baseEnd_628453 := by
    simpa [prefixWord, tailWord_628453, baseEnd_628453] using wordTrace_append hprefix tailTrace_628453
  have hstable : (prefixWord ++ tailWord_628453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628453).length < 2 ^ (prefixWord ++ tailWord_628453).sum := by decide
  have hdescent : baseEnd_628453 < baseStart_628453 := by decide
  rcases family_descends (prefixWord ++ tailWord_628453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628463 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_628463 : Nat := 118140960795 + 628463 * 2 ^ 59
def prefixEnd_628463 : Nat := 4983230072969 + 3 ^ 40 * 628463 * 2
def baseEnd_628463 : Nat := 322703592566679869322257

theorem tailTrace_628463 : CollatzResearch.WordTrace tailWord_628463 prefixEnd_628463 322703592566679869322257 := by
  unfold tailWord_628463
  simp only [CollatzResearch.WordTrace]
  refine ⟨22921928722193358780298043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15281285814795572520198695 22921928722193358780298043)
  ·
    refine ⟨34382893083290038170447065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22921928722193358780298043 34382893083290038170447065)
    ·
      refine ⟨25787169812467528627835299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34382893083290038170447065 25787169812467528627835299)
      ·
        refine ⟨38680754718701292941752949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25787169812467528627835299 38680754718701292941752949)
        ·
          refine ⟨3626320754878246213289339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38680754718701292941752949 3626320754878246213289339)
          ·
            refine ⟨5439481132317369319934009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3626320754878246213289339 5439481132317369319934009)
            ·
              refine ⟨4079610849238026989950507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5439481132317369319934009 4079610849238026989950507)
              ·
                refine ⟨6119416273857040484925761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079610849238026989950507 6119416273857040484925761)
                ·
                  refine ⟨4589562205392780363694321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6119416273857040484925761 4589562205392780363694321)
                  ·
                    refine ⟨3442171654044585272770741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4589562205392780363694321 3442171654044585272770741)
                    ·
                      refine ⟨322703592566679869322257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3442171654044585272770741 322703592566679869322257)
                      ·
                        rfl

theorem cell23_628463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_628463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628463 prefixEnd_628463 := by exact prefixLift 628463
  have htrace : WordTrace (prefixWord ++ tailWord_628463) baseStart_628463 baseEnd_628463 := by
    simpa [prefixWord, tailWord_628463, baseEnd_628463] using wordTrace_append hprefix tailTrace_628463
  have hstable : (prefixWord ++ tailWord_628463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628463).length < 2 ^ (prefixWord ++ tailWord_628463).sum := by decide
  have hdescent : baseEnd_628463 < baseStart_628463 := by decide
  rcases family_descends (prefixWord ++ tailWord_628463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628468 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_628468 : Nat := 118140960795 + 628468 * 2 ^ 59
def prefixEnd_628468 : Nat := 4983230072969 + 3 ^ 40 * 628468 * 2
def baseEnd_628468 : Nat := 322706159969952349759735

theorem tailTrace_628468 : CollatzResearch.WordTrace tailWord_628468 prefixEnd_628468 322706159969952349759735 := by
  unfold tailWord_628468
  simp only [CollatzResearch.WordTrace]
  refine ⟨11461055543587622317115029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15281407391450163089486705 11461055543587622317115029)
  ·
    refine ⟨537236978605669796114767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11461055543587622317115029 537236978605669796114767)
    ·
      refine ⟨805855467908504694172151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537236978605669796114767 805855467908504694172151)
      ·
        refine ⟨1208783201862757041258227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805855467908504694172151 1208783201862757041258227)
        ·
          refine ⟨1813174802794135561887341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208783201862757041258227 1813174802794135561887341)
          ·
            refine ⟨679940551047800835707753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1813174802794135561887341 679940551047800835707753)
            ·
              refine ⟨509955413285850626780815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679940551047800835707753 509955413285850626780815)
              ·
                refine ⟨764933119928775940171223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509955413285850626780815 764933119928775940171223)
                ·
                  refine ⟨1147399679893163910256835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764933119928775940171223 1147399679893163910256835)
                  ·
                    refine ⟨1721099519839745865385253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1147399679893163910256835 1721099519839745865385253)
                    ·
                      refine ⟨322706159969952349759735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1721099519839745865385253 322706159969952349759735)
                      ·
                        rfl

theorem cell23_628468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_628468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628468 prefixEnd_628468 := by exact prefixLift 628468
  have htrace : WordTrace (prefixWord ++ tailWord_628468) baseStart_628468 baseEnd_628468 := by
    simpa [prefixWord, tailWord_628468, baseEnd_628468] using wordTrace_append hprefix tailTrace_628468
  have hstable : (prefixWord ++ tailWord_628468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628468).length < 2 ^ (prefixWord ++ tailWord_628468).sum := by decide
  have hdescent : baseEnd_628468 < baseStart_628468 := by decide
  rcases family_descends (prefixWord ++ tailWord_628468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628483 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 2, 6]
def baseStart_628483 : Nat := 118140960795 + 628483 * 2 ^ 59
def prefixEnd_628483 : Nat := 4983230072969 + 3 ^ 40 * 628483 * 2
def baseEnd_628483 : Nat := 107571287393256597024055

theorem tailTrace_628483 : CollatzResearch.WordTrace tailWord_628483 prefixEnd_628483 107571287393256597024055 := by
  unfold tailWord_628483
  simp only [CollatzResearch.WordTrace]
  refine ⟨22922658182120902196026103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15281772121413934797350735 22922658182120902196026103)
  ·
    refine ⟨34383987273181353294039155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22922658182120902196026103 34383987273181353294039155)
    ·
      refine ⟨51575980909772029941058733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34383987273181353294039155 51575980909772029941058733)
      ·
        refine ⟨19340992841164511227897025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51575980909772029941058733 19340992841164511227897025)
        ·
          refine ⟨14505744630873383420922769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19340992841164511227897025 14505744630873383420922769)
          ·
            refine ⟨10879308473155037565692077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14505744630873383420922769 10879308473155037565692077)
            ·
              refine ⟨4079740677433139087134529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10879308473155037565692077 4079740677433139087134529)
              ·
                refine ⟨3059805508074854315350897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4079740677433139087134529 3059805508074854315350897)
                ·
                  refine ⟨2294854131056140736513173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059805508074854315350897 2294854131056140736513173)
                  ·
                    refine ⟨107571287393256597024055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2294854131056140736513173 107571287393256597024055)
                    ·
                      rfl

theorem cell23_628483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 6].length) (baseStart_628483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628483 prefixEnd_628483 := by exact prefixLift 628483
  have htrace : WordTrace (prefixWord ++ tailWord_628483) baseStart_628483 baseEnd_628483 := by
    simpa [prefixWord, tailWord_628483, baseEnd_628483] using wordTrace_append hprefix tailTrace_628483
  have hstable : (prefixWord ++ tailWord_628483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628483).length < 2 ^ (prefixWord ++ tailWord_628483).sum := by decide
  have hdescent : baseEnd_628483 < baseStart_628483 := by decide
  rcases family_descends (prefixWord ++ tailWord_628483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628484 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_628484 : Nat := 118140960795 + 628484 * 2 ^ 59
def prefixEnd_628484 : Nat := 4983230072969 + 3 ^ 40 * 628484 * 2
def baseEnd_628484 : Nat := 322714375660424287159661

theorem tailTrace_628484 : CollatzResearch.WordTrace tailWord_628484 prefixEnd_628484 322714375660424287159661 := by
  unfold tailWord_628484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11461347327558639683406253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15281796436744852911208337 11461347327558639683406253)
  ·
    refine ⟨4298005247834489881277345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11461347327558639683406253 4298005247834489881277345)
    ·
      refine ⟨3223503935875867410958009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4298005247834489881277345 3223503935875867410958009)
      ·
        refine ⟨2417627951906900558218507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3223503935875867410958009 2417627951906900558218507)
        ·
          refine ⟨3626441927860350837327761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417627951906900558218507 3626441927860350837327761)
          ·
            refine ⟨2719831445895263127995821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3626441927860350837327761 2719831445895263127995821)
            ·
              refine ⟨1019936792210723672998433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2719831445895263127995821 1019936792210723672998433)
              ·
                refine ⟨764952594158042754748825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019936792210723672998433 764952594158042754748825)
                ·
                  refine ⟨573714445618532066061619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764952594158042754748825 573714445618532066061619)
                  ·
                    refine ⟨860571668427798099092429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573714445618532066061619 860571668427798099092429)
                    ·
                      refine ⟨322714375660424287159661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860571668427798099092429 322714375660424287159661)
                      ·
                        rfl

theorem cell23_628484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_628484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628484 prefixEnd_628484 := by exact prefixLift 628484
  have htrace : WordTrace (prefixWord ++ tailWord_628484) baseStart_628484 baseEnd_628484 := by
    simpa [prefixWord, tailWord_628484, baseEnd_628484] using wordTrace_append hprefix tailTrace_628484
  have hstable : (prefixWord ++ tailWord_628484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628484).length < 2 ^ (prefixWord ++ tailWord_628484).sum := by decide
  have hdescent : baseEnd_628484 < baseStart_628484 := by decide
  rcases family_descends (prefixWord ++ tailWord_628484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628540 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_628540 : Nat := 118140960795 + 628540 * 2 ^ 59
def prefixEnd_628540 : Nat := 4983230072969 + 3 ^ 40 * 628540 * 2
def baseEnd_628540 : Nat := 322743130577076068059403

theorem tailTrace_628540 : CollatzResearch.WordTrace tailWord_628540 prefixEnd_628540 322743130577076068059403 := by
  unfold tailWord_628540
  simp only [CollatzResearch.WordTrace]
  refine ⟨11462368571457200465425537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15283158095276267287234049 11462368571457200465425537)
  ·
    refine ⟨8596776428592900349069153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11462368571457200465425537 8596776428592900349069153)
    ·
      refine ⟨6447582321444675261801865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8596776428592900349069153 6447582321444675261801865)
      ·
        refine ⟨4835686741083506446351399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6447582321444675261801865 4835686741083506446351399)
        ·
          refine ⟨7253530111625259669527099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835686741083506446351399 7253530111625259669527099)
          ·
            refine ⟨10880295167437889504290649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7253530111625259669527099 10880295167437889504290649)
            ·
              refine ⟨8160221375578417128217987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10880295167437889504290649 8160221375578417128217987)
              ·
                refine ⟨12240332063367625692326981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8160221375578417128217987 12240332063367625692326981)
                ·
                  refine ⟨2295062261881429817311309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12240332063367625692326981 2295062261881429817311309)
                  ·
                    refine ⟨860648348205536181491741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295062261881429817311309 860648348205536181491741)
                    ·
                      refine ⟨322743130577076068059403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860648348205536181491741 322743130577076068059403)
                      ·
                        rfl

theorem cell23_628540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_628540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628540 prefixEnd_628540 := by exact prefixLift 628540
  have htrace : WordTrace (prefixWord ++ tailWord_628540) baseStart_628540 baseEnd_628540 := by
    simpa [prefixWord, tailWord_628540, baseEnd_628540] using wordTrace_append hprefix tailTrace_628540
  have hstable : (prefixWord ++ tailWord_628540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628540).length < 2 ^ (prefixWord ++ tailWord_628540).sum := by decide
  have hdescent : baseEnd_628540 < baseStart_628540 := by decide
  rcases family_descends (prefixWord ++ tailWord_628540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628597 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_628597 : Nat := 118140960795 + 628597 * 2 ^ 59
def prefixEnd_628597 : Nat := 4983230072969 + 3 ^ 40 * 628597 * 2
def baseEnd_628597 : Nat := 322772398974382345046641

theorem tailTrace_628597 : CollatzResearch.WordTrace tailWord_628597 prefixEnd_628597 322772398974382345046641 := by
  unfold tailWord_628597
  simp only [CollatzResearch.WordTrace]
  refine ⟨22926816103707899665676045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15284544069138599777117363 22926816103707899665676045)
  ·
    refine ⟨8597556038890462374628517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22926816103707899665676045 8597556038890462374628517)
    ·
      refine ⟨1612041757291961695242847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8597556038890462374628517 1612041757291961695242847)
      ·
        refine ⟨2418062635937942542864271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612041757291961695242847 2418062635937942542864271)
        ·
          refine ⟨3627093953906913814296407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418062635937942542864271 3627093953906913814296407)
          ·
            refine ⟨5440640930860370721444611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3627093953906913814296407 5440640930860370721444611)
            ·
              refine ⟨8160961396290556082166917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440640930860370721444611 8160961396290556082166917)
              ·
                refine ⟨1530180261804479265406297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8160961396290556082166917 1530180261804479265406297)
                ·
                  refine ⟨1147635196353359449054723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1530180261804479265406297 1147635196353359449054723)
                  ·
                    refine ⟨1721452794530039173582085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1147635196353359449054723 1721452794530039173582085)
                    ·
                      refine ⟨322772398974382345046641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1721452794530039173582085 322772398974382345046641)
                      ·
                        rfl

theorem cell23_628597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_628597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628597 prefixEnd_628597 := by exact prefixLift 628597
  have htrace : WordTrace (prefixWord ++ tailWord_628597) baseStart_628597 baseEnd_628597 := by
    simpa [prefixWord, tailWord_628597, baseEnd_628597] using wordTrace_append hprefix tailTrace_628597
  have hstable : (prefixWord ++ tailWord_628597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628597).length < 2 ^ (prefixWord ++ tailWord_628597).sum := by decide
  have hdescent : baseEnd_628597 < baseStart_628597 := by decide
  rcases family_descends (prefixWord ++ tailWord_628597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628598 : List Nat := [5, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_628598 : Nat := 118140960795 + 628598 * 2 ^ 59
def prefixEnd_628598 : Nat := 4983230072969 + 3 ^ 40 * 628598 * 2
def baseEnd_628598 : Nat := 35863656939448537903793

theorem tailTrace_628598 : CollatzResearch.WordTrace tailWord_628598 prefixEnd_628598 35863656939448537903793 := by
  unfold tailWord_628598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432928286044017302278903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15284568384469517890974965 1432928286044017302278903)
  ·
    refine ⟨2149392429066025953418355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1432928286044017302278903 2149392429066025953418355)
    ·
      refine ⟨3224088643599038930127533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149392429066025953418355 3224088643599038930127533)
      ·
        refine ⟨1209033241349639598797825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3224088643599038930127533 1209033241349639598797825)
        ·
          refine ⟨906774931012229699098369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209033241349639598797825 906774931012229699098369)
          ·
            refine ⟨680081198259172274323777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906774931012229699098369 680081198259172274323777)
            ·
              refine ⟨510060898694379205742833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680081198259172274323777 510060898694379205742833)
              ·
                refine ⟨382545674020784404307125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510060898694379205742833 382545674020784404307125)
                ·
                  refine ⟨35863656939448537903793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382545674020784404307125 35863656939448537903793)
                  ·
                    rfl

theorem cell23_628598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_628598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628598 prefixEnd_628598 := by exact prefixLift 628598
  have htrace : WordTrace (prefixWord ++ tailWord_628598) baseStart_628598 baseEnd_628598 := by
    simpa [prefixWord, tailWord_628598, baseEnd_628598] using wordTrace_append hprefix tailTrace_628598
  have hstable : (prefixWord ++ tailWord_628598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628598).length < 2 ^ (prefixWord ++ tailWord_628598).sum := by decide
  have hdescent : baseEnd_628598 < baseStart_628598 := by decide
  rcases family_descends (prefixWord ++ tailWord_628598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628634 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_628634 : Nat := 118140960795 + 628634 * 2 ^ 59
def prefixEnd_628634 : Nat := 4983230072969 + 3 ^ 40 * 628634 * 2
def baseEnd_628634 : Nat := 322791397758598700283971

theorem tailTrace_628634 : CollatzResearch.WordTrace tailWord_628634 prefixEnd_628634 322791397758598700283971 := by
  unfold tailWord_628634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5732041401143463746193239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15285443736382569989848637 5732041401143463746193239)
  ·
    refine ⟨8598062101715195619289859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5732041401143463746193239 8598062101715195619289859)
    ·
      refine ⟨12897093152572793428934789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8598062101715195619289859 12897093152572793428934789)
      ·
        refine ⟨2418204966107398767925273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12897093152572793428934789 2418204966107398767925273)
        ·
          refine ⟨1813653724580549075943955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418204966107398767925273 1813653724580549075943955)
          ·
            refine ⟨2720480586870823613915933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813653724580549075943955 2720480586870823613915933)
            ·
              refine ⟨1020180220076558855218475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2720480586870823613915933 1020180220076558855218475)
              ·
                refine ⟨1530270330114838282827713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020180220076558855218475 1530270330114838282827713)
                ·
                  refine ⟨1147702747586128712120785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1530270330114838282827713 1147702747586128712120785)
                  ·
                    refine ⟨860777060689596534090589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147702747586128712120785 860777060689596534090589)
                    ·
                      refine ⟨322791397758598700283971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860777060689596534090589 322791397758598700283971)
                      ·
                        rfl

theorem cell23_628634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_628634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628634 prefixEnd_628634 := by exact prefixLift 628634
  have htrace : WordTrace (prefixWord ++ tailWord_628634) baseStart_628634 baseEnd_628634 := by
    simpa [prefixWord, tailWord_628634, baseEnd_628634] using wordTrace_append hprefix tailTrace_628634
  have hstable : (prefixWord ++ tailWord_628634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628634).length < 2 ^ (prefixWord ++ tailWord_628634).sum := by decide
  have hdescent : baseEnd_628634 < baseStart_628634 := by decide
  rcases family_descends (prefixWord ++ tailWord_628634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628664 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_628664 : Nat := 118140960795 + 628664 * 2 ^ 59
def prefixEnd_628664 : Nat := 4983230072969 + 3 ^ 40 * 628664 * 2
def baseEnd_628664 : Nat := 322806802178233582908833

theorem tailTrace_628664 : CollatzResearch.WordTrace tailWord_628664 prefixEnd_628664 322806802178233582908833 := by
  unfold tailWord_628664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464629897232585054182523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15286173196310113405576697 11464629897232585054182523)
  ·
    refine ⟨17196944845848877581273785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11464629897232585054182523 17196944845848877581273785)
    ·
      refine ⟨12897708634386658185955339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17196944845848877581273785 12897708634386658185955339)
      ·
        refine ⟨19346562951579987278933009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12897708634386658185955339 19346562951579987278933009)
        ·
          refine ⟨14509922213684990459199757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19346562951579987278933009 14509922213684990459199757)
          ·
            refine ⟨5441220830131871422199909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14509922213684990459199757 5441220830131871422199909)
            ·
              refine ⟨1020228905649725891662483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5441220830131871422199909 1020228905649725891662483)
              ·
                refine ⟨1530343358474588837493725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020228905649725891662483 1530343358474588837493725)
                ·
                  refine ⟨573878759427970814060147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1530343358474588837493725 573878759427970814060147)
                  ·
                    refine ⟨860818139141956221090221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573878759427970814060147 860818139141956221090221)
                    ·
                      refine ⟨322806802178233582908833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860818139141956221090221 322806802178233582908833)
                      ·
                        rfl

theorem cell23_628664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_628664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628664 prefixEnd_628664 := by exact prefixLift 628664
  have htrace : WordTrace (prefixWord ++ tailWord_628664) baseStart_628664 baseEnd_628664 := by
    simpa [prefixWord, tailWord_628664, baseEnd_628664] using wordTrace_append hprefix tailTrace_628664
  have hstable : (prefixWord ++ tailWord_628664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628664).length < 2 ^ (prefixWord ++ tailWord_628664).sum := by decide
  have hdescent : baseEnd_628664 < baseStart_628664 := by decide
  rcases family_descends (prefixWord ++ tailWord_628664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628684 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_628684 : Nat := 118140960795 + 628684 * 2 ^ 59
def prefixEnd_628684 : Nat := 4983230072969 + 3 ^ 40 * 628684 * 2
def baseEnd_628684 : Nat := 107605690597107834886247

theorem tailTrace_628684 : CollatzResearch.WordTrace tailWord_628684 prefixEnd_628684 107605690597107834886247 := by
  unfold tailWord_628684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464994627196356762046553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15286659502928475682728737 11464994627196356762046553)
  ·
    refine ⟨8598745970397267571534915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11464994627196356762046553 8598745970397267571534915)
    ·
      refine ⟨12898118955595901357302373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8598745970397267571534915 12898118955595901357302373)
      ·
        refine ⟨2418397304174231504494195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12898118955595901357302373 2418397304174231504494195)
        ·
          refine ⟨3627595956261347256741293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418397304174231504494195 3627595956261347256741293)
          ·
            refine ⟨1360348483598005221277985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3627595956261347256741293 1360348483598005221277985)
            ·
              refine ⟨1020261362698503915958489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360348483598005221277985 1020261362698503915958489)
              ·
                refine ⟨765196022023877936968867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020261362698503915958489 765196022023877936968867)
                ·
                  refine ⟨1147794033035816905453301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765196022023877936968867 1147794033035816905453301)
                  ·
                    refine ⟨107605690597107834886247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1147794033035816905453301 107605690597107834886247)
                    ·
                      rfl

theorem cell23_628684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_628684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628684 prefixEnd_628684 := by exact prefixLift 628684
  have htrace : WordTrace (prefixWord ++ tailWord_628684) baseStart_628684 baseEnd_628684 := by
    simpa [prefixWord, tailWord_628684, baseEnd_628684] using wordTrace_append hprefix tailTrace_628684
  have hstable : (prefixWord ++ tailWord_628684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628684).length < 2 ^ (prefixWord ++ tailWord_628684).sum := by decide
  have hdescent : baseEnd_628684 < baseStart_628684 := by decide
  rcases family_descends (prefixWord ++ tailWord_628684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628687 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 2, 6, 2]
def baseStart_628687 : Nat := 118140960795 + 628687 * 2 ^ 59
def prefixEnd_628687 : Nat := 4983230072969 + 3 ^ 40 * 628687 * 2
def baseEnd_628687 : Nat := 322818612233286992921227

theorem tailTrace_628687 : CollatzResearch.WordTrace tailWord_628687 prefixEnd_628687 322818612233286992921227 := by
  unfold tailWord_628687
  simp only [CollatzResearch.WordTrace]
  refine ⟨22930098673381845036452315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15286732448921230024301543 22930098673381845036452315)
  ·
    refine ⟨34395148010072767554678473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22930098673381845036452315 34395148010072767554678473)
    ·
      refine ⟨25796361007554575666008855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34395148010072767554678473 25796361007554575666008855)
      ·
        refine ⟨38694541511331863499013283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25796361007554575666008855 38694541511331863499013283)
        ·
          refine ⟨58041812266997795248519925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38694541511331863499013283 58041812266997795248519925)
          ·
            refine ⟨5441419900031043304548743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58041812266997795248519925 5441419900031043304548743)
            ·
              refine ⟨8162129850046564956823115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5441419900031043304548743 8162129850046564956823115)
              ·
                refine ⟨12243194775069847435234673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8162129850046564956823115 12243194775069847435234673)
                ·
                  refine ⟨9182396081302385576426005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12243194775069847435234673 9182396081302385576426005)
                  ·
                    refine ⟨430424816311049323894969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9182396081302385576426005 430424816311049323894969)
                    ·
                      refine ⟨322818612233286992921227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430424816311049323894969 322818612233286992921227)
                      ·
                        rfl

theorem cell23_628687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6, 2].length) (baseStart_628687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628687 prefixEnd_628687 := by exact prefixLift 628687
  have htrace : WordTrace (prefixWord ++ tailWord_628687) baseStart_628687 baseEnd_628687 := by
    simpa [prefixWord, tailWord_628687, baseEnd_628687] using wordTrace_append hprefix tailTrace_628687
  have hstable : (prefixWord ++ tailWord_628687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628687).length < 2 ^ (prefixWord ++ tailWord_628687).sum := by decide
  have hdescent : baseEnd_628687 < baseStart_628687 := by decide
  rcases family_descends (prefixWord ++ tailWord_628687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628704 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 5, 2, 2]
def baseStart_628704 : Nat := 118140960795 + 628704 * 2 ^ 59
def prefixEnd_628704 : Nat := 4983230072969 + 3 ^ 40 * 628704 * 2
def baseEnd_628704 : Nat := 322827341404413426408649

theorem tailTrace_628704 : CollatzResearch.WordTrace tailWord_628704 prefixEnd_628704 322827341404413426408649 := by
  unfold tailWord_628704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11465359357160128469910583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15287145809546837959880777 11465359357160128469910583)
  ·
    refine ⟨17198039035740192704865875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11465359357160128469910583 17198039035740192704865875)
    ·
      refine ⟨25797058553610289057298813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17198039035740192704865875 25797058553610289057298813)
      ·
        refine ⟨9673896957603858396487055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25797058553610289057298813 9673896957603858396487055)
        ·
          refine ⟨14510845436405787594730583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9673896957603858396487055 14510845436405787594730583)
          ·
            refine ⟨21766268154608681392095875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14510845436405787594730583 21766268154608681392095875)
            ·
              refine ⟨32649402231913022088143813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21766268154608681392095875 32649402231913022088143813)
              ·
                refine ⟨6121762918483691641526965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32649402231913022088143813 6121762918483691641526965)
                ·
                  refine ⟨573915273607846091393153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6121762918483691641526965 573915273607846091393153)
                  ·
                    refine ⟨430436455205884568544865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 573915273607846091393153 430436455205884568544865)
                    ·
                      refine ⟨322827341404413426408649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430436455205884568544865 322827341404413426408649)
                      ·
                        rfl

theorem cell23_628704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_628704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628704 prefixEnd_628704 := by exact prefixLift 628704
  have htrace : WordTrace (prefixWord ++ tailWord_628704) baseStart_628704 baseEnd_628704 := by
    simpa [prefixWord, tailWord_628704, baseEnd_628704] using wordTrace_append hprefix tailTrace_628704
  have hstable : (prefixWord ++ tailWord_628704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628704).length < 2 ^ (prefixWord ++ tailWord_628704).sum := by decide
  have hdescent : baseEnd_628704 < baseStart_628704 := by decide
  rcases family_descends (prefixWord ++ tailWord_628704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628707 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5]
def baseStart_628707 : Nat := 118140960795 + 628707 * 2 ^ 59
def prefixEnd_628707 : Nat := 4983230072969 + 3 ^ 40 * 628707 * 2
def baseEnd_628707 : Nat := 322828881846376914671135

theorem tailTrace_628707 : CollatzResearch.WordTrace tailWord_628707 prefixEnd_628707 322828881846376914671135 := by
  unfold tailWord_628707
  simp only [CollatzResearch.WordTrace]
  refine ⟨22930828133309388452180375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15287218755539592301453583 22930828133309388452180375)
  ·
    refine ⟨34396242199964082678270563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22930828133309388452180375 34396242199964082678270563)
    ·
      refine ⟨51594363299946124017405845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34396242199964082678270563 51594363299946124017405845)
      ·
        refine ⟨2418485779684974563315899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51594363299946124017405845 2418485779684974563315899)
        ·
          refine ⟨3627728669527461844973849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418485779684974563315899 3627728669527461844973849)
          ·
            refine ⟨2720796502145596383730387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3627728669527461844973849 2720796502145596383730387)
            ·
              refine ⟨4081194753218394575595581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720796502145596383730387 4081194753218394575595581)
              ·
                refine ⟨1530448032456897965848343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4081194753218394575595581 1530448032456897965848343)
                ·
                  refine ⟨2295672048685346948772515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530448032456897965848343 2295672048685346948772515)
                  ·
                    refine ⟨3443508073028020423158773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2295672048685346948772515 3443508073028020423158773)
                    ·
                      refine ⟨322828881846376914671135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3443508073028020423158773 322828881846376914671135)
                      ·
                        rfl

theorem cell23_628707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_628707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628707 prefixEnd_628707 := by exact prefixLift 628707
  have htrace : WordTrace (prefixWord ++ tailWord_628707) baseStart_628707 baseEnd_628707 := by
    simpa [prefixWord, tailWord_628707, baseEnd_628707] using wordTrace_append hprefix tailTrace_628707
  have hstable : (prefixWord ++ tailWord_628707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628707).length < 2 ^ (prefixWord ++ tailWord_628707).sum := by decide
  have hdescent : baseEnd_628707 < baseStart_628707 := by decide
  rcases family_descends (prefixWord ++ tailWord_628707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628714 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_628714 : Nat := 118140960795 + 628714 * 2 ^ 59
def prefixEnd_628714 : Nat := 4983230072969 + 3 ^ 40 * 628714 * 2
def baseEnd_628714 : Nat := 107610825403652795761201

theorem tailTrace_628714 : CollatzResearch.WordTrace tailWord_628714 prefixEnd_628714 107610825403652795761201 := by
  unfold tailWord_628714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5732770861071007161921299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15287388962856019098456797 5732770861071007161921299)
  ·
    refine ⟨8599156291606510742881949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5732770861071007161921299 8599156291606510742881949)
    ·
      refine ⟨3224683609352441528580731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8599156291606510742881949 3224683609352441528580731)
      ·
        refine ⟨4837025414028662292871097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224683609352441528580731 4837025414028662292871097)
        ·
          refine ⟨3627769060521496719653323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4837025414028662292871097 3627769060521496719653323)
          ·
            refine ⟨5441653590782245079479985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3627769060521496719653323 5441653590782245079479985)
            ·
              refine ⟨4081240193086683809609989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5441653590782245079479985 4081240193086683809609989)
              ·
                refine ⟨765232536203753214301873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4081240193086683809609989 765232536203753214301873)
                ·
                  refine ⟨573924402152814910726405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765232536203753214301873 573924402152814910726405)
                  ·
                    refine ⟨107610825403652795761201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 573924402152814910726405 107610825403652795761201)
                    ·
                      rfl

theorem cell23_628714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_628714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628714 prefixEnd_628714 := by exact prefixLift 628714
  have htrace : WordTrace (prefixWord ++ tailWord_628714) baseStart_628714 baseEnd_628714 := by
    simpa [prefixWord, tailWord_628714, baseEnd_628714] using wordTrace_append hprefix tailTrace_628714
  have hstable : (prefixWord ++ tailWord_628714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628714).length < 2 ^ (prefixWord ++ tailWord_628714).sum := by decide
  have hdescent : baseEnd_628714 < baseStart_628714 := by decide
  rcases family_descends (prefixWord ++ tailWord_628714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628734 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_628734 : Nat := 118140960795 + 628734 * 2 ^ 59
def prefixEnd_628734 : Nat := 4983230072969 + 3 ^ 40 * 628734 * 2
def baseEnd_628734 : Nat := 322842745824048309033511

theorem tailTrace_628734 : CollatzResearch.WordTrace tailWord_628734 prefixEnd_628734 322842745824048309033511 := by
  unfold tailWord_628734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866476613026446507926657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15287875269474381375608837 2866476613026446507926657)
  ·
    refine ⟨2149857459769834880944993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2866476613026446507926657 2149857459769834880944993)
    ·
      refine ⟨1612393094827376160708745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2149857459769834880944993 1612393094827376160708745)
      ·
        refine ⟨1209294821120532120531559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1612393094827376160708745 1209294821120532120531559)
        ·
          refine ⟨1813942231680798180797339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209294821120532120531559 1813942231680798180797339)
          ·
            refine ⟨2720913347521197271196009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813942231680798180797339 2720913347521197271196009)
            ·
              refine ⟨2040685010640897953397007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720913347521197271196009 2040685010640897953397007)
              ·
                refine ⟨3061027515961346930095511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040685010640897953397007 3061027515961346930095511)
                ·
                  refine ⟨4591541273942020395143267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061027515961346930095511 4591541273942020395143267)
                  ·
                    refine ⟨6887311910913030592714901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591541273942020395143267 6887311910913030592714901)
                    ·
                      refine ⟨322842745824048309033511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6887311910913030592714901 322842745824048309033511)
                      ·
                        rfl

theorem cell23_628734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_628734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628734 prefixEnd_628734 := by exact prefixLift 628734
  have htrace : WordTrace (prefixWord ++ tailWord_628734) baseStart_628734 baseEnd_628734 := by
    simpa [prefixWord, tailWord_628734, baseEnd_628734] using wordTrace_append hprefix tailTrace_628734
  have hstable : (prefixWord ++ tailWord_628734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628734).length < 2 ^ (prefixWord ++ tailWord_628734).sum := by decide
  have hdescent : baseEnd_628734 < baseStart_628734 := by decide
  rcases family_descends (prefixWord ++ tailWord_628734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628741 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_628741 : Nat := 118140960795 + 628741 * 2 ^ 59
def prefixEnd_628741 : Nat := 4983230072969 + 3 ^ 40 * 628741 * 2
def baseEnd_628741 : Nat := 322846340188629781645979

theorem tailTrace_628741 : CollatzResearch.WordTrace tailWord_628741 prefixEnd_628741 322846340188629781645979 := by
  unfold tailWord_628741
  simp only [CollatzResearch.WordTrace]
  refine ⟨22932068215186212258918077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15288045476790808172612051 22932068215186212258918077)
  ·
    refine ⟨8599525580694829597094279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22932068215186212258918077 8599525580694829597094279)
    ·
      refine ⟨12899288371042244395641419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8599525580694829597094279 12899288371042244395641419)
      ·
        refine ⟨19348932556563366593462129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12899288371042244395641419 19348932556563366593462129)
        ·
          refine ⟨14511699417422524945096597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19348932556563366593462129 14511699417422524945096597)
          ·
            refine ⟨680235910191680856801403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14511699417422524945096597 680235910191680856801403)
            ·
              refine ⟨1020353865287521285202105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680235910191680856801403 1020353865287521285202105)
              ·
                refine ⟨765265398965640963901579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020353865287521285202105 765265398965640963901579)
                ·
                  refine ⟨1147898098448461445852369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765265398965640963901579 1147898098448461445852369)
                  ·
                    refine ⟨860923573836346084389277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147898098448461445852369 860923573836346084389277)
                    ·
                      refine ⟨322846340188629781645979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860923573836346084389277 322846340188629781645979)
                      ·
                        rfl

theorem cell23_628741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_628741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628741 prefixEnd_628741 := by exact prefixLift 628741
  have htrace : WordTrace (prefixWord ++ tailWord_628741) baseStart_628741 baseEnd_628741 := by
    simpa [prefixWord, tailWord_628741, baseEnd_628741] using wordTrace_append hprefix tailTrace_628741
  have hstable : (prefixWord ++ tailWord_628741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628741).length < 2 ^ (prefixWord ++ tailWord_628741).sum := by decide
  have hdescent : baseEnd_628741 < baseStart_628741 := by decide
  rcases family_descends (prefixWord ++ tailWord_628741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628771 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 3]
def baseStart_628771 : Nat := 118140960795 + 628771 * 2 ^ 59
def prefixEnd_628771 : Nat := 4983230072969 + 3 ^ 40 * 628771 * 2
def baseEnd_628771 : Nat := 322861744608264664270841

theorem tailTrace_628771 : CollatzResearch.WordTrace tailWord_628771 prefixEnd_628771 322861744608264664270841 := by
  unfold tailWord_628771
  simp only [CollatzResearch.WordTrace]
  refine ⟨22933162405077527382510167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15288774936718351588340111 22933162405077527382510167)
  ·
    refine ⟨34399743607616291073765251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22933162405077527382510167 34399743607616291073765251)
    ·
      refine ⟨51599615411424436610647877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34399743607616291073765251 51599615411424436610647877)
      ·
        refine ⟨9674927889642081864496477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51599615411424436610647877 9674927889642081864496477)
        ·
          refine ⟨3628097958615780699186179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9674927889642081864496477 3628097958615780699186179)
          ·
            refine ⟨5442146937923671048779269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628097958615780699186179 5442146937923671048779269)
            ·
              refine ⟨1020402550860688321646113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5442146937923671048779269 1020402550860688321646113)
              ·
                refine ⟨765301913145516241234585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020402550860688321646113 765301913145516241234585)
                ·
                  refine ⟨573976434859137180925939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765301913145516241234585 573976434859137180925939)
                  ·
                    refine ⟨860964652288705771388909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573976434859137180925939 860964652288705771388909)
                    ·
                      refine ⟨322861744608264664270841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860964652288705771388909 322861744608264664270841)
                      ·
                        rfl

theorem cell23_628771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_628771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628771 prefixEnd_628771 := by exact prefixLift 628771
  have htrace : WordTrace (prefixWord ++ tailWord_628771) baseStart_628771 baseEnd_628771 := by
    simpa [prefixWord, tailWord_628771, baseEnd_628771] using wordTrace_append hprefix tailTrace_628771
  have hstable : (prefixWord ++ tailWord_628771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628771).length < 2 ^ (prefixWord ++ tailWord_628771).sum := by decide
  have hdescent : baseEnd_628771 < baseStart_628771 := by decide
  rcases family_descends (prefixWord ++ tailWord_628771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628788 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_628788 : Nat := 118140960795 + 628788 * 2 ^ 59
def prefixEnd_628788 : Nat := 4983230072969 + 3 ^ 40 * 628788 * 2
def baseEnd_628788 : Nat := 322870473779391097758263

theorem tailTrace_628788 : CollatzResearch.WordTrace tailWord_628788 prefixEnd_628788 322870473779391097758263 := by
  unfold tailWord_628788
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466891223007969642939509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15289188297343959523919345 11466891223007969642939509)
  ·
    refine ⟨1075021052156997154025579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11466891223007969642939509 1075021052156997154025579)
    ·
      refine ⟨1612531578235495731038369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075021052156997154025579 1612531578235495731038369)
      ·
        refine ⟨1209398683676621798278777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1612531578235495731038369 1209398683676621798278777)
        ·
          refine ⟨907049012757466348709083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209398683676621798278777 907049012757466348709083)
          ·
            refine ⟨1360573519136199523063625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907049012757466348709083 1360573519136199523063625)
            ·
              refine ⟨1020430139352149642297719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360573519136199523063625 1020430139352149642297719)
              ·
                refine ⟨1530645209028224463446579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020430139352149642297719 1530645209028224463446579)
                ·
                  refine ⟨2295967813542336695169869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530645209028224463446579 2295967813542336695169869)
                  ·
                    refine ⟨860987930078376260688701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2295967813542336695169869 860987930078376260688701)
                    ·
                      refine ⟨322870473779391097758263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 860987930078376260688701 322870473779391097758263)
                      ·
                        rfl

theorem cell23_628788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_628788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628788 prefixEnd_628788 := by exact prefixLift 628788
  have htrace : WordTrace (prefixWord ++ tailWord_628788) baseStart_628788 baseEnd_628788 := by
    simpa [prefixWord, tailWord_628788, baseEnd_628788] using wordTrace_append hprefix tailTrace_628788
  have hstable : (prefixWord ++ tailWord_628788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628788).length < 2 ^ (prefixWord ++ tailWord_628788).sum := by decide
  have hdescent : baseEnd_628788 < baseStart_628788 := by decide
  rcases family_descends (prefixWord ++ tailWord_628788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628807 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_628807 : Nat := 118140960795 + 628807 * 2 ^ 59
def prefixEnd_628807 : Nat := 4983230072969 + 3 ^ 40 * 628807 * 2
def baseEnd_628807 : Nat := 322880229911826523420675

theorem tailTrace_628807 : CollatzResearch.WordTrace tailWord_628807 prefixEnd_628807 322880229911826523420675 := by
  unfold tailWord_628807
  simp only [CollatzResearch.WordTrace]
  refine ⟨22934475432947105530820675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15289650288631403687213783 22934475432947105530820675)
  ·
    refine ⟨34401713149420658296231013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22934475432947105530820675 34401713149420658296231013)
    ·
      refine ⟨6450321215516373430543315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34401713149420658296231013 6450321215516373430543315)
      ·
        refine ⟨9675481823274560145814973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6450321215516373430543315 9675481823274560145814973)
        ·
          refine ⟨3628305683727960054680615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9675481823274560145814973 3628305683727960054680615)
          ·
            refine ⟨5442458525591940082020923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628305683727960054680615 5442458525591940082020923)
            ·
              refine ⟨8163687788387910123031385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442458525591940082020923 8163687788387910123031385)
              ·
                refine ⟨6122765841290932592273539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8163687788387910123031385 6122765841290932592273539)
                ·
                  refine ⟨9184148761936398888410309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6122765841290932592273539 9184148761936398888410309)
                  ·
                    refine ⟨1722027892863074791576933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9184148761936398888410309 1722027892863074791576933)
                    ·
                      refine ⟨322880229911826523420675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1722027892863074791576933 322880229911826523420675)
                      ·
                        rfl

theorem cell23_628807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_628807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628807 prefixEnd_628807 := by exact prefixLift 628807
  have htrace : WordTrace (prefixWord ++ tailWord_628807) baseStart_628807 baseEnd_628807 := by
    simpa [prefixWord, tailWord_628807, baseEnd_628807] using wordTrace_append hprefix tailTrace_628807
  have hstable : (prefixWord ++ tailWord_628807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628807).length < 2 ^ (prefixWord ++ tailWord_628807).sum := by decide
  have hdescent : baseEnd_628807 < baseStart_628807 := by decide
  rcases family_descends (prefixWord ++ tailWord_628807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628822 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_628822 : Nat := 118140960795 + 628822 * 2 ^ 59
def prefixEnd_628822 : Nat := 4983230072969 + 3 ^ 40 * 628822 * 2
def baseEnd_628822 : Nat := 322887932121643964733107

theorem tailTrace_628822 : CollatzResearch.WordTrace tailWord_628822 prefixEnd_628822 322887932121643964733107 := by
  unfold tailWord_628822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433438907993297693288545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15290015018595175395077813 1433438907993297693288545)
  ·
    refine ⟨1075079180994973269966409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1433438907993297693288545 1075079180994973269966409)
    ·
      refine ⟨806309385746229952474807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075079180994973269966409 806309385746229952474807)
      ·
        refine ⟨1209464078619344928712211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806309385746229952474807 1209464078619344928712211)
        ·
          refine ⟨1814196117929017393068317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209464078619344928712211 1814196117929017393068317)
          ·
            refine ⟨680323544223381522400619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1814196117929017393068317 680323544223381522400619)
            ·
              refine ⟨1020485316335072283600929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680323544223381522400619 1020485316335072283600929)
              ·
                refine ⟨765363987251304212700697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020485316335072283600929 765363987251304212700697)
                ·
                  refine ⟨574022990438478159525523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765363987251304212700697 574022990438478159525523)
                  ·
                    refine ⟨861034485657717239288285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 574022990438478159525523 861034485657717239288285)
                    ·
                      refine ⟨322887932121643964733107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861034485657717239288285 322887932121643964733107)
                      ·
                        rfl

theorem cell23_628822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_628822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628822 prefixEnd_628822 := by exact prefixLift 628822
  have htrace : WordTrace (prefixWord ++ tailWord_628822) baseStart_628822 baseEnd_628822 := by
    simpa [prefixWord, tailWord_628822, baseEnd_628822] using wordTrace_append hprefix tailTrace_628822
  have hstable : (prefixWord ++ tailWord_628822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628822).length < 2 ^ (prefixWord ++ tailWord_628822).sum := by decide
  have hdescent : baseEnd_628822 < baseStart_628822 := by decide
  rcases family_descends (prefixWord ++ tailWord_628822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628828 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_628828 : Nat := 118140960795 + 628828 * 2 ^ 59
def prefixEnd_628828 : Nat := 4983230072969 + 3 ^ 40 * 628828 * 2
def baseEnd_628828 : Nat := 322891013005570941258079

theorem tailTrace_628828 : CollatzResearch.WordTrace tailWord_628828 prefixEnd_628828 322891013005570941258079 := by
  unfold tailWord_628828
  simp only [CollatzResearch.WordTrace]
  refine ⟨11467620682935513058667569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15290160910580684078223425 11467620682935513058667569)
  ·
    refine ⟨8600715512201634794000677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11467620682935513058667569 8600715512201634794000677)
    ·
      refine ⟨1612634158537806523875127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8600715512201634794000677 1612634158537806523875127)
      ·
        refine ⟨2418951237806709785812691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612634158537806523875127 2418951237806709785812691)
        ·
          refine ⟨3628426856710064678719037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418951237806709785812691 3628426856710064678719037)
          ·
            refine ⟨1360660071266274254519639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3628426856710064678719037 1360660071266274254519639)
            ·
              refine ⟨2040990106899411381779459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360660071266274254519639 2040990106899411381779459)
              ·
                refine ⟨3061485160349117072669189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040990106899411381779459 3061485160349117072669189)
                ·
                  refine ⟨574028467565459451125473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3061485160349117072669189 574028467565459451125473)
                  ·
                    refine ⟨430521350674094588344105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 574028467565459451125473 430521350674094588344105)
                    ·
                      refine ⟨322891013005570941258079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430521350674094588344105 322891013005570941258079)
                      ·
                        rfl

theorem cell23_628828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_628828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628828 prefixEnd_628828 := by exact prefixLift 628828
  have htrace : WordTrace (prefixWord ++ tailWord_628828) baseStart_628828 baseEnd_628828 := by
    simpa [prefixWord, tailWord_628828, baseEnd_628828] using wordTrace_append hprefix tailTrace_628828
  have hstable : (prefixWord ++ tailWord_628828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628828).length < 2 ^ (prefixWord ++ tailWord_628828).sum := by decide
  have hdescent : baseEnd_628828 < baseStart_628828 := by decide
  rcases family_descends (prefixWord ++ tailWord_628828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628844 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_628844 : Nat := 118140960795 + 628844 * 2 ^ 59
def prefixEnd_628844 : Nat := 4983230072969 + 3 ^ 40 * 628844 * 2
def baseEnd_628844 : Nat := 322899228696042878658005

theorem tailTrace_628844 : CollatzResearch.WordTrace tailWord_628844 prefixEnd_628844 322899228696042878658005 := by
  unfold tailWord_628844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11467912466906530424958793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15290549955875373899945057 11467912466906530424958793)
  ·
    refine ⟨8600934350179897818719095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11467912466906530424958793 8600934350179897818719095)
    ·
      refine ⟨12901401525269846728078643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8600934350179897818719095 12901401525269846728078643)
      ·
        refine ⟨19352102287904770092117965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12901401525269846728078643 19352102287904770092117965)
        ·
          refine ⟨7257038357964288784544237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19352102287904770092117965 7257038357964288784544237)
          ·
            refine ⟨2721389384236608294204089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7257038357964288784544237 2721389384236608294204089)
            ·
              refine ⟨2041042038177456220653067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721389384236608294204089 2041042038177456220653067)
              ·
                refine ⟨3061563057266184330979601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041042038177456220653067 3061563057266184330979601)
                ·
                  refine ⟨2296172292949638248234701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061563057266184330979601 2296172292949638248234701)
                  ·
                    refine ⟨861064609856114343088013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2296172292949638248234701 861064609856114343088013)
                    ·
                      refine ⟨322899228696042878658005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861064609856114343088013 322899228696042878658005)
                      ·
                        rfl

theorem cell23_628844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_628844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628844 prefixEnd_628844 := by exact prefixLift 628844
  have htrace : WordTrace (prefixWord ++ tailWord_628844) baseStart_628844 baseEnd_628844 := by
    simpa [prefixWord, tailWord_628844, baseEnd_628844] using wordTrace_append hprefix tailTrace_628844
  have hstable : (prefixWord ++ tailWord_628844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628844).length < 2 ^ (prefixWord ++ tailWord_628844).sum := by decide
  have hdescent : baseEnd_628844 < baseStart_628844 := by decide
  rcases family_descends (prefixWord ++ tailWord_628844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628845 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_628845 : Nat := 118140960795 + 628845 * 2 ^ 59
def prefixEnd_628845 : Nat := 4983230072969 + 3 ^ 40 * 628845 * 2
def baseEnd_628845 : Nat := 322899742176697374745501

theorem tailTrace_628845 : CollatzResearch.WordTrace tailWord_628845 prefixEnd_628845 322899742176697374745501 := by
  unfold tailWord_628845
  simp only [CollatzResearch.WordTrace]
  refine ⟨22935861406809438020703989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15290574271206292013802659 22935861406809438020703989)
  ·
    refine ⟨2150237006888384814440999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22935861406809438020703989 2150237006888384814440999)
    ·
      refine ⟨3225355510332577221661499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2150237006888384814440999 3225355510332577221661499)
      ·
        refine ⟨4838033265498865832492249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225355510332577221661499 4838033265498865832492249)
        ·
          refine ⟨3628524949124149374369187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838033265498865832492249 3628524949124149374369187)
          ·
            refine ⟨5442787423686224061553781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628524949124149374369187 5442787423686224061553781)
            ·
              refine ⟨510261320970583505770667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5442787423686224061553781 510261320970583505770667)
              ·
                refine ⟨765391981455875258656001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510261320970583505770667 765391981455875258656001)
                ·
                  refine ⟨574043986091906443992001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765391981455875258656001 574043986091906443992001)
                  ·
                    refine ⟨430532989568929832994001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 574043986091906443992001 430532989568929832994001)
                    ·
                      refine ⟨322899742176697374745501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430532989568929832994001 322899742176697374745501)
                      ·
                        rfl

theorem cell23_628845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_628845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628845 prefixEnd_628845 := by exact prefixLift 628845
  have htrace : WordTrace (prefixWord ++ tailWord_628845) baseStart_628845 baseEnd_628845 := by
    simpa [prefixWord, tailWord_628845, baseEnd_628845] using wordTrace_append hprefix tailTrace_628845
  have hstable : (prefixWord ++ tailWord_628845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628845).length < 2 ^ (prefixWord ++ tailWord_628845).sum := by decide
  have hdescent : baseEnd_628845 < baseStart_628845 := by decide
  rcases family_descends (prefixWord ++ tailWord_628845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628847 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 1, 7]
def baseStart_628847 : Nat := 118140960795 + 628847 * 2 ^ 59
def prefixEnd_628847 : Nat := 4983230072969 + 3 ^ 40 * 628847 * 2
def baseEnd_628847 : Nat := 107633589712668788973497

theorem tailTrace_628847 : CollatzResearch.WordTrace tailWord_628847 prefixEnd_628847 107633589712668788973497 := by
  unfold tailWord_628847
  simp only [CollatzResearch.WordTrace]
  refine ⟨22935934352802192362276795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15290622901868128241517863 22935934352802192362276795)
  ·
    refine ⟨34403901529203288543415193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22935934352802192362276795 34403901529203288543415193)
    ·
      refine ⟨25802926146902466407561395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34403901529203288543415193 25802926146902466407561395)
      ·
        refine ⟨38704389220353699611342093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25802926146902466407561395 38704389220353699611342093)
        ·
          refine ⟨14514145957632637354253285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38704389220353699611342093 14514145957632637354253285)
          ·
            refine ⟨2721402367056119503922491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14514145957632637354253285 2721402367056119503922491)
            ·
              refine ⟨4082103550584179255883737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721402367056119503922491 4082103550584179255883737)
              ·
                refine ⟨3061577662938134441912803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4082103550584179255883737 3061577662938134441912803)
                ·
                  refine ⟨4592366494407201662869205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061577662938134441912803 4592366494407201662869205)
                  ·
                    refine ⟨107633589712668788973497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4592366494407201662869205 107633589712668788973497)
                    ·
                      rfl

theorem cell23_628847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_628847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628847 prefixEnd_628847 := by exact prefixLift 628847
  have htrace : WordTrace (prefixWord ++ tailWord_628847) baseStart_628847 baseEnd_628847 := by
    simpa [prefixWord, tailWord_628847, baseEnd_628847] using wordTrace_append hprefix tailTrace_628847
  have hstable : (prefixWord ++ tailWord_628847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628847).length < 2 ^ (prefixWord ++ tailWord_628847).sum := by decide
  have hdescent : baseEnd_628847 < baseStart_628847 := by decide
  rcases family_descends (prefixWord ++ tailWord_628847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628921 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 3]
def baseStart_628921 : Nat := 118140960795 + 628921 * 2 ^ 59
def prefixEnd_628921 : Nat := 4983230072969 + 3 ^ 40 * 628921 * 2
def baseEnd_628921 : Nat := 322938766706439077395151

theorem tailTrace_628921 : CollatzResearch.WordTrace tailWord_628921 prefixEnd_628921 322938766706439077395151 := by
  unfold tailWord_628921
  simp only [CollatzResearch.WordTrace]
  refine ⟨22938633354534103000470617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15292422236356068666980411 22938633354534103000470617)
  ·
    refine ⟨17203975015900577250352963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22938633354534103000470617 17203975015900577250352963)
    ·
      refine ⟨25805962523850865875529445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17203975015900577250352963 25805962523850865875529445)
      ·
        refine ⟨4838617973222037351661771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25805962523850865875529445 4838617973222037351661771)
        ·
          refine ⟨7257926959833056027492657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838617973222037351661771 7257926959833056027492657)
          ·
            refine ⟨5443445219874792020619493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7257926959833056027492657 5443445219874792020619493)
            ·
              refine ⟨1020645978726523503866155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5443445219874792020619493 1020645978726523503866155)
              ·
                refine ⟨1530968968089785255799233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020645978726523503866155 1530968968089785255799233)
                ·
                  refine ⟨1148226726067338941849425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1530968968089785255799233 1148226726067338941849425)
                  ·
                    refine ⟨861170044550504206387069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148226726067338941849425 861170044550504206387069)
                    ·
                      refine ⟨322938766706439077395151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861170044550504206387069 322938766706439077395151)
                      ·
                        rfl

theorem cell23_628921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_628921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628921 prefixEnd_628921 := by exact prefixLift 628921
  have htrace : WordTrace (prefixWord ++ tailWord_628921) baseStart_628921 baseEnd_628921 := by
    simpa [prefixWord, tailWord_628921, baseEnd_628921] using wordTrace_append hprefix tailTrace_628921
  have hstable : (prefixWord ++ tailWord_628921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628921).length < 2 ^ (prefixWord ++ tailWord_628921).sum := by decide
  have hdescent : baseEnd_628921 < baseStart_628921 := by decide
  rcases family_descends (prefixWord ++ tailWord_628921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628927 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_628927 : Nat := 118140960795 + 628927 * 2 ^ 59
def prefixEnd_628927 : Nat := 4983230072969 + 3 ^ 40 * 628927 * 2
def baseEnd_628927 : Nat := 322941847590366053920123

theorem tailTrace_628927 : CollatzResearch.WordTrace tailWord_628927 prefixEnd_628927 322941847590366053920123 := by
  unfold tailWord_628927
  simp only [CollatzResearch.WordTrace]
  refine ⟨22938852192512366025189035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15292568128341577350126023 22938852192512366025189035)
  ·
    refine ⟨34408278288768549037783553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22938852192512366025189035 34408278288768549037783553)
    ·
      refine ⟨25806208716576411778337665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34408278288768549037783553 25806208716576411778337665)
      ·
        refine ⟨19354656537432308833753249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25806208716576411778337665 19354656537432308833753249)
        ·
          refine ⟨14515992403074231625314937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19354656537432308833753249 14515992403074231625314937)
          ·
            refine ⟨10886994302305673718986203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14515992403074231625314937 10886994302305673718986203)
            ·
              refine ⟨16330491453458510578479305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10886994302305673718986203 16330491453458510578479305)
              ·
                refine ⟨12247868590093882933859479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16330491453458510578479305 12247868590093882933859479)
                ·
                  refine ⟨18371802885140824400789219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12247868590093882933859479 18371802885140824400789219)
                  ·
                    refine ⟨27557704327711236601183829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18371802885140824400789219 27557704327711236601183829)
                    ·
                      refine ⟨322941847590366053920123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 27557704327711236601183829 322941847590366053920123)
                      ·
                        rfl

theorem cell23_628927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_628927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628927 prefixEnd_628927 := by exact prefixLift 628927
  have htrace : WordTrace (prefixWord ++ tailWord_628927) baseStart_628927 baseEnd_628927 := by
    simpa [prefixWord, tailWord_628927, baseEnd_628927] using wordTrace_append hprefix tailTrace_628927
  have hstable : (prefixWord ++ tailWord_628927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628927).length < 2 ^ (prefixWord ++ tailWord_628927).sum := by decide
  have hdescent : baseEnd_628927 < baseStart_628927 := by decide
  rcases family_descends (prefixWord ++ tailWord_628927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628947 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7]
def baseStart_628947 : Nat := 118140960795 + 628947 * 2 ^ 59
def prefixEnd_628947 : Nat := 4983230072969 + 3 ^ 40 * 628947 * 2
def baseEnd_628947 : Nat := 322952117203455975670031

theorem tailTrace_628947 : CollatzResearch.WordTrace tailWord_628947 prefixEnd_628947 322952117203455975670031 := by
  unfold tailWord_628947
  simp only [CollatzResearch.WordTrace]
  refine ⟨22939581652439909440917095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15293054434959939627278063 22939581652439909440917095)
  ·
    refine ⟨34409372478659864161375643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22939581652439909440917095 34409372478659864161375643)
    ·
      refine ⟨51614058717989796242063465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34409372478659864161375643 51614058717989796242063465)
      ·
        refine ⟨38710544038492347181547599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51614058717989796242063465 38710544038492347181547599)
        ·
          refine ⟨58065816057738520772321399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38710544038492347181547599 58065816057738520772321399)
          ·
            refine ⟨87098724086607781158482099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58065816057738520772321399 87098724086607781158482099)
            ·
              refine ⟨130648086129911671737723149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87098724086607781158482099 130648086129911671737723149)
              ·
                refine ⟨48993032298716876901646181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130648086129911671737723149 48993032298716876901646181)
                ·
                  refine ⟨9186193556009414419058659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48993032298716876901646181 9186193556009414419058659)
                  ·
                    refine ⟨13779290334014121628587989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9186193556009414419058659 13779290334014121628587989)
                    ·
                      refine ⟨322952117203455975670031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13779290334014121628587989 322952117203455975670031)
                      ·
                        rfl

theorem cell23_628947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_628947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628947 prefixEnd_628947 := by exact prefixLift 628947
  have htrace : WordTrace (prefixWord ++ tailWord_628947) baseStart_628947 baseEnd_628947 := by
    simpa [prefixWord, tailWord_628947, baseEnd_628947] using wordTrace_append hprefix tailTrace_628947
  have hstable : (prefixWord ++ tailWord_628947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628947).length < 2 ^ (prefixWord ++ tailWord_628947).sum := by decide
  have hdescent : baseEnd_628947 < baseStart_628947 := by decide
  rcases family_descends (prefixWord ++ tailWord_628947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628951 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_628951 : Nat := 118140960795 + 628951 * 2 ^ 59
def prefixEnd_628951 : Nat := 4983230072969 + 3 ^ 40 * 628951 * 2
def baseEnd_628951 : Nat := 322954171126073960020013

theorem tailTrace_628951 : CollatzResearch.WordTrace tailWord_628951 prefixEnd_628951 322954171126073960020013 := by
  unfold tailWord_628951
  simp only [CollatzResearch.WordTrace]
  refine ⟨22939727544425418124062707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15293151696283612082708471 22939727544425418124062707)
  ·
    refine ⟨34409591316638127186094061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22939727544425418124062707 34409591316638127186094061)
    ·
      refine ⟨12903596743739297694785273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34409591316638127186094061 12903596743739297694785273)
      ·
        refine ⟨9677697557804473271088955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12903596743739297694785273 9677697557804473271088955)
        ·
          refine ⟨14516546336706709906633433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677697557804473271088955 14516546336706709906633433)
          ·
            refine ⟨10887409752530032429975075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14516546336706709906633433 10887409752530032429975075)
            ·
              refine ⟨16331114628795048644962613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10887409752530032429975075 16331114628795048644962613)
              ·
                refine ⟨1531041996449535810465245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16331114628795048644962613 1531041996449535810465245)
                ·
                  refine ⟨574140748668575928924467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1531041996449535810465245 574140748668575928924467)
                  ·
                    refine ⟨861211123002863893386701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 574140748668575928924467 861211123002863893386701)
                    ·
                      refine ⟨322954171126073960020013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861211123002863893386701 322954171126073960020013)
                      ·
                        rfl

theorem cell23_628951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_628951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628951 prefixEnd_628951 := by exact prefixLift 628951
  have htrace : WordTrace (prefixWord ++ tailWord_628951) baseStart_628951 baseEnd_628951 := by
    simpa [prefixWord, tailWord_628951, baseEnd_628951] using wordTrace_append hprefix tailTrace_628951
  have hstable : (prefixWord ++ tailWord_628951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628951).length < 2 ^ (prefixWord ++ tailWord_628951).sum := by decide
  have hdescent : baseEnd_628951 < baseStart_628951 := by decide
  rcases family_descends (prefixWord ++ tailWord_628951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628954 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_628954 : Nat := 118140960795 + 628954 * 2 ^ 59
def prefixEnd_628954 : Nat := 4983230072969 + 3 ^ 40 * 628954 * 2
def baseEnd_628954 : Nat := 107651903856012482760833

theorem tailTrace_628954 : CollatzResearch.WordTrace tailWord_628954 prefixEnd_628954 107651903856012482760833 := by
  unfold tailWord_628954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734959240853637409105479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15293224642276366424281277 5734959240853637409105479)
  ·
    refine ⟨8602438861280456113658219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5734959240853637409105479 8602438861280456113658219)
    ·
      refine ⟨12903658291920684170487329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8602438861280456113658219 12903658291920684170487329)
      ·
        refine ⟨9677743718940513127865497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12903658291920684170487329 9677743718940513127865497)
        ·
          refine ⟨7258307789205384845899123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9677743718940513127865497 7258307789205384845899123)
          ·
            refine ⟨10887461683808077268848685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7258307789205384845899123 10887461683808077268848685)
            ·
              refine ⟨4082798131428028975818257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10887461683808077268848685 4082798131428028975818257)
              ·
                refine ⟨3062098598571021731863693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4082798131428028975818257 3062098598571021731863693)
                ·
                  refine ⟨1148286974464133149448885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3062098598571021731863693 1148286974464133149448885)
                  ·
                    refine ⟨107651903856012482760833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1148286974464133149448885 107651903856012482760833)
                    ·
                      rfl

theorem cell23_628954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_628954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628954 prefixEnd_628954 := by exact prefixLift 628954
  have htrace : WordTrace (prefixWord ++ tailWord_628954) baseStart_628954 baseEnd_628954 := by
    simpa [prefixWord, tailWord_628954, baseEnd_628954] using wordTrace_append hprefix tailTrace_628954
  have hstable : (prefixWord ++ tailWord_628954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628954).length < 2 ^ (prefixWord ++ tailWord_628954).sum := by decide
  have hdescent : baseEnd_628954 < baseStart_628954 := by decide
  rcases family_descends (prefixWord ++ tailWord_628954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628961 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_628961 : Nat := 118140960795 + 628961 * 2 ^ 59
def prefixEnd_628961 : Nat := 4983230072969 + 3 ^ 40 * 628961 * 2
def baseEnd_628961 : Nat := 322959305932618920894967

theorem tailTrace_628961 : CollatzResearch.WordTrace tailWord_628961 prefixEnd_628961 322959305932618920894967 := by
  unfold tailWord_628961
  simp only [CollatzResearch.WordTrace]
  refine ⟨22940092274389189831926737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15293394849592793221284491 22940092274389189831926737)
  ·
    refine ⟨17205069205791892373945053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22940092274389189831926737 17205069205791892373945053)
    ·
      refine ⟨6451900952171959640229395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17205069205791892373945053 6451900952171959640229395)
      ·
        refine ⟨9677851428257939460344093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6451900952171959640229395 9677851428257939460344093)
        ·
          refine ⟨3629194285596727297629035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9677851428257939460344093 3629194285596727297629035)
          ·
            refine ⟨5443791428395090946443553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629194285596727297629035 5443791428395090946443553)
            ·
              refine ⟨4082843571296318209832665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5443791428395090946443553 4082843571296318209832665)
              ·
                refine ⟨3062132678472238657374499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4082843571296318209832665 3062132678472238657374499)
                ·
                  refine ⟨4593199017708357986061749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062132678472238657374499 4593199017708357986061749)
                  ·
                    refine ⟨430612407910158561193289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4593199017708357986061749 430612407910158561193289)
                    ·
                      refine ⟨322959305932618920894967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430612407910158561193289 322959305932618920894967)
                      ·
                        rfl

theorem cell23_628961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_628961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628961 prefixEnd_628961 := by exact prefixLift 628961
  have htrace : WordTrace (prefixWord ++ tailWord_628961) baseStart_628961 baseEnd_628961 := by
    simpa [prefixWord, tailWord_628961, baseEnd_628961] using wordTrace_append hprefix tailTrace_628961
  have hstable : (prefixWord ++ tailWord_628961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628961).length < 2 ^ (prefixWord ++ tailWord_628961).sum := by decide
  have hdescent : baseEnd_628961 < baseStart_628961 := by decide
  rcases family_descends (prefixWord ++ tailWord_628961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628962 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_628962 : Nat := 118140960795 + 628962 * 2 ^ 59
def prefixEnd_628962 : Nat := 4983230072969 + 3 ^ 40 * 628962 * 2
def baseEnd_628962 : Nat := 107653273137757805660821

theorem tailTrace_628962 : CollatzResearch.WordTrace tailWord_628962 prefixEnd_628962 107653273137757805660821 := by
  unfold tailWord_628962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735032186846391750678285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15293419164923711335142093 5735032186846391750678285)
  ·
    refine ⟨2150637070067396906504357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5735032186846391750678285 2150637070067396906504357)
    ·
      refine ⟨403244450637636919969567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2150637070067396906504357 403244450637636919969567)
      ·
        refine ⟨604866675956455379954351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403244450637636919969567 604866675956455379954351)
        ·
          refine ⟨907300013934683069931527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604866675956455379954351 907300013934683069931527)
          ·
            refine ⟨1360950020902024604897291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907300013934683069931527 1360950020902024604897291)
            ·
              refine ⟨2041425031353036907345937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360950020902024604897291 2041425031353036907345937)
              ·
                refine ⟨1531068773514777680509453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041425031353036907345937 1531068773514777680509453)
                ·
                  refine ⟨574150790068041630191045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1531068773514777680509453 574150790068041630191045)
                  ·
                    refine ⟨107653273137757805660821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 574150790068041630191045 107653273137757805660821)
                    ·
                      rfl

theorem cell23_628962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_628962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628962 prefixEnd_628962 := by exact prefixLift 628962
  have htrace : WordTrace (prefixWord ++ tailWord_628962) baseStart_628962 baseEnd_628962 := by
    simpa [prefixWord, tailWord_628962, baseEnd_628962] using wordTrace_append hprefix tailTrace_628962
  have hstable : (prefixWord ++ tailWord_628962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628962).length < 2 ^ (prefixWord ++ tailWord_628962).sum := by decide
  have hdescent : baseEnd_628962 < baseStart_628962 := by decide
  rcases family_descends (prefixWord ++ tailWord_628962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628968 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_628968 : Nat := 118140960795 + 628968 * 2 ^ 59
def prefixEnd_628968 : Nat := 4983230072969 + 3 ^ 40 * 628968 * 2
def baseEnd_628968 : Nat := 322962900297200393507435

theorem tailTrace_628968 : CollatzResearch.WordTrace tailWord_628968 prefixEnd_628968 322962900297200393507435 := by
  unfold tailWord_628968
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470173792681915013715779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15293565056909220018287705 11470173792681915013715779)
  ·
    refine ⟨17205260689022872520573669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11470173792681915013715779 17205260689022872520573669)
    ·
      refine ⟨3225986379191788597607563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17205260689022872520573669 3225986379191788597607563)
      ·
        refine ⟨4838979568787682896411345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225986379191788597607563 4838979568787682896411345)
        ·
          refine ⟨3629234676590762172308509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838979568787682896411345 3629234676590762172308509)
          ·
            refine ⟨1360963003721535814615691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3629234676590762172308509 1360963003721535814615691)
            ·
              refine ⟨2041444505582303721923537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360963003721535814615691 2041444505582303721923537)
              ·
                refine ⟨1531083379186727791442653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041444505582303721923537 1531083379186727791442653)
                ·
                  refine ⟨574156267195022921790995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1531083379186727791442653 574156267195022921790995)
                  ·
                    refine ⟨861234400792534382686493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 574156267195022921790995 861234400792534382686493)
                    ·
                      refine ⟨322962900297200393507435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861234400792534382686493 322962900297200393507435)
                      ·
                        rfl

theorem cell23_628968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_628968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628968 prefixEnd_628968 := by exact prefixLift 628968
  have htrace : WordTrace (prefixWord ++ tailWord_628968) baseStart_628968 baseEnd_628968 := by
    simpa [prefixWord, tailWord_628968, baseEnd_628968] using wordTrace_append hprefix tailTrace_628968
  have hstable : (prefixWord ++ tailWord_628968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628968).length < 2 ^ (prefixWord ++ tailWord_628968).sum := by decide
  have hdescent : baseEnd_628968 < baseStart_628968 := by decide
  rcases family_descends (prefixWord ++ tailWord_628968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628978 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_628978 : Nat := 118140960795 + 628978 * 2 ^ 59
def prefixEnd_628978 : Nat := 4983230072969 + 3 ^ 40 * 628978 * 2
def baseEnd_628978 : Nat := 322968035103745354382389

theorem tailTrace_628978 : CollatzResearch.WordTrace tailWord_628978 prefixEnd_628978 322968035103745354382389 := by
  unfold tailWord_628978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735178078831900433823897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15293808210218401156863725 5735178078831900433823897)
  ·
    refine ⟨4301383559123925325367923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5735178078831900433823897 4301383559123925325367923)
    ·
      refine ⟨6452075338685887988051885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301383559123925325367923 6452075338685887988051885)
      ·
        refine ⟨2419528252007207995519457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6452075338685887988051885 2419528252007207995519457)
        ·
          refine ⟨1814646189005405996639593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2419528252007207995519457 1814646189005405996639593)
          ·
            refine ⟨1360984641754054497479695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1814646189005405996639593 1360984641754054497479695)
            ·
              refine ⟨2041476962631081746219543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360984641754054497479695 2041476962631081746219543)
              ·
                refine ⟨3062215443946622619329315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041476962631081746219543 3062215443946622619329315)
                ·
                  refine ⟨4593323165919933928993973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062215443946622619329315 4593323165919933928993973)
                  ·
                    refine ⟨430624046804993805843185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4593323165919933928993973 430624046804993805843185)
                    ·
                      refine ⟨322968035103745354382389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430624046804993805843185 322968035103745354382389)
                      ·
                        rfl

theorem cell23_628978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_628978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628978 prefixEnd_628978 := by exact prefixLift 628978
  have htrace : WordTrace (prefixWord ++ tailWord_628978) baseStart_628978 baseEnd_628978 := by
    simpa [prefixWord, tailWord_628978, baseEnd_628978] using wordTrace_append hprefix tailTrace_628978
  have hstable : (prefixWord ++ tailWord_628978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628978).length < 2 ^ (prefixWord ++ tailWord_628978).sum := by decide
  have hdescent : baseEnd_628978 < baseStart_628978 := by decide
  rcases family_descends (prefixWord ++ tailWord_628978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628988 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_628988 : Nat := 118140960795 + 628988 * 2 ^ 59
def prefixEnd_628988 : Nat := 4983230072969 + 3 ^ 40 * 628988 * 2
def baseEnd_628988 : Nat := 107657723303430105085781

theorem tailTrace_628988 : CollatzResearch.WordTrace tailWord_628988 prefixEnd_628988 107657723303430105085781 := by
  unfold tailWord_628988
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470538522645686721579809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15294051363527582295439745 11470538522645686721579809)
  ·
    refine ⟨8602903891984265041184857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11470538522645686721579809 8602903891984265041184857)
    ·
      refine ⟨6452177918988198780888643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8602903891984265041184857 6452177918988198780888643)
      ·
        refine ⟨9678266878482298171332965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6452177918988198780888643 9678266878482298171332965)
        ·
          refine ⟨1814675039715430907124931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9678266878482298171332965 1814675039715430907124931)
          ·
            refine ⟨2722012559573146360687397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814675039715430907124931 2722012559573146360687397)
            ·
              refine ⟨510377354919964942628887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2722012559573146360687397 510377354919964942628887)
              ·
                refine ⟨765566032379947413943331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510377354919964942628887 765566032379947413943331)
                ·
                  refine ⟨1148349048569921120914997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765566032379947413943331 1148349048569921120914997)
                  ·
                    refine ⟨107657723303430105085781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1148349048569921120914997 107657723303430105085781)
                    ·
                      rfl

theorem cell23_628988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_628988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628988 prefixEnd_628988 := by exact prefixLift 628988
  have htrace : WordTrace (prefixWord ++ tailWord_628988) baseStart_628988 baseEnd_628988 := by
    simpa [prefixWord, tailWord_628988, baseEnd_628988] using wordTrace_append hprefix tailTrace_628988
  have hstable : (prefixWord ++ tailWord_628988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628988).length < 2 ^ (prefixWord ++ tailWord_628988).sum := by decide
  have hdescent : baseEnd_628988 < baseStart_628988 := by decide
  rcases family_descends (prefixWord ++ tailWord_628988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628991 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 4]
def baseStart_628991 : Nat := 118140960795 + 628991 * 2 ^ 59
def prefixEnd_628991 : Nat := 4983230072969 + 3 ^ 40 * 628991 * 2
def baseEnd_628991 : Nat := 322974710352253803519829

theorem tailTrace_628991 : CollatzResearch.WordTrace tailWord_628991 prefixEnd_628991 322974710352253803519829 := by
  unfold tailWord_628991
  simp only [CollatzResearch.WordTrace]
  refine ⟨22941186464280504955518827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15294124309520336637012551 22941186464280504955518827)
  ·
    refine ⟨34411779696420757433278241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22941186464280504955518827 34411779696420757433278241)
    ·
      refine ⟨25808834772315568074958681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34411779696420757433278241 25808834772315568074958681)
      ·
        refine ⟨19356626079236676056219011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25808834772315568074958681 19356626079236676056219011)
        ·
          refine ⟨29034939118855014084328517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19356626079236676056219011 29034939118855014084328517)
          ·
            refine ⟨5444051084785315140811597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29034939118855014084328517 5444051084785315140811597)
            ·
              refine ⟨2041519156794493177804349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5444051084785315140811597 2041519156794493177804349)
              ·
                refine ⟨765569683797934941676631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2041519156794493177804349 765569683797934941676631)
                ·
                  refine ⟨1148354525696902412514947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765569683797934941676631 1148354525696902412514947)
                  ·
                    refine ⟨1722531788545353618772421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1148354525696902412514947 1722531788545353618772421)
                    ·
                      refine ⟨322974710352253803519829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1722531788545353618772421 322974710352253803519829)
                      ·
                        rfl

theorem cell23_628991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_628991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_628991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_628991 prefixEnd_628991 := by exact prefixLift 628991
  have htrace : WordTrace (prefixWord ++ tailWord_628991) baseStart_628991 baseEnd_628991 := by
    simpa [prefixWord, tailWord_628991, baseEnd_628991] using wordTrace_append hprefix tailTrace_628991
  have hstable : (prefixWord ++ tailWord_628991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628991).length < 2 ^ (prefixWord ++ tailWord_628991).sum := by decide
  have hdescent : baseEnd_628991 < baseStart_628991 := by decide
  rcases family_descends (prefixWord ++ tailWord_628991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629001 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 4, 4]
def baseStart_629001 : Nat := 118140960795 + 629001 * 2 ^ 59
def prefixEnd_629001 : Nat := 4983230072969 + 3 ^ 40 * 629001 * 2
def baseEnd_629001 : Nat := 107659948386266254798261

theorem tailTrace_629001 : CollatzResearch.WordTrace tailWord_629001 prefixEnd_629001 107659948386266254798261 := by
  unfold tailWord_629001
  simp only [CollatzResearch.WordTrace]
  refine ⟨22941551194244276663382857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15294367462829517775588571 22941551194244276663382857)
  ·
    refine ⟨17206163395683207497537143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22941551194244276663382857 17206163395683207497537143)
    ·
      refine ⟨25809245093524811246305715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17206163395683207497537143 25809245093524811246305715)
      ·
        refine ⟨38713867640287216869458573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25809245093524811246305715 38713867640287216869458573)
        ·
          refine ⟨14517700365107706326046965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38713867640287216869458573 14517700365107706326046965)
          ·
            refine ⟨1361034409228847468066903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14517700365107706326046965 1361034409228847468066903)
            ·
              refine ⟨2041551613843271202100355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361034409228847468066903 2041551613843271202100355)
              ·
                refine ⟨3062327420764906803150533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041551613843271202100355 3062327420764906803150533)
                ·
                  refine ⟨574186391393420025590725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3062327420764906803150533 574186391393420025590725)
                  ·
                    refine ⟨107659948386266254798261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 574186391393420025590725 107659948386266254798261)
                    ·
                      rfl

theorem cell23_629001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_629001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629001 prefixEnd_629001 := by exact prefixLift 629001
  have htrace : WordTrace (prefixWord ++ tailWord_629001) baseStart_629001 baseEnd_629001 := by
    simpa [prefixWord, tailWord_629001, baseEnd_629001] using wordTrace_append hprefix tailTrace_629001
  have hstable : (prefixWord ++ tailWord_629001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629001).length < 2 ^ (prefixWord ++ tailWord_629001).sum := by decide
  have hdescent : baseEnd_629001 < baseStart_629001 := by decide
  rcases family_descends (prefixWord ++ tailWord_629001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629004 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_629004 : Nat := 118140960795 + 629004 * 2 ^ 59
def prefixEnd_629004 : Nat := 4983230072969 + 3 ^ 40 * 629004 * 2
def baseEnd_629004 : Nat := 322981385600762252657269

theorem tailTrace_629004 : CollatzResearch.WordTrace tailWord_629004 prefixEnd_629004 322981385600762252657269 := by
  unfold tailWord_629004
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470830306616704087871033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15294440408822272117161377 11470830306616704087871033)
  ·
    refine ⟨8603122729962528065903275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11470830306616704087871033 8603122729962528065903275)
    ·
      refine ⟨12904684094943792098854913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8603122729962528065903275 12904684094943792098854913)
      ·
        refine ⟨9678513071207844074141185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12904684094943792098854913 9678513071207844074141185)
        ·
          refine ⟨7258884803405883055605889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9678513071207844074141185 7258884803405883055605889)
          ·
            refine ⟨5444163602554412291704417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7258884803405883055605889 5444163602554412291704417)
            ·
              refine ⟨4083122701915809218778313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5444163602554412291704417 4083122701915809218778313)
              ·
                refine ⟨3062342026436856914083735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4083122701915809218778313 3062342026436856914083735)
                ·
                  refine ⟨4593513039655285371125603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062342026436856914083735 4593513039655285371125603)
                  ·
                    refine ⟨6890269559482928056688405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4593513039655285371125603 6890269559482928056688405)
                    ·
                      refine ⟨322981385600762252657269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6890269559482928056688405 322981385600762252657269)
                      ·
                        rfl

theorem cell23_629004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_629004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629004 prefixEnd_629004 := by exact prefixLift 629004
  have htrace : WordTrace (prefixWord ++ tailWord_629004) baseStart_629004 baseEnd_629004 := by
    simpa [prefixWord, tailWord_629004, baseEnd_629004] using wordTrace_append hprefix tailTrace_629004
  have hstable : (prefixWord ++ tailWord_629004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629004).length < 2 ^ (prefixWord ++ tailWord_629004).sum := by decide
  have hdescent : baseEnd_629004 < baseStart_629004 := by decide
  rcases family_descends (prefixWord ++ tailWord_629004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629018 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_629018 : Nat := 118140960795 + 629018 * 2 ^ 59
def prefixEnd_629018 : Nat := 4983230072969 + 3 ^ 40 * 629018 * 2
def baseEnd_629018 : Nat := 107662858109975065960735

theorem tailTrace_629018 : CollatzResearch.WordTrace tailWord_629018 prefixEnd_629018 107662858109975065960735 := by
  unfold tailWord_629018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735542808795672141687927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15294780823455125711167805 5735542808795672141687927)
  ·
    refine ⟨8603314213193508212531891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5735542808795672141687927 8603314213193508212531891)
    ·
      refine ⟨12904971319790262318797837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8603314213193508212531891 12904971319790262318797837)
      ·
        refine ⟨4839364244921348369549189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12904971319790262318797837 4839364244921348369549189)
        ·
          refine ⟨907380795922752819290473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4839364244921348369549189 907380795922752819290473)
          ·
            refine ⟨680535596942064614467855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907380795922752819290473 680535596942064614467855)
            ·
              refine ⟨1020803395413096921701783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680535596942064614467855 1020803395413096921701783)
              ·
                refine ⟨1531205093119645382552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020803395413096921701783 1531205093119645382552675)
                ·
                  refine ⟨2296807639679468073829013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531205093119645382552675 2296807639679468073829013)
                  ·
                    refine ⟨107662858109975065960735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2296807639679468073829013 107662858109975065960735)
                    ·
                      rfl

theorem cell23_629018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_629018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629018 prefixEnd_629018 := by exact prefixLift 629018
  have htrace : WordTrace (prefixWord ++ tailWord_629018) baseStart_629018 baseEnd_629018 := by
    simpa [prefixWord, tailWord_629018, baseEnd_629018] using wordTrace_append hprefix tailTrace_629018
  have hstable : (prefixWord ++ tailWord_629018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629018).length < 2 ^ (prefixWord ++ tailWord_629018).sum := by decide
  have hdescent : baseEnd_629018 < baseStart_629018 := by decide
  rcases family_descends (prefixWord ++ tailWord_629018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629028 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_629028 : Nat := 118140960795 + 629028 * 2 ^ 59
def prefixEnd_629028 : Nat := 4983230072969 + 3 ^ 40 * 629028 * 2
def baseEnd_629028 : Nat := 322993709136470158757159

theorem tailTrace_629028 : CollatzResearch.WordTrace tailWord_629028 prefixEnd_629028 322993709136470158757159 := by
  unfold tailWord_629028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11471267982573230137307869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15295023976764306849743825 11471267982573230137307869)
  ·
    refine ⟨4301725493464961301490451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11471267982573230137307869 4301725493464961301490451)
    ·
      refine ⟨6452588240197441952235677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301725493464961301490451 6452588240197441952235677)
      ·
        refine ⟨2419720590074040732088379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6452588240197441952235677 2419720590074040732088379)
        ·
          refine ⟨3629580885111061098132569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419720590074040732088379 3629580885111061098132569)
          ·
            refine ⟨2722185663833295823599427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3629580885111061098132569 2722185663833295823599427)
            ·
              refine ⟨4083278495749943735399141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722185663833295823599427 4083278495749943735399141)
              ·
                refine ⟨765614717953114450387339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4083278495749943735399141 765614717953114450387339)
                ·
                  refine ⟨1148422076929671675581009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765614717953114450387339 1148422076929671675581009)
                  ·
                    refine ⟨861316557697253756685757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148422076929671675581009 861316557697253756685757)
                    ·
                      refine ⟨322993709136470158757159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861316557697253756685757 322993709136470158757159)
                      ·
                        rfl

theorem cell23_629028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_629028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629028 prefixEnd_629028 := by exact prefixLift 629028
  have htrace : WordTrace (prefixWord ++ tailWord_629028) baseStart_629028 baseEnd_629028 := by
    simpa [prefixWord, tailWord_629028, baseEnd_629028] using wordTrace_append hprefix tailTrace_629028
  have hstable : (prefixWord ++ tailWord_629028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629028).length < 2 ^ (prefixWord ++ tailWord_629028).sum := by decide
  have hdescent : baseEnd_629028 < baseStart_629028 := by decide
  rcases family_descends (prefixWord ++ tailWord_629028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629068 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 3, 3, 2]
def baseStart_629068 : Nat := 118140960795 + 629068 * 2 ^ 59
def prefixEnd_629068 : Nat := 4983230072969 + 3 ^ 40 * 629068 * 2
def baseEnd_629068 : Nat := 323014248362650002256975

theorem tailTrace_629068 : CollatzResearch.WordTrace tailWord_629068 prefixEnd_629068 323014248362650002256975 := by
  unfold tailWord_629068
  simp only [CollatzResearch.WordTrace]
  refine ⟨11471997442500773553035929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15295996590001031404047905 11471997442500773553035929)
  ·
    refine ⟨8603998081875580164776947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11471997442500773553035929 8603998081875580164776947)
    ·
      refine ⟨12905997122813370247165421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8603998081875580164776947 12905997122813370247165421)
      ·
        refine ⟨4839748921055013842687033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12905997122813370247165421 4839748921055013842687033)
        ·
          refine ⟨3629811690791260382015275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4839748921055013842687033 3629811690791260382015275)
          ·
            refine ⟨5444717536186890573022913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629811690791260382015275 5444717536186890573022913)
            ·
              refine ⟨4083538152140167929767185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5444717536186890573022913 4083538152140167929767185)
              ·
                refine ⟨3062653614105125947325389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4083538152140167929767185 3062653614105125947325389)
                ·
                  refine ⟨1148495105289422230247021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3062653614105125947325389 1148495105289422230247021)
                  ·
                    refine ⟨430685664483533336342633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1148495105289422230247021 430685664483533336342633)
                    ·
                      refine ⟨323014248362650002256975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430685664483533336342633 323014248362650002256975)
                      ·
                        rfl

theorem cell23_629068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_629068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629068 prefixEnd_629068 := by exact prefixLift 629068
  have htrace : WordTrace (prefixWord ++ tailWord_629068) baseStart_629068 baseEnd_629068 := by
    simpa [prefixWord, tailWord_629068, baseEnd_629068] using wordTrace_append hprefix tailTrace_629068
  have hstable : (prefixWord ++ tailWord_629068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629068).length < 2 ^ (prefixWord ++ tailWord_629068).sum := by decide
  have hdescent : baseEnd_629068 < baseStart_629068 := by decide
  rcases family_descends (prefixWord ++ tailWord_629068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629101 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_629101 : Nat := 118140960795 + 629101 * 2 ^ 59
def prefixEnd_629101 : Nat := 4983230072969 + 3 ^ 40 * 629101 * 2
def baseEnd_629101 : Nat := 323031193224248373144323

theorem tailTrace_629101 : CollatzResearch.WordTrace tailWord_629101 prefixEnd_629101 323031193224248373144323 := by
  unfold tailWord_629101
  simp only [CollatzResearch.WordTrace]
  refine ⟨22945198493881993742023157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15296798995921329161348771 22945198493881993742023157)
  ·
    refine ⟨2151112358801436913314671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22945198493881993742023157 2151112358801436913314671)
    ·
      refine ⟨3226668538202155369972007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151112358801436913314671 3226668538202155369972007)
      ·
        refine ⟨4840002807303233054958011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226668538202155369972007 4840002807303233054958011)
        ·
          refine ⟨7260004210954849582437017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4840002807303233054958011 7260004210954849582437017)
          ·
            refine ⟨5445003158216137186827763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7260004210954849582437017 5445003158216137186827763)
            ·
              refine ⟨8167504737324205780241645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445003158216137186827763 8167504737324205780241645)
              ·
                refine ⟨3062814276496577167590617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8167504737324205780241645 3062814276496577167590617)
                ·
                  refine ⟨2297110707372432875692963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3062814276496577167590617 2297110707372432875692963)
                  ·
                    refine ⟨3445666061058649313539445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297110707372432875692963 3445666061058649313539445)
                    ·
                      refine ⟨323031193224248373144323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3445666061058649313539445 323031193224248373144323)
                      ·
                        rfl

theorem cell23_629101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_629101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629101 prefixEnd_629101 := by exact prefixLift 629101
  have htrace : WordTrace (prefixWord ++ tailWord_629101) baseStart_629101 baseEnd_629101 := by
    simpa [prefixWord, tailWord_629101, baseEnd_629101] using wordTrace_append hprefix tailTrace_629101
  have hstable : (prefixWord ++ tailWord_629101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629101).length < 2 ^ (prefixWord ++ tailWord_629101).sum := by decide
  have hdescent : baseEnd_629101 < baseStart_629101 := by decide
  rcases family_descends (prefixWord ++ tailWord_629101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629110 : List Nat := [5, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_629110 : Nat := 118140960795 + 629110 * 2 ^ 59
def prefixEnd_629110 : Nat := 4983230072969 + 3 ^ 40 * 629110 * 2
def baseEnd_629110 : Nat := 323035814550138837931783

theorem tailTrace_629110 : CollatzResearch.WordTrace tailWord_629110 prefixEnd_629110 323035814550138837931783 := by
  unfold tailWord_629110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434095421928086767443799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15297017833899592186067189 1434095421928086767443799)
  ·
    refine ⟨2151143132892130151165699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1434095421928086767443799 2151143132892130151165699)
    ·
      refine ⟨3226714699338195226748549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151143132892130151165699 3226714699338195226748549)
      ·
        refine ⟨605009006125911605015353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3226714699338195226748549 605009006125911605015353)
        ·
          refine ⟨453756754594433703761515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605009006125911605015353 453756754594433703761515)
          ·
            refine ⟨680635131891650555642273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453756754594433703761515 680635131891650555642273)
            ·
              refine ⟨510476348918737916731705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680635131891650555642273 510476348918737916731705)
              ·
                refine ⟨382857261689053437548779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510476348918737916731705 382857261689053437548779)
                ·
                  refine ⟨574285892533580156323169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382857261689053437548779 574285892533580156323169)
                  ·
                    refine ⟨430714419400185117242377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 574285892533580156323169 430714419400185117242377)
                    ·
                      refine ⟨323035814550138837931783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430714419400185117242377 323035814550138837931783)
                      ·
                        rfl

theorem cell23_629110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_629110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629110 prefixEnd_629110 := by exact prefixLift 629110
  have htrace : WordTrace (prefixWord ++ tailWord_629110) baseStart_629110 baseEnd_629110 := by
    simpa [prefixWord, tailWord_629110, baseEnd_629110] using wordTrace_append hprefix tailTrace_629110
  have hstable : (prefixWord ++ tailWord_629110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629110).length < 2 ^ (prefixWord ++ tailWord_629110).sum := by decide
  have hdescent : baseEnd_629110 < baseStart_629110 := by decide
  rcases family_descends (prefixWord ++ tailWord_629110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629115 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 2, 2, 2]
def baseStart_629115 : Nat := 118140960795 + 629115 * 2 ^ 59
def prefixEnd_629115 : Nat := 4983230072969 + 3 ^ 40 * 629115 * 2
def baseEnd_629115 : Nat := 323038381953411318369259

theorem tailTrace_629115 : CollatzResearch.WordTrace tailWord_629115 prefixEnd_629115 323038381953411318369259 := by
  unfold tailWord_629115
  simp only [CollatzResearch.WordTrace]
  refine ⟨22945709115831274133032799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15297139410554182755355199 22945709115831274133032799)
  ·
    refine ⟨34418563673746911199549199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22945709115831274133032799 34418563673746911199549199)
    ·
      refine ⟨51627845510620366799323799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34418563673746911199549199 51627845510620366799323799)
      ·
        refine ⟨77441768265930550198985699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51627845510620366799323799 77441768265930550198985699)
        ·
          refine ⟨116162652398895825298478549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77441768265930550198985699 116162652398895825298478549)
          ·
            refine ⟨2722562165599120905433091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 116162652398895825298478549 2722562165599120905433091)
            ·
              refine ⟨4083843248398681358149637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722562165599120905433091 4083843248398681358149637)
              ·
                refine ⟨765720609074752754653057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4083843248398681358149637 765720609074752754653057)
                ·
                  refine ⟨574290456806064565989793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765720609074752754653057 574290456806064565989793)
                  ·
                    refine ⟨430717842604548424492345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 574290456806064565989793 430717842604548424492345)
                    ·
                      refine ⟨323038381953411318369259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430717842604548424492345 323038381953411318369259)
                      ·
                        rfl

theorem cell23_629115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 2, 2].length) (baseStart_629115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629115 prefixEnd_629115 := by exact prefixLift 629115
  have htrace : WordTrace (prefixWord ++ tailWord_629115) baseStart_629115 baseEnd_629115 := by
    simpa [prefixWord, tailWord_629115, baseEnd_629115] using wordTrace_append hprefix tailTrace_629115
  have hstable : (prefixWord ++ tailWord_629115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629115).length < 2 ^ (prefixWord ++ tailWord_629115).sum := by decide
  have hdescent : baseEnd_629115 < baseStart_629115 := by decide
  rcases family_descends (prefixWord ++ tailWord_629115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629131 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 3]
def baseStart_629131 : Nat := 118140960795 + 629131 * 2 ^ 59
def prefixEnd_629131 : Nat := 4983230072969 + 3 ^ 40 * 629131 * 2
def baseEnd_629131 : Nat := 323046597643883255769185

theorem tailTrace_629131 : CollatzResearch.WordTrace tailWord_629131 prefixEnd_629131 323046597643883255769185 := by
  unfold tailWord_629131
  simp only [CollatzResearch.WordTrace]
  refine ⟨22946292683773308865615247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15297528455848872577076831 22946292683773308865615247)
  ·
    refine ⟨34419439025659963298422871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22946292683773308865615247 34419439025659963298422871)
    ·
      refine ⟨51629158538489944947634307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34419439025659963298422871 51629158538489944947634307)
      ·
        refine ⟨77443737807734917421451461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51629158538489944947634307 77443737807734917421451461)
        ·
          refine ⟨14520700838950297016522149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77443737807734917421451461 14520700838950297016522149)
          ·
            refine ⟨2722631407303180690597903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14520700838950297016522149 2722631407303180690597903)
            ·
              refine ⟨4083947110954771035896855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722631407303180690597903 4083947110954771035896855)
              ·
                refine ⟨6125920666432156553845283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4083947110954771035896855 6125920666432156553845283)
                ·
                  refine ⟨9188880999648234830767925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6125920666432156553845283 9188880999648234830767925)
                  ·
                    refine ⟨861457593717022015384493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9188880999648234830767925 861457593717022015384493)
                    ·
                      refine ⟨323046597643883255769185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861457593717022015384493 323046597643883255769185)
                      ·
                        rfl

theorem cell23_629131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 3].length) (baseStart_629131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629131 prefixEnd_629131 := by exact prefixLift 629131
  have htrace : WordTrace (prefixWord ++ tailWord_629131) baseStart_629131 baseEnd_629131 := by
    simpa [prefixWord, tailWord_629131, baseEnd_629131] using wordTrace_append hprefix tailTrace_629131
  have hstable : (prefixWord ++ tailWord_629131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629131).length < 2 ^ (prefixWord ++ tailWord_629131).sum := by decide
  have hdescent : baseEnd_629131 < baseStart_629131 := by decide
  rcases family_descends (prefixWord ++ tailWord_629131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629151 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 1, 7]
def baseStart_629151 : Nat := 118140960795 + 629151 * 2 ^ 59
def prefixEnd_629151 : Nat := 4983230072969 + 3 ^ 40 * 629151 * 2
def baseEnd_629151 : Nat := 107685622418991059173031

theorem tailTrace_629151 : CollatzResearch.WordTrace tailWord_629151 prefixEnd_629151 107685622418991059173031 := by
  unfold tailWord_629151
  simp only [CollatzResearch.WordTrace]
  refine ⟨22947022143700852281343307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15298014762467234854228871 22947022143700852281343307)
  ·
    refine ⟨34420533215551278422014961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22947022143700852281343307 34420533215551278422014961)
    ·
      refine ⟨25815399911663458816511221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34420533215551278422014961 25815399911663458816511221)
      ·
        refine ⟨2420193741718449264047927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25815399911663458816511221 2420193741718449264047927)
        ·
          refine ⟨3630290612577673896071891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420193741718449264047927 3630290612577673896071891)
          ·
            refine ⟨5445435918866510844107837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630290612577673896071891 5445435918866510844107837)
            ·
              refine ⟨2042038469574941566540439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5445435918866510844107837 2042038469574941566540439)
              ·
                refine ⟨3063057704362412349810659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042038469574941566540439 3063057704362412349810659)
                ·
                  refine ⟨4594586556543618524715989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063057704362412349810659 4594586556543618524715989)
                  ·
                    refine ⟨107685622418991059173031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4594586556543618524715989 107685622418991059173031)
                    ·
                      rfl

theorem cell23_629151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_629151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629151 prefixEnd_629151 := by exact prefixLift 629151
  have htrace : WordTrace (prefixWord ++ tailWord_629151) baseStart_629151 baseEnd_629151 := by
    simpa [prefixWord, tailWord_629151, baseEnd_629151] using wordTrace_append hprefix tailTrace_629151
  have hstable : (prefixWord ++ tailWord_629151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629151).length < 2 ^ (prefixWord ++ tailWord_629151).sum := by decide
  have hdescent : baseEnd_629151 < baseStart_629151 := by decide
  rcases family_descends (prefixWord ++ tailWord_629151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629172 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 7]
def baseStart_629172 : Nat := 118140960795 + 629172 * 2 ^ 59
def prefixEnd_629172 : Nat := 4983230072969 + 3 ^ 40 * 629172 * 2
def baseEnd_629172 : Nat := 35896405594524177261833

theorem tailTrace_629172 : CollatzResearch.WordTrace tailWord_629172 prefixEnd_629172 35896405594524177261833 := by
  unfold tailWord_629172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11473894038312386433928885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15298525384416515245238513 11473894038312386433928885)
  ·
    refine ⟨1075677566091786228180833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11473894038312386433928885 1075677566091786228180833)
    ·
      refine ⟨806758174568839671135625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075677566091786228180833 806758174568839671135625)
      ·
        refine ⟨605068630926629753351719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806758174568839671135625 605068630926629753351719)
        ·
          refine ⟨907602946389944630027579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605068630926629753351719 907602946389944630027579)
          ·
            refine ⟨1361404419584916945041369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907602946389944630027579 1361404419584916945041369)
            ·
              refine ⟨1021053314688687708781027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361404419584916945041369 1021053314688687708781027)
              ·
                refine ⟨1531579972033031563171541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021053314688687708781027 1531579972033031563171541)
                ·
                  refine ⟨35896405594524177261833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1531579972033031563171541 35896405594524177261833)
                  ·
                    rfl

theorem cell23_629172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_629172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629172 prefixEnd_629172 := by exact prefixLift 629172
  have htrace : WordTrace (prefixWord ++ tailWord_629172) baseStart_629172 baseEnd_629172 := by
    simpa [prefixWord, tailWord_629172, baseEnd_629172] using wordTrace_append hprefix tailTrace_629172
  have hstable : (prefixWord ++ tailWord_629172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629172).length < 2 ^ (prefixWord ++ tailWord_629172).sum := by decide
  have hdescent : baseEnd_629172 < baseStart_629172 := by decide
  rcases family_descends (prefixWord ++ tailWord_629172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629208 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_629208 : Nat := 118140960795 + 629208 * 2 ^ 59
def prefixEnd_629208 : Nat := 4983230072969 + 3 ^ 40 * 629208 * 2
def baseEnd_629208 : Nat := 323086135654279454506331

theorem tailTrace_629208 : CollatzResearch.WordTrace tailWord_629208 prefixEnd_629208 323086135654279454506331 := by
  unfold tailWord_629208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11474550552247175508084139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15299400736329567344112185 11474550552247175508084139)
  ·
    refine ⟨17211825828370763262126209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11474550552247175508084139 17211825828370763262126209)
    ·
      refine ⟨12908869371278072446594657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17211825828370763262126209 12908869371278072446594657)
      ·
        refine ⟨9681652028458554334945993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12908869371278072446594657 9681652028458554334945993)
        ·
          refine ⟨7261239021343915751209495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9681652028458554334945993 7261239021343915751209495)
          ·
            refine ⟨10891858532015873626814243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7261239021343915751209495 10891858532015873626814243)
            ·
              refine ⟨16337787798023810440221365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10891858532015873626814243 16337787798023810440221365)
              ·
                refine ⟨1531667606064732228770753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16337787798023810440221365 1531667606064732228770753)
                ·
                  refine ⟨1148750704548549171578065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531667606064732228770753 1148750704548549171578065)
                  ·
                    refine ⟨861563028411411878683549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148750704548549171578065 861563028411411878683549)
                    ·
                      refine ⟨323086135654279454506331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861563028411411878683549 323086135654279454506331)
                      ·
                        rfl

theorem cell23_629208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_629208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629208 prefixEnd_629208 := by exact prefixLift 629208
  have htrace : WordTrace (prefixWord ++ tailWord_629208) baseStart_629208 baseEnd_629208 := by
    simpa [prefixWord, tailWord_629208, baseEnd_629208] using wordTrace_append hprefix tailTrace_629208
  have hstable : (prefixWord ++ tailWord_629208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629208).length < 2 ^ (prefixWord ++ tailWord_629208).sum := by decide
  have hdescent : baseEnd_629208 < baseStart_629208 := by decide
  rcases family_descends (prefixWord ++ tailWord_629208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629232 : List Nat := [2, 1, 1, 1, 3, 3, 5, 2, 1, 4]
def baseStart_629232 : Nat := 118140960795 + 629232 * 2 ^ 59
def prefixEnd_629232 : Nat := 4983230072969 + 3 ^ 40 * 629232 * 2
def baseEnd_629232 : Nat := 107699486396662453535407

theorem tailTrace_629232 : CollatzResearch.WordTrace tailWord_629232 prefixEnd_629232 107699486396662453535407 := by
  unfold tailWord_629232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11474988228203701557520975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15299984304271602076694633 11474988228203701557520975)
  ·
    refine ⟨17212482342305552336281463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11474988228203701557520975 17212482342305552336281463)
    ·
      refine ⟨25818723513458328504422195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17212482342305552336281463 25818723513458328504422195)
      ·
        refine ⟨38728085270187492756633293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25818723513458328504422195 38728085270187492756633293)
        ·
          refine ⟨14523031976320309783737485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38728085270187492756633293 14523031976320309783737485)
          ·
            refine ⟨5446136991120116168901557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14523031976320309783737485 5446136991120116168901557)
            ·
              refine ⟨510575342917510890834521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5446136991120116168901557 510575342917510890834521)
              ·
                refine ⟨382931507188133168125891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510575342917510890834521 382931507188133168125891)
                ·
                  refine ⟨574397260782199752188837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382931507188133168125891 574397260782199752188837)
                  ·
                    refine ⟨107699486396662453535407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 574397260782199752188837 107699486396662453535407)
                    ·
                      rfl

theorem cell23_629232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 4].length) (baseStart_629232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629232 prefixEnd_629232 := by exact prefixLift 629232
  have htrace : WordTrace (prefixWord ++ tailWord_629232) baseStart_629232 baseEnd_629232 := by
    simpa [prefixWord, tailWord_629232, baseEnd_629232] using wordTrace_append hprefix tailTrace_629232
  have hstable : (prefixWord ++ tailWord_629232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629232).length < 2 ^ (prefixWord ++ tailWord_629232).sum := by decide
  have hdescent : baseEnd_629232 < baseStart_629232 := by decide
  rcases family_descends (prefixWord ++ tailWord_629232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629258 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_629258 : Nat := 118140960795 + 629258 * 2 ^ 59
def prefixEnd_629258 : Nat := 4983230072969 + 3 ^ 40 * 629258 * 2
def baseEnd_629258 : Nat := 107703936562334752960367

theorem tailTrace_629258 : CollatzResearch.WordTrace tailWord_629258 prefixEnd_629258 107703936562334752960367 := by
  unfold tailWord_629258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737731188578302388872107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15300616502875473036992285 5737731188578302388872107)
  ·
    refine ⟨8606596782867453583308161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5737731188578302388872107 8606596782867453583308161)
    ·
      refine ⟨6454947587150590187481121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8606596782867453583308161 6454947587150590187481121)
      ·
        refine ⟨4841210690362942640610841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6454947587150590187481121 4841210690362942640610841)
        ·
          refine ⟨3630908017772206980458131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4841210690362942640610841 3630908017772206980458131)
          ·
            refine ⟨5446362026658310470687197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630908017772206980458131 5446362026658310470687197)
            ·
              refine ⟨2042385759996866426507699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5446362026658310470687197 2042385759996866426507699)
              ·
                refine ⟨3063578639995299639761549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042385759996866426507699 3063578639995299639761549)
                ·
                  refine ⟨1148841989998237364910581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3063578639995299639761549 1148841989998237364910581)
                  ·
                    refine ⟨107703936562334752960367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1148841989998237364910581 107703936562334752960367)
                    ·
                      rfl

theorem cell23_629258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_629258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629258 prefixEnd_629258 := by exact prefixLift 629258
  have htrace : WordTrace (prefixWord ++ tailWord_629258) baseStart_629258 baseEnd_629258 := by
    simpa [prefixWord, tailWord_629258, baseEnd_629258] using wordTrace_append hprefix tailTrace_629258
  have hstable : (prefixWord ++ tailWord_629258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629258).length < 2 ^ (prefixWord ++ tailWord_629258).sum := by decide
  have hdescent : baseEnd_629258 < baseStart_629258 := by decide
  rcases family_descends (prefixWord ++ tailWord_629258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629291 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6]
def baseStart_629291 : Nat := 118140960795 + 629291 * 2 ^ 59
def prefixEnd_629291 : Nat := 4983230072969 + 3 ^ 40 * 629291 * 2
def baseEnd_629291 : Nat := 323128754548602629768449

theorem tailTrace_629291 : CollatzResearch.WordTrace tailWord_629291 prefixEnd_629291 323128754548602629768449 := by
  unfold tailWord_629291
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952128363193656191439727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15301418908795770794293151 22952128363193656191439727)
  ·
    refine ⟨34428192544790484287159591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22952128363193656191439727 34428192544790484287159591)
    ·
      refine ⟨51642288817185726430739387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34428192544790484287159591 51642288817185726430739387)
      ·
        refine ⟨77463433225778589646109081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51642288817185726430739387 77463433225778589646109081)
        ·
          refine ⟨58097574919333942234581811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77463433225778589646109081 58097574919333942234581811)
          ·
            refine ⟨87146362379000913351872717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58097574919333942234581811 87146362379000913351872717)
            ·
              refine ⟨32679885892125342506952269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87146362379000913351872717 32679885892125342506952269)
              ·
                refine ⟨12254957209547003440107101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32679885892125342506952269 12254957209547003440107101)
                ·
                  refine ⟨4595608953580126290040163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12254957209547003440107101 4595608953580126290040163)
                  ·
                    refine ⟨6893413430370189435060245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595608953580126290040163 6893413430370189435060245)
                    ·
                      refine ⟨323128754548602629768449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6893413430370189435060245 323128754548602629768449)
                      ·
                        rfl

theorem cell23_629291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_629291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629291 prefixEnd_629291 := by exact prefixLift 629291
  have htrace : WordTrace (prefixWord ++ tailWord_629291) baseStart_629291 baseEnd_629291 := by
    simpa [prefixWord, tailWord_629291, baseEnd_629291] using wordTrace_append hprefix tailTrace_629291
  have hstable : (prefixWord ++ tailWord_629291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629291).length < 2 ^ (prefixWord ++ tailWord_629291).sum := by decide
  have hdescent : baseEnd_629291 < baseStart_629291 := by decide
  rcases family_descends (prefixWord ++ tailWord_629291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629295 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 9, 2, 2]
def baseStart_629295 : Nat := 118140960795 + 629295 * 2 ^ 59
def prefixEnd_629295 : Nat := 4983230072969 + 3 ^ 40 * 629295 * 2
def baseEnd_629295 : Nat := 323130808471220614118431

theorem tailTrace_629295 : CollatzResearch.WordTrace tailWord_629295 prefixEnd_629295 323130808471220614118431 := by
  unfold tailWord_629295
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952274255179164874585339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15301516170119443249723559 22952274255179164874585339)
  ·
    refine ⟨34428411382768747311878009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22952274255179164874585339 34428411382768747311878009)
    ·
      refine ⟨25821308537076560483908507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34428411382768747311878009 25821308537076560483908507)
      ·
        refine ⟨38731962805614840725862761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25821308537076560483908507 38731962805614840725862761)
        ·
          refine ⟨29048972104211130544397071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38731962805614840725862761 29048972104211130544397071)
          ·
            refine ⟨43573458156316695816595607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29048972104211130544397071 43573458156316695816595607)
            ·
              refine ⟨65360187234475043724893411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43573458156316695816595607 65360187234475043724893411)
              ·
                refine ⟨98040280851712565587340117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65360187234475043724893411 98040280851712565587340117)
                ·
                  refine ⟨574454770615503313988321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 98040280851712565587340117 574454770615503313988321)
                  ·
                    refine ⟨430841077961627485491241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 574454770615503313988321 430841077961627485491241)
                    ·
                      refine ⟨323130808471220614118431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430841077961627485491241 323130808471220614118431)
                      ·
                        rfl

theorem cell23_629295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 2, 2].length) (baseStart_629295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629295 prefixEnd_629295 := by exact prefixLift 629295
  have htrace : WordTrace (prefixWord ++ tailWord_629295) baseStart_629295 baseEnd_629295 := by
    simpa [prefixWord, tailWord_629295, baseEnd_629295] using wordTrace_append hprefix tailTrace_629295
  have hstable : (prefixWord ++ tailWord_629295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629295).length < 2 ^ (prefixWord ++ tailWord_629295).sum := by decide
  have hdescent : baseEnd_629295 < baseStart_629295 := by decide
  rcases family_descends (prefixWord ++ tailWord_629295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629298 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_629298 : Nat := 118140960795 + 629298 * 2 ^ 59
def prefixEnd_629298 : Nat := 4983230072969 + 3 ^ 40 * 629298 * 2
def baseEnd_629298 : Nat := 323132348913184102380917

theorem tailTrace_629298 : CollatzResearch.WordTrace tailWord_629298 prefixEnd_629298 323132348913184102380917 := by
  unfold tailWord_629298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5738095918542074096736137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15301589116112197591296365 5738095918542074096736137)
  ·
    refine ⟨4303571938906555572552103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5738095918542074096736137 4303571938906555572552103)
    ·
      refine ⟨6455357908359833358828155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4303571938906555572552103 6455357908359833358828155)
      ·
        refine ⟨9683036862539750038242233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6455357908359833358828155 9683036862539750038242233)
        ·
          refine ⟨7262277646904812528681675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9683036862539750038242233 7262277646904812528681675)
          ·
            refine ⟨10893416470357218793022513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7262277646904812528681675 10893416470357218793022513)
            ·
              refine ⟨8170062352767914094766885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10893416470357218793022513 8170062352767914094766885)
              ·
                refine ⟨1531886691143983892768791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8170062352767914094766885 1531886691143983892768791)
                ·
                  refine ⟨2297830036715975839153187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531886691143983892768791 2297830036715975839153187)
                  ·
                    refine ⟨3446745055073963758729781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297830036715975839153187 3446745055073963758729781)
                    ·
                      refine ⟨323132348913184102380917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3446745055073963758729781 323132348913184102380917)
                      ·
                        rfl

theorem cell23_629298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_629298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629298 prefixEnd_629298 := by exact prefixLift 629298
  have htrace : WordTrace (prefixWord ++ tailWord_629298) baseStart_629298 baseEnd_629298 := by
    simpa [prefixWord, tailWord_629298, baseEnd_629298] using wordTrace_append hprefix tailTrace_629298
  have hstable : (prefixWord ++ tailWord_629298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629298).length < 2 ^ (prefixWord ++ tailWord_629298).sum := by decide
  have hdescent : baseEnd_629298 < baseStart_629298 := by decide
  rcases family_descends (prefixWord ++ tailWord_629298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629305 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 2, 4]
def baseStart_629305 : Nat := 118140960795 + 629305 * 2 ^ 59
def prefixEnd_629305 : Nat := 4983230072969 + 3 ^ 40 * 629305 * 2
def baseEnd_629305 : Nat := 107711981092588524997795

theorem tailTrace_629305 : CollatzResearch.WordTrace tailWord_629305 prefixEnd_629305 107711981092588524997795 := by
  unfold tailWord_629305
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952638985142936582449369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15301759323428624388299579 22952638985142936582449369)
  ·
    refine ⟨17214479238857202436837027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22952638985142936582449369 17214479238857202436837027)
    ·
      refine ⟨25821718858285803655255541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17214479238857202436837027 25821718858285803655255541)
      ·
        refine ⟨2420786142964294092680207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25821718858285803655255541 2420786142964294092680207)
        ·
          refine ⟨3631179214446441139020311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420786142964294092680207 3631179214446441139020311)
          ·
            refine ⟨5446768821669661708530467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631179214446441139020311 5446768821669661708530467)
            ·
              refine ⟨8170153232504492562795701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446768821669661708530467 8170153232504492562795701)
              ·
                refine ⟨765951865547296177762097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8170153232504492562795701 765951865547296177762097)
                ·
                  refine ⟨574463899160472133321573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765951865547296177762097 574463899160472133321573)
                  ·
                    refine ⟨107711981092588524997795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 574463899160472133321573 107711981092588524997795)
                    ·
                      rfl

theorem cell23_629305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_629305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629305 prefixEnd_629305 := by exact prefixLift 629305
  have htrace : WordTrace (prefixWord ++ tailWord_629305) baseStart_629305 baseEnd_629305 := by
    simpa [prefixWord, tailWord_629305, baseEnd_629305] using wordTrace_append hprefix tailTrace_629305
  have hstable : (prefixWord ++ tailWord_629305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629305).length < 2 ^ (prefixWord ++ tailWord_629305).sum := by decide
  have hdescent : baseEnd_629305 < baseStart_629305 := by decide
  rcases family_descends (prefixWord ++ tailWord_629305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629316 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_629316 : Nat := 118140960795 + 629316 * 2 ^ 59
def prefixEnd_629316 : Nat := 4983230072969 + 3 ^ 40 * 629316 * 2
def baseEnd_629316 : Nat := 323141591564965031955835

theorem tailTrace_629316 : CollatzResearch.WordTrace tailWord_629316 prefixEnd_629316 323141591564965031955835 := by
  unfold tailWord_629316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476520094051542730549901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15302026792068723640733201 11476520094051542730549901)
  ·
    refine ⟨4303695035269328523956213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11476520094051542730549901 4303695035269328523956213)
    ·
      refine ⟨403471409556499549120895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4303695035269328523956213 403471409556499549120895)
      ·
        refine ⟨605207114334749323681343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403471409556499549120895 605207114334749323681343)
        ·
          refine ⟨907810671502123985522015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605207114334749323681343 907810671502123985522015)
          ·
            refine ⟨1361716007253185978283023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907810671502123985522015 1361716007253185978283023)
            ·
              refine ⟨2042574010879778967424535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361716007253185978283023 2042574010879778967424535)
              ·
                refine ⟨3063861016319668451136803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042574010879778967424535 3063861016319668451136803)
                ·
                  refine ⟨4595791524479502676705205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063861016319668451136803 4595791524479502676705205)
                  ·
                    refine ⟨430855455419953375941113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4595791524479502676705205 430855455419953375941113)
                    ·
                      refine ⟨323141591564965031955835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430855455419953375941113 323141591564965031955835)
                      ·
                        rfl

theorem cell23_629316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_629316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629316 prefixEnd_629316 := by exact prefixLift 629316
  have htrace : WordTrace (prefixWord ++ tailWord_629316) baseStart_629316 baseEnd_629316 := by
    simpa [prefixWord, tailWord_629316, baseEnd_629316] using wordTrace_append hprefix tailTrace_629316
  have hstable : (prefixWord ++ tailWord_629316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629316).length < 2 ^ (prefixWord ++ tailWord_629316).sum := by decide
  have hdescent : baseEnd_629316 < baseStart_629316 := by decide
  rcases family_descends (prefixWord ++ tailWord_629316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629328 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3]
def baseStart_629328 : Nat := 118140960795 + 629328 * 2 ^ 59
def prefixEnd_629328 : Nat := 4983230072969 + 3 ^ 40 * 629328 * 2
def baseEnd_629328 : Nat := 323147753332818985005779

theorem tailTrace_629328 : CollatzResearch.WordTrace tailWord_629328 prefixEnd_629328 323147753332818985005779 := by
  unfold tailWord_629328
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476738932029805755268319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15302318576039741007024425 11476738932029805755268319)
  ·
    refine ⟨17215108398044708632902479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11476738932029805755268319 17215108398044708632902479)
    ·
      refine ⟨25822662597067062949353719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17215108398044708632902479 25822662597067062949353719)
      ·
        refine ⟨38733993895600594424030579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25822662597067062949353719 38733993895600594424030579)
        ·
          refine ⟨58100990843400891636045869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38733993895600594424030579 58100990843400891636045869)
          ·
            refine ⟨21787871566275334363517201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58100990843400891636045869 21787871566275334363517201)
            ·
              refine ⟨16340903674706500772637901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21787871566275334363517201 16340903674706500772637901)
              ·
                refine ⟨6127838878014937789739213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16340903674706500772637901 6127838878014937789739213)
                ·
                  refine ⟨2297939579255601671152205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6127838878014937789739213 2297939579255601671152205)
                  ·
                    refine ⟨861727342220850626682077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2297939579255601671152205 861727342220850626682077)
                    ·
                      refine ⟨323147753332818985005779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861727342220850626682077 323147753332818985005779)
                      ·
                        rfl

theorem cell23_629328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_629328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629328 prefixEnd_629328 := by exact prefixLift 629328
  have htrace : WordTrace (prefixWord ++ tailWord_629328) baseStart_629328 baseEnd_629328 := by
    simpa [prefixWord, tailWord_629328, baseEnd_629328] using wordTrace_append hprefix tailTrace_629328
  have hstable : (prefixWord ++ tailWord_629328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629328).length < 2 ^ (prefixWord ++ tailWord_629328).sum := by decide
  have hdescent : baseEnd_629328 < baseStart_629328 := by decide
  rcases family_descends (prefixWord ++ tailWord_629328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629329 : List Nat := [1, 2, 2, 1, 3, 3, 1, 5, 1, 2, 2]
def baseStart_629329 : Nat := 118140960795 + 629329 * 2 ^ 59
def prefixEnd_629329 : Nat := 4983230072969 + 3 ^ 40 * 629329 * 2
def baseEnd_629329 : Nat := 323148266813473481093275

theorem tailTrace_629329 : CollatzResearch.WordTrace tailWord_629329 prefixEnd_629329 323148266813473481093275 := by
  unfold tailWord_629329
  simp only [CollatzResearch.WordTrace]
  refine ⟨22953514337055988681323041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15302342891370659120882027 22953514337055988681323041)
  ·
    refine ⟨17215135752791991510992281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22953514337055988681323041 17215135752791991510992281)
    ·
      refine ⟨12911351814593993633244211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17215135752791991510992281 12911351814593993633244211)
      ·
        refine ⟨19367027721890990449866317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12911351814593993633244211 19367027721890990449866317)
        ·
          refine ⟨7262635395709121418699869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19367027721890990449866317 7262635395709121418699869)
          ·
            refine ⟨2723488273390920532012451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7262635395709121418699869 2723488273390920532012451)
            ·
              refine ⟨4085232410086380798018677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723488273390920532012451 4085232410086380798018677)
              ·
                refine ⟨382990538445598199814251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4085232410086380798018677 382990538445598199814251)
                ·
                  refine ⟨574485807668397299721377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382990538445598199814251 574485807668397299721377)
                  ·
                    refine ⟨430864355751297974791033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 574485807668397299721377 430864355751297974791033)
                    ·
                      refine ⟨323148266813473481093275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430864355751297974791033 323148266813473481093275)
                      ·
                        rfl

theorem cell23_629329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_629329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629329 prefixEnd_629329 := by exact prefixLift 629329
  have htrace : WordTrace (prefixWord ++ tailWord_629329) baseStart_629329 baseEnd_629329 := by
    simpa [prefixWord, tailWord_629329, baseEnd_629329] using wordTrace_append hprefix tailTrace_629329
  have hstable : (prefixWord ++ tailWord_629329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629329).length < 2 ^ (prefixWord ++ tailWord_629329).sum := by decide
  have hdescent : baseEnd_629329 < baseStart_629329 := by decide
  rcases family_descends (prefixWord ++ tailWord_629329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629332 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_629332 : Nat := 118140960795 + 629332 * 2 ^ 59
def prefixEnd_629332 : Nat := 4983230072969 + 3 ^ 40 * 629332 * 2
def baseEnd_629332 : Nat := 323149807255436969355761

theorem tailTrace_629332 : CollatzResearch.WordTrace tailWord_629332 prefixEnd_629332 323149807255436969355761 := by
  unfold tailWord_629332
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476811878022560096841125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15302415837363413462454833 11476811878022560096841125)
  ·
    refine ⟨2151902227129230018157711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11476811878022560096841125 2151902227129230018157711)
    ·
      refine ⟨3227853340693845027236567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151902227129230018157711 3227853340693845027236567)
      ·
        refine ⟨4841780011040767540854851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227853340693845027236567 4841780011040767540854851)
        ·
          refine ⟨7262670016561151311282277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4841780011040767540854851 7262670016561151311282277)
          ·
            refine ⟨1361750628105215870865427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7262670016561151311282277 1361750628105215870865427)
            ·
              refine ⟨2042625942157823806298141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361750628105215870865427 2042625942157823806298141)
              ·
                refine ⟨765984728309183927361803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2042625942157823806298141 765984728309183927361803)
                ·
                  refine ⟨1148977092463775891042705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765984728309183927361803 1148977092463775891042705)
                  ·
                    refine ⟨861732819347831918282029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148977092463775891042705 861732819347831918282029)
                    ·
                      refine ⟨323149807255436969355761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 861732819347831918282029 323149807255436969355761)
                      ·
                        rfl

theorem cell23_629332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_629332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629332 prefixEnd_629332 := by exact prefixLift 629332
  have htrace : WordTrace (prefixWord ++ tailWord_629332) baseStart_629332 baseEnd_629332 := by
    simpa [prefixWord, tailWord_629332, baseEnd_629332] using wordTrace_append hprefix tailTrace_629332
  have hstable : (prefixWord ++ tailWord_629332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629332).length < 2 ^ (prefixWord ++ tailWord_629332).sum := by decide
  have hdescent : baseEnd_629332 < baseStart_629332 := by decide
  rcases family_descends (prefixWord ++ tailWord_629332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629355 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 3, 3, 2]
def baseStart_629355 : Nat := 118140960795 + 629355 * 2 ^ 59
def prefixEnd_629355 : Nat := 4983230072969 + 3 ^ 40 * 629355 * 2
def baseEnd_629355 : Nat := 323161617310490379368155

theorem tailTrace_629355 : CollatzResearch.WordTrace tailWord_629355 prefixEnd_629355 323161617310490379368155 := by
  unfold tailWord_629355
  simp only [CollatzResearch.WordTrace]
  refine ⟨22954462634961795121769519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15302975089974530081179679 22954462634961795121769519)
  ·
    refine ⟨34431693952442692682654279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22954462634961795121769519 34431693952442692682654279)
    ·
      refine ⟨51647540928664039023981419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34431693952442692682654279 51647540928664039023981419)
      ·
        refine ⟨77471311392996058535972129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51647540928664039023981419 77471311392996058535972129)
        ·
          refine ⟨58103483544747043901979097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77471311392996058535972129 58103483544747043901979097)
          ·
            refine ⟨43577612658560282926484323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58103483544747043901979097 43577612658560282926484323)
            ·
              refine ⟨65366418987840424389726485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43577612658560282926484323 65366418987840424389726485)
              ·
                refine ⟨3064050890055019893268429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65366418987840424389726485 3064050890055019893268429)
                ·
                  refine ⟨1149019083770632459975661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3064050890055019893268429 1149019083770632459975661)
                  ·
                    refine ⟨430882156413987172490873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149019083770632459975661 430882156413987172490873)
                    ·
                      refine ⟨323161617310490379368155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430882156413987172490873 323161617310490379368155)
                      ·
                        rfl

theorem cell23_629355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3, 2].length) (baseStart_629355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629355 prefixEnd_629355 := by exact prefixLift 629355
  have htrace : WordTrace (prefixWord ++ tailWord_629355) baseStart_629355 baseEnd_629355 := by
    simpa [prefixWord, tailWord_629355, baseEnd_629355] using wordTrace_append hprefix tailTrace_629355
  have hstable : (prefixWord ++ tailWord_629355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629355).length < 2 ^ (prefixWord ++ tailWord_629355).sum := by decide
  have hdescent : baseEnd_629355 < baseStart_629355 := by decide
  rcases family_descends (prefixWord ++ tailWord_629355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629372 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_629372 : Nat := 118140960795 + 629372 * 2 ^ 59
def prefixEnd_629372 : Nat := 4983230072969 + 3 ^ 40 * 629372 * 2
def baseEnd_629372 : Nat := 323170346481616812855577

theorem tailTrace_629372 : CollatzResearch.WordTrace tailWord_629372 prefixEnd_629372 323170346481616812855577 := by
  unfold tailWord_629372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477541337950103512569185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15303388450600138016758913 11477541337950103512569185)
  ·
    refine ⟨8608156003462577634426889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11477541337950103512569185 8608156003462577634426889)
    ·
      refine ⟨6456117002596933225820167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8608156003462577634426889 6456117002596933225820167)
      ·
        refine ⟨9684175503895399838730251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6456117002596933225820167 9684175503895399838730251)
        ·
          refine ⟨14526263255843099758095377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9684175503895399838730251 14526263255843099758095377)
          ·
            refine ⟨10894697441882324818571533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14526263255843099758095377 10894697441882324818571533)
            ·
              refine ⟨4085511540705871806964325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10894697441882324818571533 4085511540705871806964325)
              ·
                refine ⟨766033413882350963805811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4085511540705871806964325 766033413882350963805811)
                ·
                  refine ⟨1149050120823526445708717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766033413882350963805811 1149050120823526445708717)
                  ·
                    refine ⟨430893795308822417140769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149050120823526445708717 430893795308822417140769)
                    ·
                      refine ⟨323170346481616812855577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430893795308822417140769 323170346481616812855577)
                      ·
                        rfl

theorem cell23_629372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_629372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629372 prefixEnd_629372 := by exact prefixLift 629372
  have htrace : WordTrace (prefixWord ++ tailWord_629372) baseStart_629372 baseEnd_629372 := by
    simpa [prefixWord, tailWord_629372, baseEnd_629372] using wordTrace_append hprefix tailTrace_629372
  have hstable : (prefixWord ++ tailWord_629372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629372).length < 2 ^ (prefixWord ++ tailWord_629372).sum := by decide
  have hdescent : baseEnd_629372 < baseStart_629372 := by decide
  rcases family_descends (prefixWord ++ tailWord_629372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629385 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 3, 4, 2]
def baseStart_629385 : Nat := 118140960795 + 629385 * 2 ^ 59
def prefixEnd_629385 : Nat := 4983230072969 + 3 ^ 40 * 629385 * 2
def baseEnd_629385 : Nat := 323177021730125261993017

theorem tailTrace_629385 : CollatzResearch.WordTrace tailWord_629385 prefixEnd_629385 323177021730125261993017 := by
  unfold tailWord_629385
  simp only [CollatzResearch.WordTrace]
  refine ⟨22955556824853110245361609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15303704549902073496907739 22955556824853110245361609)
  ·
    refine ⟨17216667618639832684021207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22955556824853110245361609 17216667618639832684021207)
    ·
      refine ⟨25825001427959749026031811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17216667618639832684021207 25825001427959749026031811)
      ·
        refine ⟨38737502141939623539047717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25825001427959749026031811 38737502141939623539047717)
        ·
          refine ⟨7263281651613679413571447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38737502141939623539047717 7263281651613679413571447)
          ·
            refine ⟨10894922477420519120357171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7263281651613679413571447 10894922477420519120357171)
            ·
              refine ⟨16342383716130778680535757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10894922477420519120357171 16342383716130778680535757)
              ·
                refine ⟨6128393893549042005200909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16342383716130778680535757 6128393893549042005200909)
                ·
                  refine ⟨2298147710080890751950341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6128393893549042005200909 2298147710080890751950341)
                  ·
                    refine ⟨430902695640167015990689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298147710080890751950341 430902695640167015990689)
                    ·
                      refine ⟨323177021730125261993017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430902695640167015990689 323177021730125261993017)
                      ·
                        rfl

theorem cell23_629385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 4, 2].length) (baseStart_629385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629385 prefixEnd_629385 := by exact prefixLift 629385
  have htrace : WordTrace (prefixWord ++ tailWord_629385) baseStart_629385 baseEnd_629385 := by
    simpa [prefixWord, tailWord_629385, baseEnd_629385] using wordTrace_append hprefix tailTrace_629385
  have hstable : (prefixWord ++ tailWord_629385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629385).length < 2 ^ (prefixWord ++ tailWord_629385).sum := by decide
  have hdescent : baseEnd_629385 < baseStart_629385 := by decide
  rcases family_descends (prefixWord ++ tailWord_629385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629422 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_629422 : Nat := 118140960795 + 629422 * 2 ^ 59
def prefixEnd_629422 : Nat := 4983230072969 + 3 ^ 40 * 629422 * 2
def baseEnd_629422 : Nat := 323196020514341617230347

theorem tailTrace_629422 : CollatzResearch.WordTrace tailWord_629422 prefixEnd_629422 323196020514341617230347 := by
  unfold tailWord_629422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2869613290714883195557315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15304604217146043709639013 2869613290714883195557315)
  ·
    refine ⟨4304419936072324793335973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2869613290714883195557315 4304419936072324793335973)
    ·
      refine ⟨807078738013560898750495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4304419936072324793335973 807078738013560898750495)
      ·
        refine ⟨1210618107020341348125743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807078738013560898750495 1210618107020341348125743)
        ·
          refine ⟨1815927160530512022188615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210618107020341348125743 1815927160530512022188615)
          ·
            refine ⟨2723890740795768033282923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815927160530512022188615 2723890740795768033282923)
            ·
              refine ⟨4085836111193652049924385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723890740795768033282923 4085836111193652049924385)
              ·
                refine ⟨3064377083395239037443289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4085836111193652049924385 3064377083395239037443289)
                ·
                  refine ⟨2298282812546429278082467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3064377083395239037443289 2298282812546429278082467)
                  ·
                    refine ⟨3447424218819643917123701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2298282812546429278082467 3447424218819643917123701)
                    ·
                      refine ⟨323196020514341617230347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3447424218819643917123701 323196020514341617230347)
                      ·
                        rfl

theorem cell23_629422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_629422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629422 prefixEnd_629422 := by exact prefixLift 629422
  have htrace : WordTrace (prefixWord ++ tailWord_629422) baseStart_629422 baseEnd_629422 := by
    simpa [prefixWord, tailWord_629422, baseEnd_629422] using wordTrace_append hprefix tailTrace_629422
  have hstable : (prefixWord ++ tailWord_629422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629422).length < 2 ^ (prefixWord ++ tailWord_629422).sum := by decide
  have hdescent : baseEnd_629422 < baseStart_629422 := by decide
  rcases family_descends (prefixWord ++ tailWord_629422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629445 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 7, 2]
def baseStart_629445 : Nat := 118140960795 + 629445 * 2 ^ 59
def prefixEnd_629445 : Nat := 4983230072969 + 3 ^ 40 * 629445 * 2
def baseEnd_629445 : Nat := 323207830569395027242741

theorem tailTrace_629445 : CollatzResearch.WordTrace tailWord_629445 prefixEnd_629445 323207830569395027242741 := by
  unfold tailWord_629445
  simp only [CollatzResearch.WordTrace]
  refine ⟨22957745204635740492545789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15305163469757160328363859 22957745204635740492545789)
  ·
    refine ⟨8609154451738402684704671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22957745204635740492545789 8609154451738402684704671)
    ·
      refine ⟨12913731677607604027057007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8609154451738402684704671 12913731677607604027057007)
      ·
        refine ⟨19370597516411406040585511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12913731677607604027057007 19370597516411406040585511)
        ·
          refine ⟨29055896274617109060878267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19370597516411406040585511 29055896274617109060878267)
          ·
            refine ⟨43583844411925663591317401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29055896274617109060878267 43583844411925663591317401)
            ·
              refine ⟨32687883308944247693488051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43583844411925663591317401 32687883308944247693488051)
              ·
                refine ⟨49031824963416371540232077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32687883308944247693488051 49031824963416371540232077)
                ·
                  refine ⟨18386934361281139327587029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49031824963416371540232077 18386934361281139327587029)
                  ·
                    refine ⟨430943774092526702990321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18386934361281139327587029 430943774092526702990321)
                    ·
                      refine ⟨323207830569395027242741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 430943774092526702990321 323207830569395027242741)
                      ·
                        rfl

theorem cell23_629445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_629445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629445 prefixEnd_629445 := by exact prefixLift 629445
  have htrace : WordTrace (prefixWord ++ tailWord_629445) baseStart_629445 baseEnd_629445 := by
    simpa [prefixWord, tailWord_629445, baseEnd_629445] using wordTrace_append hprefix tailTrace_629445
  have hstable : (prefixWord ++ tailWord_629445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629445).length < 2 ^ (prefixWord ++ tailWord_629445).sum := by decide
  have hdescent : baseEnd_629445 < baseStart_629445 := by decide
  rcases family_descends (prefixWord ++ tailWord_629445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629493 : List Nat := [1, 3, 6, 1, 1, 1, 2, 3, 5]
def baseStart_629493 : Nat := 118140960795 + 629493 * 2 ^ 59
def prefixEnd_629493 : Nat := 4983230072969 + 3 ^ 40 * 629493 * 2
def baseEnd_629493 : Nat := 35914719737867871049169

theorem tailTrace_629493 : CollatzResearch.WordTrace tailWord_629493 prefixEnd_629493 35914719737867871049169 := by
  unfold tailWord_629493
  simp only [CollatzResearch.WordTrace]
  refine ⟨22959495908461844690293133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15306330605641229793528755 22959495908461844690293133)
  ·
    refine ⟨8609810965673191758859925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22959495908461844690293133 8609810965673191758859925)
    ·
      refine ⟨403584889015930863696559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8609810965673191758859925 403584889015930863696559)
      ·
        refine ⟨605377333523896295544839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403584889015930863696559 605377333523896295544839)
        ·
          refine ⟨908066000285844443317259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605377333523896295544839 908066000285844443317259)
          ·
            refine ⟨1362099000428766664975889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908066000285844443317259 1362099000428766664975889)
            ·
              refine ⟨1021574250321574998731917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362099000428766664975889 1021574250321574998731917)
              ·
                refine ⟨383090343870590624524469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1021574250321574998731917 383090343870590624524469)
                ·
                  refine ⟨35914719737867871049169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 383090343870590624524469 35914719737867871049169)
                  ·
                    rfl

theorem cell23_629493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_629493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629493 prefixEnd_629493 := by exact prefixLift 629493
  have htrace : WordTrace (prefixWord ++ tailWord_629493) baseStart_629493 baseEnd_629493 := by
    simpa [prefixWord, tailWord_629493, baseEnd_629493] using wordTrace_append hprefix tailTrace_629493
  have hstable : (prefixWord ++ tailWord_629493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629493).length < 2 ^ (prefixWord ++ tailWord_629493).sum := by decide
  have hdescent : baseEnd_629493 < baseStart_629493 := by decide
  rcases family_descends (prefixWord ++ tailWord_629493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629552 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 6, 3, 2]
def baseStart_629552 : Nat := 118140960795 + 629552 * 2 ^ 59
def prefixEnd_629552 : Nat := 4983230072969 + 3 ^ 40 * 629552 * 2
def baseEnd_629552 : Nat := 323262772999426108604749

theorem tailTrace_629552 : CollatzResearch.WordTrace tailWord_629552 prefixEnd_629552 323262772999426108604749 := by
  unfold tailWord_629552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11480823907624048883345455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15307765210165398511127273 11480823907624048883345455)
  ·
    refine ⟨17221235861436073325018183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11480823907624048883345455 17221235861436073325018183)
    ·
      refine ⟨25831853792154109987527275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17221235861436073325018183 25831853792154109987527275)
      ·
        refine ⟨38747780688231164981290913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25831853792154109987527275 38747780688231164981290913)
        ·
          refine ⟨29060835516173373735968185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38747780688231164981290913 29060835516173373735968185)
          ·
            refine ⟨21795626637130030301976139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29060835516173373735968185 21795626637130030301976139)
            ·
              refine ⟨32693439955695045452964209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21795626637130030301976139 32693439955695045452964209)
              ·
                refine ⟨24520079966771284089723157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32693439955695045452964209 24520079966771284089723157)
                ·
                  refine ⟨1149378748442403941705773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24520079966771284089723157 1149378748442403941705773)
                  ·
                    refine ⟨431017030665901478139665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149378748442403941705773 431017030665901478139665)
                    ·
                      refine ⟨323262772999426108604749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431017030665901478139665 323262772999426108604749)
                      ·
                        rfl

theorem cell23_629552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 3, 2].length) (baseStart_629552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629552 prefixEnd_629552 := by exact prefixLift 629552
  have htrace : WordTrace (prefixWord ++ tailWord_629552) baseStart_629552 baseEnd_629552 := by
    simpa [prefixWord, tailWord_629552, baseEnd_629552] using wordTrace_append hprefix tailTrace_629552
  have hstable : (prefixWord ++ tailWord_629552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629552).length < 2 ^ (prefixWord ++ tailWord_629552).sum := by decide
  have hdescent : baseEnd_629552 < baseStart_629552 := by decide
  rcases family_descends (prefixWord ++ tailWord_629552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629596 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_629596 : Nat := 118140960795 + 629596 * 2 ^ 59
def prefixEnd_629596 : Nat := 4983230072969 + 3 ^ 40 * 629596 * 2
def baseEnd_629596 : Nat := 107761788716074645484849

theorem tailTrace_629596 : CollatzResearch.WordTrace tailWord_629596 prefixEnd_629596 107761788716074645484849 := by
  unfold tailWord_629596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481626313544346640646321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15308835084725795520861761 11481626313544346640646321)
  ·
    refine ⟨8611219735158259980484741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11481626313544346640646321 8611219735158259980484741)
    ·
      refine ⟨1614603700342173746340889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8611219735158259980484741 1614603700342173746340889)
      ·
        refine ⟨1210952775256630309755667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1614603700342173746340889 1210952775256630309755667)
        ·
          refine ⟨1816429162884945464633501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210952775256630309755667 1816429162884945464633501)
          ·
            refine ⟨681160936081854549237563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1816429162884945464633501 681160936081854549237563)
            ·
              refine ⟨1021741404122781823856345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681160936081854549237563 1021741404122781823856345)
              ·
                refine ⟨766306053092086367892259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021741404122781823856345 766306053092086367892259)
                ·
                  refine ⟨1149459079638129551838389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766306053092086367892259 1149459079638129551838389)
                  ·
                    refine ⟨107761788716074645484849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1149459079638129551838389 107761788716074645484849)
                    ·
                      rfl

theorem cell23_629596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_629596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629596 prefixEnd_629596 := by exact prefixLift 629596
  have htrace : WordTrace (prefixWord ++ tailWord_629596) baseStart_629596 baseEnd_629596 := by
    simpa [prefixWord, tailWord_629596, baseEnd_629596] using wordTrace_append hprefix tailTrace_629596
  have hstable : (prefixWord ++ tailWord_629596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629596).length < 2 ^ (prefixWord ++ tailWord_629596).sum := by decide
  have hdescent : baseEnd_629596 < baseStart_629596 := by decide
  rcases family_descends (prefixWord ++ tailWord_629596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629599 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 5, 2, 2]
def baseStart_629599 : Nat := 118140960795 + 629599 * 2 ^ 59
def prefixEnd_629599 : Nat := 4983230072969 + 3 ^ 40 * 629599 * 2
def baseEnd_629599 : Nat := 323286906590187424717033

theorem tailTrace_629599 : CollatzResearch.WordTrace tailWord_629599 prefixEnd_629599 323286906590187424717033 := by
  unfold tailWord_629599
  simp only [CollatzResearch.WordTrace]
  refine ⟨22963362046077824793651851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15308908030718549862434567 22963362046077824793651851)
  ·
    refine ⟨34445043069116737190477777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22963362046077824793651851 34445043069116737190477777)
    ·
      refine ⟨25833782301837552892858333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34445043069116737190477777 25833782301837552892858333)
      ·
        refine ⟨9687668363189082334821875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25833782301837552892858333 9687668363189082334821875)
        ·
          refine ⟨14531502544783623502232813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9687668363189082334821875 14531502544783623502232813)
          ·
            refine ⟨5449313454293858813337305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14531502544783623502232813 5449313454293858813337305)
            ·
              refine ⟨4086985090720394110002979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449313454293858813337305 4086985090720394110002979)
              ·
                refine ⟨6130477636080591165004469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086985090720394110002979 6130477636080591165004469)
                ·
                  refine ⟨574732278382555421719169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6130477636080591165004469 574732278382555421719169)
                  ·
                    refine ⟨431049208786916566289377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 574732278382555421719169 431049208786916566289377)
                    ·
                      refine ⟨323286906590187424717033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431049208786916566289377 323286906590187424717033)
                      ·
                        rfl

theorem cell23_629599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_629599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629599 prefixEnd_629599 := by exact prefixLift 629599
  have htrace : WordTrace (prefixWord ++ tailWord_629599) baseStart_629599 baseEnd_629599 := by
    simpa [prefixWord, tailWord_629599, baseEnd_629599] using wordTrace_append hprefix tailTrace_629599
  have hstable : (prefixWord ++ tailWord_629599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629599).length < 2 ^ (prefixWord ++ tailWord_629599).sum := by decide
  have hdescent : baseEnd_629599 < baseStart_629599 := by decide
  rcases family_descends (prefixWord ++ tailWord_629599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629605 : List Nat := [1, 3, 1, 3, 1, 1, 4, 9]
def baseStart_629605 : Nat := 118140960795 + 629605 * 2 ^ 59
def prefixEnd_629605 : Nat := 4983230072969 + 3 ^ 40 * 629605 * 2
def baseEnd_629605 : Nat := 11973703239782014860815

theorem tailTrace_629605 : CollatzResearch.WordTrace tailWord_629605 prefixEnd_629605 11973703239782014860815 := by
  unfold tailWord_629605
  simp only [CollatzResearch.WordTrace]
  refine ⟨22963580884056087818370269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15309053922704058545580179 22963580884056087818370269)
  ·
    refine ⟨8611342831521032931888851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22963580884056087818370269 8611342831521032931888851)
    ·
      refine ⟨12917014247281549397833277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8611342831521032931888851 12917014247281549397833277)
      ·
        refine ⟨4843880342730581024187479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12917014247281549397833277 4843880342730581024187479)
        ·
          refine ⟨7265820514095871536281219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4843880342730581024187479 7265820514095871536281219)
          ·
            refine ⟨10898730771143807304421829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7265820514095871536281219 10898730771143807304421829)
            ·
              refine ⟨2043512019589463869579093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10898730771143807304421829 2043512019589463869579093)
              ·
                refine ⟨11973703239782014860815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2043512019589463869579093 11973703239782014860815)
                ·
                  rfl

theorem cell23_629605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 9].length) (baseStart_629605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629605 prefixEnd_629605 := by exact prefixLift 629605
  have htrace : WordTrace (prefixWord ++ tailWord_629605) baseStart_629605 baseEnd_629605 := by
    simpa [prefixWord, tailWord_629605, baseEnd_629605] using wordTrace_append hprefix tailTrace_629605
  have hstable : (prefixWord ++ tailWord_629605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629605).length < 2 ^ (prefixWord ++ tailWord_629605).sum := by decide
  have hdescent : baseEnd_629605 < baseStart_629605 := by decide
  rcases family_descends (prefixWord ++ tailWord_629605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629612 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_629612 : Nat := 118140960795 + 629612 * 2 ^ 59
def prefixEnd_629612 : Nat := 4983230072969 + 3 ^ 40 * 629612 * 2
def baseEnd_629612 : Nat := 323293581838695873854473

theorem tailTrace_629612 : CollatzResearch.WordTrace tailWord_629612 prefixEnd_629612 323293581838695873854473 := by
  unfold tailWord_629612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481918097515364006937545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15309224130020485342583393 11481918097515364006937545)
  ·
    refine ⟨8611438573136523005203159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11481918097515364006937545 8611438573136523005203159)
    ·
      refine ⟨12917157859704784507804739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8611438573136523005203159 12917157859704784507804739)
      ·
        refine ⟨19375736789557176761707109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12917157859704784507804739 19375736789557176761707109)
        ·
          refine ⟨3632950648041970642820083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19375736789557176761707109 3632950648041970642820083)
          ·
            refine ⟨5449425972062955964230125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632950648041970642820083 5449425972062955964230125)
            ·
              refine ⟨2043534739523608486586297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5449425972062955964230125 2043534739523608486586297)
              ·
                refine ⟨1532651054642706364939723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043534739523608486586297 1532651054642706364939723)
                ·
                  refine ⟨2298976581964059547409585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532651054642706364939723 2298976581964059547409585)
                  ·
                    refine ⟨1724232436473044660557189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2298976581964059547409585 1724232436473044660557189)
                    ·
                      refine ⟨323293581838695873854473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1724232436473044660557189 323293581838695873854473)
                      ·
                        rfl

theorem cell23_629612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_629612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629612 prefixEnd_629612 := by exact prefixLift 629612
  have htrace : WordTrace (prefixWord ++ tailWord_629612) baseStart_629612 baseEnd_629612 := by
    simpa [prefixWord, tailWord_629612, baseEnd_629612] using wordTrace_append hprefix tailTrace_629612
  have hstable : (prefixWord ++ tailWord_629612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629612).length < 2 ^ (prefixWord ++ tailWord_629612).sum := by decide
  have hdescent : baseEnd_629612 < baseStart_629612 := by decide
  rcases family_descends (prefixWord ++ tailWord_629612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629622 : List Nat := [5, 1, 1, 3, 1, 12]
def baseStart_629622 : Nat := 118140960795 + 629622 * 2 ^ 59
def prefixEnd_629622 : Nat := 4983230072969 + 3 ^ 40 * 629622 * 2
def baseEnd_629622 : Nat := 1330447393601814134689

theorem tailTrace_629622 : CollatzResearch.WordTrace tailWord_629622 prefixEnd_629622 1330447393601814134689 := by
  unfold tailWord_629622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435262557812156232608695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15309467283329666481159413 1435262557812156232608695)
  ·
    refine ⟨2152893836718234348913043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1435262557812156232608695 2152893836718234348913043)
    ·
      refine ⟨3229340755077351523369565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2152893836718234348913043 3229340755077351523369565)
      ·
        refine ⟨1211002783154006821263587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3229340755077351523369565 1211002783154006821263587)
        ·
          refine ⟨1816504174731010231895381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211002783154006821263587 1816504174731010231895381)
          ·
            refine ⟨1330447393601814134689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1816504174731010231895381 1330447393601814134689)
            ·
              rfl

theorem cell23_629622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 12].length) (baseStart_629622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629622 prefixEnd_629622 := by exact prefixLift 629622
  have htrace : WordTrace (prefixWord ++ tailWord_629622) baseStart_629622 baseEnd_629622 := by
    simpa [prefixWord, tailWord_629622, baseEnd_629622] using wordTrace_append hprefix tailTrace_629622
  have hstable : (prefixWord ++ tailWord_629622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629622).length < 2 ^ (prefixWord ++ tailWord_629622).sum := by decide
  have hdescent : baseEnd_629622 < baseStart_629622 := by decide
  rcases family_descends (prefixWord ++ tailWord_629622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629635 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 9]
def baseStart_629635 : Nat := 118140960795 + 629635 * 2 ^ 59
def prefixEnd_629635 : Nat := 4983230072969 + 3 ^ 40 * 629635 * 2
def baseEnd_629635 : Nat := 107768463964583094622289

theorem tailTrace_629635 : CollatzResearch.WordTrace tailWord_629635 prefixEnd_629635 107768463964583094622289 := by
  unfold tailWord_629635
  simp only [CollatzResearch.WordTrace]
  refine ⟨22964675073947402941962359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15309783382631601961308239 22964675073947402941962359)
  ·
    refine ⟨34447012610921104412943539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22964675073947402941962359 34447012610921104412943539)
    ·
      refine ⟨51670518916381656619415309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34447012610921104412943539 51670518916381656619415309)
      ·
        refine ⟨19376444593643121232280741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51670518916381656619415309 19376444593643121232280741)
        ·
          refine ⟨3633083361308085231052639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19376444593643121232280741 3633083361308085231052639)
          ·
            refine ⟨5449625041962127846578959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633083361308085231052639 5449625041962127846578959)
            ·
              refine ⟨8174437562943191769868439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449625041962127846578959 8174437562943191769868439)
              ·
                refine ⟨12261656344414787654802659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8174437562943191769868439 12261656344414787654802659)
                ·
                  refine ⟨18392484516622181482203989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12261656344414787654802659 18392484516622181482203989)
                  ·
                    refine ⟨107768463964583094622289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 18392484516622181482203989 107768463964583094622289)
                    ·
                      rfl

theorem cell23_629635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 9].length) (baseStart_629635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629635 prefixEnd_629635 := by exact prefixLift 629635
  have htrace : WordTrace (prefixWord ++ tailWord_629635) baseStart_629635 baseEnd_629635 := by
    simpa [prefixWord, tailWord_629635, baseEnd_629635] using wordTrace_append hprefix tailTrace_629635
  have hstable : (prefixWord ++ tailWord_629635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629635).length < 2 ^ (prefixWord ++ tailWord_629635).sum := by decide
  have hdescent : baseEnd_629635 < baseStart_629635 := by decide
  rcases family_descends (prefixWord ++ tailWord_629635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629652 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_629652 : Nat := 118140960795 + 629652 * 2 ^ 59
def prefixEnd_629652 : Nat := 4983230072969 + 3 ^ 40 * 629652 * 2
def baseEnd_629652 : Nat := 107771373688291905784763

theorem tailTrace_629652 : CollatzResearch.WordTrace tailWord_629652 prefixEnd_629652 107771373688291905784763 := by
  unfold tailWord_629652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11482647557442907422665605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15310196743257209896887473 11482647557442907422665605)
  ·
    refine ⟨2152996417020545141749801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11482647557442907422665605 2152996417020545141749801)
    ·
      refine ⟨1614747312765408856312351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2152996417020545141749801 1614747312765408856312351)
      ·
        refine ⟨2422120969148113284468527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1614747312765408856312351 2422120969148113284468527)
        ·
          refine ⟨3633181453722169926702791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422120969148113284468527 3633181453722169926702791)
          ·
            refine ⟨5449772180583254890054187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633181453722169926702791 5449772180583254890054187)
            ·
              refine ⟨8174658270874882335081281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5449772180583254890054187 8174658270874882335081281)
              ·
                refine ⟨6130993703156161751310961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8174658270874882335081281 6130993703156161751310961)
                ·
                  refine ⟨4598245277367121313483221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130993703156161751310961 4598245277367121313483221)
                  ·
                    refine ⟨107771373688291905784763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4598245277367121313483221 107771373688291905784763)
                    ·
                      rfl

theorem cell23_629652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_629652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629652 prefixEnd_629652 := by exact prefixLift 629652
  have htrace : WordTrace (prefixWord ++ tailWord_629652) baseStart_629652 baseEnd_629652 := by
    simpa [prefixWord, tailWord_629652, baseEnd_629652] using wordTrace_append hprefix tailTrace_629652
  have hstable : (prefixWord ++ tailWord_629652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629652).length < 2 ^ (prefixWord ++ tailWord_629652).sum := by decide
  have hdescent : baseEnd_629652 < baseStart_629652 := by decide
  rcases family_descends (prefixWord ++ tailWord_629652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629700 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_629700 : Nat := 118140960795 + 629700 * 2 ^ 59
def prefixEnd_629700 : Nat := 4983230072969 + 3 ^ 40 * 629700 * 2
def baseEnd_629700 : Nat := 323338768136291529554069

theorem tailTrace_629700 : CollatzResearch.WordTrace tailWord_629700 prefixEnd_629700 323338768136291529554069 := by
  unfold tailWord_629700
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483522909355959521539277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15311363879141279362052369 11483522909355959521539277)
  ·
    refine ⟨4306321091008484820577229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11483522909355959521539277 4306321091008484820577229)
    ·
      refine ⟨1614870409128181807716461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4306321091008484820577229 1614870409128181807716461)
      ·
        refine ⟨605576403423068177893673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1614870409128181807716461 605576403423068177893673)
        ·
          refine ⟨454182302567301133420255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605576403423068177893673 454182302567301133420255)
          ·
            refine ⟨681273453850951700130383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454182302567301133420255 681273453850951700130383)
            ·
              refine ⟨1021910180776427550195575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681273453850951700130383 1021910180776427550195575)
              ·
                refine ⟨1532865271164641325293363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021910180776427550195575 1532865271164641325293363)
                ·
                  refine ⟨2299297906746961987940045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532865271164641325293363 2299297906746961987940045)
                  ·
                    refine ⟨862236715030110745477517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2299297906746961987940045 862236715030110745477517)
                    ·
                      refine ⟨323338768136291529554069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 862236715030110745477517 323338768136291529554069)
                      ·
                        rfl

theorem cell23_629700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_629700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629700 prefixEnd_629700 := by exact prefixLift 629700
  have htrace : WordTrace (prefixWord ++ tailWord_629700) baseStart_629700 baseEnd_629700 := by
    simpa [prefixWord, tailWord_629700, baseEnd_629700] using wordTrace_append hprefix tailTrace_629700
  have hstable : (prefixWord ++ tailWord_629700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629700).length < 2 ^ (prefixWord ++ tailWord_629700).sum := by decide
  have hdescent : baseEnd_629700 < baseStart_629700 := by decide
  rcases family_descends (prefixWord ++ tailWord_629700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629779 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 4, 4, 2]
def baseStart_629779 : Nat := 118140960795 + 629779 * 2 ^ 59
def prefixEnd_629779 : Nat := 4983230072969 + 3 ^ 40 * 629779 * 2
def baseEnd_629779 : Nat := 323379333107996720466205

theorem tailTrace_629779 : CollatzResearch.WordTrace tailWord_629779 prefixEnd_629779 323379333107996720466205 := by
  unfold tailWord_629779
  simp only [CollatzResearch.WordTrace]
  refine ⟨22969927185425715535204391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15313284790283810356802927 22969927185425715535204391)
  ·
    refine ⟨34454890778138573302806587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22969927185425715535204391 34454890778138573302806587)
    ·
      refine ⟨51682336167207859954209881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34454890778138573302806587 51682336167207859954209881)
      ·
        refine ⟨38761752125405894965657411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51682336167207859954209881 38761752125405894965657411)
        ·
          refine ⟨58142628188108842448486117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38761752125405894965657411 58142628188108842448486117)
          ·
            refine ⟨10901742785270407959091147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58142628188108842448486117 10901742785270407959091147)
            ·
              refine ⟨16352614177905611938636721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10901742785270407959091147 16352614177905611938636721)
              ·
                refine ⟨12264460633429208953977541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16352614177905611938636721 12264460633429208953977541)
                ·
                  refine ⟨2299586368767976678870789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12264460633429208953977541 2299586368767976678870789)
                  ·
                    refine ⟨431172444143995627288273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2299586368767976678870789 431172444143995627288273)
                    ·
                      refine ⟨323379333107996720466205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431172444143995627288273 323379333107996720466205)
                      ·
                        rfl

theorem cell23_629779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4, 2].length) (baseStart_629779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629779 prefixEnd_629779 := by exact prefixLift 629779
  have htrace : WordTrace (prefixWord ++ tailWord_629779) baseStart_629779 baseEnd_629779 := by
    simpa [prefixWord, tailWord_629779, baseEnd_629779] using wordTrace_append hprefix tailTrace_629779
  have hstable : (prefixWord ++ tailWord_629779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629779).length < 2 ^ (prefixWord ++ tailWord_629779).sum := by decide
  have hdescent : baseEnd_629779 < baseStart_629779 := by decide
  rcases family_descends (prefixWord ++ tailWord_629779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629796 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_629796 : Nat := 118140960795 + 629796 * 2 ^ 59
def prefixEnd_629796 : Nat := 4983230072969 + 3 ^ 40 * 629796 * 2
def baseEnd_629796 : Nat := 323388062279123153953627

theorem tailTrace_629796 : CollatzResearch.WordTrace tailWord_629796 prefixEnd_629796 323388062279123153953627 := by
  unfold tailWord_629796
  simp only [CollatzResearch.WordTrace]
  refine ⟨11485273613182063719286621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15313698150909418292382161 11485273613182063719286621)
  ·
    refine ⟨4306977604943273894732483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11485273613182063719286621 4306977604943273894732483)
    ·
      refine ⟨6460466407414910842098725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4306977604943273894732483 6460466407414910842098725)
      ·
        refine ⟨1211337451390295782893511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6460466407414910842098725 1211337451390295782893511)
        ·
          refine ⟨1817006177085443674340267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211337451390295782893511 1817006177085443674340267)
          ·
            refine ⟨2725509265628165511510401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817006177085443674340267 2725509265628165511510401)
            ·
              refine ⟨2044131949221124133632801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2725509265628165511510401 2044131949221124133632801)
              ·
                refine ⟨1533098961915843100224601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044131949221124133632801 1533098961915843100224601)
                ·
                  refine ⟨1149824221436882325168451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1533098961915843100224601 1149824221436882325168451)
                  ·
                    refine ⟨1724736332155323487752677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1149824221436882325168451 1724736332155323487752677)
                    ·
                      refine ⟨323388062279123153953627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1724736332155323487752677 323388062279123153953627)
                      ·
                        rfl

theorem cell23_629796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_629796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629796 prefixEnd_629796 := by exact prefixLift 629796
  have htrace : WordTrace (prefixWord ++ tailWord_629796) baseStart_629796 baseEnd_629796 := by
    simpa [prefixWord, tailWord_629796, baseEnd_629796] using wordTrace_append hprefix tailTrace_629796
  have hstable : (prefixWord ++ tailWord_629796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629796).length < 2 ^ (prefixWord ++ tailWord_629796).sum := by decide
  have hdescent : baseEnd_629796 < baseStart_629796 := by decide
  rcases family_descends (prefixWord ++ tailWord_629796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629806 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_629806 : Nat := 118140960795 + 629806 * 2 ^ 59
def prefixEnd_629806 : Nat := 4983230072969 + 3 ^ 40 * 629806 * 2
def baseEnd_629806 : Nat := 107797732361889371609527

theorem tailTrace_629806 : CollatzResearch.WordTrace tailWord_629806 prefixEnd_629806 107797732361889371609527 := by
  unfold tailWord_629806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871363994540987393304659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15313941304218599430958181 2871363994540987393304659)
  ·
    refine ⟨4307045991811481089956989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2871363994540987393304659 4307045991811481089956989)
    ·
      refine ⟨1615142246929305408733871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4307045991811481089956989 1615142246929305408733871)
      ·
        refine ⟨2422713370393958113100807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615142246929305408733871 2422713370393958113100807)
        ·
          refine ⟨3634070055590937169651211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422713370393958113100807 3634070055590937169651211)
          ·
            refine ⟨5451105083386405754476817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634070055590937169651211 5451105083386405754476817)
            ·
              refine ⟨4088328812539804315857613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451105083386405754476817 4088328812539804315857613)
              ·
                refine ⟨1533123304702426618446605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4088328812539804315857613 1533123304702426618446605)
                ·
                  refine ⟨574921239263409981917477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1533123304702426618446605 574921239263409981917477)
                  ·
                    refine ⟨107797732361889371609527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 574921239263409981917477 107797732361889371609527)
                    ·
                      rfl

theorem cell23_629806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_629806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629806 prefixEnd_629806 := by exact prefixLift 629806
  have htrace : WordTrace (prefixWord ++ tailWord_629806) baseStart_629806 baseEnd_629806 := by
    simpa [prefixWord, tailWord_629806, baseEnd_629806] using wordTrace_append hprefix tailTrace_629806
  have hstable : (prefixWord ++ tailWord_629806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629806).length < 2 ^ (prefixWord ++ tailWord_629806).sum := by decide
  have hdescent : baseEnd_629806 < baseStart_629806 := by decide
  rcases family_descends (prefixWord ++ tailWord_629806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629830 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_629830 : Nat := 118140960795 + 629830 * 2 ^ 59
def prefixEnd_629830 : Nat := 4983230072969 + 3 ^ 40 * 629830 * 2
def baseEnd_629830 : Nat := 323405520621376020928471

theorem tailTrace_629830 : CollatzResearch.WordTrace tailWord_629830 prefixEnd_629830 323405520621376020928471 := by
  unfold tailWord_629830
  simp only [CollatzResearch.WordTrace]
  refine ⟨717868353382529726415967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15314524872160634163540629 717868353382529726415967)
  ·
    refine ⟨1076802530073794589623951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717868353382529726415967 1076802530073794589623951)
    ·
      refine ⟨1615203795110691884435927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076802530073794589623951 1615203795110691884435927)
      ·
        refine ⟨2422805692666037826653891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615203795110691884435927 2422805692666037826653891)
        ·
          refine ⟨3634208538999056739980837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422805692666037826653891 3634208538999056739980837)
          ·
            refine ⟨681414101062323138746407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3634208538999056739980837 681414101062323138746407)
            ·
              refine ⟨1022121151593484708119611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681414101062323138746407 1022121151593484708119611)
              ·
                refine ⟨1533181727390227062179417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022121151593484708119611 1533181727390227062179417)
                ·
                  refine ⟨1149886295542670296634563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1533181727390227062179417 1149886295542670296634563)
                  ·
                    refine ⟨1724829443314005444951845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1149886295542670296634563 1724829443314005444951845)
                    ·
                      refine ⟨323405520621376020928471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1724829443314005444951845 323405520621376020928471)
                      ·
                        rfl

theorem cell23_629830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_629830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629830 prefixEnd_629830 := by exact prefixLift 629830
  have htrace : WordTrace (prefixWord ++ tailWord_629830) baseStart_629830 baseEnd_629830 := by
    simpa [prefixWord, tailWord_629830, baseEnd_629830] using wordTrace_append hprefix tailTrace_629830
  have hstable : (prefixWord ++ tailWord_629830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629830).length < 2 ^ (prefixWord ++ tailWord_629830).sum := by decide
  have hdescent : baseEnd_629830 < baseStart_629830 := by decide
  rcases family_descends (prefixWord ++ tailWord_629830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629856 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 4, 3, 2]
def baseStart_629856 : Nat := 118140960795 + 629856 * 2 ^ 59
def prefixEnd_629856 : Nat := 4983230072969 + 3 ^ 40 * 629856 * 2
def baseEnd_629856 : Nat := 323418871118392919203351

theorem tailTrace_629856 : CollatzResearch.WordTrace tailWord_629856 prefixEnd_629856 323418871118392919203351 := by
  unfold tailWord_629856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11486367803073378842878711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15315157070764505123838281 11486367803073378842878711)
  ·
    refine ⟨17229551704610068264318067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11486367803073378842878711 17229551704610068264318067)
    ·
      refine ⟨25844327556915102396477101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17229551704610068264318067 25844327556915102396477101)
      ·
        refine ⟨9691622833843163398678913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25844327556915102396477101 9691622833843163398678913)
        ·
          refine ⟨7268717125382372549009185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9691622833843163398678913 7268717125382372549009185)
          ·
            refine ⟨5451537844036779411756889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7268717125382372549009185 5451537844036779411756889)
            ·
              refine ⟨4088653383027584558817667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5451537844036779411756889 4088653383027584558817667)
              ·
                refine ⟨6132980074541376838226501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4088653383027584558817667 6132980074541376838226501)
                ·
                  refine ⟨1149933763976508157167469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6132980074541376838226501 1149933763976508157167469)
                  ·
                    refine ⟨431225161491190558937801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149933763976508157167469 431225161491190558937801)
                    ·
                      refine ⟨323418871118392919203351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431225161491190558937801 323418871118392919203351)
                      ·
                        rfl

theorem cell23_629856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_629856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629856 prefixEnd_629856 := by exact prefixLift 629856
  have htrace : WordTrace (prefixWord ++ tailWord_629856) baseStart_629856 baseEnd_629856 := by
    simpa [prefixWord, tailWord_629856, baseEnd_629856] using wordTrace_append hprefix tailTrace_629856
  have hstable : (prefixWord ++ tailWord_629856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629856).length < 2 ^ (prefixWord ++ tailWord_629856).sum := by decide
  have hdescent : baseEnd_629856 < baseStart_629856 := by decide
  rcases family_descends (prefixWord ++ tailWord_629856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629863 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_629863 : Nat := 118140960795 + 629863 * 2 ^ 59
def prefixEnd_629863 : Nat := 4983230072969 + 3 ^ 40 * 629863 * 2
def baseEnd_629863 : Nat := 323422465482974391815819

theorem tailTrace_629863 : CollatzResearch.WordTrace tailWord_629863 prefixEnd_629863 323422465482974391815819 := by
  unfold tailWord_629863
  simp only [CollatzResearch.WordTrace]
  refine ⟨22972990917121397881262243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15315327278080931920841495 22972990917121397881262243)
  ·
    refine ⟨34459486375682096821893365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22972990917121397881262243 34459486375682096821893365)
    ·
      refine ⟨3230576847720196577052503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34459486375682096821893365 3230576847720196577052503)
      ·
        refine ⟨4845865271580294865578755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3230576847720196577052503 4845865271580294865578755)
        ·
          refine ⟨7268797907370442298368133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4845865271580294865578755 7268797907370442298368133)
          ·
            refine ⟨1362899607631957930944025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7268797907370442298368133 1362899607631957930944025)
            ·
              refine ⟨1022174705723968448208019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362899607631957930944025 1022174705723968448208019)
              ·
                refine ⟨1533262058585952672312029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022174705723968448208019 1533262058585952672312029)
                ·
                  refine ⟨574973271969732252117011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1533262058585952672312029 574973271969732252117011)
                  ·
                    refine ⟨862459907954598378175517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 574973271969732252117011 862459907954598378175517)
                    ·
                      refine ⟨323422465482974391815819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 862459907954598378175517 323422465482974391815819)
                      ·
                        rfl

theorem cell23_629863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_629863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629863 prefixEnd_629863 := by exact prefixLift 629863
  have htrace : WordTrace (prefixWord ++ tailWord_629863) baseStart_629863 baseEnd_629863 := by
    simpa [prefixWord, tailWord_629863, baseEnd_629863] using wordTrace_append hprefix tailTrace_629863
  have hstable : (prefixWord ++ tailWord_629863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629863).length < 2 ^ (prefixWord ++ tailWord_629863).sum := by decide
  have hdescent : baseEnd_629863 < baseStart_629863 := by decide
  rcases family_descends (prefixWord ++ tailWord_629863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629899 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4]
def baseStart_629899 : Nat := 118140960795 + 629899 * 2 ^ 59
def prefixEnd_629899 : Nat := 4983230072969 + 3 ^ 40 * 629899 * 2
def baseEnd_629899 : Nat := 323440950786536250965653

theorem tailTrace_629899 : CollatzResearch.WordTrace tailWord_629899 prefixEnd_629899 323440950786536250965653 := by
  unfold tailWord_629899
  simp only [CollatzResearch.WordTrace]
  refine ⟨22974303944990976029572751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15316202629993984019715167 22974303944990976029572751)
  ·
    refine ⟨34461455917486464044359127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22974303944990976029572751 34461455917486464044359127)
    ·
      refine ⟨51692183876229696066538691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34461455917486464044359127 51692183876229696066538691)
      ·
        refine ⟨77538275814344544099808037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51692183876229696066538691 77538275814344544099808037)
        ·
          refine ⟨14538426715189602018714007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77538275814344544099808037 14538426715189602018714007)
          ·
            refine ⟨21807640072784403028071011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14538426715189602018714007 21807640072784403028071011)
            ·
              refine ⟨32711460109176604542106517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21807640072784403028071011 32711460109176604542106517)
              ·
                refine ⟨1533349692617653337911243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32711460109176604542106517 1533349692617653337911243)
                ·
                  refine ⟨2300024538926480006866865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533349692617653337911243 2300024538926480006866865)
                  ·
                    refine ⟨1725018404194860005150149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2300024538926480006866865 1725018404194860005150149)
                    ·
                      refine ⟨323440950786536250965653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1725018404194860005150149 323440950786536250965653)
                      ·
                        rfl

theorem cell23_629899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4].length) (baseStart_629899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629899 prefixEnd_629899 := by exact prefixLift 629899
  have htrace : WordTrace (prefixWord ++ tailWord_629899) baseStart_629899 baseEnd_629899 := by
    simpa [prefixWord, tailWord_629899, baseEnd_629899] using wordTrace_append hprefix tailTrace_629899
  have hstable : (prefixWord ++ tailWord_629899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629899).length < 2 ^ (prefixWord ++ tailWord_629899).sum := by decide
  have hdescent : baseEnd_629899 < baseStart_629899 := by decide
  rcases family_descends (prefixWord ++ tailWord_629899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629906 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_629906 : Nat := 118140960795 + 629906 * 2 ^ 59
def prefixEnd_629906 : Nat := 4983230072969 + 3 ^ 40 * 629906 * 2
def baseEnd_629906 : Nat := 323444545151117723578121

theorem tailTrace_629906 : CollatzResearch.WordTrace tailWord_629906 prefixEnd_629906 323444545151117723578121 := by
  unfold tailWord_629906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743639813991404056269393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15316372837310410816718381 5743639813991404056269393)
  ·
    refine ⟨4307729860493553042202045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5743639813991404056269393 4307729860493553042202045)
    ·
      refine ⟨1615398697685082390825767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4307729860493553042202045 1615398697685082390825767)
      ·
        refine ⟨2423098046527623586238651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615398697685082390825767 2423098046527623586238651)
        ·
          refine ⟨3634647069791435379357977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423098046527623586238651 3634647069791435379357977)
          ·
            refine ⟨2725985302343576534518483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3634647069791435379357977 2725985302343576534518483)
            ·
              refine ⟨4088977953515364801777725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725985302343576534518483 4088977953515364801777725)
              ·
                refine ⟨1533366732568261800666647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4088977953515364801777725 1533366732568261800666647)
                ·
                  refine ⟨2300050098852392700999971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533366732568261800666647 2300050098852392700999971)
                  ·
                    refine ⟨3450075148278589051499957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2300050098852392700999971 3450075148278589051499957)
                    ·
                      refine ⟨323444545151117723578121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3450075148278589051499957 323444545151117723578121)
                      ·
                        rfl

theorem cell23_629906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_629906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629906 prefixEnd_629906 := by exact prefixLift 629906
  have htrace : WordTrace (prefixWord ++ tailWord_629906) baseStart_629906 baseEnd_629906 := by
    simpa [prefixWord, tailWord_629906, baseEnd_629906] using wordTrace_append hprefix tailTrace_629906
  have hstable : (prefixWord ++ tailWord_629906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629906).length < 2 ^ (prefixWord ++ tailWord_629906).sum := by decide
  have hdescent : baseEnd_629906 < baseStart_629906 := by decide
  rcases family_descends (prefixWord ++ tailWord_629906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629930 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_629930 : Nat := 118140960795 + 629930 * 2 ^ 59
def prefixEnd_629930 : Nat := 4983230072969 + 3 ^ 40 * 629930 * 2
def baseEnd_629930 : Nat := 107818956228941876559337

theorem tailTrace_629930 : CollatzResearch.WordTrace tailWord_629930 prefixEnd_629930 107818956228941876559337 := by
  unfold tailWord_629930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743858651969667080987811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15316956405252445549300829 5743858651969667080987811)
  ·
    refine ⟨8615787977954500621481717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5743858651969667080987811 8615787977954500621481717)
    ·
      refine ⟨807730122933234433263911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8615787977954500621481717 807730122933234433263911)
      ·
        refine ⟨1211595184399851649895867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807730122933234433263911 1211595184399851649895867)
        ·
          refine ⟨1817392776599777474843801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211595184399851649895867 1817392776599777474843801)
          ·
            refine ⟨1363044582449833106132851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1817392776599777474843801 1363044582449833106132851)
            ·
              refine ⟨2044566873674749659199277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363044582449833106132851 2044566873674749659199277)
              ·
                refine ⟨766712577628031122199729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2044566873674749659199277 766712577628031122199729)
                ·
                  refine ⟨575034433221023341649797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 766712577628031122199729 575034433221023341649797)
                  ·
                    refine ⟨107818956228941876559337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575034433221023341649797 107818956228941876559337)
                    ·
                      rfl

theorem cell23_629930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_629930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629930 prefixEnd_629930 := by exact prefixLift 629930
  have htrace : WordTrace (prefixWord ++ tailWord_629930) baseStart_629930 baseEnd_629930 := by
    simpa [prefixWord, tailWord_629930, baseEnd_629930] using wordTrace_append hprefix tailTrace_629930
  have hstable : (prefixWord ++ tailWord_629930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629930).length < 2 ^ (prefixWord ++ tailWord_629930).sum := by decide
  have hdescent : baseEnd_629930 < baseStart_629930 := by decide
  rcases family_descends (prefixWord ++ tailWord_629930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629949 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_629949 : Nat := 118140960795 + 629949 * 2 ^ 59
def prefixEnd_629949 : Nat := 4983230072969 + 3 ^ 40 * 629949 * 2
def baseEnd_629949 : Nat := 323466624819261055340423

theorem tailTrace_629949 : CollatzResearch.WordTrace tailWord_629949 prefixEnd_629949 323466624819261055340423 := by
  unfold tailWord_629949
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976127594809834568892901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15317418396539889712595267 22976127594809834568892901)
  ·
    refine ⟨4308023924026843981667419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22976127594809834568892901 4308023924026843981667419)
    ·
      refine ⟨6462035886040265972501129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4308023924026843981667419 6462035886040265972501129)
      ·
        refine ⟨4846526914530199479375847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6462035886040265972501129 4846526914530199479375847)
        ·
          refine ⟨7269790371795299219063771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846526914530199479375847 7269790371795299219063771)
          ·
            refine ⟨10904685557692948828595657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7269790371795299219063771 10904685557692948828595657)
            ·
              refine ⟨8178514168269711621446743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10904685557692948828595657 8178514168269711621446743)
              ·
                refine ⟨12267771252404567432170115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8178514168269711621446743 12267771252404567432170115)
                ·
                  refine ⟨18401656878606851148255173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12267771252404567432170115 18401656878606851148255173)
                  ·
                    refine ⟨3450310664738784590297845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18401656878606851148255173 3450310664738784590297845)
                    ·
                      refine ⟨323466624819261055340423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3450310664738784590297845 323466624819261055340423)
                      ·
                        rfl

theorem cell23_629949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_629949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629949 prefixEnd_629949 := by exact prefixLift 629949
  have htrace : WordTrace (prefixWord ++ tailWord_629949) baseStart_629949 baseEnd_629949 := by
    simpa [prefixWord, tailWord_629949, baseEnd_629949] using wordTrace_append hprefix tailTrace_629949
  have hstable : (prefixWord ++ tailWord_629949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629949).length < 2 ^ (prefixWord ++ tailWord_629949).sum := by decide
  have hdescent : baseEnd_629949 < baseStart_629949 := by decide
  rcases family_descends (prefixWord ++ tailWord_629949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629953 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_629953 : Nat := 118140960795 + 629953 * 2 ^ 59
def prefixEnd_629953 : Nat := 4983230072969 + 3 ^ 40 * 629953 * 2
def baseEnd_629953 : Nat := 323468678741879039690405

theorem tailTrace_629953 : CollatzResearch.WordTrace tailWord_629953 prefixEnd_629953 323468678741879039690405 := by
  unfold tailWord_629953
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976273486795343252038513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15317515657863562168025675 22976273486795343252038513)
  ·
    refine ⟨17232205115096507439028885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22976273486795343252038513 17232205115096507439028885)
    ·
      refine ⟨807759614770148786204479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17232205115096507439028885 807759614770148786204479)
      ·
        refine ⟨1211639422155223179306719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807759614770148786204479 1211639422155223179306719)
        ·
          refine ⟨1817459133232834768960079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211639422155223179306719 1817459133232834768960079)
          ·
            refine ⟨2726188699849252153440119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817459133232834768960079 2726188699849252153440119)
            ·
              refine ⟨4089283049773878230160179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2726188699849252153440119 4089283049773878230160179)
              ·
                refine ⟨6133924574660817345240269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4089283049773878230160179 6133924574660817345240269)
                ·
                  refine ⟨2300221715497806504465101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6133924574660817345240269 2300221715497806504465101)
                  ·
                    refine ⟨862583143311677439174413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2300221715497806504465101 862583143311677439174413)
                    ·
                      refine ⟨323468678741879039690405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 862583143311677439174413 323468678741879039690405)
                      ·
                        rfl

theorem cell23_629953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_629953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629953 prefixEnd_629953 := by exact prefixLift 629953
  have htrace : WordTrace (prefixWord ++ tailWord_629953) baseStart_629953 baseEnd_629953 := by
    simpa [prefixWord, tailWord_629953, baseEnd_629953] using wordTrace_append hprefix tailTrace_629953
  have hstable : (prefixWord ++ tailWord_629953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629953).length < 2 ^ (prefixWord ++ tailWord_629953).sum := by decide
  have hdescent : baseEnd_629953 < baseStart_629953 := by decide
  rcases family_descends (prefixWord ++ tailWord_629953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629954 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_629954 : Nat := 118140960795 + 629954 * 2 ^ 59
def prefixEnd_629954 : Nat := 4983230072969 + 3 ^ 40 * 629954 * 2
def baseEnd_629954 : Nat := 323469192222533535777901

theorem tailTrace_629954 : CollatzResearch.WordTrace tailWord_629954 prefixEnd_629954 323469192222533535777901 := by
  unfold tailWord_629954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744077489947930105706229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15317539973194480281883277 5744077489947930105706229)
  ·
    refine ⟨538507264682618447409959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5744077489947930105706229 538507264682618447409959)
    ·
      refine ⟨807760897023927671114939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538507264682618447409959 807760897023927671114939)
      ·
        refine ⟨1211641345535891506672409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807760897023927671114939 1211641345535891506672409)
        ·
          refine ⟨908731009151918630004307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211641345535891506672409 908731009151918630004307)
          ·
            refine ⟨1363096513727877945006461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908731009151918630004307 1363096513727877945006461)
            ·
              refine ⟨511161192647954229377423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1363096513727877945006461 511161192647954229377423)
              ·
                refine ⟨766741788971931344066135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511161192647954229377423 766741788971931344066135)
                ·
                  refine ⟨1150112683457897016099203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766741788971931344066135 1150112683457897016099203)
                  ·
                    refine ⟨1725169025186845524148805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1150112683457897016099203 1725169025186845524148805)
                    ·
                      refine ⟨323469192222533535777901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1725169025186845524148805 323469192222533535777901)
                      ·
                        rfl

theorem cell23_629954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_629954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629954 prefixEnd_629954 := by exact prefixLift 629954
  have htrace : WordTrace (prefixWord ++ tailWord_629954) baseStart_629954 baseEnd_629954 := by
    simpa [prefixWord, tailWord_629954, baseEnd_629954] using wordTrace_append hprefix tailTrace_629954
  have hstable : (prefixWord ++ tailWord_629954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629954).length < 2 ^ (prefixWord ++ tailWord_629954).sum := by decide
  have hdescent : baseEnd_629954 < baseStart_629954 := by decide
  rcases family_descends (prefixWord ++ tailWord_629954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629959 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_629959 : Nat := 118140960795 + 629959 * 2 ^ 59
def prefixEnd_629959 : Nat := 4983230072969 + 3 ^ 40 * 629959 * 2
def baseEnd_629959 : Nat := 323471759625806016215377

theorem tailTrace_629959 : CollatzResearch.WordTrace tailWord_629959 prefixEnd_629959 323471759625806016215377 := by
  unfold tailWord_629959
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976492324773606276756931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15317661549849070851171287 22976492324773606276756931)
  ·
    refine ⟨34464738487160409415135397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22976492324773606276756931 34464738487160409415135397)
    ·
      refine ⟨6462138466342576765337887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34464738487160409415135397 6462138466342576765337887)
      ·
        refine ⟨9693207699513865148006831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6462138466342576765337887 9693207699513865148006831)
        ·
          refine ⟨14539811549270797722010247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9693207699513865148006831 14539811549270797722010247)
          ·
            refine ⟨21809717323906196583015371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14539811549270797722010247 21809717323906196583015371)
            ·
              refine ⟨32714575985859294874523057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21809717323906196583015371 32714575985859294874523057)
              ·
                refine ⟨24535931989394471155892293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32714575985859294874523057 24535931989394471155892293)
                ·
                  refine ⟨4600487248011463341729805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24535931989394471155892293 4600487248011463341729805)
                  ·
                    refine ⟨1725182718004298753148677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4600487248011463341729805 1725182718004298753148677)
                    ·
                      refine ⟨323471759625806016215377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1725182718004298753148677 323471759625806016215377)
                      ·
                        rfl

theorem cell23_629959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_629959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629959 prefixEnd_629959 := by exact prefixLift 629959
  have htrace : WordTrace (prefixWord ++ tailWord_629959) baseStart_629959 baseEnd_629959 := by
    simpa [prefixWord, tailWord_629959, baseEnd_629959] using wordTrace_append hprefix tailTrace_629959
  have hstable : (prefixWord ++ tailWord_629959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629959).length < 2 ^ (prefixWord ++ tailWord_629959).sum := by decide
  have hdescent : baseEnd_629959 < baseStart_629959 := by decide
  rcases family_descends (prefixWord ++ tailWord_629959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629969 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 2, 6]
def baseStart_629969 : Nat := 118140960795 + 629969 * 2 ^ 59
def prefixEnd_629969 : Nat := 4983230072969 + 3 ^ 40 * 629969 * 2
def baseEnd_629969 : Nat := 107825631477450325696777

theorem tailTrace_629969 : CollatzResearch.WordTrace tailWord_629969 prefixEnd_629969 107825631477450325696777 := by
  unfold tailWord_629969
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976857054737377984620961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15317904703158251989747307 22976857054737377984620961)
  ·
    refine ⟨17232642791053033488465721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22976857054737377984620961 17232642791053033488465721)
    ·
      refine ⟨12924482093289775116349291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17232642791053033488465721 12924482093289775116349291)
      ·
        refine ⟨19386723139934662674523937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12924482093289775116349291 19386723139934662674523937)
        ·
          refine ⟨14540042354950997005892953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19386723139934662674523937 14540042354950997005892953)
          ·
            refine ⟨10905031766213247754419715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14540042354950997005892953 10905031766213247754419715)
            ·
              refine ⟨16357547649319871631629573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10905031766213247754419715 16357547649319871631629573)
              ·
                refine ⟨3067040184247475930930545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16357547649319871631629573 3067040184247475930930545)
                ·
                  refine ⟨2300280138185606948197909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067040184247475930930545 2300280138185606948197909)
                  ·
                    refine ⟨107825631477450325696777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2300280138185606948197909 107825631477450325696777)
                    ·
                      rfl

theorem cell23_629969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_629969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629969 prefixEnd_629969 := by exact prefixLift 629969
  have htrace : WordTrace (prefixWord ++ tailWord_629969) baseStart_629969 baseEnd_629969 := by
    simpa [prefixWord, tailWord_629969, baseEnd_629969] using wordTrace_append hprefix tailTrace_629969
  have hstable : (prefixWord ++ tailWord_629969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629969).length < 2 ^ (prefixWord ++ tailWord_629969).sum := by decide
  have hdescent : baseEnd_629969 < baseStart_629969 := by decide
  rcases family_descends (prefixWord ++ tailWord_629969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629970 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_629970 : Nat := 118140960795 + 629970 * 2 ^ 59
def prefixEnd_629970 : Nat := 4983230072969 + 3 ^ 40 * 629970 * 2
def baseEnd_629970 : Nat := 323477407913005473177827

theorem tailTrace_629970 : CollatzResearch.WordTrace tailWord_629970 prefixEnd_629970 323477407913005473177827 := by
  unfold tailWord_629970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744223381933438788851841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15317929018489170103604909 5744223381933438788851841)
  ·
    refine ⟨4308167536450079091638881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5744223381933438788851841 4308167536450079091638881)
    ·
      refine ⟨3231125652337559318729161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4308167536450079091638881 3231125652337559318729161)
      ·
        refine ⟨2423344239253169489046871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3231125652337559318729161 2423344239253169489046871)
        ·
          refine ⟨3635016358879754233570307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423344239253169489046871 3635016358879754233570307)
          ·
            refine ⟨5452524538319631350355461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3635016358879754233570307 5452524538319631350355461)
            ·
              refine ⟨1022348350934930878191649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5452524538319631350355461 1022348350934930878191649)
              ·
                refine ⟨766761263201198158643737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022348350934930878191649 766761263201198158643737)
                ·
                  refine ⟨575070947400898618982803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 766761263201198158643737 575070947400898618982803)
                  ·
                    refine ⟨862606421101347928474205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 575070947400898618982803 862606421101347928474205)
                    ·
                      refine ⟨323477407913005473177827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 862606421101347928474205 323477407913005473177827)
                      ·
                        rfl

theorem cell23_629970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_629970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_629970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_629970 prefixEnd_629970 := by exact prefixLift 629970
  have htrace : WordTrace (prefixWord ++ tailWord_629970) baseStart_629970 baseEnd_629970 := by
    simpa [prefixWord, tailWord_629970, baseEnd_629970] using wordTrace_append hprefix tailTrace_629970
  have hstable : (prefixWord ++ tailWord_629970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629970).length < 2 ^ (prefixWord ++ tailWord_629970).sum := by decide
  have hdescent : baseEnd_629970 < baseStart_629970 := by decide
  rcases family_descends (prefixWord ++ tailWord_629970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630006 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_630006 : Nat := 118140960795 + 630006 * 2 ^ 59
def prefixEnd_630006 : Nat := 4983230072969 + 3 ^ 40 * 630006 * 2
def baseEnd_630006 : Nat := 323495893216567332327661

theorem tailTrace_630006 : CollatzResearch.WordTrace tailWord_630006 prefixEnd_630006 323495893216567332327661 := by
  unfold tailWord_630006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436137909725208331482367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15318804370402222202478581 1436137909725208331482367)
  ·
    refine ⟨2154206864587812497223551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1436137909725208331482367 2154206864587812497223551)
    ·
      refine ⟨3231310296881718745835327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154206864587812497223551 3231310296881718745835327)
      ·
        refine ⟨4846965445322578118752991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231310296881718745835327 4846965445322578118752991)
        ·
          refine ⟨7270448167983867178129487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4846965445322578118752991 7270448167983867178129487)
          ·
            refine ⟨10905672251975800767194231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7270448167983867178129487 10905672251975800767194231)
            ·
              refine ⟨16358508377963701150791347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10905672251975800767194231 16358508377963701150791347)
              ·
                refine ⟨24537762566945551726187021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16358508377963701150791347 24537762566945551726187021)
                ·
                  refine ⟨9201660962604581897320133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24537762566945551726187021 9201660962604581897320133)
                  ·
                    refine ⟨1725311430488359105747525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9201660962604581897320133 1725311430488359105747525)
                    ·
                      refine ⟨323495893216567332327661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1725311430488359105747525 323495893216567332327661)
                      ·
                        rfl

theorem cell23_630006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_630006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630006 prefixEnd_630006 := by exact prefixLift 630006
  have htrace : WordTrace (prefixWord ++ tailWord_630006) baseStart_630006 baseEnd_630006 := by
    simpa [prefixWord, tailWord_630006, baseEnd_630006] using wordTrace_append hprefix tailTrace_630006
  have hstable : (prefixWord ++ tailWord_630006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630006).length < 2 ^ (prefixWord ++ tailWord_630006).sum := by decide
  have hdescent : baseEnd_630006 < baseStart_630006 := by decide
  rcases family_descends (prefixWord ++ tailWord_630006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630014 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_630014 : Nat := 118140960795 + 630014 * 2 ^ 59
def prefixEnd_630014 : Nat := 4983230072969 + 3 ^ 40 * 630014 * 2
def baseEnd_630014 : Nat := 323500001061803301027625

theorem tailTrace_630014 : CollatzResearch.WordTrace tailWord_630014 prefixEnd_630014 323500001061803301027625 := by
  unfold tailWord_630014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2872312292446793833751137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15318998893049567113339397 2872312292446793833751137)
  ·
    refine ⟨2154234219335095375313353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2872312292446793833751137 2154234219335095375313353)
    ·
      refine ⟨1615675664501321531485015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2154234219335095375313353 1615675664501321531485015)
      ·
        refine ⟨2423513496751982297227523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615675664501321531485015 2423513496751982297227523)
        ·
          refine ⟨3635270245127973445841285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423513496751982297227523 3635270245127973445841285)
          ·
            refine ⟨681613170961495021095241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3635270245127973445841285 681613170961495021095241)
            ·
              refine ⟨511209878221121265821431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681613170961495021095241 511209878221121265821431)
              ·
                refine ⟨766814817331681898732147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511209878221121265821431 766814817331681898732147)
                ·
                  refine ⟨1150222225997522848098221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766814817331681898732147 1150222225997522848098221)
                  ·
                    refine ⟨431333334749071068036833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1150222225997522848098221 431333334749071068036833)
                    ·
                      refine ⟨323500001061803301027625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431333334749071068036833 323500001061803301027625)
                      ·
                        rfl

theorem cell23_630014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_630014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630014 prefixEnd_630014 := by exact prefixLift 630014
  have htrace : WordTrace (prefixWord ++ tailWord_630014) baseStart_630014 baseEnd_630014 := by
    simpa [prefixWord, tailWord_630014, baseEnd_630014] using wordTrace_append hprefix tailTrace_630014
  have hstable : (prefixWord ++ tailWord_630014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630014).length < 2 ^ (prefixWord ++ tailWord_630014).sum := by decide
  have hdescent : baseEnd_630014 < baseStart_630014 := by decide
  rcases family_descends (prefixWord ++ tailWord_630014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630027 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 2, 2, 2]
def baseStart_630027 : Nat := 118140960795 + 630027 * 2 ^ 59
def prefixEnd_630027 : Nat := 4983230072969 + 3 ^ 40 * 630027 * 2
def baseEnd_630027 : Nat := 323506676310311750165065

theorem tailTrace_630027 : CollatzResearch.WordTrace tailWord_630027 prefixEnd_630027 323506676310311750165065 := by
  unfold tailWord_630027
  simp only [CollatzResearch.WordTrace]
  refine ⟨22978972488527253890232335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15319314992351502593488223 22978972488527253890232335)
  ·
    refine ⟨34468458732790880835348503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22978972488527253890232335 34468458732790880835348503)
    ·
      refine ⟨51702688099186321253022755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34468458732790880835348503 51702688099186321253022755)
      ·
        refine ⟨77554032148779481879534133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51702688099186321253022755 77554032148779481879534133)
        ·
          refine ⟨7270690513948076426206325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77554032148779481879534133 7270690513948076426206325)
          ·
            refine ⟨681627235682632164956843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7270690513948076426206325 681627235682632164956843)
            ·
              refine ⟨1022440853523948247435265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681627235682632164956843 1022440853523948247435265)
              ·
                refine ⟨766830640142961185576449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022440853523948247435265 766830640142961185576449)
                ·
                  refine ⟨575122980107220889182337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 766830640142961185576449 575122980107220889182337)
                  ·
                    refine ⟨431342235080415666886753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575122980107220889182337 431342235080415666886753)
                    ·
                      refine ⟨323506676310311750165065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431342235080415666886753 323506676310311750165065)
                      ·
                        rfl

theorem cell23_630027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 2, 2].length) (baseStart_630027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630027 prefixEnd_630027 := by exact prefixLift 630027
  have htrace : WordTrace (prefixWord ++ tailWord_630027) baseStart_630027 baseEnd_630027 := by
    simpa [prefixWord, tailWord_630027, baseEnd_630027] using wordTrace_append hprefix tailTrace_630027
  have hstable : (prefixWord ++ tailWord_630027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630027).length < 2 ^ (prefixWord ++ tailWord_630027).sum := by decide
  have hdescent : baseEnd_630027 < baseStart_630027 := by decide
  rcases family_descends (prefixWord ++ tailWord_630027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630183 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 1, 6]
def baseStart_630183 : Nat := 118140960795 + 630183 * 2 ^ 59
def prefixEnd_630183 : Nat := 4983230072969 + 3 ^ 40 * 630183 * 2
def baseEnd_630183 : Nat := 107862259764137713271449

theorem tailTrace_630183 : CollatzResearch.WordTrace tailWord_630183 prefixEnd_630183 107862259764137713271449 := by
  unfold tailWord_630183
  simp only [CollatzResearch.WordTrace]
  refine ⟨22984662275962092532911203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15323108183974728355274135 22984662275962092532911203)
  ·
    refine ⟨34476993413943138799366805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22984662275962092532911203 34476993413943138799366805)
    ·
      refine ⟨1616109066278584631220319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34476993413943138799366805 1616109066278584631220319)
      ·
        refine ⟨2424163599417876946830479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616109066278584631220319 2424163599417876946830479)
        ·
          refine ⟨3636245399126815420245719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424163599417876946830479 3636245399126815420245719)
          ·
            refine ⟨5454368098690223130368579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636245399126815420245719 5454368098690223130368579)
            ·
              refine ⟨8181552148035334695552869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5454368098690223130368579 8181552148035334695552869)
              ·
                refine ⟨1534041027756625255416163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8181552148035334695552869 1534041027756625255416163)
                ·
                  refine ⟨2301061541634937883124245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534041027756625255416163 2301061541634937883124245)
                  ·
                    refine ⟨107862259764137713271449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2301061541634937883124245 107862259764137713271449)
                    ·
                      rfl

theorem cell23_630183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_630183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630183 prefixEnd_630183 := by exact prefixLift 630183
  have htrace : WordTrace (prefixWord ++ tailWord_630183) baseStart_630183 baseEnd_630183 := by
    simpa [prefixWord, tailWord_630183, baseEnd_630183] using wordTrace_append hprefix tailTrace_630183
  have hstable : (prefixWord ++ tailWord_630183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630183).length < 2 ^ (prefixWord ++ tailWord_630183).sum := by decide
  have hdescent : baseEnd_630183 < baseStart_630183 := by decide
  rcases family_descends (prefixWord ++ tailWord_630183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630193 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_630193 : Nat := 118140960795 + 630193 * 2 ^ 59
def prefixEnd_630193 : Nat := 4983230072969 + 3 ^ 40 * 630193 * 2
def baseEnd_630193 : Nat := 323591914098958100689301

theorem tailTrace_630193 : CollatzResearch.WordTrace tailWord_630193 prefixEnd_630193 323591914098958100689301 := by
  unfold tailWord_630193
  simp only [CollatzResearch.WordTrace]
  refine ⟨22985027005925864240775233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15323351337283909493850155 22985027005925864240775233)
  ·
    refine ⟨17238770254444398180581425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22985027005925864240775233 17238770254444398180581425)
    ·
      refine ⟨12929077690833298635436069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17238770254444398180581425 12929077690833298635436069)
      ·
        refine ⟨2424202067031243494144263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12929077690833298635436069 2424202067031243494144263)
        ·
          refine ⟨3636303100546865241216395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424202067031243494144263 3636303100546865241216395)
          ·
            refine ⟨5454454650820297861824593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636303100546865241216395 5454454650820297861824593)
            ·
              refine ⟨4090840988115223396368445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5454454650820297861824593 4090840988115223396368445)
              ·
                refine ⟨1534065370543208773638167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4090840988115223396368445 1534065370543208773638167)
                ·
                  refine ⟨2301098055814813160457251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534065370543208773638167 2301098055814813160457251)
                  ·
                    refine ⟨3451647083722219740685877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2301098055814813160457251 3451647083722219740685877)
                    ·
                      refine ⟨323591914098958100689301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3451647083722219740685877 323591914098958100689301)
                      ·
                        rfl

theorem cell23_630193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_630193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630193 prefixEnd_630193 := by exact prefixLift 630193
  have htrace : WordTrace (prefixWord ++ tailWord_630193) baseStart_630193 baseEnd_630193 := by
    simpa [prefixWord, tailWord_630193, baseEnd_630193] using wordTrace_append hprefix tailTrace_630193
  have hstable : (prefixWord ++ tailWord_630193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630193).length < 2 ^ (prefixWord ++ tailWord_630193).sum := by decide
  have hdescent : baseEnd_630193 < baseStart_630193 := by decide
  rcases family_descends (prefixWord ++ tailWord_630193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630200 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 2, 4]
def baseStart_630200 : Nat := 118140960795 + 630200 * 2 ^ 59
def prefixEnd_630200 : Nat := 4983230072969 + 3 ^ 40 * 630200 * 2
def baseEnd_630200 : Nat := 107865169487846524433923

theorem tailTrace_630200 : CollatzResearch.WordTrace tailWord_630200 prefixEnd_630200 107865169487846524433923 := by
  unfold tailWord_630200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492641158450252218140027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15323521544600336290853369 11492641158450252218140027)
  ·
    refine ⟨17238961737675378327210041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11492641158450252218140027 17238961737675378327210041)
    ·
      refine ⟨12929221303256533745407531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17238961737675378327210041 12929221303256533745407531)
      ·
        refine ⟨19393831954884800618111297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12929221303256533745407531 19393831954884800618111297)
        ·
          refine ⟨14545373966163600463583473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19393831954884800618111297 14545373966163600463583473)
          ·
            refine ⟨10909030474622700347687605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14545373966163600463583473 10909030474622700347687605)
            ·
              refine ⟨1022721606995878157595713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10909030474622700347687605 1022721606995878157595713)
              ·
                refine ⟨767041205246908618196785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022721606995878157595713 767041205246908618196785)
                ·
                  refine ⟨575280903935181463647589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767041205246908618196785 575280903935181463647589)
                  ·
                    refine ⟨107865169487846524433923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575280903935181463647589 107865169487846524433923)
                    ·
                      rfl

theorem cell23_630200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_630200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630200 prefixEnd_630200 := by exact prefixLift 630200
  have htrace : WordTrace (prefixWord ++ tailWord_630200) baseStart_630200 baseEnd_630200 := by
    simpa [prefixWord, tailWord_630200, baseEnd_630200] using wordTrace_append hprefix tailTrace_630200
  have hstable : (prefixWord ++ tailWord_630200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630200).length < 2 ^ (prefixWord ++ tailWord_630200).sum := by decide
  have hdescent : baseEnd_630200 < baseStart_630200 := by decide
  rcases family_descends (prefixWord ++ tailWord_630200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630220 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_630220 : Nat := 118140960795 + 630220 * 2 ^ 59
def prefixEnd_630220 : Nat := 4983230072969 + 3 ^ 40 * 630220 * 2
def baseEnd_630220 : Nat := 323605778076629495051677

theorem tailTrace_630220 : CollatzResearch.WordTrace tailWord_630220 prefixEnd_630220 323605778076629495051677 := by
  unfold tailWord_630220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493005888414023926004057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15324007851218698568005409 11493005888414023926004057)
  ·
    refine ⟨8619754416310517944503043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11493005888414023926004057 8619754416310517944503043)
    ·
      refine ⟨12929631624465776916754565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8619754416310517944503043 12929631624465776916754565)
      ·
        refine ⟨2424305929587333171891481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12929631624465776916754565 2424305929587333171891481)
        ·
          refine ⟨1818229447190499878918611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2424305929587333171891481 1818229447190499878918611)
          ·
            refine ⟨2727344170785749818377917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818229447190499878918611 2727344170785749818377917)
            ·
              refine ⟨1022754064044656181891719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2727344170785749818377917 1022754064044656181891719)
              ·
                refine ⟨1534131096066984272837579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022754064044656181891719 1534131096066984272837579)
                ·
                  refine ⟨2301196644100476409256369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534131096066984272837579 2301196644100476409256369)
                  ·
                    refine ⟨1725897483075357306942277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2301196644100476409256369 1725897483075357306942277)
                    ·
                      refine ⟨323605778076629495051677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1725897483075357306942277 323605778076629495051677)
                      ·
                        rfl

theorem cell23_630220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_630220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630220 prefixEnd_630220 := by exact prefixLift 630220
  have htrace : WordTrace (prefixWord ++ tailWord_630220) baseStart_630220 baseEnd_630220 := by
    simpa [prefixWord, tailWord_630220, baseEnd_630220] using wordTrace_append hprefix tailTrace_630220
  have hstable : (prefixWord ++ tailWord_630220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630220).length < 2 ^ (prefixWord ++ tailWord_630220).sum := by decide
  have hdescent : baseEnd_630220 < baseStart_630220 := by decide
  rcases family_descends (prefixWord ++ tailWord_630220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630230 : List Nat := [5, 2, 1, 1, 1, 3, 1, 9]
def baseStart_630230 : Nat := 118140960795 + 630230 * 2 ^ 59
def prefixEnd_630230 : Nat := 4983230072969 + 3 ^ 40 * 630230 * 2
def baseEnd_630230 : Nat := 11985589366043498367653

theorem tailTrace_630230 : CollatzResearch.WordTrace tailWord_630230 prefixEnd_630230 11985589366043498367653 := by
  unfold tailWord_630230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436648531674488722492009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15324251004527879706581429 1436648531674488722492009)
  ·
    refine ⟨1077486398755866541869007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1436648531674488722492009 1077486398755866541869007)
    ·
      refine ⟨1616229598133799812803511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1077486398755866541869007 1616229598133799812803511)
      ·
        refine ⟨2424344397200699719205267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616229598133799812803511 2424344397200699719205267)
        ·
          refine ⟨3636516595801049578807901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424344397200699719205267 3636516595801049578807901)
          ·
            refine ⟨1363693723425393592052963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3636516595801049578807901 1363693723425393592052963)
            ·
              refine ⟨2045540585138090388079445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363693723425393592052963 2045540585138090388079445)
              ·
                refine ⟨11985589366043498367653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2045540585138090388079445 11985589366043498367653)
                ·
                  rfl

theorem cell23_630230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_630230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630230 prefixEnd_630230 := by exact prefixLift 630230
  have htrace : WordTrace (prefixWord ++ tailWord_630230) baseStart_630230 baseEnd_630230 := by
    simpa [prefixWord, tailWord_630230, baseEnd_630230] using wordTrace_append hprefix tailTrace_630230
  have hstable : (prefixWord ++ tailWord_630230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630230).length < 2 ^ (prefixWord ++ tailWord_630230).sum := by decide
  have hdescent : baseEnd_630230 < baseStart_630230 := by decide
  rcases family_descends (prefixWord ++ tailWord_630230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630241 : List Nat := [1, 2, 3, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_630241 : Nat := 118140960795 + 630241 * 2 ^ 59
def prefixEnd_630241 : Nat := 4983230072969 + 3 ^ 40 * 630241 * 2
def baseEnd_630241 : Nat := 323616561170373912889081

theorem tailTrace_630241 : CollatzResearch.WordTrace tailWord_630241 prefixEnd_630241 323616561170373912889081 := by
  unfold tailWord_630241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22986777709751968438522577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15324518473167978959015051 22986777709751968438522577)
  ·
    refine ⟨17240083282313976328891933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22986777709751968438522577 17240083282313976328891933)
    ·
      refine ⟨6465031230867741123334475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17240083282313976328891933 6465031230867741123334475)
      ·
        refine ⟨9697546846301611685001713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6465031230867741123334475 9697546846301611685001713)
        ·
          refine ⟨7273160134726208763751285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9697546846301611685001713 7273160134726208763751285)
          ·
            refine ⟨681858762630582071601683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7273160134726208763751285 681858762630582071601683)
            ·
              refine ⟨1022788143945873107402525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681858762630582071601683 1022788143945873107402525)
              ·
                refine ⟨383545553979702415275947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022788143945873107402525 383545553979702415275947)
                ·
                  refine ⟨575318330969553622913921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383545553979702415275947 575318330969553622913921)
                  ·
                    refine ⟨431488748227165217185441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575318330969553622913921 431488748227165217185441)
                    ·
                      refine ⟨323616561170373912889081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431488748227165217185441 323616561170373912889081)
                      ·
                        rfl

theorem cell23_630241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_630241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630241 prefixEnd_630241 := by exact prefixLift 630241
  have htrace : WordTrace (prefixWord ++ tailWord_630241) baseStart_630241 baseEnd_630241 := by
    simpa [prefixWord, tailWord_630241, baseEnd_630241] using wordTrace_append hprefix tailTrace_630241
  have hstable : (prefixWord ++ tailWord_630241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630241).length < 2 ^ (prefixWord ++ tailWord_630241).sum := by decide
  have hdescent : baseEnd_630241 < baseStart_630241 := by decide
  rcases family_descends (prefixWord ++ tailWord_630241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630258 : List Nat := [3, 2, 1, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_630258 : Nat := 118140960795 + 630258 * 2 ^ 59
def prefixEnd_630258 : Nat := 4983230072969 + 3 ^ 40 * 630258 * 2
def baseEnd_630258 : Nat := 323625290341500346376503

theorem tailTrace_630258 : CollatzResearch.WordTrace tailWord_630258 prefixEnd_630258 323625290341500346376503 := by
  unfold tailWord_630258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5746849437672595085472857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15324931833793586894594285 5746849437672595085472857)
  ·
    refine ⟨4310137078254446314104643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5746849437672595085472857 4310137078254446314104643)
    ·
      refine ⟨6465205617381669471156965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4310137078254446314104643 6465205617381669471156965)
      ·
        refine ⟨1212226053259063025841931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6465205617381669471156965 1212226053259063025841931)
        ·
          refine ⟨1818339079888594538762897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212226053259063025841931 1818339079888594538762897)
          ·
            refine ⟨1363754309916445904072173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1818339079888594538762897 1363754309916445904072173)
            ·
              refine ⟨511407866218667214027065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1363754309916445904072173 511407866218667214027065)
              ·
                refine ⟨383555899664000410520299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511407866218667214027065 383555899664000410520299)
                ·
                  refine ⟨575333849496000615780449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383555899664000410520299 575333849496000615780449)
                  ·
                    refine ⟨431500387122000461835337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575333849496000615780449 431500387122000461835337)
                    ·
                      refine ⟨323625290341500346376503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431500387122000461835337 323625290341500346376503)
                      ·
                        rfl

theorem cell23_630258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_630258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630258 prefixEnd_630258 := by exact prefixLift 630258
  have htrace : WordTrace (prefixWord ++ tailWord_630258) baseStart_630258 baseEnd_630258 := by
    simpa [prefixWord, tailWord_630258, baseEnd_630258] using wordTrace_append hprefix tailTrace_630258
  have hstable : (prefixWord ++ tailWord_630258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630258).length < 2 ^ (prefixWord ++ tailWord_630258).sum := by decide
  have hdescent : baseEnd_630258 < baseStart_630258 := by decide
  rcases family_descends (prefixWord ++ tailWord_630258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630330 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_630330 : Nat := 118140960795 + 630330 * 2 ^ 59
def prefixEnd_630330 : Nat := 4983230072969 + 3 ^ 40 * 630330 * 2
def baseEnd_630330 : Nat := 323662260948624064676171

theorem tailTrace_630330 : CollatzResearch.WordTrace tailWord_630330 prefixEnd_630330 323662260948624064676171 := by
  unfold tailWord_630330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747505951607384159628111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15326682537619691092341629 5747505951607384159628111)
  ·
    refine ⟨8621258927411076239442167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5747505951607384159628111 8621258927411076239442167)
    ·
      refine ⟨12931888391116614359163251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8621258927411076239442167 12931888391116614359163251)
      ·
        refine ⟨19397832586674921538744877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12931888391116614359163251 19397832586674921538744877)
        ·
          refine ⟨7274187220003095577029329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19397832586674921538744877 7274187220003095577029329)
          ·
            refine ⟨5455640415002321682771997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7274187220003095577029329 5455640415002321682771997)
            ·
              refine ⟨2045865155625870631039499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5455640415002321682771997 2045865155625870631039499)
              ·
                refine ⟨3068797733438805946559249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045865155625870631039499 3068797733438805946559249)
                ·
                  refine ⟨2301598300079104459919437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068797733438805946559249 2301598300079104459919437)
                  ·
                    refine ⟨863099362529664172469789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2301598300079104459919437 863099362529664172469789)
                    ·
                      refine ⟨323662260948624064676171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 863099362529664172469789 323662260948624064676171)
                      ·
                        rfl

theorem cell23_630330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_630330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630330 prefixEnd_630330 := by exact prefixLift 630330
  have htrace : WordTrace (prefixWord ++ tailWord_630330) baseStart_630330 baseEnd_630330 := by
    simpa [prefixWord, tailWord_630330, baseEnd_630330] using wordTrace_append hprefix tailTrace_630330
  have hstable : (prefixWord ++ tailWord_630330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630330).length < 2 ^ (prefixWord ++ tailWord_630330).sum := by decide
  have hdescent : baseEnd_630330 < baseStart_630330 := by decide
  rcases family_descends (prefixWord ++ tailWord_630330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630365 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_630365 : Nat := 118140960795 + 630365 * 2 ^ 59
def prefixEnd_630365 : Nat := 4983230072969 + 3 ^ 40 * 630365 * 2
def baseEnd_630365 : Nat := 323680232771531427738511

theorem tailTrace_630365 : CollatzResearch.WordTrace tailWord_630365 prefixEnd_630365 323680232771531427738511 := by
  unfold tailWord_630365
  simp only [CollatzResearch.WordTrace]
  refine ⟨22991300361302737616036549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15327533574201825077357699 22991300361302737616036549)
  ·
    refine ⟨4310868817744263303006853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22991300361302737616036549 4310868817744263303006853)
    ·
      refine ⟨808287903327049369313785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4310868817744263303006853 808287903327049369313785)
      ·
        refine ⟨606215927495287026985339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 808287903327049369313785 606215927495287026985339)
        ·
          refine ⟨909323891242930540478009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606215927495287026985339 909323891242930540478009)
          ·
            refine ⟨681992918432197905358507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909323891242930540478009 681992918432197905358507)
            ·
              refine ⟨1022989377648296858037761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681992918432197905358507 1022989377648296858037761)
              ·
                refine ⟨767242033236222643528321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022989377648296858037761 767242033236222643528321)
                ·
                  refine ⟨575431524927166982646241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767242033236222643528321 575431524927166982646241)
                  ·
                    refine ⟨431573643695375236984681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575431524927166982646241 431573643695375236984681)
                    ·
                      refine ⟨323680232771531427738511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431573643695375236984681 323680232771531427738511)
                      ·
                        rfl

theorem cell23_630365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_630365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630365 prefixEnd_630365 := by exact prefixLift 630365
  have htrace : WordTrace (prefixWord ++ tailWord_630365) baseStart_630365 baseEnd_630365 := by
    simpa [prefixWord, tailWord_630365, baseEnd_630365] using wordTrace_append hprefix tailTrace_630365
  have hstable : (prefixWord ++ tailWord_630365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630365).length < 2 ^ (prefixWord ++ tailWord_630365).sum := by decide
  have hdescent : baseEnd_630365 < baseStart_630365 := by decide
  rcases family_descends (prefixWord ++ tailWord_630365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630383 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_630383 : Nat := 118140960795 + 630383 * 2 ^ 59
def prefixEnd_630383 : Nat := 4983230072969 + 3 ^ 40 * 630383 * 2
def baseEnd_630383 : Nat := 323689475423312357313427

theorem tailTrace_630383 : CollatzResearch.WordTrace tailWord_630383 prefixEnd_630383 323689475423312357313427 := by
  unfold tailWord_630383
  simp only [CollatzResearch.WordTrace]
  refine ⟨22991956875237526690191803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15327971250158351126794535 22991956875237526690191803)
  ·
    refine ⟨34487935312856290035287705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22991956875237526690191803 34487935312856290035287705)
    ·
      refine ⟨25865951484642217526465779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34487935312856290035287705 25865951484642217526465779)
      ·
        refine ⟨38798927226963326289698669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25865951484642217526465779 38798927226963326289698669)
        ·
          refine ⟨14549597710111247358637001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38798927226963326289698669 14549597710111247358637001)
          ·
            refine ⟨10912198282583435518977751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14549597710111247358637001 10912198282583435518977751)
            ·
              refine ⟨16368297423875153278466627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10912198282583435518977751 16368297423875153278466627)
              ·
                refine ⟨24552446135812729917699941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16368297423875153278466627 24552446135812729917699941)
                ·
                  refine ⟨4603583650464886859568739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24552446135812729917699941 4603583650464886859568739)
                  ·
                    refine ⟨6905375475697330289353109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4603583650464886859568739 6905375475697330289353109)
                    ·
                      refine ⟨323689475423312357313427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6905375475697330289353109 323689475423312357313427)
                      ·
                        rfl

theorem cell23_630383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_630383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630383 prefixEnd_630383 := by exact prefixLift 630383
  have htrace : WordTrace (prefixWord ++ tailWord_630383) baseStart_630383 baseEnd_630383 := by
    simpa [prefixWord, tailWord_630383, baseEnd_630383] using wordTrace_append hprefix tailTrace_630383
  have hstable : (prefixWord ++ tailWord_630383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630383).length < 2 ^ (prefixWord ++ tailWord_630383).sum := by decide
  have hdescent : baseEnd_630383 < baseStart_630383 := by decide
  rcases family_descends (prefixWord ++ tailWord_630383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630397 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_630397 : Nat := 118140960795 + 630397 * 2 ^ 59
def prefixEnd_630397 : Nat := 4983230072969 + 3 ^ 40 * 630397 * 2
def baseEnd_630397 : Nat := 107898888050825100846121

theorem tailTrace_630397 : CollatzResearch.WordTrace tailWord_630397 prefixEnd_630397 107898888050825100846121 := by
  unfold tailWord_630397
  simp only [CollatzResearch.WordTrace]
  refine ⟨22992467497186807081201445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15328311664791204720800963 22992467497186807081201445)
  ·
    refine ⟨4311087655722526327725271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22992467497186807081201445 4311087655722526327725271)
    ·
      refine ⟨6466631483583789491587907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311087655722526327725271 6466631483583789491587907)
      ·
        refine ⟨9699947225375684237381861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466631483583789491587907 9699947225375684237381861)
        ·
          refine ⟨1818740104757940794509099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9699947225375684237381861 1818740104757940794509099)
          ·
            refine ⟨2728110157136911191763649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818740104757940794509099 2728110157136911191763649)
            ·
              refine ⟨2046082617852683393822737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728110157136911191763649 2046082617852683393822737)
              ·
                refine ⟨1534561963389512545367053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046082617852683393822737 1534561963389512545367053)
                ·
                  refine ⟨575460736271067204512645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1534561963389512545367053 575460736271067204512645)
                  ·
                    refine ⟨107898888050825100846121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575460736271067204512645 107898888050825100846121)
                    ·
                      rfl

theorem cell23_630397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_630397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630397 prefixEnd_630397 := by exact prefixLift 630397
  have htrace : WordTrace (prefixWord ++ tailWord_630397) baseStart_630397 baseEnd_630397 := by
    simpa [prefixWord, tailWord_630397, baseEnd_630397] using wordTrace_append hprefix tailTrace_630397
  have hstable : (prefixWord ++ tailWord_630397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630397).length < 2 ^ (prefixWord ++ tailWord_630397).sum := by decide
  have hdescent : baseEnd_630397 < baseStart_630397 := by decide
  rcases family_descends (prefixWord ++ tailWord_630397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630410 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 8]
def baseStart_630410 : Nat := 118140960795 + 630410 * 2 ^ 59
def prefixEnd_630410 : Nat := 4983230072969 + 3 ^ 40 * 630410 * 2
def baseEnd_630410 : Nat := 35967037711220416852867

theorem tailTrace_630410 : CollatzResearch.WordTrace tailWord_630410 prefixEnd_630410 35967037711220416852867 := by
  unfold tailWord_630410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748235411534927575356171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15328627764093140200949789 5748235411534927575356171)
  ·
    refine ⟨8622353117302391363034257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748235411534927575356171 8622353117302391363034257)
    ·
      refine ⟨6466764837976793522275693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8622353117302391363034257 6466764837976793522275693)
      ·
        refine ⟨2425036814241297570853385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6466764837976793522275693 2425036814241297570853385)
        ·
          refine ⟨1818777610680973178140039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2425036814241297570853385 1818777610680973178140039)
          ·
            refine ⟨2728166416021459767210059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818777610680973178140039 2728166416021459767210059)
            ·
              refine ⟨4092249624032189650815089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728166416021459767210059 4092249624032189650815089)
              ·
                refine ⟨3069187218024142238111317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4092249624032189650815089 3069187218024142238111317)
                ·
                  refine ⟨35967037711220416852867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3069187218024142238111317 35967037711220416852867)
                  ·
                    rfl

theorem cell23_630410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_630410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630410 prefixEnd_630410 := by exact prefixLift 630410
  have htrace : WordTrace (prefixWord ++ tailWord_630410) baseStart_630410 baseEnd_630410 := by
    simpa [prefixWord, tailWord_630410, baseEnd_630410] using wordTrace_append hprefix tailTrace_630410
  have hstable : (prefixWord ++ tailWord_630410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630410).length < 2 ^ (prefixWord ++ tailWord_630410).sum := by decide
  have hdescent : baseEnd_630410 < baseStart_630410 := by decide
  rcases family_descends (prefixWord ++ tailWord_630410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630431 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 3, 4]
def baseStart_630431 : Nat := 118140960795 + 630431 * 2 ^ 59
def prefixEnd_630431 : Nat := 4983230072969 + 3 ^ 40 * 630431 * 2
def baseEnd_630431 : Nat := 107904707498242723171069

theorem tailTrace_630431 : CollatzResearch.WordTrace tailWord_630431 prefixEnd_630431 107904707498242723171069 := by
  unfold tailWord_630431
  simp only [CollatzResearch.WordTrace]
  refine ⟨22993707579063630887939147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15329138386042420591959431 22993707579063630887939147)
  ·
    refine ⟨34490561368595446331908721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22993707579063630887939147 34490561368595446331908721)
    ·
      refine ⟨25867921026446584748931541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34490561368595446331908721 25867921026446584748931541)
      ·
        refine ⟨606279399057341830053083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25867921026446584748931541 606279399057341830053083)
        ·
          refine ⟨909419098586012745079625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606279399057341830053083 909419098586012745079625)
          ·
            refine ⟨682064323939509558809719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909419098586012745079625 682064323939509558809719)
            ·
              refine ⟨1023096485909264338214579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682064323939509558809719 1023096485909264338214579)
              ·
                refine ⟨1534644728863896507321869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023096485909264338214579 1534644728863896507321869)
                ·
                  refine ⟨575491773323961190245701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1534644728863896507321869 575491773323961190245701)
                  ·
                    refine ⟨107904707498242723171069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575491773323961190245701 107904707498242723171069)
                    ·
                      rfl

theorem cell23_630431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_630431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630431 prefixEnd_630431 := by exact prefixLift 630431
  have htrace : WordTrace (prefixWord ++ tailWord_630431) baseStart_630431 baseEnd_630431 := by
    simpa [prefixWord, tailWord_630431, baseEnd_630431] using wordTrace_append hprefix tailTrace_630431
  have hstable : (prefixWord ++ tailWord_630431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630431).length < 2 ^ (prefixWord ++ tailWord_630431).sum := by decide
  have hdescent : baseEnd_630431 < baseStart_630431 := by decide
  rcases family_descends (prefixWord ++ tailWord_630431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630443 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10]
def baseStart_630443 : Nat := 118140960795 + 630443 * 2 ^ 59
def prefixEnd_630443 : Nat := 4983230072969 + 3 ^ 40 * 630443 * 2
def baseEnd_630443 : Nat := 323720284262582122563151

theorem tailTrace_630443 : CollatzResearch.WordTrace tailWord_630443 prefixEnd_630443 323720284262582122563151 := by
  unfold tailWord_630443
  simp only [CollatzResearch.WordTrace]
  refine ⟨22994145255020156937375983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15329430170013437958250655 22994145255020156937375983)
  ·
    refine ⟨34491217882530235406063975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22994145255020156937375983 34491217882530235406063975)
    ·
      refine ⟨51736826823795353109095963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34491217882530235406063975 51736826823795353109095963)
      ·
        refine ⟨77605240235693029663643945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51736826823795353109095963 77605240235693029663643945)
        ·
          refine ⟨58203930176769772247732959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77605240235693029663643945 58203930176769772247732959)
          ·
            refine ⟨87305895265154658371599439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58203930176769772247732959 87305895265154658371599439)
            ·
              refine ⟨130958842897731987557399159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87305895265154658371599439 130958842897731987557399159)
              ·
                refine ⟨196438264346597981336098739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130958842897731987557399159 196438264346597981336098739)
                ·
                  refine ⟨294657396519896972004148109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196438264346597981336098739 294657396519896972004148109)
                  ·
                    refine ⟨110496523694961364501555541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294657396519896972004148109 110496523694961364501555541)
                    ·
                      refine ⟨323720284262582122563151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 110496523694961364501555541 323720284262582122563151)
                      ·
                        rfl

theorem cell23_630443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_630443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630443 prefixEnd_630443 := by exact prefixLift 630443
  have htrace : WordTrace (prefixWord ++ tailWord_630443) baseStart_630443 baseEnd_630443 := by
    simpa [prefixWord, tailWord_630443, baseEnd_630443] using wordTrace_append hprefix tailTrace_630443
  have hstable : (prefixWord ++ tailWord_630443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630443).length < 2 ^ (prefixWord ++ tailWord_630443).sum := by decide
  have hdescent : baseEnd_630443 < baseStart_630443 := by decide
  rcases family_descends (prefixWord ++ tailWord_630443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630447 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 4, 3, 2]
def baseStart_630447 : Nat := 118140960795 + 630447 * 2 ^ 59
def prefixEnd_630447 : Nat := 4983230072969 + 3 ^ 40 * 630447 * 2
def baseEnd_630447 : Nat := 323722338185200106913133

theorem tailTrace_630447 : CollatzResearch.WordTrace tailWord_630447 prefixEnd_630447 323722338185200106913133 := by
  unfold tailWord_630447
  simp only [CollatzResearch.WordTrace]
  refine ⟨22994291147005665620521595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15329527431337110413681063 22994291147005665620521595)
  ·
    refine ⟨34491436720508498430782393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22994291147005665620521595 34491436720508498430782393)
    ·
      refine ⟨25868577540381373823086795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34491436720508498430782393 25868577540381373823086795)
      ·
        refine ⟨38802866310572060734630193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25868577540381373823086795 38802866310572060734630193)
        ·
          refine ⟨29102149732929045550972645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38802866310572060734630193 29102149732929045550972645)
          ·
            refine ⟨5456653074924196040807371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29102149732929045550972645 5456653074924196040807371)
            ·
              refine ⟨8184979612386294061211057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5456653074924196040807371 8184979612386294061211057)
              ·
                refine ⟨6138734709289720545908293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8184979612386294061211057 6138734709289720545908293)
                ·
                  refine ⟨1151012757991822602357805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6138734709289720545908293 1151012757991822602357805)
                  ·
                    refine ⟨431629784246933475884177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151012757991822602357805 431629784246933475884177)
                    ·
                      refine ⟨323722338185200106913133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431629784246933475884177 323722338185200106913133)
                      ·
                        rfl

theorem cell23_630447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 3, 2].length) (baseStart_630447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630447 prefixEnd_630447 := by exact prefixLift 630447
  have htrace : WordTrace (prefixWord ++ tailWord_630447) baseStart_630447 baseEnd_630447 := by
    simpa [prefixWord, tailWord_630447, baseEnd_630447] using wordTrace_append hprefix tailTrace_630447
  have hstable : (prefixWord ++ tailWord_630447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630447).length < 2 ^ (prefixWord ++ tailWord_630447).sum := by decide
  have hdescent : baseEnd_630447 < baseStart_630447 := by decide
  rcases family_descends (prefixWord ++ tailWord_630447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630457 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 1, 5]
def baseStart_630457 : Nat := 118140960795 + 630457 * 2 ^ 59
def prefixEnd_630457 : Nat := 4983230072969 + 3 ^ 40 * 630457 * 2
def baseEnd_630457 : Nat := 107909157663915022596029

theorem tailTrace_630457 : CollatzResearch.WordTrace tailWord_630457 prefixEnd_630457 107909157663915022596029 := by
  unfold tailWord_630457
  simp only [CollatzResearch.WordTrace]
  refine ⟨22994655876969437328385625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15329770584646291552257083 22994655876969437328385625)
  ·
    refine ⟨17245991907727077996289219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22994655876969437328385625 17245991907727077996289219)
    ·
      refine ⟨25868987861590616994433829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17245991907727077996289219 25868987861590616994433829)
      ·
        refine ⟨4850435224048240686456343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25868987861590616994433829 4850435224048240686456343)
        ·
          refine ⟨7275652836072361029684515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850435224048240686456343 7275652836072361029684515)
          ·
            refine ⟨10913479254108541544526773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275652836072361029684515 10913479254108541544526773)
            ·
              refine ⟨1023138680072675769799385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10913479254108541544526773 1023138680072675769799385)
              ·
                refine ⟨767354010054506827349539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023138680072675769799385 767354010054506827349539)
                ·
                  refine ⟨1151031015081760241024309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767354010054506827349539 1151031015081760241024309)
                  ·
                    refine ⟨107909157663915022596029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1151031015081760241024309 107909157663915022596029)
                    ·
                      rfl

theorem cell23_630457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_630457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630457 prefixEnd_630457 := by exact prefixLift 630457
  have htrace : WordTrace (prefixWord ++ tailWord_630457) baseStart_630457 baseEnd_630457 := by
    simpa [prefixWord, tailWord_630457, baseEnd_630457] using wordTrace_append hprefix tailTrace_630457
  have hstable : (prefixWord ++ tailWord_630457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630457).length < 2 ^ (prefixWord ++ tailWord_630457).sum := by decide
  have hdescent : baseEnd_630457 < baseStart_630457 := by decide
  rcases family_descends (prefixWord ++ tailWord_630457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630464 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 2, 3, 2]
def baseStart_630464 : Nat := 118140960795 + 630464 * 2 ^ 59
def prefixEnd_630464 : Nat := 4983230072969 + 3 ^ 40 * 630464 * 2
def baseEnd_630464 : Nat := 323731067356326540400555

theorem tailTrace_630464 : CollatzResearch.WordTrace tailWord_630464 prefixEnd_630464 323731067356326540400555 := by
  unfold tailWord_630464
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497455593972038761945223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15329940791962718349260297 11497455593972038761945223)
  ·
    refine ⟨17246183390958058142917835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11497455593972038761945223 17246183390958058142917835)
    ·
      refine ⟨25869275086437087214376753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17246183390958058142917835 25869275086437087214376753)
      ·
        refine ⟨19401956314827815410782565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25869275086437087214376753 19401956314827815410782565)
        ·
          refine ⟨3637866809030215389521731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19401956314827815410782565 3637866809030215389521731)
          ·
            refine ⟨5456800213545323084282597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637866809030215389521731 5456800213545323084282597)
            ·
              refine ⟨1023150040039748078302987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5456800213545323084282597 1023150040039748078302987)
              ·
                refine ⟨1534725060059622117454481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023150040039748078302987 1534725060059622117454481)
                ·
                  refine ⟨1151043795044716588090861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1534725060059622117454481 1151043795044716588090861)
                  ·
                    refine ⟨431641423141768720534073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151043795044716588090861 431641423141768720534073)
                    ·
                      refine ⟨323731067356326540400555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431641423141768720534073 323731067356326540400555)
                      ·
                        rfl

theorem cell23_630464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_630464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630464 prefixEnd_630464 := by exact prefixLift 630464
  have htrace : WordTrace (prefixWord ++ tailWord_630464) baseStart_630464 baseEnd_630464 := by
    simpa [prefixWord, tailWord_630464, baseEnd_630464] using wordTrace_append hprefix tailTrace_630464
  have hstable : (prefixWord ++ tailWord_630464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630464).length < 2 ^ (prefixWord ++ tailWord_630464).sum := by decide
  have hdescent : baseEnd_630464 < baseStart_630464 := by decide
  rcases family_descends (prefixWord ++ tailWord_630464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630480 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_630480 : Nat := 118140960795 + 630480 * 2 ^ 59
def prefixEnd_630480 : Nat := 4983230072969 + 3 ^ 40 * 630480 * 2
def baseEnd_630480 : Nat := 323739283046798477800481

theorem tailTrace_630480 : CollatzResearch.WordTrace tailWord_630480 prefixEnd_630480 323739283046798477800481 := by
  unfold tailWord_630480
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497747377943056128236447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15330329837257408170981929 11497747377943056128236447)
  ·
    refine ⟨17246621066914584192354671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11497747377943056128236447 17246621066914584192354671)
    ·
      refine ⟨25869931600371876288532007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17246621066914584192354671 25869931600371876288532007)
      ·
        refine ⟨38804897400557814432798011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25869931600371876288532007 38804897400557814432798011)
        ·
          refine ⟨58207346100836721649197017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38804897400557814432798011 58207346100836721649197017)
          ·
            refine ⟨43655509575627541236897763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58207346100836721649197017 43655509575627541236897763)
            ·
              refine ⟨65483264363441311855346645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43655509575627541236897763 65483264363441311855346645)
              ·
                refine ⟨1534764008518155746609687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65483264363441311855346645 1534764008518155746609687)
                ·
                  refine ⟨2302146012777233619914531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534764008518155746609687 2302146012777233619914531)
                  ·
                    refine ⟨3453219019165850429871797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2302146012777233619914531 3453219019165850429871797)
                    ·
                      refine ⟨323739283046798477800481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3453219019165850429871797 323739283046798477800481)
                      ·
                        rfl

theorem cell23_630480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_630480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630480 prefixEnd_630480 := by exact prefixLift 630480
  have htrace : WordTrace (prefixWord ++ tailWord_630480) baseStart_630480 baseEnd_630480 := by
    simpa [prefixWord, tailWord_630480, baseEnd_630480] using wordTrace_append hprefix tailTrace_630480
  have hstable : (prefixWord ++ tailWord_630480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630480).length < 2 ^ (prefixWord ++ tailWord_630480).sum := by decide
  have hdescent : baseEnd_630480 < baseStart_630480 := by decide
  rcases family_descends (prefixWord ++ tailWord_630480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630504 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 2, 4]
def baseStart_630504 : Nat := 118140960795 + 630504 * 2 ^ 59
def prefixEnd_630504 : Nat := 4983230072969 + 3 ^ 40 * 630504 * 2
def baseEnd_630504 : Nat := 107917202194168794633457

theorem tailTrace_630504 : CollatzResearch.WordTrace tailWord_630504 prefixEnd_630504 107917202194168794633457 := by
  unfold tailWord_630504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11498185053899582177673283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15330913405199442903564377 11498185053899582177673283)
  ·
    refine ⟨17247277580849373266509925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11498185053899582177673283 17247277580849373266509925)
    ·
      refine ⟨3233864546409257487470611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17247277580849373266509925 3233864546409257487470611)
      ·
        refine ⟨4850796819613886231205917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233864546409257487470611 4850796819613886231205917)
        ·
          refine ⟨1819048807355207336702219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4850796819613886231205917 1819048807355207336702219)
          ·
            refine ⟨2728573211032811005053329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819048807355207336702219 2728573211032811005053329)
            ·
              refine ⟨2046429908274608253789997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728573211032811005053329 2046429908274608253789997)
              ·
                refine ⟨767411215602978095171249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2046429908274608253789997 767411215602978095171249)
                ·
                  refine ⟨575558411702233571378437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767411215602978095171249 575558411702233571378437)
                  ·
                    refine ⟨107917202194168794633457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575558411702233571378437 107917202194168794633457)
                    ·
                      rfl

theorem cell23_630504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_630504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630504 prefixEnd_630504 := by exact prefixLift 630504
  have htrace : WordTrace (prefixWord ++ tailWord_630504) baseStart_630504 baseEnd_630504 := by
    simpa [prefixWord, tailWord_630504, baseEnd_630504] using wordTrace_append hprefix tailTrace_630504
  have hstable : (prefixWord ++ tailWord_630504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630504).length < 2 ^ (prefixWord ++ tailWord_630504).sum := by decide
  have hdescent : baseEnd_630504 < baseStart_630504 := by decide
  rcases family_descends (prefixWord ++ tailWord_630504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630514 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_630514 : Nat := 118140960795 + 630514 * 2 ^ 59
def prefixEnd_630514 : Nat := 4983230072969 + 3 ^ 40 * 630514 * 2
def baseEnd_630514 : Nat := 323756741389051344775325

theorem tailTrace_630514 : CollatzResearch.WordTrace tailWord_630514 prefixEnd_630514 323756741389051344775325 := by
  unfold tailWord_630514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5749183709440734015802649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15331156558508624042140397 5749183709440734015802649)
  ·
    refine ⟨4311887782080550511851987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5749183709440734015802649 4311887782080550511851987)
    ·
      refine ⟨6467831673120825767777981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311887782080550511851987 6467831673120825767777981)
      ·
        refine ⟨2425436877420309662916743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6467831673120825767777981 2425436877420309662916743)
        ·
          refine ⟨3638155316130464494375115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425436877420309662916743 3638155316130464494375115)
          ·
            refine ⟨5457232974195696741562673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638155316130464494375115 5457232974195696741562673)
            ·
              refine ⟨4092924730646772556172005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457232974195696741562673 4092924730646772556172005)
              ·
                refine ⟨767423386996269854282251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4092924730646772556172005 767423386996269854282251)
                ·
                  refine ⟨1151135080494404781423377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767423386996269854282251 1151135080494404781423377)
                  ·
                    refine ⟨863351310370803586067533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1151135080494404781423377 863351310370803586067533)
                    ·
                      refine ⟨323756741389051344775325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 863351310370803586067533 323756741389051344775325)
                      ·
                        rfl

theorem cell23_630514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_630514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630514 prefixEnd_630514 := by exact prefixLift 630514
  have htrace : WordTrace (prefixWord ++ tailWord_630514) baseStart_630514 baseEnd_630514 := by
    simpa [prefixWord, tailWord_630514, baseEnd_630514] using wordTrace_append hprefix tailTrace_630514
  have hstable : (prefixWord ++ tailWord_630514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630514).length < 2 ^ (prefixWord ++ tailWord_630514).sum := by decide
  have hdescent : baseEnd_630514 < baseStart_630514 := by decide
  rcases family_descends (prefixWord ++ tailWord_630514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630527 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 3]
def baseStart_630527 : Nat := 118140960795 + 630527 * 2 ^ 59
def prefixEnd_630527 : Nat := 4983230072969 + 3 ^ 40 * 630527 * 2
def baseEnd_630527 : Nat := 323763416637559793912765

theorem tailTrace_630527 : CollatzResearch.WordTrace tailWord_630527 prefixEnd_630527 323763416637559793912765 := by
  unfold tailWord_630527
  simp only [CollatzResearch.WordTrace]
  refine ⟨22997208986715839283433835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15331472657810559522289223 22997208986715839283433835)
  ·
    refine ⟨34495813480073758925150753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22997208986715839283433835 34495813480073758925150753)
    ·
      refine ⟨25871860110055319193863065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34495813480073758925150753 25871860110055319193863065)
      ·
        refine ⟨19403895082541489395397299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25871860110055319193863065 19403895082541489395397299)
        ·
          refine ⟨29105842623812234093095949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19403895082541489395397299 29105842623812234093095949)
          ·
            refine ⟨10914690983929587784910981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29105842623812234093095949 10914690983929587784910981)
            ·
              refine ⟨2046504559486797709670809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10914690983929587784910981 2046504559486797709670809)
              ·
                refine ⟨1534878419615098282253107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046504559486797709670809 1534878419615098282253107)
                ·
                  refine ⟨2302317629422647423379661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534878419615098282253107 2302317629422647423379661)
                  ·
                    refine ⟨863369111033492783767373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2302317629422647423379661 863369111033492783767373)
                    ·
                      refine ⟨323763416637559793912765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 863369111033492783767373 323763416637559793912765)
                      ·
                        rfl

theorem cell23_630527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_630527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630527 prefixEnd_630527 := by exact prefixLift 630527
  have htrace : WordTrace (prefixWord ++ tailWord_630527) baseStart_630527 baseEnd_630527 := by
    simpa [prefixWord, tailWord_630527, baseEnd_630527] using wordTrace_append hprefix tailTrace_630527
  have hstable : (prefixWord ++ tailWord_630527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630527).length < 2 ^ (prefixWord ++ tailWord_630527).sum := by decide
  have hdescent : baseEnd_630527 < baseStart_630527 := by decide
  rcases family_descends (prefixWord ++ tailWord_630527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630548 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_630548 : Nat := 118140960795 + 630548 * 2 ^ 59
def prefixEnd_630548 : Nat := 4983230072969 + 3 ^ 40 * 630548 * 2
def baseEnd_630548 : Nat := 323774199731304211750169

theorem tailTrace_630548 : CollatzResearch.WordTrace tailWord_630548 prefixEnd_630548 323774199731304211750169 := by
  unfold tailWord_630548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11498987459819879934974149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15331983279759839913298865 11498987459819879934974149)
  ·
    refine ⟨2156060148716227487807653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11498987459819879934974149 2156060148716227487807653)
    ·
      refine ⟨404261277884292653963935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2156060148716227487807653 404261277884292653963935)
      ·
        refine ⟨606391916826438980945903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404261277884292653963935 606391916826438980945903)
        ·
          refine ⟨909587875239658471418855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606391916826438980945903 909587875239658471418855)
          ·
            refine ⟨1364381812859487707128283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909587875239658471418855 1364381812859487707128283)
            ·
              refine ⟨2046572719289231560692425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364381812859487707128283 2046572719289231560692425)
              ·
                refine ⟨1534929539466923670519319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046572719289231560692425 1534929539466923670519319)
                ·
                  refine ⟨2302394309200385505778979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534929539466923670519319 2302394309200385505778979)
                  ·
                    refine ⟨3453591463800578258668469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2302394309200385505778979 3453591463800578258668469)
                    ·
                      refine ⟨323774199731304211750169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3453591463800578258668469 323774199731304211750169)
                      ·
                        rfl

theorem cell23_630548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_630548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630548 prefixEnd_630548 := by exact prefixLift 630548
  have htrace : WordTrace (prefixWord ++ tailWord_630548) baseStart_630548 baseEnd_630548 := by
    simpa [prefixWord, tailWord_630548, baseEnd_630548] using wordTrace_append hprefix tailTrace_630548
  have hstable : (prefixWord ++ tailWord_630548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630548).length < 2 ^ (prefixWord ++ tailWord_630548).sum := by decide
  have hdescent : baseEnd_630548 < baseStart_630548 := by decide
  rcases family_descends (prefixWord ++ tailWord_630548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630601 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 2, 2, 2]
def baseStart_630601 : Nat := 118140960795 + 630601 * 2 ^ 59
def prefixEnd_630601 : Nat := 4983230072969 + 3 ^ 40 * 630601 * 2
def baseEnd_630601 : Nat := 323801414205992504387425

theorem tailTrace_630601 : CollatzResearch.WordTrace tailWord_630601 prefixEnd_630601 323801414205992504387425 := by
  unfold tailWord_630601
  simp only [CollatzResearch.WordTrace]
  refine ⟨22999907988447749921627657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15333271992298499947751771 22999907988447749921627657)
  ·
    refine ⟨17249930991335812441220743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22999907988447749921627657 17249930991335812441220743)
    ·
      refine ⟨25874896487003718661831115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17249930991335812441220743 25874896487003718661831115)
      ·
        refine ⟨38812344730505577992746673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25874896487003718661831115 38812344730505577992746673)
        ·
          refine ⟨29109258547879183494560005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38812344730505577992746673 29109258547879183494560005)
          ·
            refine ⟨5457985977727346905230001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29109258547879183494560005 5457985977727346905230001)
            ·
              refine ⟨4093489483295510178922501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457985977727346905230001 4093489483295510178922501)
              ·
                refine ⟨767529278117908158547969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4093489483295510178922501 767529278117908158547969)
                ·
                  refine ⟨575646958588431118910977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767529278117908158547969 575646958588431118910977)
                  ·
                    refine ⟨431735218941323339183233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575646958588431118910977 431735218941323339183233)
                    ·
                      refine ⟨323801414205992504387425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431735218941323339183233 323801414205992504387425)
                      ·
                        rfl

theorem cell23_630601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 2, 2].length) (baseStart_630601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630601 prefixEnd_630601 := by exact prefixLift 630601
  have htrace : WordTrace (prefixWord ++ tailWord_630601) baseStart_630601 baseEnd_630601 := by
    simpa [prefixWord, tailWord_630601, baseEnd_630601] using wordTrace_append hprefix tailTrace_630601
  have hstable : (prefixWord ++ tailWord_630601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630601).length < 2 ^ (prefixWord ++ tailWord_630601).sum := by decide
  have hdescent : baseEnd_630601 < baseStart_630601 := by decide
  rcases family_descends (prefixWord ++ tailWord_630601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630617 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 3]
def baseStart_630617 : Nat := 118140960795 + 630617 * 2 ^ 59
def prefixEnd_630617 : Nat := 4983230072969 + 3 ^ 40 * 630617 * 2
def baseEnd_630617 : Nat := 323809629896464441787351

theorem tailTrace_630617 : CollatzResearch.WordTrace tailWord_630617 prefixEnd_630617 323809629896464441787351 := by
  unfold tailWord_630617
  simp only [CollatzResearch.WordTrace]
  refine ⟨23000491556389784654210105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15333661037593189769473403 23000491556389784654210105)
  ·
    refine ⟨17250368667292338490657579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23000491556389784654210105 17250368667292338490657579)
    ·
      refine ⟨25875553000938507735986369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17250368667292338490657579 25875553000938507735986369)
      ·
        refine ⟨19406664750703880801989777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25875553000938507735986369 19406664750703880801989777)
        ·
          refine ⟨14554998563027910601492333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19406664750703880801989777 14554998563027910601492333)
          ·
            refine ⟨5458124461135466475559625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14554998563027910601492333 5458124461135466475559625)
            ·
              refine ⟨4093593345851599856669719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458124461135466475559625 4093593345851599856669719)
              ·
                refine ⟨6140390018777399785004579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093593345851599856669719 6140390018777399785004579)
                ·
                  refine ⟨9210585028166099677506869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140390018777399785004579 9210585028166099677506869)
                  ·
                    refine ⟨863492346390571844766269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9210585028166099677506869 863492346390571844766269)
                    ·
                      refine ⟨323809629896464441787351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 863492346390571844766269 323809629896464441787351)
                      ·
                        rfl

theorem cell23_630617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_630617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630617 prefixEnd_630617 := by exact prefixLift 630617
  have htrace : WordTrace (prefixWord ++ tailWord_630617) baseStart_630617 baseEnd_630617 := by
    simpa [prefixWord, tailWord_630617, baseEnd_630617] using wordTrace_append hprefix tailTrace_630617
  have hstable : (prefixWord ++ tailWord_630617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630617).length < 2 ^ (prefixWord ++ tailWord_630617).sum := by decide
  have hdescent : baseEnd_630617 < baseStart_630617 := by decide
  rcases family_descends (prefixWord ++ tailWord_630617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630637 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_630637 : Nat := 118140960795 + 630637 * 2 ^ 59
def prefixEnd_630637 : Nat := 4983230072969 + 3 ^ 40 * 630637 * 2
def baseEnd_630637 : Nat := 107939966503184787845753

theorem tailTrace_630637 : CollatzResearch.WordTrace tailWord_630637 prefixEnd_630637 107939966503184787845753 := by
  unfold tailWord_630637
  simp only [CollatzResearch.WordTrace]
  refine ⟨23001221016317328069938165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15334147344211552046625443 23001221016317328069938165)
  ·
    refine ⟨2156364470279749506556703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23001221016317328069938165 2156364470279749506556703)
    ·
      refine ⟨3234546705419624259835055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156364470279749506556703 3234546705419624259835055)
      ·
        refine ⟨4851820058129436389752583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234546705419624259835055 4851820058129436389752583)
        ·
          refine ⟨7277730087194154584628875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851820058129436389752583 7277730087194154584628875)
          ·
            refine ⟨10916595130791231876943313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7277730087194154584628875 10916595130791231876943313)
            ·
              refine ⟨8187446348093423907707485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10916595130791231876943313 8187446348093423907707485)
              ·
                refine ⟨3070292380535033965390307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8187446348093423907707485 3070292380535033965390307)
                ·
                  refine ⟨4605438570802550948085461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070292380535033965390307 4605438570802550948085461)
                  ·
                    refine ⟨107939966503184787845753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4605438570802550948085461 107939966503184787845753)
                    ·
                      rfl

theorem cell23_630637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_630637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630637 prefixEnd_630637 := by exact prefixLift 630637
  have htrace : WordTrace (prefixWord ++ tailWord_630637) baseStart_630637 baseEnd_630637 := by
    simpa [prefixWord, tailWord_630637, baseEnd_630637] using wordTrace_append hprefix tailTrace_630637
  have hstable : (prefixWord ++ tailWord_630637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630637).length < 2 ^ (prefixWord ++ tailWord_630637).sum := by decide
  have hdescent : baseEnd_630637 < baseStart_630637 := by decide
  rcases family_descends (prefixWord ++ tailWord_630637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630718 : List Nat := [4, 2, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_630718 : Nat := 118140960795 + 630718 * 2 ^ 59
def prefixEnd_630718 : Nat := 4983230072969 + 3 ^ 40 * 630718 * 2
def baseEnd_630718 : Nat := 107953830480856182208129

theorem tailTrace_630718 : CollatzResearch.WordTrace tailWord_630718 prefixEnd_630718 107953830480856182208129 := by
  unfold tailWord_630718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875521916127984862954601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15336116886015919269091205 2875521916127984862954601)
  ·
    refine ⟨2156641437095988647215951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2875521916127984862954601 2156641437095988647215951)
    ·
      refine ⟨3234962155643982970823927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156641437095988647215951 3234962155643982970823927)
      ·
        refine ⟨4852443233465974456235891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234962155643982970823927 4852443233465974456235891)
        ·
          refine ⟨7278664850198961684353837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4852443233465974456235891 7278664850198961684353837)
          ·
            refine ⟨2729499318824610631632689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7278664850198961684353837 2729499318824610631632689)
            ·
              refine ⟨2047124489118457973724517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729499318824610631632689 2047124489118457973724517)
              ·
                refine ⟨383835841709710870073347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2047124489118457973724517 383835841709710870073347)
                ·
                  refine ⟨575753762564566305110021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383835841709710870073347 575753762564566305110021)
                  ·
                    refine ⟨107953830480856182208129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575753762564566305110021 107953830480856182208129)
                    ·
                      rfl

theorem cell23_630718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_630718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630718 prefixEnd_630718 := by exact prefixLift 630718
  have htrace : WordTrace (prefixWord ++ tailWord_630718) baseStart_630718 baseEnd_630718 := by
    simpa [prefixWord, tailWord_630718, baseEnd_630718] using wordTrace_append hprefix tailTrace_630718
  have hstable : (prefixWord ++ tailWord_630718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630718).length < 2 ^ (prefixWord ++ tailWord_630718).sum := by decide
  have hdescent : baseEnd_630718 < baseStart_630718 := by decide
  rcases family_descends (prefixWord ++ tailWord_630718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630751 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 1, 5, 2]
def baseStart_630751 : Nat := 118140960795 + 630751 * 2 ^ 59
def prefixEnd_630751 : Nat := 4983230072969 + 3 ^ 40 * 630751 * 2
def baseEnd_630751 : Nat := 323878436304166917511735

theorem tailTrace_630751 : CollatzResearch.WordTrace tailWord_630751 prefixEnd_630751 323878436304166917511735 := by
  unfold tailWord_630751
  simp only [CollatzResearch.WordTrace]
  refine ⟨23005378937904325539588107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15336919291936217026392071 23005378937904325539588107)
  ·
    refine ⟨34508068406856488309382161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23005378937904325539588107 34508068406856488309382161)
    ·
      refine ⟨25881051305142366232036621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34508068406856488309382161 25881051305142366232036621)
      ·
        refine ⟨9705394239428387337013733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25881051305142366232036621 9705394239428387337013733)
        ·
          refine ⟨1819761419892822625690075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9705394239428387337013733 1819761419892822625690075)
          ·
            refine ⟨2729642129839233938535113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819761419892822625690075 2729642129839233938535113)
            ·
              refine ⟨2047231597379425453901335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729642129839233938535113 2047231597379425453901335)
              ·
                refine ⟨3070847396069138180852003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047231597379425453901335 3070847396069138180852003)
                ·
                  refine ⟨4606271094103707271278005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070847396069138180852003 4606271094103707271278005)
                  ·
                    refine ⟨431837915072222556682313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4606271094103707271278005 431837915072222556682313)
                    ·
                      refine ⟨323878436304166917511735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431837915072222556682313 323878436304166917511735)
                      ·
                        rfl

theorem cell23_630751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_630751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630751 prefixEnd_630751 := by exact prefixLift 630751
  have htrace : WordTrace (prefixWord ++ tailWord_630751) baseStart_630751 baseEnd_630751 := by
    simpa [prefixWord, tailWord_630751, baseEnd_630751] using wordTrace_append hprefix tailTrace_630751
  have hstable : (prefixWord ++ tailWord_630751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630751).length < 2 ^ (prefixWord ++ tailWord_630751).sum := by decide
  have hdescent : baseEnd_630751 < baseStart_630751 := by decide
  rcases family_descends (prefixWord ++ tailWord_630751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630798 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_630798 : Nat := 118140960795 + 630798 * 2 ^ 59
def prefixEnd_630798 : Nat := 4983230072969 + 3 ^ 40 * 630798 * 2
def baseEnd_630798 : Nat := 323902569894928233624019

theorem tailTrace_630798 : CollatzResearch.WordTrace tailWord_630798 prefixEnd_630798 323902569894928233624019 := by
  unfold tailWord_630798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875886646091756570818631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15338062112489368377699365 2875886646091756570818631)
  ·
    refine ⟨4313829969137634856227947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2875886646091756570818631 4313829969137634856227947)
    ·
      refine ⟨6470744953706452284341921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4313829969137634856227947 6470744953706452284341921)
      ·
        refine ⟨4853058715279839213256441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6470744953706452284341921 4853058715279839213256441)
        ·
          refine ⟨3639794036459879409942331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4853058715279839213256441 3639794036459879409942331)
          ·
            refine ⟨5459691054689819114913497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639794036459879409942331 5459691054689819114913497)
            ·
              refine ⟨4094768291017364336185123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5459691054689819114913497 4094768291017364336185123)
              ·
                refine ⟨6142152436526046504277685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094768291017364336185123 6142152436526046504277685)
                ·
                  refine ⟨575826790924316859776033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6142152436526046504277685 575826790924316859776033)
                  ·
                    refine ⟨431870093193237644832025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575826790924316859776033 431870093193237644832025)
                    ·
                      refine ⟨323902569894928233624019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431870093193237644832025 323902569894928233624019)
                      ·
                        rfl

theorem cell23_630798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_630798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630798 prefixEnd_630798 := by exact prefixLift 630798
  have htrace : WordTrace (prefixWord ++ tailWord_630798) baseStart_630798 baseEnd_630798 := by
    simpa [prefixWord, tailWord_630798, baseEnd_630798] using wordTrace_append hprefix tailTrace_630798
  have hstable : (prefixWord ++ tailWord_630798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630798).length < 2 ^ (prefixWord ++ tailWord_630798).sum := by decide
  have hdescent : baseEnd_630798 < baseStart_630798 := by decide
  rcases family_descends (prefixWord ++ tailWord_630798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630815 : List Nat := [1, 1, 2, 4, 1, 2, 2, 5, 1, 2, 2]
def baseStart_630815 : Nat := 118140960795 + 630815 * 2 ^ 59
def prefixEnd_630815 : Nat := 4983230072969 + 3 ^ 40 * 630815 * 2
def baseEnd_630815 : Nat := 323911299066054667111441

theorem tailTrace_630815 : CollatzResearch.WordTrace tailWord_630815 prefixEnd_630815 323911299066054667111441 := by
  unfold tailWord_630815
  simp only [CollatzResearch.WordTrace]
  refine ⟨23007713209672464469917899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15338475473114976313278599 23007713209672464469917899)
  ·
    refine ⟨34511569814508696704876849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23007713209672464469917899 34511569814508696704876849)
    ·
      refine ⟨25883677360881522528657637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34511569814508696704876849 25883677360881522528657637)
      ·
        refine ⟨4853189505165285474123307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25883677360881522528657637 4853189505165285474123307)
        ·
          refine ⟨7279784257747928211184961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853189505165285474123307 7279784257747928211184961)
          ·
            refine ⟨5459838193310946158388721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7279784257747928211184961 5459838193310946158388721)
            ·
              refine ⟨4094878644983209618791541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5459838193310946158388721 4094878644983209618791541)
              ·
                refine ⟨383894872967175901761707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4094878644983209618791541 383894872967175901761707)
                ·
                  refine ⟨575842309450763852642561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383894872967175901761707 575842309450763852642561)
                  ·
                    refine ⟨431881732088072889481921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575842309450763852642561 431881732088072889481921)
                    ·
                      refine ⟨323911299066054667111441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431881732088072889481921 323911299066054667111441)
                      ·
                        rfl

theorem cell23_630815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_630815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630815 prefixEnd_630815 := by exact prefixLift 630815
  have htrace : WordTrace (prefixWord ++ tailWord_630815) baseStart_630815 baseEnd_630815 := by
    simpa [prefixWord, tailWord_630815, baseEnd_630815] using wordTrace_append hprefix tailTrace_630815
  have hstable : (prefixWord ++ tailWord_630815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630815).length < 2 ^ (prefixWord ++ tailWord_630815).sum := by decide
  have hdescent : baseEnd_630815 < baseStart_630815 := by decide
  rcases family_descends (prefixWord ++ tailWord_630815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630832 : List Nat := [2, 1, 1, 1, 2, 5, 4, 2, 1, 2, 2]
def baseStart_630832 : Nat := 118140960795 + 630832 * 2 ^ 59
def prefixEnd_630832 : Nat := 4983230072969 + 3 ^ 40 * 630832 * 2
def baseEnd_630832 : Nat := 323920028237181100598863

theorem tailTrace_630832 : CollatzResearch.WordTrace tailWord_630832 prefixEnd_630832 323920028237181100598863 := by
  unfold tailWord_630832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504166625305438186643375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15338888833740584248857833 11504166625305438186643375)
  ·
    refine ⟨17256249937958157279965063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11504166625305438186643375 17256249937958157279965063)
    ·
      refine ⟨25884374906937235919947595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17256249937958157279965063 25884374906937235919947595)
      ·
        refine ⟨38826562360405853879921393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25884374906937235919947595 38826562360405853879921393)
        ·
          refine ⟨29119921770304390409941045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38826562360405853879921393 29119921770304390409941045)
          ·
            refine ⟨2729992665966036600931973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29119921770304390409941045 2729992665966036600931973)
            ·
              refine ⟨511873624868631862674745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2729992665966036600931973 511873624868631862674745)
              ·
                refine ⟨383905218651473897006059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511873624868631862674745 383905218651473897006059)
                ·
                  refine ⟨575857827977210845509089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383905218651473897006059 575857827977210845509089)
                  ·
                    refine ⟨431893370982908134131817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575857827977210845509089 431893370982908134131817)
                    ·
                      refine ⟨323920028237181100598863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431893370982908134131817 323920028237181100598863)
                      ·
                        rfl

theorem cell23_630832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 2, 2].length) (baseStart_630832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630832 prefixEnd_630832 := by exact prefixLift 630832
  have htrace : WordTrace (prefixWord ++ tailWord_630832) baseStart_630832 baseEnd_630832 := by
    simpa [prefixWord, tailWord_630832, baseEnd_630832] using wordTrace_append hprefix tailTrace_630832
  have hstable : (prefixWord ++ tailWord_630832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630832).length < 2 ^ (prefixWord ++ tailWord_630832).sum := by decide
  have hdescent : baseEnd_630832 < baseStart_630832 := by decide
  rcases family_descends (prefixWord ++ tailWord_630832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630834 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_630834 : Nat := 118140960795 + 630834 * 2 ^ 59
def prefixEnd_630834 : Nat := 4983230072969 + 3 ^ 40 * 630834 * 2
def baseEnd_630834 : Nat := 107973685066163364257951

theorem tailTrace_630834 : CollatzResearch.WordTrace tailWord_630834 prefixEnd_630834 107973685066163364257951 := by
  unfold tailWord_630834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752101549150907678714889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15338937464402420476573037 5752101549150907678714889)
  ·
    refine ⟨4314076161863180759036167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5752101549150907678714889 4314076161863180759036167)
    ·
      refine ⟨6471114242794771138554251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4314076161863180759036167 6471114242794771138554251)
      ·
        refine ⟨9706671364192156707831377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6471114242794771138554251 9706671364192156707831377)
        ·
          refine ⟨7280003523144117530873533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9706671364192156707831377 7280003523144117530873533)
          ·
            refine ⟨2730001321179044074077575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7280003523144117530873533 2730001321179044074077575)
            ·
              refine ⟨4095001981768566111116363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730001321179044074077575 4095001981768566111116363)
              ·
                refine ⟨6142502972652849166674545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095001981768566111116363 6142502972652849166674545)
                ·
                  refine ⟨4606877229489636875005909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6142502972652849166674545 4606877229489636875005909)
                  ·
                    refine ⟨107973685066163364257951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4606877229489636875005909 107973685066163364257951)
                    ·
                      rfl

theorem cell23_630834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_630834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630834 prefixEnd_630834 := by exact prefixLift 630834
  have htrace : WordTrace (prefixWord ++ tailWord_630834) baseStart_630834 baseEnd_630834 := by
    simpa [prefixWord, tailWord_630834, baseEnd_630834] using wordTrace_append hprefix tailTrace_630834
  have hstable : (prefixWord ++ tailWord_630834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630834).length < 2 ^ (prefixWord ++ tailWord_630834).sum := by decide
  have hdescent : baseEnd_630834 < baseStart_630834 := by decide
  rcases family_descends (prefixWord ++ tailWord_630834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630848 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 2, 1, 3]
def baseStart_630848 : Nat := 118140960795 + 630848 * 2 ^ 59
def prefixEnd_630848 : Nat := 4983230072969 + 3 ^ 40 * 630848 * 2
def baseEnd_630848 : Nat := 323928243927653037998789

theorem tailTrace_630848 : CollatzResearch.WordTrace tailWord_630848 prefixEnd_630848 323928243927653037998789 := by
  unfold tailWord_630848
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504458409276455552934599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15339277879035274070579465 11504458409276455552934599)
  ·
    refine ⟨17256687613914683329401899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11504458409276455552934599 17256687613914683329401899)
    ·
      refine ⟨25885031420872024994102849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17256687613914683329401899 25885031420872024994102849)
      ·
        refine ⟨19413773565654018745577137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25885031420872024994102849 19413773565654018745577137)
        ·
          refine ⟨14560330174240514059182853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19413773565654018745577137 14560330174240514059182853)
          ·
            refine ⟨2730061907670096386096785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14560330174240514059182853 2730061907670096386096785)
            ·
              refine ⟨2047546430752572289572589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2730061907670096386096785 2047546430752572289572589)
              ·
                refine ⟨767829911532214608589721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2047546430752572289572589 767829911532214608589721)
                ·
                  refine ⟨575872433649160956442291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767829911532214608589721 575872433649160956442291)
                  ·
                    refine ⟨863808650473741434663437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 575872433649160956442291 863808650473741434663437)
                    ·
                      refine ⟨323928243927653037998789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 863808650473741434663437 323928243927653037998789)
                      ·
                        rfl

theorem cell23_630848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_630848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630848 prefixEnd_630848 := by exact prefixLift 630848
  have htrace : WordTrace (prefixWord ++ tailWord_630848) baseStart_630848 baseEnd_630848 := by
    simpa [prefixWord, tailWord_630848, baseEnd_630848] using wordTrace_append hprefix tailTrace_630848
  have hstable : (prefixWord ++ tailWord_630848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630848).length < 2 ^ (prefixWord ++ tailWord_630848).sum := by decide
  have hdescent : baseEnd_630848 < baseStart_630848 := by decide
  rcases family_descends (prefixWord ++ tailWord_630848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630858 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_630858 : Nat := 118140960795 + 630858 * 2 ^ 59
def prefixEnd_630858 : Nat := 4983230072969 + 3 ^ 40 * 630858 * 2
def baseEnd_630858 : Nat := 323933378734197998873743

theorem tailTrace_630858 : CollatzResearch.WordTrace tailWord_630858 prefixEnd_630858 323933378734197998873743 := by
  unfold tailWord_630858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752320387129170703433307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15339521032344455209155485 5752320387129170703433307)
  ·
    refine ⟨8628480580693756055149961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5752320387129170703433307 8628480580693756055149961)
    ·
      refine ⟨6471360435520317041362471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8628480580693756055149961 6471360435520317041362471)
      ·
        refine ⟨9707040653280475562043707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6471360435520317041362471 9707040653280475562043707)
        ·
          refine ⟨14560560979920713343065561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9707040653280475562043707 14560560979920713343065561)
          ·
            refine ⟨10920420734940535007299171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14560560979920713343065561 10920420734940535007299171)
            ·
              refine ⟨16380631102410802510948757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10920420734940535007299171 16380631102410802510948757)
              ·
                refine ⟨767842082925506367700723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16380631102410802510948757 767842082925506367700723)
                ·
                  refine ⟨1151763124388259551551085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767842082925506367700723 1151763124388259551551085)
                  ·
                    refine ⟨431911171645597331831657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1151763124388259551551085 431911171645597331831657)
                    ·
                      refine ⟨323933378734197998873743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431911171645597331831657 323933378734197998873743)
                      ·
                        rfl

theorem cell23_630858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_630858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630858 prefixEnd_630858 := by exact prefixLift 630858
  have htrace : WordTrace (prefixWord ++ tailWord_630858) baseStart_630858 baseEnd_630858 := by
    simpa [prefixWord, tailWord_630858, baseEnd_630858] using wordTrace_append hprefix tailTrace_630858
  have hstable : (prefixWord ++ tailWord_630858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630858).length < 2 ^ (prefixWord ++ tailWord_630858).sum := by decide
  have hdescent : baseEnd_630858 < baseStart_630858 := by decide
  rcases family_descends (prefixWord ++ tailWord_630858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630861 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_630861 : Nat := 118140960795 + 630861 * 2 ^ 59
def prefixEnd_630861 : Nat := 4983230072969 + 3 ^ 40 * 630861 * 2
def baseEnd_630861 : Nat := 323934919176161487136229

theorem tailTrace_630861 : CollatzResearch.WordTrace tailWord_630861 prefixEnd_630861 323934919176161487136229 := by
  unfold tailWord_630861
  simp only [CollatzResearch.WordTrace]
  refine ⟨23009390967505814326092437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15339593978337209550728291 23009390967505814326092437)
  ·
    refine ⟨1078565201601835046535583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23009390967505814326092437 1078565201601835046535583)
    ·
      refine ⟨1617847802402752569803375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078565201601835046535583 1617847802402752569803375)
      ·
        refine ⟨2426771703604128854705063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617847802402752569803375 2426771703604128854705063)
        ·
          refine ⟨3640157555406193282057595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426771703604128854705063 3640157555406193282057595)
          ·
            refine ⟨5460236333109289923086393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640157555406193282057595 5460236333109289923086393)
            ·
              refine ⟨4095177249831967442314795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460236333109289923086393 4095177249831967442314795)
              ·
                refine ⟨6142765874747951163472193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095177249831967442314795 6142765874747951163472193)
                ·
                  refine ⟨4607074406060963372604145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6142765874747951163472193 4607074406060963372604145)
                  ·
                    refine ⟨3455305804545722529453109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4607074406060963372604145 3455305804545722529453109)
                    ·
                      refine ⟨323934919176161487136229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3455305804545722529453109 323934919176161487136229)
                      ·
                        rfl

theorem cell23_630861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_630861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630861 prefixEnd_630861 := by exact prefixLift 630861
  have htrace : WordTrace (prefixWord ++ tailWord_630861) baseStart_630861 baseEnd_630861 := by
    simpa [prefixWord, tailWord_630861, baseEnd_630861] using wordTrace_append hprefix tailTrace_630861
  have hstable : (prefixWord ++ tailWord_630861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630861).length < 2 ^ (prefixWord ++ tailWord_630861).sum := by decide
  have hdescent : baseEnd_630861 < baseStart_630861 := by decide
  rcases family_descends (prefixWord ++ tailWord_630861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630874 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_630874 : Nat := 118140960795 + 630874 * 2 ^ 59
def prefixEnd_630874 : Nat := 4983230072969 + 3 ^ 40 * 630874 * 2
def baseEnd_630874 : Nat := 323941594424669936273669

theorem tailTrace_630874 : CollatzResearch.WordTrace tailWord_630874 prefixEnd_630874 323941594424669936273669 := by
  unfold tailWord_630874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5752466279114679386578919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15339910077639145030877117 5752466279114679386578919)
  ·
    refine ⟨8628699418672019079868379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5752466279114679386578919 8628699418672019079868379)
    ·
      refine ⟨12943049128008028619802569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8628699418672019079868379 12943049128008028619802569)
      ·
        refine ⟨9707286846006021464851927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12943049128008028619802569 9707286846006021464851927)
        ·
          refine ⟨14560930269009032197277891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9707286846006021464851927 14560930269009032197277891)
          ·
            refine ⟨21841395403513548295916837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14560930269009032197277891 21841395403513548295916837)
            ·
              refine ⟨4095261638158790305484407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21841395403513548295916837 4095261638158790305484407)
              ·
                refine ⟨6142892457238185458226611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095261638158790305484407 6142892457238185458226611)
                ·
                  refine ⟨9214338685857278187339917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6142892457238185458226611 9214338685857278187339917)
                  ·
                    refine ⟨3455377007196479320252469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9214338685857278187339917 3455377007196479320252469)
                    ·
                      refine ⟨323941594424669936273669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3455377007196479320252469 323941594424669936273669)
                      ·
                        rfl

theorem cell23_630874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_630874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630874 prefixEnd_630874 := by exact prefixLift 630874
  have htrace : WordTrace (prefixWord ++ tailWord_630874) baseStart_630874 baseEnd_630874 := by
    simpa [prefixWord, tailWord_630874, baseEnd_630874] using wordTrace_append hprefix tailTrace_630874
  have hstable : (prefixWord ++ tailWord_630874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630874).length < 2 ^ (prefixWord ++ tailWord_630874).sum := by decide
  have hdescent : baseEnd_630874 < baseStart_630874 := by decide
  rcases family_descends (prefixWord ++ tailWord_630874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630905 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 1, 4, 2]
def baseStart_630905 : Nat := 118140960795 + 630905 * 2 ^ 59
def prefixEnd_630905 : Nat := 4983230072969 + 3 ^ 40 * 630905 * 2
def baseEnd_630905 : Nat := 323957512324959314986027

theorem tailTrace_630905 : CollatzResearch.WordTrace tailWord_630905 prefixEnd_630905 323957512324959314986027 := by
  unfold tailWord_630905
  simp only [CollatzResearch.WordTrace]
  refine ⟨23010995779346409840694169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15340663852897606560462779 23010995779346409840694169)
  ·
    refine ⟨17258246834509807380520627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23010995779346409840694169 17258246834509807380520627)
    ·
      refine ⟨25887370251764711070780941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17258246834509807380520627 25887370251764711070780941)
      ·
        refine ⟨9707763844411766651542853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25887370251764711070780941 9707763844411766651542853)
        ·
          refine ⟨1820205720827206247164285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9707763844411766651542853 1820205720827206247164285)
          ·
            refine ⟨682577145310202342686607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1820205720827206247164285 682577145310202342686607)
            ·
              refine ⟨1023865717965303514029911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682577145310202342686607 1023865717965303514029911)
              ·
                refine ⟨1535798576947955271044867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023865717965303514029911 1535798576947955271044867)
                ·
                  refine ⟨2303697865421932906567301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535798576947955271044867 2303697865421932906567301)
                  ·
                    refine ⟨431943349766612419981369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2303697865421932906567301 431943349766612419981369)
                    ·
                      refine ⟨323957512324959314986027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431943349766612419981369 323957512324959314986027)
                      ·
                        rfl

theorem cell23_630905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_630905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630905 prefixEnd_630905 := by exact prefixLift 630905
  have htrace : WordTrace (prefixWord ++ tailWord_630905) baseStart_630905 baseEnd_630905 := by
    simpa [prefixWord, tailWord_630905, baseEnd_630905] using wordTrace_append hprefix tailTrace_630905
  have hstable : (prefixWord ++ tailWord_630905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630905).length < 2 ^ (prefixWord ++ tailWord_630905).sum := by decide
  have hdescent : baseEnd_630905 < baseStart_630905 := by decide
  rcases family_descends (prefixWord ++ tailWord_630905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630931 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 7, 2]
def baseStart_630931 : Nat := 118140960795 + 630931 * 2 ^ 59
def prefixEnd_630931 : Nat := 4983230072969 + 3 ^ 40 * 630931 * 2
def baseEnd_630931 : Nat := 323970862821976213260907

theorem tailTrace_630931 : CollatzResearch.WordTrace tailWord_630931 prefixEnd_630931 323970862821976213260907 := by
  unfold tailWord_630931
  simp only [CollatzResearch.WordTrace]
  refine ⟨23011944077252216281140647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15341296051501477520760431 23011944077252216281140647)
  ·
    refine ⟨34517916115878324421710971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23011944077252216281140647 34517916115878324421710971)
    ·
      refine ⟨51776874173817486632566457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34517916115878324421710971 51776874173817486632566457)
      ·
        refine ⟨38832655630363114974424843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51776874173817486632566457 38832655630363114974424843)
        ·
          refine ⟨58248983445544672461637265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38832655630363114974424843 58248983445544672461637265)
          ·
            refine ⟨43686737584158504346227949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58248983445544672461637265 43686737584158504346227949)
            ·
              refine ⟨16382526594059439129835481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43686737584158504346227949 16382526594059439129835481)
              ·
                refine ⟨12286894945544579347376611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16382526594059439129835481 12286894945544579347376611)
                ·
                  refine ⟨18430342418316869021064917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12286894945544579347376611 18430342418316869021064917)
                  ·
                    refine ⟨431961150429301617681209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18430342418316869021064917 431961150429301617681209)
                    ·
                      refine ⟨323970862821976213260907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 431961150429301617681209 323970862821976213260907)
                      ·
                        rfl

theorem cell23_630931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7, 2].length) (baseStart_630931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630931 prefixEnd_630931 := by exact prefixLift 630931
  have htrace : WordTrace (prefixWord ++ tailWord_630931) baseStart_630931 baseEnd_630931 := by
    simpa [prefixWord, tailWord_630931, baseEnd_630931] using wordTrace_append hprefix tailTrace_630931
  have hstable : (prefixWord ++ tailWord_630931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630931).length < 2 ^ (prefixWord ++ tailWord_630931).sum := by decide
  have hdescent : baseEnd_630931 < baseStart_630931 := by decide
  rcases family_descends (prefixWord ++ tailWord_630931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630941 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_630941 : Nat := 118140960795 + 630941 * 2 ^ 59
def prefixEnd_630941 : Nat := 4983230072969 + 3 ^ 40 * 630941 * 2
def baseEnd_630941 : Nat := 107991999209507058045287

theorem tailTrace_630941 : CollatzResearch.WordTrace tailWord_630941 prefixEnd_630941 107991999209507058045287 := by
  unfold tailWord_630941
  simp only [CollatzResearch.WordTrace]
  refine ⟨23012308807215987989004677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15341539204810658659336451 23012308807215987989004677)
  ·
    refine ⟨4314807901352997747938377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23012308807215987989004677 4314807901352997747938377)
    ·
      refine ⟨3236105926014748310953783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4314807901352997747938377 3236105926014748310953783)
      ·
        refine ⟨4854158889022122466430675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3236105926014748310953783 4854158889022122466430675)
        ·
          refine ⟨7281238333533183699646013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854158889022122466430675 7281238333533183699646013)
          ·
            refine ⟨2730464375074943887367255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7281238333533183699646013 2730464375074943887367255)
            ·
              refine ⟨4095696562612415831050883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730464375074943887367255 4095696562612415831050883)
              ·
                refine ⟨6143544843918623746576325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095696562612415831050883 6143544843918623746576325)
                ·
                  refine ⟨1151914658234741952483061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6143544843918623746576325 1151914658234741952483061)
                  ·
                    refine ⟨107991999209507058045287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1151914658234741952483061 107991999209507058045287)
                    ·
                      rfl

theorem cell23_630941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_630941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630941 prefixEnd_630941 := by exact prefixLift 630941
  have htrace : WordTrace (prefixWord ++ tailWord_630941) baseStart_630941 baseEnd_630941 := by
    simpa [prefixWord, tailWord_630941, baseEnd_630941] using wordTrace_append hprefix tailTrace_630941
  have hstable : (prefixWord ++ tailWord_630941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630941).length < 2 ^ (prefixWord ++ tailWord_630941).sum := by decide
  have hdescent : baseEnd_630941 < baseStart_630941 := by decide
  rcases family_descends (prefixWord ++ tailWord_630941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630945 : List Nat := [1, 2, 3, 3, 1, 3, 3, 2, 5]
def baseStart_630945 : Nat := 118140960795 + 630945 * 2 ^ 59
def prefixEnd_630945 : Nat := 4983230072969 + 3 ^ 40 * 630945 * 2
def baseEnd_630945 : Nat := 35997561283459906498427

theorem tailTrace_630945 : CollatzResearch.WordTrace tailWord_630945 prefixEnd_630945 35997561283459906498427 := by
  unfold tailWord_630945
  simp only [CollatzResearch.WordTrace]
  refine ⟨23012454699201496672150289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15341636466134331114766859 23012454699201496672150289)
  ·
    refine ⟨17259341024401122504112717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23012454699201496672150289 17259341024401122504112717)
    ·
      refine ⟨6472252884150420939042269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17259341024401122504112717 6472252884150420939042269)
      ·
        refine ⟨2427094831556407852140851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6472252884150420939042269 2427094831556407852140851)
        ·
          refine ⟨3640642247334611778211277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2427094831556407852140851 3640642247334611778211277)
          ·
            refine ⟨1365240842750479416829229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3640642247334611778211277 1365240842750479416829229)
            ·
              refine ⟨511965316031429781310961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1365240842750479416829229 511965316031429781310961)
              ·
                refine ⟨383973987023572335983221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511965316031429781310961 383973987023572335983221)
                ·
                  refine ⟨35997561283459906498427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 383973987023572335983221 35997561283459906498427)
                  ·
                    rfl

theorem cell23_630945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 5].length) (baseStart_630945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630945 prefixEnd_630945 := by exact prefixLift 630945
  have htrace : WordTrace (prefixWord ++ tailWord_630945) baseStart_630945 baseEnd_630945 := by
    simpa [prefixWord, tailWord_630945, baseEnd_630945] using wordTrace_append hprefix tailTrace_630945
  have hstable : (prefixWord ++ tailWord_630945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630945).length < 2 ^ (prefixWord ++ tailWord_630945).sum := by decide
  have hdescent : baseEnd_630945 < baseStart_630945 := by decide
  rcases family_descends (prefixWord ++ tailWord_630945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630971 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 5, 4]
def baseStart_630971 : Nat := 118140960795 + 630971 * 2 ^ 59
def prefixEnd_630971 : Nat := 4983230072969 + 3 ^ 40 * 630971 * 2
def baseEnd_630971 : Nat := 107997134016052018920241

theorem tailTrace_630971 : CollatzResearch.WordTrace tailWord_630971 prefixEnd_630971 107997134016052018920241 := by
  unfold tailWord_630971
  simp only [CollatzResearch.WordTrace]
  refine ⟨23013402997107303112596767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15342268664738202075064511 23013402997107303112596767)
  ·
    refine ⟨34520104495660954668895151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23013402997107303112596767 34520104495660954668895151)
    ·
      refine ⟨51780156743491432003342727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34520104495660954668895151 51780156743491432003342727)
      ·
        refine ⟨77670235115237148005014091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51780156743491432003342727 77670235115237148005014091)
        ·
          refine ⟨116505352672855722007521137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77670235115237148005014091 116505352672855722007521137)
          ·
            refine ⟨87379014504641791505640853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116505352672855722007521137 87379014504641791505640853)
            ·
              refine ⟨4095891304905083976826915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87379014504641791505640853 4095891304905083976826915)
              ·
                refine ⟨6143836957357625965240373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095891304905083976826915 6143836957357625965240373)
                ·
                  refine ⟨575984714752277434241285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6143836957357625965240373 575984714752277434241285)
                  ·
                    refine ⟨107997134016052018920241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 575984714752277434241285 107997134016052018920241)
                    ·
                      rfl

theorem cell23_630971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 4].length) (baseStart_630971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630971 prefixEnd_630971 := by exact prefixLift 630971
  have htrace : WordTrace (prefixWord ++ tailWord_630971) baseStart_630971 baseEnd_630971 := by
    simpa [prefixWord, tailWord_630971, baseEnd_630971] using wordTrace_append hprefix tailTrace_630971
  have hstable : (prefixWord ++ tailWord_630971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630971).length < 2 ^ (prefixWord ++ tailWord_630971).sum := by decide
  have hdescent : baseEnd_630971 < baseStart_630971 := by decide
  rcases family_descends (prefixWord ++ tailWord_630971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630981 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_630981 : Nat := 118140960795 + 630981 * 2 ^ 59
def prefixEnd_630981 : Nat := 4983230072969 + 3 ^ 40 * 630981 * 2
def baseEnd_630981 : Nat := 323996536854701017635677

theorem tailTrace_630981 : CollatzResearch.WordTrace tailWord_630981 prefixEnd_630981 323996536854701017635677 := by
  unfold tailWord_630981
  simp only [CollatzResearch.WordTrace]
  refine ⟨23013767727071074820460797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15342511818047383213640531 23013767727071074820460797)
  ·
    refine ⟨8630162897651653057672799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23013767727071074820460797 8630162897651653057672799)
    ·
      refine ⟨12945244346477479586509199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8630162897651653057672799 12945244346477479586509199)
      ·
        refine ⟨19417866519716219379763799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12945244346477479586509199 19417866519716219379763799)
        ·
          refine ⟨29126799779574329069645699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19417866519716219379763799 29126799779574329069645699)
          ·
            refine ⟨43690199669361493604468549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29126799779574329069645699 43690199669361493604468549)
            ·
              refine ⟨8191912438005280050837853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43690199669361493604468549 8191912438005280050837853)
              ·
                refine ⟨3071967164251980019064195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8191912438005280050837853 3071967164251980019064195)
                ·
                  refine ⟨4607950746377970028596293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071967164251980019064195 4607950746377970028596293)
                  ·
                    refine ⟨863990764945869380361805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607950746377970028596293 863990764945869380361805)
                    ·
                      refine ⟨323996536854701017635677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 863990764945869380361805 323996536854701017635677)
                      ·
                        rfl

theorem cell23_630981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_630981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_630981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_630981 prefixEnd_630981 := by exact prefixLift 630981
  have htrace : WordTrace (prefixWord ++ tailWord_630981) baseStart_630981 baseEnd_630981 := by
    simpa [prefixWord, tailWord_630981, baseEnd_630981] using wordTrace_append hprefix tailTrace_630981
  have hstable : (prefixWord ++ tailWord_630981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630981).length < 2 ^ (prefixWord ++ tailWord_630981).sum := by decide
  have hdescent : baseEnd_630981 < baseStart_630981 := by decide
  rcases family_descends (prefixWord ++ tailWord_630981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631001 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 6]
def baseStart_631001 : Nat := 118140960795 + 631001 * 2 ^ 59
def prefixEnd_631001 : Nat := 4983230072969 + 3 ^ 40 * 631001 * 2
def baseEnd_631001 : Nat := 36000756274198993265065

theorem tailTrace_631001 : CollatzResearch.WordTrace tailWord_631001 prefixEnd_631001 36000756274198993265065 := by
  unfold tailWord_631001
  simp only [CollatzResearch.WordTrace]
  refine ⟨23014497186998618236188857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15342998124665745490792571 23014497186998618236188857)
  ·
    refine ⟨17260872890248963677141643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23014497186998618236188857 17260872890248963677141643)
    ·
      refine ⟨25891309335373445515712465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17260872890248963677141643 25891309335373445515712465)
      ·
        refine ⟨19418482001530084136784349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25891309335373445515712465 19418482001530084136784349)
        ·
          refine ⟨7281930750573781551294131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19418482001530084136784349 7281930750573781551294131)
          ·
            refine ⟨10922896125860672326941197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281930750573781551294131 10922896125860672326941197)
            ·
              refine ⟨4096086047197752122602949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10922896125860672326941197 4096086047197752122602949)
              ·
                refine ⟨768016133849578522988053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4096086047197752122602949 768016133849578522988053)
                ·
                  refine ⟨36000756274198993265065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 768016133849578522988053 36000756274198993265065)
                  ·
                    rfl

theorem cell23_631001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 6].length) (baseStart_631001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631001 prefixEnd_631001 := by exact prefixLift 631001
  have htrace : WordTrace (prefixWord ++ tailWord_631001) baseStart_631001 baseEnd_631001 := by
    simpa [prefixWord, tailWord_631001, baseEnd_631001] using wordTrace_append hprefix tailTrace_631001
  have hstable : (prefixWord ++ tailWord_631001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631001).length < 2 ^ (prefixWord ++ tailWord_631001).sum := by decide
  have hdescent : baseEnd_631001 < baseStart_631001 := by decide
  rcases family_descends (prefixWord ++ tailWord_631001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631061 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_631061 : Nat := 118140960795 + 631061 * 2 ^ 59
def prefixEnd_631061 : Nat := 4983230072969 + 3 ^ 40 * 631061 * 2
def baseEnd_631061 : Nat := 108012538435686901545103

theorem tailTrace_631061 : CollatzResearch.WordTrace tailWord_631061 prefixEnd_631061 108012538435686901545103 := by
  unfold tailWord_631061
  simp only [CollatzResearch.WordTrace]
  refine ⟨23016685566781248483373037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15344457044520832322248691 23016685566781248483373037)
  ·
    refine ⟨8631257087542968181264889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23016685566781248483373037 8631257087542968181264889)
    ·
      refine ⟨6473442815657226135948667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8631257087542968181264889 6473442815657226135948667)
      ·
        refine ⟨9710164223485839203923001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6473442815657226135948667 9710164223485839203923001)
        ·
          refine ⟨7282623167614379402942251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9710164223485839203923001 7282623167614379402942251)
          ·
            refine ⟨10923934751421569104413377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282623167614379402942251 10923934751421569104413377)
            ·
              refine ⟨8192951063566176828310033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10923934751421569104413377 8192951063566176828310033)
              ·
                refine ⟨6144713297674632621232525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8192951063566176828310033 6144713297674632621232525)
                ·
                  refine ⟨2304267486627987232962197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6144713297674632621232525 2304267486627987232962197)
                  ·
                    refine ⟨108012538435686901545103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2304267486627987232962197 108012538435686901545103)
                    ·
                      rfl

theorem cell23_631061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_631061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631061 prefixEnd_631061 := by exact prefixLift 631061
  have htrace : WordTrace (prefixWord ++ tailWord_631061) baseStart_631061 baseEnd_631061 := by
    simpa [prefixWord, tailWord_631061, baseEnd_631061] using wordTrace_append hprefix tailTrace_631061
  have hstable : (prefixWord ++ tailWord_631061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631061).length < 2 ^ (prefixWord ++ tailWord_631061).sum := by decide
  have hdescent : baseEnd_631061 < baseStart_631061 := by decide
  rcases family_descends (prefixWord ++ tailWord_631061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631082 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_631082 : Nat := 118140960795 + 631082 * 2 ^ 59
def prefixEnd_631082 : Nat := 4983230072969 + 3 ^ 40 * 631082 * 2
def baseEnd_631082 : Nat := 108016132800268374157571

theorem tailTrace_631082 : CollatzResearch.WordTrace tailWord_631082 prefixEnd_631082 108016132800268374157571 := by
  unfold tailWord_631082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754362874926292267471875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15344967666470112713258333 5754362874926292267471875)
  ·
    refine ⟨8631544312389438401207813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5754362874926292267471875 8631544312389438401207813)
    ·
      refine ⟨1618414558573019700226465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8631544312389438401207813 1618414558573019700226465)
      ·
        refine ⟨1213810918929764775169849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1618414558573019700226465 1213810918929764775169849)
        ·
          refine ⟨910358189197323581377387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1213810918929764775169849 910358189197323581377387)
          ·
            refine ⟨1365537283795985372066081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910358189197323581377387 1365537283795985372066081)
            ·
              refine ⟨1024152962846989029049561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365537283795985372066081 1024152962846989029049561)
              ·
                refine ⟨768114722135241771787171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024152962846989029049561 768114722135241771787171)
                ·
                  refine ⟨1152172083202862657680757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768114722135241771787171 1152172083202862657680757)
                  ·
                    refine ⟨108016132800268374157571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1152172083202862657680757 108016132800268374157571)
                    ·
                      rfl

theorem cell23_631082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_631082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631082 prefixEnd_631082 := by exact prefixLift 631082
  have htrace : WordTrace (prefixWord ++ tailWord_631082) baseStart_631082 baseEnd_631082 := by
    simpa [prefixWord, tailWord_631082, baseEnd_631082] using wordTrace_append hprefix tailTrace_631082
  have hstable : (prefixWord ++ tailWord_631082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631082).length < 2 ^ (prefixWord ++ tailWord_631082).sum := by decide
  have hdescent : baseEnd_631082 < baseStart_631082 := by decide
  rcases family_descends (prefixWord ++ tailWord_631082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631091 : List Nat := [1, 1, 1, 2, 5, 1, 3, 9]
def baseStart_631091 : Nat := 118140960795 + 631091 * 2 ^ 59
def prefixEnd_631091 : Nat := 4983230072969 + 3 ^ 40 * 631091 * 2
def baseEnd_631091 : Nat := 12001963693581318046673

theorem tailTrace_631091 : CollatzResearch.WordTrace tailWord_631091 prefixEnd_631091 12001963693581318046673 := by
  unfold tailWord_631091
  simp only [CollatzResearch.WordTrace]
  refine ⟨23017779756672563606965127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15345186504448375737976751 23017779756672563606965127)
  ·
    refine ⟨34526669635008845410447691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23017779756672563606965127 34526669635008845410447691)
    ·
      refine ⟨51790004452513268115671537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34526669635008845410447691 51790004452513268115671537)
      ·
        refine ⟨38842503339384951086753653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51790004452513268115671537 38842503339384951086753653)
        ·
          refine ⟨3641484688067339164383155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38842503339384951086753653 3641484688067339164383155)
          ·
            refine ⟨5462227032101008746574733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3641484688067339164383155 5462227032101008746574733)
            ·
              refine ⟨2048335137037878279965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5462227032101008746574733 2048335137037878279965525)
              ·
                refine ⟨12001963693581318046673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2048335137037878279965525 12001963693581318046673)
                ·
                  rfl

theorem cell23_631091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 9].length) (baseStart_631091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631091 prefixEnd_631091 := by exact prefixLift 631091
  have htrace : WordTrace (prefixWord ++ tailWord_631091) baseStart_631091 baseEnd_631091 := by
    simpa [prefixWord, tailWord_631091, baseEnd_631091] using wordTrace_append hprefix tailTrace_631091
  have hstable : (prefixWord ++ tailWord_631091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631091).length < 2 ^ (prefixWord ++ tailWord_631091).sum := by decide
  have hdescent : baseEnd_631091 < baseStart_631091 := by decide
  rcases family_descends (prefixWord ++ tailWord_631091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631118 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_631118 : Nat := 118140960795 + 631118 * 2 ^ 59
def prefixEnd_631118 : Nat := 4983230072969 + 3 ^ 40 * 631118 * 2
def baseEnd_631118 : Nat := 324066883704366981622547

theorem tailTrace_631118 : CollatzResearch.WordTrace tailWord_631118 prefixEnd_631118 324066883704366981622547 := by
  unfold tailWord_631118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877345565946843402274751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15345843018383164812132005 2877345565946843402274751)
  ·
    refine ⟨4316018348920265103412127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877345565946843402274751 4316018348920265103412127)
    ·
      refine ⟨6474027523380397655118191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316018348920265103412127 6474027523380397655118191)
      ·
        refine ⟨9711041285070596482677287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6474027523380397655118191 9711041285070596482677287)
        ·
          refine ⟨14566561927605894724015931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9711041285070596482677287 14566561927605894724015931)
          ·
            refine ⟨21849842891408842086023897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14566561927605894724015931 21849842891408842086023897)
            ·
              refine ⟨16387382168556631564517923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21849842891408842086023897 16387382168556631564517923)
              ·
                refine ⟨24581073252834947346776885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16387382168556631564517923 24581073252834947346776885)
                ·
                  refine ⟨2304475617453276313760333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24581073252834947346776885 2304475617453276313760333)
                  ·
                    refine ⟨864178356544978617660125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304475617453276313760333 864178356544978617660125)
                    ·
                      refine ⟨324066883704366981622547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 864178356544978617660125 324066883704366981622547)
                      ·
                        rfl

theorem cell23_631118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_631118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631118 prefixEnd_631118 := by exact prefixLift 631118
  have htrace : WordTrace (prefixWord ++ tailWord_631118) baseStart_631118 baseEnd_631118 := by
    simpa [prefixWord, tailWord_631118, baseEnd_631118] using wordTrace_append hprefix tailTrace_631118
  have hstable : (prefixWord ++ tailWord_631118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631118).length < 2 ^ (prefixWord ++ tailWord_631118).sum := by decide
  have hdescent : baseEnd_631118 < baseStart_631118 := by decide
  rcases family_descends (prefixWord ++ tailWord_631118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631145 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 3, 3, 2]
def baseStart_631145 : Nat := 118140960795 + 631145 * 2 ^ 59
def prefixEnd_631145 : Nat := 4983230072969 + 3 ^ 40 * 631145 * 2
def baseEnd_631145 : Nat := 324080747682038375984923

theorem tailTrace_631145 : CollatzResearch.WordTrace tailWord_631145 prefixEnd_631145 324080747682038375984923 := by
  unfold tailWord_631145
  simp only [CollatzResearch.WordTrace]
  refine ⟨23019749298476930829430889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15346499532317953886287259 23019749298476930829430889)
  ·
    refine ⟨17264811973857698122073167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23019749298476930829430889 17264811973857698122073167)
    ·
      refine ⟨25897217960786547183109751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17264811973857698122073167 25897217960786547183109751)
      ·
        refine ⟨38845826941179820774664627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25897217960786547183109751 38845826941179820774664627)
        ·
          refine ⟨58268740411769731161996941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38845826941179820774664627 58268740411769731161996941)
          ·
            refine ⟨21850777654413649185748853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58268740411769731161996941 21850777654413649185748853)
            ·
              refine ⟨2048510405101279611163955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21850777654413649185748853 2048510405101279611163955)
              ·
                refine ⟨3072765607651919416745933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048510405101279611163955 3072765607651919416745933)
                ·
                  refine ⟨1152287102869469781279725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3072765607651919416745933 1152287102869469781279725)
                  ·
                    refine ⟨432107663576051167979897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1152287102869469781279725 432107663576051167979897)
                    ·
                      refine ⟨324080747682038375984923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432107663576051167979897 324080747682038375984923)
                      ·
                        rfl

theorem cell23_631145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 3, 2].length) (baseStart_631145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631145 prefixEnd_631145 := by exact prefixLift 631145
  have htrace : WordTrace (prefixWord ++ tailWord_631145) baseStart_631145 baseEnd_631145 := by
    simpa [prefixWord, tailWord_631145, baseEnd_631145] using wordTrace_append hprefix tailTrace_631145
  have hstable : (prefixWord ++ tailWord_631145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631145).length < 2 ^ (prefixWord ++ tailWord_631145).sum := by decide
  have hdescent : baseEnd_631145 < baseStart_631145 := by decide
  rcases family_descends (prefixWord ++ tailWord_631145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631151 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 3, 8]
def baseStart_631151 : Nat := 118140960795 + 631151 * 2 ^ 59
def prefixEnd_631151 : Nat := 4983230072969 + 3 ^ 40 * 631151 * 2
def baseEnd_631151 : Nat := 108027942855321784169965

theorem tailTrace_631151 : CollatzResearch.WordTrace tailWord_631151 prefixEnd_631151 108027942855321784169965 := by
  unfold tailWord_631151
  simp only [CollatzResearch.WordTrace]
  refine ⟨23019968136455193854149307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15346645424303462569432871 23019968136455193854149307)
  ·
    refine ⟨34529952204682790781223961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23019968136455193854149307 34529952204682790781223961)
    ·
      refine ⟨25897464153512093085917971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34529952204682790781223961 25897464153512093085917971)
      ·
        refine ⟨38846196230268139628876957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25897464153512093085917971 38846196230268139628876957)
        ·
          refine ⟨14567323586350552360828859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38846196230268139628876957 14567323586350552360828859)
          ·
            refine ⟨21850985379525828541243289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14567323586350552360828859 21850985379525828541243289)
            ·
              refine ⟨16388239034644371405932467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21850985379525828541243289 16388239034644371405932467)
              ·
                refine ⟨24582358551966557108898701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16388239034644371405932467 24582358551966557108898701)
                ·
                  refine ⟨9218384456987458915837013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24582358551966557108898701 9218384456987458915837013)
                  ·
                    refine ⟨108027942855321784169965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9218384456987458915837013 108027942855321784169965)
                    ·
                      rfl

theorem cell23_631151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_631151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631151 prefixEnd_631151 := by exact prefixLift 631151
  have htrace : WordTrace (prefixWord ++ tailWord_631151) baseStart_631151 baseEnd_631151 := by
    simpa [prefixWord, tailWord_631151, baseEnd_631151] using wordTrace_append hprefix tailTrace_631151
  have hstable : (prefixWord ++ tailWord_631151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631151).length < 2 ^ (prefixWord ++ tailWord_631151).sum := by decide
  have hdescent : baseEnd_631151 < baseStart_631151 := by decide
  rcases family_descends (prefixWord ++ tailWord_631151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631169 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_631169 : Nat := 118140960795 + 631169 * 2 ^ 59
def prefixEnd_631169 : Nat := 4983230072969 + 3 ^ 40 * 631169 * 2
def baseEnd_631169 : Nat := 324093071217746282084813

theorem tailTrace_631169 : CollatzResearch.WordTrace tailWord_631169 prefixEnd_631169 324093071217746282084813 := by
  unfold tailWord_631169
  simp only [CollatzResearch.WordTrace]
  refine ⟨23020624650389982928304561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15347083100259988618869707 23020624650389982928304561)
  ·
    refine ⟨17265468487792487196228421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23020624650389982928304561 17265468487792487196228421)
    ·
      refine ⟨3237275341461091349292829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17265468487792487196228421 3237275341461091349292829)
      ·
        refine ⟨1213978253047909255984811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3237275341461091349292829 1213978253047909255984811)
        ·
          refine ⟨1820967379571863883977217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213978253047909255984811 1820967379571863883977217)
          ·
            refine ⟨1365725534678897912982913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1820967379571863883977217 1365725534678897912982913)
            ·
              refine ⟨1024294151009173434737185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365725534678897912982913 1024294151009173434737185)
              ·
                refine ⟨768220613256880076052889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024294151009173434737185 768220613256880076052889)
                ·
                  refine ⟨576165459942660057039667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 768220613256880076052889 576165459942660057039667)
                  ·
                    refine ⟨864248189913990085559501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 576165459942660057039667 864248189913990085559501)
                    ·
                      refine ⟨324093071217746282084813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 864248189913990085559501 324093071217746282084813)
                      ·
                        rfl

theorem cell23_631169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_631169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631169 prefixEnd_631169 := by exact prefixLift 631169
  have htrace : WordTrace (prefixWord ++ tailWord_631169) baseStart_631169 baseEnd_631169 := by
    simpa [prefixWord, tailWord_631169, baseEnd_631169] using wordTrace_append hprefix tailTrace_631169
  have hstable : (prefixWord ++ tailWord_631169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631169).length < 2 ^ (prefixWord ++ tailWord_631169).sum := by decide
  have hdescent : baseEnd_631169 < baseStart_631169 := by decide
  rcases family_descends (prefixWord ++ tailWord_631169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631175 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_631175 : Nat := 118140960795 + 631175 * 2 ^ 59
def prefixEnd_631175 : Nat := 4983230072969 + 3 ^ 40 * 631175 * 2
def baseEnd_631175 : Nat := 324096152101673258609785

theorem tailTrace_631175 : CollatzResearch.WordTrace tailWord_631175 prefixEnd_631175 324096152101673258609785 := by
  unfold tailWord_631175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23020843488368245953022979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15347228992245497302015319 23020843488368245953022979)
  ·
    refine ⟨34531265232552368929534469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23020843488368245953022979 34531265232552368929534469)
    ·
      refine ⟨6474612231103569174287713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34531265232552368929534469 6474612231103569174287713)
      ·
        refine ⟨4855959173327676880715785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6474612231103569174287713 4855959173327676880715785)
        ·
          refine ⟨3641969379995757660536839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4855959173327676880715785 3641969379995757660536839)
          ·
            refine ⟨5462954069993636490805259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3641969379995757660536839 5462954069993636490805259)
            ·
              refine ⟨8194431104990454736207889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462954069993636490805259 8194431104990454736207889)
              ·
                refine ⟨6145823328742841052155917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8194431104990454736207889 6145823328742841052155917)
                ·
                  refine ⟨2304683748278565394558469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6145823328742841052155917 2304683748278565394558469)
                  ·
                    refine ⟨432128202802231011479713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304683748278565394558469 432128202802231011479713)
                    ·
                      refine ⟨324096152101673258609785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432128202802231011479713 324096152101673258609785)
                      ·
                        rfl

theorem cell23_631175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_631175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631175 prefixEnd_631175 := by exact prefixLift 631175
  have htrace : WordTrace (prefixWord ++ tailWord_631175) baseStart_631175 baseEnd_631175 := by
    simpa [prefixWord, tailWord_631175, baseEnd_631175] using wordTrace_append hprefix tailTrace_631175
  have hstable : (prefixWord ++ tailWord_631175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631175).length < 2 ^ (prefixWord ++ tailWord_631175).sum := by decide
  have hdescent : baseEnd_631175 < baseStart_631175 := by decide
  rcases family_descends (prefixWord ++ tailWord_631175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631192 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 1, 4, 2]
def baseStart_631192 : Nat := 118140960795 + 631192 * 2 ^ 59
def prefixEnd_631192 : Nat := 4983230072969 + 3 ^ 40 * 631192 * 2
def baseEnd_631192 : Nat := 324104881272799692097207

theorem tailTrace_631192 : CollatzResearch.WordTrace tailWord_631192 prefixEnd_631192 324104881272799692097207 := by
  unfold tailWord_631192
  simp only [CollatzResearch.WordTrace]
  refine ⟨11510731764653328928195915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15347642352871105237594553 11510731764653328928195915)
  ·
    refine ⟨17266097646979993392293873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11510731764653328928195915 17266097646979993392293873)
    ·
      refine ⟨12949573235234995044220405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17266097646979993392293873 12949573235234995044220405)
      ·
        refine ⟨1214022490803280785395663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12949573235234995044220405 1214022490803280785395663)
        ·
          refine ⟨1821033736204921178093495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214022490803280785395663 1821033736204921178093495)
          ·
            refine ⟨2731550604307381767140243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821033736204921178093495 2731550604307381767140243)
            ·
              refine ⟨4097325906461072650710365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731550604307381767140243 4097325906461072650710365)
              ·
                refine ⟨1536497214922902244016387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4097325906461072650710365 1536497214922902244016387)
                ·
                  refine ⟨2304745822384353366024581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536497214922902244016387 2304745822384353366024581)
                  ·
                    refine ⟨432139841697066256129609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304745822384353366024581 432139841697066256129609)
                    ·
                      refine ⟨324104881272799692097207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432139841697066256129609 324104881272799692097207)
                      ·
                        rfl

theorem cell23_631192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_631192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631192 prefixEnd_631192 := by exact prefixLift 631192
  have htrace : WordTrace (prefixWord ++ tailWord_631192) baseStart_631192 baseEnd_631192 := by
    simpa [prefixWord, tailWord_631192, baseEnd_631192] using wordTrace_append hprefix tailTrace_631192
  have hstable : (prefixWord ++ tailWord_631192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631192).length < 2 ^ (prefixWord ++ tailWord_631192).sum := by decide
  have hdescent : baseEnd_631192 < baseStart_631192 := by decide
  rcases family_descends (prefixWord ++ tailWord_631192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631213 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_631213 : Nat := 118140960795 + 631213 * 2 ^ 59
def prefixEnd_631213 : Nat := 4983230072969 + 3 ^ 40 * 631213 * 2
def baseEnd_631213 : Nat := 324115664366544109934611

theorem tailTrace_631213 : CollatzResearch.WordTrace tailWord_631213 prefixEnd_631213 324115664366544109934611 := by
  unfold tailWord_631213
  simp only [CollatzResearch.WordTrace]
  refine ⟨23022229462230578442906293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15348152974820385628604195 23022229462230578442906293)
  ·
    refine ⟨2158334012084116729022465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23022229462230578442906293 2158334012084116729022465)
    ·
      refine ⟨1618750509063087546766849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2158334012084116729022465 1618750509063087546766849)
      ·
        refine ⟨1214062881797315660075137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1618750509063087546766849 1214062881797315660075137)
        ·
          refine ⟨910547161347986745056353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1214062881797315660075137 910547161347986745056353)
          ·
            refine ⟨682910371010990058792265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910547161347986745056353 682910371010990058792265)
            ·
              refine ⟨512182778258242544094199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682910371010990058792265 512182778258242544094199)
              ·
                refine ⟨768274167387363816141299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512182778258242544094199 768274167387363816141299)
                ·
                  refine ⟨1152411251081045724211949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768274167387363816141299 1152411251081045724211949)
                  ·
                    refine ⟨432154219155392146579481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1152411251081045724211949 432154219155392146579481)
                    ·
                      refine ⟨324115664366544109934611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432154219155392146579481 324115664366544109934611)
                      ·
                        rfl

theorem cell23_631213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_631213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631213 prefixEnd_631213 := by exact prefixLift 631213
  have htrace : WordTrace (prefixWord ++ tailWord_631213) baseStart_631213 baseEnd_631213 := by
    simpa [prefixWord, tailWord_631213, baseEnd_631213] using wordTrace_append hprefix tailTrace_631213
  have hstable : (prefixWord ++ tailWord_631213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631213).length < 2 ^ (prefixWord ++ tailWord_631213).sum := by decide
  have hdescent : baseEnd_631213 < baseStart_631213 := by decide
  rcases family_descends (prefixWord ++ tailWord_631213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631220 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_631220 : Nat := 118140960795 + 631220 * 2 ^ 59
def prefixEnd_631220 : Nat := 4983230072969 + 3 ^ 40 * 631220 * 2
def baseEnd_631220 : Nat := 324119258731125582547079

theorem tailTrace_631220 : CollatzResearch.WordTrace tailWord_631220 prefixEnd_631220 324119258731125582547079 := by
  unfold tailWord_631220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11511242386602609319205557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15348323182136812425607409 11511242386602609319205557)
  ·
    refine ⟨1079178973743994623675521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11511242386602609319205557 1079178973743994623675521)
    ·
      refine ⟨809384230307995967756641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079178973743994623675521 809384230307995967756641)
      ·
        refine ⟨607038172730996975817481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809384230307995967756641 607038172730996975817481)
        ·
          refine ⟨455278629548247731863111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607038172730996975817481 455278629548247731863111)
          ·
            refine ⟨682917944322371597794667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455278629548247731863111 682917944322371597794667)
            ·
              refine ⟨1024376916483557396692001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682917944322371597794667 1024376916483557396692001)
              ·
                refine ⟨768282687362668047519001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024376916483557396692001 768282687362668047519001)
                ·
                  refine ⟨576212015522001035639251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 768282687362668047519001 576212015522001035639251)
                  ·
                    refine ⟨864318023283001553458877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 576212015522001035639251 864318023283001553458877)
                    ·
                      refine ⟨324119258731125582547079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 864318023283001553458877 324119258731125582547079)
                      ·
                        rfl

theorem cell23_631220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_631220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631220 prefixEnd_631220 := by exact prefixLift 631220
  have htrace : WordTrace (prefixWord ++ tailWord_631220) baseStart_631220 baseEnd_631220 := by
    simpa [prefixWord, tailWord_631220, baseEnd_631220] using wordTrace_append hprefix tailTrace_631220
  have hstable : (prefixWord ++ tailWord_631220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631220).length < 2 ^ (prefixWord ++ tailWord_631220).sum := by decide
  have hdescent : baseEnd_631220 < baseStart_631220 := by decide
  rcases family_descends (prefixWord ++ tailWord_631220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631225 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 3]
def baseStart_631225 : Nat := 118140960795 + 631225 * 2 ^ 59
def prefixEnd_631225 : Nat := 4983230072969 + 3 ^ 40 * 631225 * 2
def baseEnd_631225 : Nat := 324121826134398062984555

theorem tailTrace_631225 : CollatzResearch.WordTrace tailWord_631225 prefixEnd_631225 324121826134398062984555 := by
  unfold tailWord_631225
  simp only [CollatzResearch.WordTrace]
  refine ⟨23022667138187104492343129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15348444758791402994895419 23022667138187104492343129)
  ·
    refine ⟨17267000353640328369257347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23022667138187104492343129 17267000353640328369257347)
    ·
      refine ⟨25900500530460492553886021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17267000353640328369257347 25900500530460492553886021)
      ·
        refine ⟨4856343849461342353853629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25900500530460492553886021 4856343849461342353853629)
        ·
          refine ⟨1821128943548003382695111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4856343849461342353853629 1821128943548003382695111)
          ·
            refine ⟨2731693415322005074042667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821128943548003382695111 2731693415322005074042667)
            ·
              refine ⟨4097540122983007611064001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731693415322005074042667 4097540122983007611064001)
              ·
                refine ⟨3073155092237255708298001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4097540122983007611064001 3073155092237255708298001)
                ·
                  refine ⟨2304866319177941781223501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073155092237255708298001 2304866319177941781223501)
                  ·
                    refine ⟨864324869691728167958813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304866319177941781223501 864324869691728167958813)
                    ·
                      refine ⟨324121826134398062984555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 864324869691728167958813 324121826134398062984555)
                      ·
                        rfl

theorem cell23_631225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_631225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631225 prefixEnd_631225 := by exact prefixLift 631225
  have htrace : WordTrace (prefixWord ++ tailWord_631225) baseStart_631225 baseEnd_631225 := by
    simpa [prefixWord, tailWord_631225, baseEnd_631225] using wordTrace_append hprefix tailTrace_631225
  have hstable : (prefixWord ++ tailWord_631225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631225).length < 2 ^ (prefixWord ++ tailWord_631225).sum := by decide
  have hdescent : baseEnd_631225 < baseStart_631225 := by decide
  rcases family_descends (prefixWord ++ tailWord_631225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631258 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_631258 : Nat := 118140960795 + 631258 * 2 ^ 59
def prefixEnd_631258 : Nat := 4983230072969 + 3 ^ 40 * 631258 * 2
def baseEnd_631258 : Nat := 108046256998665477957301

theorem tailTrace_631258 : CollatzResearch.WordTrace tailWord_631258 prefixEnd_631258 108046256998665477957301 := by
  unfold tailWord_631258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755967686766887782073607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15349247164711700752196285 5755967686766887782073607)
  ·
    refine ⟨8633951530150331673110411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5755967686766887782073607 8633951530150331673110411)
    ·
      refine ⟨12950927295225497509665617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8633951530150331673110411 12950927295225497509665617)
      ·
        refine ⟨9713195471419123132249213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12950927295225497509665617 9713195471419123132249213)
        ·
          refine ⟨3642448301782171174593455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9713195471419123132249213 3642448301782171174593455)
          ·
            refine ⟨5463672452673256761890183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642448301782171174593455 5463672452673256761890183)
            ·
              refine ⟨8195508679009885142835275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463672452673256761890183 8195508679009885142835275)
              ·
                refine ⟨12293263018514827714252913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8195508679009885142835275 12293263018514827714252913)
                ·
                  refine ⟨9219947263886120785689685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12293263018514827714252913 9219947263886120785689685)
                  ·
                    refine ⟨108046256998665477957301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9219947263886120785689685 108046256998665477957301)
                    ·
                      rfl

theorem cell23_631258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_631258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631258 prefixEnd_631258 := by exact prefixLift 631258
  have htrace : WordTrace (prefixWord ++ tailWord_631258) baseStart_631258 baseEnd_631258 := by
    simpa [prefixWord, tailWord_631258, baseEnd_631258] using wordTrace_append hprefix tailTrace_631258
  have hstable : (prefixWord ++ tailWord_631258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631258).length < 2 ^ (prefixWord ++ tailWord_631258).sum := by decide
  have hdescent : baseEnd_631258 < baseStart_631258 := by decide
  rcases family_descends (prefixWord ++ tailWord_631258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631265 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_631265 : Nat := 118140960795 + 631265 * 2 ^ 59
def prefixEnd_631265 : Nat := 4983230072969 + 3 ^ 40 * 631265 * 2
def baseEnd_631265 : Nat := 324142365360577906484371

theorem tailTrace_631265 : CollatzResearch.WordTrace tailWord_631265 prefixEnd_631265 324142365360577906484371 := by
  unfold tailWord_631265
  simp only [CollatzResearch.WordTrace]
  refine ⟨23024126058042191323799249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15349417372028127549199499 23024126058042191323799249)
  ·
    refine ⟨17268094543531643492849437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23024126058042191323799249 17268094543531643492849437)
    ·
      refine ⟨6475535453824366309818539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17268094543531643492849437 6475535453824366309818539)
      ·
        refine ⟨9713303180736549464727809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475535453824366309818539 9713303180736549464727809)
        ·
          refine ⟨7284977385552412098545857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713303180736549464727809 7284977385552412098545857)
          ·
            refine ⟨5463733039164309073909393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7284977385552412098545857 5463733039164309073909393)
            ·
              refine ⟨4097799779373231805432045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5463733039164309073909393 4097799779373231805432045)
              ·
                refine ⟨1536674917264961927037017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4097799779373231805432045 1536674917264961927037017)
                ·
                  refine ⟨1152506187948721445277763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1536674917264961927037017 1152506187948721445277763)
                  ·
                    refine ⟨1728759281923082167916645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1152506187948721445277763 1728759281923082167916645)
                    ·
                      refine ⟨324142365360577906484371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1728759281923082167916645 324142365360577906484371)
                      ·
                        rfl

theorem cell23_631265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_631265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631265 prefixEnd_631265 := by exact prefixLift 631265
  have htrace : WordTrace (prefixWord ++ tailWord_631265) baseStart_631265 baseEnd_631265 := by
    simpa [prefixWord, tailWord_631265, baseEnd_631265] using wordTrace_append hprefix tailTrace_631265
  have hstable : (prefixWord ++ tailWord_631265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631265).length < 2 ^ (prefixWord ++ tailWord_631265).sum := by decide
  have hdescent : baseEnd_631265 < baseStart_631265 := by decide
  rcases family_descends (prefixWord ++ tailWord_631265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631268 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_631268 : Nat := 118140960795 + 631268 * 2 ^ 59
def prefixEnd_631268 : Nat := 4983230072969 + 3 ^ 40 * 631268 * 2
def baseEnd_631268 : Nat := 324143905802541394746857

theorem tailTrace_631268 : CollatzResearch.WordTrace tailWord_631268 prefixEnd_631268 324143905802541394746857 := by
  unfold tailWord_631268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11512117738515661418079229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15349490318020881890772305 11512117738515661418079229)
  ·
    refine ⟨4317044151943373031779711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11512117738515661418079229 4317044151943373031779711)
    ·
      refine ⟨6475566227915059547669567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4317044151943373031779711 6475566227915059547669567)
      ·
        refine ⟨9713349341872589321504351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475566227915059547669567 9713349341872589321504351)
        ·
          refine ⟨14570024012808883982256527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9713349341872589321504351 14570024012808883982256527)
          ·
            refine ⟨21855036019213325973384791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14570024012808883982256527 21855036019213325973384791)
            ·
              refine ⟨32782554028819988960077187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21855036019213325973384791 32782554028819988960077187)
              ·
                refine ⟨49173831043229983440115781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32782554028819988960077187 49173831043229983440115781)
                ·
                  refine ⟨9220093320605621895021709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49173831043229983440115781 9220093320605621895021709)
                  ·
                    refine ⟨3457534995227108210633141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9220093320605621895021709 3457534995227108210633141)
                    ·
                      refine ⟨324143905802541394746857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3457534995227108210633141 324143905802541394746857)
                      ·
                        rfl

theorem cell23_631268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_631268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631268 prefixEnd_631268 := by exact prefixLift 631268
  have htrace : WordTrace (prefixWord ++ tailWord_631268) baseStart_631268 baseEnd_631268 := by
    simpa [prefixWord, tailWord_631268, baseEnd_631268] using wordTrace_append hprefix tailTrace_631268
  have hstable : (prefixWord ++ tailWord_631268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631268).length < 2 ^ (prefixWord ++ tailWord_631268).sum := by decide
  have hdescent : baseEnd_631268 < baseStart_631268 := by decide
  rcases family_descends (prefixWord ++ tailWord_631268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631288 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 8]
def baseStart_631288 : Nat := 118140960795 + 631288 * 2 ^ 59
def prefixEnd_631288 : Nat := 4983230072969 + 3 ^ 40 * 631288 * 2
def baseEnd_631288 : Nat := 36017130601736812944085

theorem tailTrace_631288 : CollatzResearch.WordTrace tailWord_631288 prefixEnd_631288 36017130601736812944085 := by
  unfold tailWord_631288
  simp only [CollatzResearch.WordTrace]
  refine ⟨11512482468479433125943259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15349976624639244167924345 11512482468479433125943259)
  ·
    refine ⟨17268723702719149688914889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11512482468479433125943259 17268723702719149688914889)
    ·
      refine ⟨12951542777039362266686167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17268723702719149688914889 12951542777039362266686167)
      ·
        refine ⟨19427314165559043400029251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12951542777039362266686167 19427314165559043400029251)
        ·
          refine ⟨29140971248338565100043877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19427314165559043400029251 29140971248338565100043877)
          ·
            refine ⟨5463932109063480956258227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29140971248338565100043877 5463932109063480956258227)
            ·
              refine ⟨8195898163595221434387341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463932109063480956258227 8195898163595221434387341)
              ·
                refine ⟨3073461811348208037895253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8195898163595221434387341 3073461811348208037895253)
                ·
                  refine ⟨36017130601736812944085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3073461811348208037895253 36017130601736812944085)
                  ·
                    rfl

theorem cell23_631288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 8].length) (baseStart_631288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631288 prefixEnd_631288 := by exact prefixLift 631288
  have htrace : WordTrace (prefixWord ++ tailWord_631288) baseStart_631288 baseEnd_631288 := by
    simpa [prefixWord, tailWord_631288, baseEnd_631288] using wordTrace_append hprefix tailTrace_631288
  have hstable : (prefixWord ++ tailWord_631288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631288).length < 2 ^ (prefixWord ++ tailWord_631288).sum := by decide
  have hdescent : baseEnd_631288 < baseStart_631288 := by decide
  rcases family_descends (prefixWord ++ tailWord_631288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631365 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_631365 : Nat := 118140960795 + 631365 * 2 ^ 59
def prefixEnd_631365 : Nat := 4983230072969 + 3 ^ 40 * 631365 * 2
def baseEnd_631365 : Nat := 108064571142009171744637

theorem tailTrace_631365 : CollatzResearch.WordTrace tailWord_631365 prefixEnd_631365 108064571142009171744637 := by
  unfold tailWord_631365
  simp only [CollatzResearch.WordTrace]
  refine ⟨23027773357679908402439549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15351848905119938934959699 23027773357679908402439549)
  ·
    refine ⟨8635415009129965650914831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23027773357679908402439549 8635415009129965650914831)
    ·
      refine ⟨12953122513694948476372247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8635415009129965650914831 12953122513694948476372247)
      ·
        refine ⟨19429683770542422714558371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12953122513694948476372247 19429683770542422714558371)
        ·
          refine ⟨29144525655813634071837557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19429683770542422714558371 29144525655813634071837557)
          ·
            refine ⟨2732299280232528194234771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29144525655813634071837557 2732299280232528194234771)
            ·
              refine ⟨4098448920348792291352157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732299280232528194234771 4098448920348792291352157)
              ·
                refine ⟨1536918345130797109257059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4098448920348792291352157 1536918345130797109257059)
                ·
                  refine ⟨2305377517696195663885589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536918345130797109257059 2305377517696195663885589)
                  ·
                    refine ⟨108064571142009171744637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2305377517696195663885589 108064571142009171744637)
                    ·
                      rfl

theorem cell23_631365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_631365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631365 prefixEnd_631365 := by exact prefixLift 631365
  have htrace : WordTrace (prefixWord ++ tailWord_631365) baseStart_631365 baseEnd_631365 := by
    simpa [prefixWord, tailWord_631365, baseEnd_631365] using wordTrace_append hprefix tailTrace_631365
  have hstable : (prefixWord ++ tailWord_631365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631365).length < 2 ^ (prefixWord ++ tailWord_631365).sum := by decide
  have hdescent : baseEnd_631365 < baseStart_631365 := by decide
  rcases family_descends (prefixWord ++ tailWord_631365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631366 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_631366 : Nat := 118140960795 + 631366 * 2 ^ 59
def prefixEnd_631366 : Nat := 4983230072969 + 3 ^ 40 * 631366 * 2
def baseEnd_631366 : Nat := 324194226906682011321407

theorem tailTrace_631366 : CollatzResearch.WordTrace tailWord_631366 prefixEnd_631366 324194226906682011321407 := by
  unfold tailWord_631366
  simp only [CollatzResearch.WordTrace]
  refine ⟨719619057208633924163311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15351873220450857048817301 719619057208633924163311)
  ·
    refine ⟨1079428585812950886244967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 719619057208633924163311 1079428585812950886244967)
    ·
      refine ⟨1619142878719426329367451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079428585812950886244967 1619142878719426329367451)
      ·
        refine ⟨2428714318079139494051177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619142878719426329367451 2428714318079139494051177)
        ·
          refine ⟨1821535738559354620538383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2428714318079139494051177 1821535738559354620538383)
          ·
            refine ⟨2732303607839031930807575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821535738559354620538383 2732303607839031930807575)
            ·
              refine ⟨4098455411758547896211363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732303607839031930807575 4098455411758547896211363)
              ·
                refine ⟨6147683117637821844317045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098455411758547896211363 6147683117637821844317045)
                ·
                  refine ⟨576345292278545797904723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6147683117637821844317045 576345292278545797904723)
                  ·
                    refine ⟨864517938417818696857085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 576345292278545797904723 864517938417818696857085)
                    ·
                      refine ⟨324194226906682011321407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 864517938417818696857085 324194226906682011321407)
                      ·
                        rfl

theorem cell23_631366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_631366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631366 prefixEnd_631366 := by exact prefixLift 631366
  have htrace : WordTrace (prefixWord ++ tailWord_631366) baseStart_631366 baseEnd_631366 := by
    simpa [prefixWord, tailWord_631366, baseEnd_631366] using wordTrace_append hprefix tailTrace_631366
  have hstable : (prefixWord ++ tailWord_631366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631366).length < 2 ^ (prefixWord ++ tailWord_631366).sum := by decide
  have hdescent : baseEnd_631366 < baseStart_631366 := by decide
  rcases family_descends (prefixWord ++ tailWord_631366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631372 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_631372 : Nat := 118140960795 + 631372 * 2 ^ 59
def prefixEnd_631372 : Nat := 4983230072969 + 3 ^ 40 * 631372 * 2
def baseEnd_631372 : Nat := 324197307790608987846379

theorem tailTrace_631372 : CollatzResearch.WordTrace tailWord_631372 prefixEnd_631372 324197307790608987846379 := by
  unfold tailWord_631372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11514014334327274298972185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15352019112436365731962913 11514014334327274298972185)
  ·
    refine ⟨8635510750745455724229139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11514014334327274298972185 8635510750745455724229139)
    ·
      refine ⟨12953266126118183586343709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8635510750745455724229139 12953266126118183586343709)
      ·
        refine ⟨4857474797294318844878891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12953266126118183586343709 4857474797294318844878891)
        ·
          refine ⟨7286212195941478267318337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4857474797294318844878891 7286212195941478267318337)
          ·
            refine ⟨5464659146956108700488753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7286212195941478267318337 5464659146956108700488753)
            ·
              refine ⟨4098494360217081525366565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464659146956108700488753 4098494360217081525366565)
              ·
                refine ⟨768467692540702786006231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4098494360217081525366565 768467692540702786006231)
                ·
                  refine ⟨1152701538811054179009347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768467692540702786006231 1152701538811054179009347)
                  ·
                    refine ⟨1729052308216581268514021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1152701538811054179009347 1729052308216581268514021)
                    ·
                      refine ⟨324197307790608987846379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1729052308216581268514021 324197307790608987846379)
                      ·
                        rfl

theorem cell23_631372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_631372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631372 prefixEnd_631372 := by exact prefixLift 631372
  have htrace : WordTrace (prefixWord ++ tailWord_631372) baseStart_631372 baseEnd_631372 := by
    simpa [prefixWord, tailWord_631372, baseEnd_631372] using wordTrace_append hprefix tailTrace_631372
  have hstable : (prefixWord ++ tailWord_631372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631372).length < 2 ^ (prefixWord ++ tailWord_631372).sum := by decide
  have hdescent : baseEnd_631372 < baseStart_631372 := by decide
  rcases family_descends (prefixWord ++ tailWord_631372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631390 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_631390 : Nat := 118140960795 + 631390 * 2 ^ 59
def prefixEnd_631390 : Nat := 4983230072969 + 3 ^ 40 * 631390 * 2
def baseEnd_631390 : Nat := 36022950049154435269033

theorem tailTrace_631390 : CollatzResearch.WordTrace tailWord_631390 prefixEnd_631390 36022950049154435269033 := by
  unfold tailWord_631390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878585647823667209012453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15352456788392891781399749 2878585647823667209012453)
  ·
    refine ⟨539734808966937601689835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2878585647823667209012453 539734808966937601689835)
    ·
      refine ⟨809602213450406402534753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539734808966937601689835 809602213450406402534753)
      ·
        refine ⟨607201660087804801901065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809602213450406402534753 607201660087804801901065)
        ·
          refine ⟨455401245065853601425799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607201660087804801901065 455401245065853601425799)
          ·
            refine ⟨683101867598780402138699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455401245065853601425799 683101867598780402138699)
            ·
              refine ⟨1024652801398170603208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683101867598780402138699 1024652801398170603208049)
              ·
                refine ⟨768489601048627952406037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024652801398170603208049 768489601048627952406037)
                ·
                  refine ⟨36022950049154435269033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 768489601048627952406037 36022950049154435269033)
                  ·
                    rfl

theorem cell23_631390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_631390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631390 prefixEnd_631390 := by exact prefixLift 631390
  have htrace : WordTrace (prefixWord ++ tailWord_631390) baseStart_631390 baseEnd_631390 := by
    simpa [prefixWord, tailWord_631390, baseEnd_631390] using wordTrace_append hprefix tailTrace_631390
  have hstable : (prefixWord ++ tailWord_631390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631390).length < 2 ^ (prefixWord ++ tailWord_631390).sum := by decide
  have hdescent : baseEnd_631390 < baseStart_631390 := by decide
  rcases family_descends (prefixWord ++ tailWord_631390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631406 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_631406 : Nat := 118140960795 + 631406 * 2 ^ 59
def prefixEnd_631406 : Nat := 4983230072969 + 3 ^ 40 * 631406 * 2
def baseEnd_631406 : Nat := 324214766132861854821223

theorem tailTrace_631406 : CollatzResearch.WordTrace tailWord_631406 prefixEnd_631406 324214766132861854821223 := by
  unfold tailWord_631406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878658593816421550585259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15352845833687581603121381 2878658593816421550585259)
  ·
    refine ⟨4317987890724632325877889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2878658593816421550585259 4317987890724632325877889)
    ·
      refine ⟨3238490918043474244408417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4317987890724632325877889 3238490918043474244408417)
      ·
        refine ⟨2428868188532605683306313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3238490918043474244408417 2428868188532605683306313)
        ·
          refine ⟨1821651141399454262479735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2428868188532605683306313 1821651141399454262479735)
          ·
            refine ⟨2732476712099181393719603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821651141399454262479735 2732476712099181393719603)
            ·
              refine ⟨4098715068148772090579405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732476712099181393719603 4098715068148772090579405)
              ·
                refine ⟨1537018150555789533967277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4098715068148772090579405 1537018150555789533967277)
                ·
                  refine ⟨576381806458421075237729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1537018150555789533967277 576381806458421075237729)
                  ·
                    refine ⟨432286354843815806428297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 576381806458421075237729 432286354843815806428297)
                    ·
                      refine ⟨324214766132861854821223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432286354843815806428297 324214766132861854821223)
                      ·
                        rfl

theorem cell23_631406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_631406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631406 prefixEnd_631406 := by exact prefixLift 631406
  have htrace : WordTrace (prefixWord ++ tailWord_631406) baseStart_631406 baseEnd_631406 := by
    simpa [prefixWord, tailWord_631406, baseEnd_631406] using wordTrace_append hprefix tailTrace_631406
  have hstable : (prefixWord ++ tailWord_631406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631406).length < 2 ^ (prefixWord ++ tailWord_631406).sum := by decide
  have hdescent : baseEnd_631406 < baseStart_631406 := by decide
  rcases family_descends (prefixWord ++ tailWord_631406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631445 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_631445 : Nat := 118140960795 + 631445 * 2 ^ 59
def prefixEnd_631445 : Nat := 4983230072969 + 3 ^ 40 * 631445 * 2
def baseEnd_631445 : Nat := 324234791878387202233543

theorem tailTrace_631445 : CollatzResearch.WordTrace tailWord_631445 prefixEnd_631445 324234791878387202233543 := by
  unfold tailWord_631445
  simp only [CollatzResearch.WordTrace]
  refine ⟨23030691197390082065351789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15353794131593388043567859 23030691197390082065351789)
  ·
    refine ⟨8636509199021280774506921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23030691197390082065351789 8636509199021280774506921)
    ·
      refine ⟨6477381899265960580880191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8636509199021280774506921 6477381899265960580880191)
      ·
        refine ⟨9716072848898940871320287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477381899265960580880191 9716072848898940871320287)
        ·
          refine ⟨14574109273348411306980431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716072848898940871320287 14574109273348411306980431)
          ·
            refine ⟨21861163910022616960470647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14574109273348411306980431 21861163910022616960470647)
            ·
              refine ⟨32791745865033925440705971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21861163910022616960470647 32791745865033925440705971)
              ·
                refine ⟨49187618797550888161058957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32791745865033925440705971 49187618797550888161058957)
                ·
                  refine ⟨18445357049081583060397109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49187618797550888161058957 18445357049081583060397109)
                  ·
                    refine ⟨1729252223351398411912229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18445357049081583060397109 1729252223351398411912229)
                    ·
                      refine ⟨324234791878387202233543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1729252223351398411912229 324234791878387202233543)
                      ·
                        rfl

theorem cell23_631445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_631445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631445 prefixEnd_631445 := by exact prefixLift 631445
  have htrace : WordTrace (prefixWord ++ tailWord_631445) baseStart_631445 baseEnd_631445 := by
    simpa [prefixWord, tailWord_631445, baseEnd_631445] using wordTrace_append hprefix tailTrace_631445
  have hstable : (prefixWord ++ tailWord_631445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631445).length < 2 ^ (prefixWord ++ tailWord_631445).sum := by decide
  have hdescent : baseEnd_631445 < baseStart_631445 := by decide
  rcases family_descends (prefixWord ++ tailWord_631445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631449 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 1, 3, 2]
def baseStart_631449 : Nat := 118140960795 + 631449 * 2 ^ 59
def prefixEnd_631449 : Nat := 4983230072969 + 3 ^ 40 * 631449 * 2
def baseEnd_631449 : Nat := 324236845801005186583525

theorem tailTrace_631449 : CollatzResearch.WordTrace tailWord_631449 prefixEnd_631449 324236845801005186583525 := by
  unfold tailWord_631449
  simp only [CollatzResearch.WordTrace]
  refine ⟨23030837089375590748497401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15353891392917060498998267 23030837089375590748497401)
  ·
    refine ⟨17273127817031693061373051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23030837089375590748497401 17273127817031693061373051)
    ·
      refine ⟨25909691725547539592059577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17273127817031693061373051 25909691725547539592059577)
      ·
        refine ⟨19432268794160654694044683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25909691725547539592059577 19432268794160654694044683)
        ·
          refine ⟨29148403191240982041067025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19432268794160654694044683 29148403191240982041067025)
          ·
            refine ⟨21861302393430736530800269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29148403191240982041067025 21861302393430736530800269)
            ·
              refine ⟨8197988397536526199050101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21861302393430736530800269 8197988397536526199050101)
              ·
                refine ⟨768561412269049331160947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8197988397536526199050101 768561412269049331160947)
                ·
                  refine ⟨1152842118403573996741421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768561412269049331160947 1152842118403573996741421)
                  ·
                    refine ⟨432315794401340248778033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1152842118403573996741421 432315794401340248778033)
                    ·
                      refine ⟨324236845801005186583525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432315794401340248778033 324236845801005186583525)
                      ·
                        rfl

theorem cell23_631449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_631449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631449 prefixEnd_631449 := by exact prefixLift 631449
  have htrace : WordTrace (prefixWord ++ tailWord_631449) baseStart_631449 baseEnd_631449 := by
    simpa [prefixWord, tailWord_631449, baseEnd_631449] using wordTrace_append hprefix tailTrace_631449
  have hstable : (prefixWord ++ tailWord_631449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631449).length < 2 ^ (prefixWord ++ tailWord_631449).sum := by decide
  have hdescent : baseEnd_631449 < baseStart_631449 := by decide
  rcases family_descends (prefixWord ++ tailWord_631449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631465 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_631465 : Nat := 118140960795 + 631465 * 2 ^ 59
def prefixEnd_631465 : Nat := 4983230072969 + 3 ^ 40 * 631465 * 2
def baseEnd_631465 : Nat := 324245061491477123983451

theorem tailTrace_631465 : CollatzResearch.WordTrace tailWord_631465 prefixEnd_631465 324245061491477123983451 := by
  unfold tailWord_631465
  simp only [CollatzResearch.WordTrace]
  refine ⟨23031420657317625481079849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15354280438211750320719899 23031420657317625481079849)
  ·
    refine ⟨17273565492988219110809887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23031420657317625481079849 17273565492988219110809887)
    ·
      refine ⟨25910348239482328666214831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17273565492988219110809887 25910348239482328666214831)
      ·
        refine ⟨38865522359223492999322247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25910348239482328666214831 38865522359223492999322247)
        ·
          refine ⟨58298283538835239498983371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38865522359223492999322247 58298283538835239498983371)
          ·
            refine ⟨87447425308252859248475057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58298283538835239498983371 87447425308252859248475057)
            ·
              refine ⟨65585568981189644436356293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87447425308252859248475057 65585568981189644436356293)
              ·
                refine ⟨12297294183973058331816805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65585568981189644436356293 12297294183973058331816805)
                ·
                  refine ⟨2305742659494948437215651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12297294183973058331816805 2305742659494948437215651)
                  ·
                    refine ⟨3458613989242422655823477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305742659494948437215651 3458613989242422655823477)
                    ·
                      refine ⟨324245061491477123983451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3458613989242422655823477 324245061491477123983451)
                      ·
                        rfl

theorem cell23_631465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_631465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631465 prefixEnd_631465 := by exact prefixLift 631465
  have htrace : WordTrace (prefixWord ++ tailWord_631465) baseStart_631465 baseEnd_631465 := by
    simpa [prefixWord, tailWord_631465, baseEnd_631465] using wordTrace_append hprefix tailTrace_631465
  have hstable : (prefixWord ++ tailWord_631465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631465).length < 2 ^ (prefixWord ++ tailWord_631465).sum := by decide
  have hdescent : baseEnd_631465 < baseStart_631465 := by decide
  rcases family_descends (prefixWord ++ tailWord_631465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631473 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_631473 : Nat := 118140960795 + 631473 * 2 ^ 59
def prefixEnd_631473 : Nat := 4983230072969 + 3 ^ 40 * 631473 * 2
def baseEnd_631473 : Nat := 324249169336713092683415

theorem tailTrace_631473 : CollatzResearch.WordTrace tailWord_631473 prefixEnd_631473 324249169336713092683415 := by
  unfold tailWord_631473
  simp only [CollatzResearch.WordTrace]
  refine ⟨23031712441288642847371073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15354474960859095231580715 23031712441288642847371073)
  ·
    refine ⟨17273784330966482135528305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23031712441288642847371073 17273784330966482135528305)
    ·
      refine ⟨12955338248224861601646229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17273784330966482135528305 12955338248224861601646229)
      ·
        refine ⟨607281480385540387577167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12955338248224861601646229 607281480385540387577167)
        ·
          refine ⟨910922220578310581365751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607281480385540387577167 910922220578310581365751)
          ·
            refine ⟨1366383330867465872048627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910922220578310581365751 1366383330867465872048627)
            ·
              refine ⟨2049574996301198808072941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366383330867465872048627 2049574996301198808072941)
              ·
                refine ⟨768590623612949553027353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2049574996301198808072941 768590623612949553027353)
                ·
                  refine ⟨576442967709712164770515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 768590623612949553027353 576442967709712164770515)
                  ·
                    refine ⟨864664451564568247155773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 576442967709712164770515 864664451564568247155773)
                    ·
                      refine ⟨324249169336713092683415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 864664451564568247155773 324249169336713092683415)
                      ·
                        rfl

theorem cell23_631473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_631473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631473 prefixEnd_631473 := by exact prefixLift 631473
  have htrace : WordTrace (prefixWord ++ tailWord_631473) baseStart_631473 baseEnd_631473 := by
    simpa [prefixWord, tailWord_631473, baseEnd_631473] using wordTrace_append hprefix tailTrace_631473
  have hstable : (prefixWord ++ tailWord_631473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631473).length < 2 ^ (prefixWord ++ tailWord_631473).sum := by decide
  have hdescent : baseEnd_631473 < baseStart_631473 := by decide
  rcases family_descends (prefixWord ++ tailWord_631473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631495 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_631495 : Nat := 118140960795 + 631495 * 2 ^ 59
def prefixEnd_631495 : Nat := 4983230072969 + 3 ^ 40 * 631495 * 2
def baseEnd_631495 : Nat := 324260465911112006608313

theorem tailTrace_631495 : CollatzResearch.WordTrace tailWord_631495 prefixEnd_631495 324260465911112006608313 := by
  unfold tailWord_631495
  simp only [CollatzResearch.WordTrace]
  refine ⟨23032514847208940604671939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15355009898139293736447959 23032514847208940604671939)
  ·
    refine ⟨34548772270813410907007909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23032514847208940604671939 34548772270813410907007909)
    ·
      refine ⟨6477894800777514545063983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34548772270813410907007909 6477894800777514545063983)
      ·
        refine ⟨9716842201166271817595975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477894800777514545063983 9716842201166271817595975)
        ·
          refine ⟨14575263301749407726393963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716842201166271817595975 14575263301749407726393963)
          ·
            refine ⟨21862894952624111589590945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14575263301749407726393963 21862894952624111589590945)
            ·
              refine ⟨16397171214468083692193209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21862894952624111589590945 16397171214468083692193209)
              ·
                refine ⟨12297878410851062769144907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16397171214468083692193209 12297878410851062769144907)
                ·
                  refine ⟨18446817616276594153717361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12297878410851062769144907 18446817616276594153717361)
                  ·
                    refine ⟨13835113212207445615288021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18446817616276594153717361 13835113212207445615288021)
                    ·
                      refine ⟨324260465911112006608313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13835113212207445615288021 324260465911112006608313)
                      ·
                        rfl

theorem cell23_631495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_631495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631495 prefixEnd_631495 := by exact prefixLift 631495
  have htrace : WordTrace (prefixWord ++ tailWord_631495) baseStart_631495 baseEnd_631495 := by
    simpa [prefixWord, tailWord_631495, baseEnd_631495] using wordTrace_append hprefix tailTrace_631495
  have hstable : (prefixWord ++ tailWord_631495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631495).length < 2 ^ (prefixWord ++ tailWord_631495).sum := by decide
  have hdescent : baseEnd_631495 < baseStart_631495 := by decide
  rcases family_descends (prefixWord ++ tailWord_631495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631519 : List Nat := [1, 1, 2, 3, 2, 4, 1, 4, 5]
def baseStart_631519 : Nat := 118140960795 + 631519 * 2 ^ 59
def prefixEnd_631519 : Nat := 4983230072969 + 3 ^ 40 * 631519 * 2
def baseEnd_631519 : Nat := 36030309938535545856467

theorem tailTrace_631519 : CollatzResearch.WordTrace tailWord_631519 prefixEnd_631519 36030309938535545856467 := by
  unfold tailWord_631519
  simp only [CollatzResearch.WordTrace]
  refine ⟨23033390199121992703545611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15355593466081328469030407 23033390199121992703545611)
  ·
    refine ⟨34550085298682989055318417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23033390199121992703545611 34550085298682989055318417)
    ·
      refine ⟨25912563974012241791488813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34550085298682989055318417 25912563974012241791488813)
      ·
        refine ⟨9717211490254590671808305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25912563974012241791488813 9717211490254590671808305)
        ·
          refine ⟨7287908617690943003856229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9717211490254590671808305 7287908617690943003856229)
          ·
            refine ⟨1366482865817051813223043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7287908617690943003856229 1366482865817051813223043)
            ·
              refine ⟨2049724298725577719834565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366482865817051813223043 2049724298725577719834565)
              ·
                refine ⟨384323306011045822468981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2049724298725577719834565 384323306011045822468981)
                ·
                  refine ⟨36030309938535545856467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384323306011045822468981 36030309938535545856467)
                  ·
                    rfl

theorem cell23_631519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 5].length) (baseStart_631519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631519 prefixEnd_631519 := by exact prefixLift 631519
  have htrace : WordTrace (prefixWord ++ tailWord_631519) baseStart_631519 baseEnd_631519 := by
    simpa [prefixWord, tailWord_631519, baseEnd_631519] using wordTrace_append hprefix tailTrace_631519
  have hstable : (prefixWord ++ tailWord_631519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631519).length < 2 ^ (prefixWord ++ tailWord_631519).sum := by decide
  have hdescent : baseEnd_631519 < baseStart_631519 := by decide
  rcases family_descends (prefixWord ++ tailWord_631519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631569 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 2, 4, 2]
def baseStart_631569 : Nat := 118140960795 + 631569 * 2 ^ 59
def prefixEnd_631569 : Nat := 4983230072969 + 3 ^ 40 * 631569 * 2
def baseEnd_631569 : Nat := 324298463479544717082973

theorem tailTrace_631569 : CollatzResearch.WordTrace tailWord_631569 prefixEnd_631569 324298463479544717082973 := by
  unfold tailWord_631569
  simp only [CollatzResearch.WordTrace]
  refine ⟨23035213848940851242865761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15356809232627234161910507 23035213848940851242865761)
  ·
    refine ⟨17276410386705638432149321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23035213848940851242865761 17276410386705638432149321)
    ·
      refine ⟨12957307790029228824111991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17276410386705638432149321 12957307790029228824111991)
      ·
        refine ⟨19435961685043843236167987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12957307790029228824111991 19435961685043843236167987)
        ·
          refine ⟨29153942527565764854251981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19435961685043843236167987 29153942527565764854251981)
          ·
            refine ⟨10932728447837161820344493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29153942527565764854251981 10932728447837161820344493)
            ·
              refine ⟨4099773167938935682629185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10932728447837161820344493 4099773167938935682629185)
              ·
                refine ⟨3074829875954201761971889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4099773167938935682629185 3074829875954201761971889)
                ·
                  refine ⟨2306122406965651321478917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3074829875954201761971889 2306122406965651321478917)
                  ·
                    refine ⟨432397951306059622777297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306122406965651321478917 432397951306059622777297)
                    ·
                      refine ⟨324298463479544717082973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432397951306059622777297 324298463479544717082973)
                      ·
                        rfl

theorem cell23_631569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_631569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631569 prefixEnd_631569 := by exact prefixLift 631569
  have htrace : WordTrace (prefixWord ++ tailWord_631569) baseStart_631569 baseEnd_631569 := by
    simpa [prefixWord, tailWord_631569, baseEnd_631569] using wordTrace_append hprefix tailTrace_631569
  have hstable : (prefixWord ++ tailWord_631569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631569).length < 2 ^ (prefixWord ++ tailWord_631569).sum := by decide
  have hdescent : baseEnd_631569 < baseStart_631569 := by decide
  rcases family_descends (prefixWord ++ tailWord_631569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631586 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_631586 : Nat := 118140960795 + 631586 * 2 ^ 59
def prefixEnd_631586 : Nat := 4983230072969 + 3 ^ 40 * 631586 * 2
def baseEnd_631586 : Nat := 324307192650671150570395

theorem tailTrace_631586 : CollatzResearch.WordTrace tailWord_631586 prefixEnd_631586 324307192650671150570395 := by
  unfold tailWord_631586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5758958472469815786558653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15357222593252842097489741 5758958472469815786558653)
  ·
    refine ⟨2159609427176180919959495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5758958472469815786558653 2159609427176180919959495)
    ·
      refine ⟨3239414140764271379939243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2159609427176180919959495 3239414140764271379939243)
      ·
        refine ⟨4859121211146407069908865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239414140764271379939243 4859121211146407069908865)
        ·
          refine ⟨3644340908359805302431649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4859121211146407069908865 3644340908359805302431649)
          ·
            refine ⟨2733255681269853976823737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3644340908359805302431649 2733255681269853976823737)
            ·
              refine ⟨2049941760952390482617803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733255681269853976823737 2049941760952390482617803)
              ·
                refine ⟨3074912641428585723926705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049941760952390482617803 3074912641428585723926705)
                ·
                  refine ⟨2306184481071439292945029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3074912641428585723926705 2306184481071439292945029)
                  ·
                    refine ⟨432409590200894867427193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306184481071439292945029 432409590200894867427193)
                    ·
                      refine ⟨324307192650671150570395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432409590200894867427193 324307192650671150570395)
                      ·
                        rfl

theorem cell23_631586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_631586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631586 prefixEnd_631586 := by exact prefixLift 631586
  have htrace : WordTrace (prefixWord ++ tailWord_631586) baseStart_631586 baseEnd_631586 := by
    simpa [prefixWord, tailWord_631586, baseEnd_631586] using wordTrace_append hprefix tailTrace_631586
  have hstable : (prefixWord ++ tailWord_631586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631586).length < 2 ^ (prefixWord ++ tailWord_631586).sum := by decide
  have hdescent : baseEnd_631586 < baseStart_631586 := by decide
  rcases family_descends (prefixWord ++ tailWord_631586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631656 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 1, 5]
def baseStart_631656 : Nat := 118140960795 + 631656 * 2 ^ 59
def prefixEnd_631656 : Nat := 4983230072969 + 3 ^ 40 * 631656 * 2
def baseEnd_631656 : Nat := 108114378765495292231691

theorem tailTrace_631656 : CollatzResearch.WordTrace tailWord_631656 prefixEnd_631656 108114378765495292231691 := by
  unfold tailWord_631656
  simp only [CollatzResearch.WordTrace]
  refine ⟨11519193499812832550641411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15358924666417110067521881 11519193499812832550641411)
  ·
    refine ⟨17278790249719248825962117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11519193499812832550641411 17278790249719248825962117)
    ·
      refine ⟨3239773171822359154867897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17278790249719248825962117 3239773171822359154867897)
      ·
        refine ⟨2429829878866769366150923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3239773171822359154867897 2429829878866769366150923)
        ·
          refine ⟨3644744818300154049226385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429829878866769366150923 3644744818300154049226385)
          ·
            refine ⟨2733558613725115536919789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3644744818300154049226385 2733558613725115536919789)
            ·
              refine ⟨1025084480146918326344921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2733558613725115536919789 1025084480146918326344921)
              ·
                refine ⟨768813360110188744758691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025084480146918326344921 768813360110188744758691)
                ·
                  refine ⟨1153220040165283117138037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768813360110188744758691 1153220040165283117138037)
                  ·
                    refine ⟨108114378765495292231691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1153220040165283117138037 108114378765495292231691)
                    ·
                      rfl

theorem cell23_631656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_631656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631656 prefixEnd_631656 := by exact prefixLift 631656
  have htrace : WordTrace (prefixWord ++ tailWord_631656) baseStart_631656 baseEnd_631656 := by
    simpa [prefixWord, tailWord_631656, baseEnd_631656] using wordTrace_append hprefix tailTrace_631656
  have hstable : (prefixWord ++ tailWord_631656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631656).length < 2 ^ (prefixWord ++ tailWord_631656).sum := by decide
  have hdescent : baseEnd_631656 < baseStart_631656 := by decide
  rcases family_descends (prefixWord ++ tailWord_631656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631659 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 2, 6, 2]
def baseStart_631659 : Nat := 118140960795 + 631659 * 2 ^ 59
def prefixEnd_631659 : Nat := 4983230072969 + 3 ^ 40 * 631659 * 2
def baseEnd_631659 : Nat := 324344676738449364957559

theorem tailTrace_631659 : CollatzResearch.WordTrace tailWord_631659 prefixEnd_631659 324344676738449364957559 := by
  unfold tailWord_631659
  simp only [CollatzResearch.WordTrace]
  refine ⟨23038496418614796613642031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15358997612409864409094687 23038496418614796613642031)
  ·
    refine ⟨34557744627922194920463047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23038496418614796613642031 34557744627922194920463047)
    ·
      refine ⟨51836616941883292380694571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34557744627922194920463047 51836616941883292380694571)
      ·
        refine ⟨77754925412824938571041857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51836616941883292380694571 77754925412824938571041857)
        ·
          refine ⟨58316194059618703928281393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77754925412824938571041857 58316194059618703928281393)
          ·
            refine ⟨43737145544714027946211045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58316194059618703928281393 43737145544714027946211045)
            ·
              refine ⟨8200714789633880239914571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43737145544714027946211045 8200714789633880239914571)
              ·
                refine ⟨12301072184450820359871857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8200714789633880239914571 12301072184450820359871857)
                ·
                  refine ⟨9225804138338115269903893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12301072184450820359871857 9225804138338115269903893)
                  ·
                    refine ⟨432459568984599153276745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9225804138338115269903893 432459568984599153276745)
                    ·
                      refine ⟨324344676738449364957559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432459568984599153276745 324344676738449364957559)
                      ·
                        rfl

theorem cell23_631659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 6, 2].length) (baseStart_631659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631659 prefixEnd_631659 := by exact prefixLift 631659
  have htrace : WordTrace (prefixWord ++ tailWord_631659) baseStart_631659 baseEnd_631659 := by
    simpa [prefixWord, tailWord_631659, baseEnd_631659] using wordTrace_append hprefix tailTrace_631659
  have hstable : (prefixWord ++ tailWord_631659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631659).length < 2 ^ (prefixWord ++ tailWord_631659).sum := by decide
  have hdescent : baseEnd_631659 < baseStart_631659 := by decide
  rcases family_descends (prefixWord ++ tailWord_631659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631669 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_631669 : Nat := 118140960795 + 631669 * 2 ^ 59
def prefixEnd_631669 : Nat := 4983230072969 + 3 ^ 40 * 631669 * 2
def baseEnd_631669 : Nat := 108116603848331441944171

theorem tailTrace_631669 : CollatzResearch.WordTrace tailWord_631669 prefixEnd_631669 108116603848331441944171 := by
  unfold tailWord_631669
  simp only [CollatzResearch.WordTrace]
  refine ⟨23038861148578568321506061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15359240765719045547670707 23038861148578568321506061)
  ·
    refine ⟨8639572930716963120564773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23038861148578568321506061 8639572930716963120564773)
    ·
      refine ⟨1619919924509430585105895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8639572930716963120564773 1619919924509430585105895)
      ·
        refine ⟨2429879886764145877658843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619919924509430585105895 2429879886764145877658843)
        ·
          refine ⟨3644819830146218816488265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429879886764145877658843 3644819830146218816488265)
          ·
            refine ⟨2733614872609664112366199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3644819830146218816488265 2733614872609664112366199)
            ·
              refine ⟨4100422308914496168549299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733614872609664112366199 4100422308914496168549299)
              ·
                refine ⟨6150633463371744252823949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100422308914496168549299 6150633463371744252823949)
                ·
                  refine ⟨2306487548764404094808981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6150633463371744252823949 2306487548764404094808981)
                  ·
                    refine ⟨108116603848331441944171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2306487548764404094808981 108116603848331441944171)
                    ·
                      rfl

theorem cell23_631669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_631669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631669 prefixEnd_631669 := by exact prefixLift 631669
  have htrace : WordTrace (prefixWord ++ tailWord_631669) baseStart_631669 baseEnd_631669 := by
    simpa [prefixWord, tailWord_631669, baseEnd_631669] using wordTrace_append hprefix tailTrace_631669
  have hstable : (prefixWord ++ tailWord_631669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631669).length < 2 ^ (prefixWord ++ tailWord_631669).sum := by decide
  have hdescent : baseEnd_631669 < baseStart_631669 := by decide
  rcases family_descends (prefixWord ++ tailWord_631669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631672 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_631672 : Nat := 118140960795 + 631672 * 2 ^ 59
def prefixEnd_631672 : Nat := 4983230072969 + 3 ^ 40 * 631672 * 2
def baseEnd_631672 : Nat := 324351351986957814094999

theorem tailTrace_631672 : CollatzResearch.WordTrace tailWord_631672 prefixEnd_631672 324351351986957814094999 := by
  unfold tailWord_631672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11519485283783849916932635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15359313711711799889243513 11519485283783849916932635)
  ·
    refine ⟨17279227925675774875398953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11519485283783849916932635 17279227925675774875398953)
    ·
      refine ⟨12959420944256831156549215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17279227925675774875398953 12959420944256831156549215)
      ·
        refine ⟨19439131416385246734823823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12959420944256831156549215 19439131416385246734823823)
        ·
          refine ⟨29158697124577870102235735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19439131416385246734823823 29158697124577870102235735)
          ·
            refine ⟨43738045686866805153353603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29158697124577870102235735 43738045686866805153353603)
            ·
              refine ⟨65607068530300207730030405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43738045686866805153353603 65607068530300207730030405)
              ·
                refine ⟨12301325349431288949380701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65607068530300207730030405 12301325349431288949380701)
                ·
                  refine ⟨4612997006036733356017763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12301325349431288949380701 4612997006036733356017763)
                  ·
                    refine ⟨6919495509055100034026645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612997006036733356017763 6919495509055100034026645)
                    ·
                      refine ⟨324351351986957814094999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6919495509055100034026645 324351351986957814094999)
                      ·
                        rfl

theorem cell23_631672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_631672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631672 prefixEnd_631672 := by exact prefixLift 631672
  have htrace : WordTrace (prefixWord ++ tailWord_631672) baseStart_631672 baseEnd_631672 := by
    simpa [prefixWord, tailWord_631672, baseEnd_631672] using wordTrace_append hprefix tailTrace_631672
  have hstable : (prefixWord ++ tailWord_631672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631672).length < 2 ^ (prefixWord ++ tailWord_631672).sum := by decide
  have hdescent : baseEnd_631672 < baseStart_631672 := by decide
  rcases family_descends (prefixWord ++ tailWord_631672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631679 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 5]
def baseStart_631679 : Nat := 118140960795 + 631679 * 2 ^ 59
def prefixEnd_631679 : Nat := 4983230072969 + 3 ^ 40 * 631679 * 2
def baseEnd_631679 : Nat := 324354946351539286707467

theorem tailTrace_631679 : CollatzResearch.WordTrace tailWord_631679 prefixEnd_631679 324354946351539286707467 := by
  unfold tailWord_631679
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039225878542340029370091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15359483919028226686246727 23039225878542340029370091)
  ·
    refine ⟨34558838817813510044055137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23039225878542340029370091 34558838817813510044055137)
    ·
      refine ⟨25919129113360132533041353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34558838817813510044055137 25919129113360132533041353)
      ·
        refine ⟨19439346835020099399781015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25919129113360132533041353 19439346835020099399781015)
        ·
          refine ⟨29159020252530149099671523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19439346835020099399781015 29159020252530149099671523)
          ·
            refine ⟨43738530378795223649507285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29159020252530149099671523 43738530378795223649507285)
            ·
              refine ⟨1025121805753013054285327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43738530378795223649507285 1025121805753013054285327)
              ·
                refine ⟨1537682708629519581427991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025121805753013054285327 1537682708629519581427991)
                ·
                  refine ⟨2306524062944279372141987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537682708629519581427991 2306524062944279372141987)
                  ·
                    refine ⟨3459786094416419058212981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306524062944279372141987 3459786094416419058212981)
                    ·
                      refine ⟨324354946351539286707467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3459786094416419058212981 324354946351539286707467)
                      ·
                        rfl

theorem cell23_631679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_631679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631679 prefixEnd_631679 := by exact prefixLift 631679
  have htrace : WordTrace (prefixWord ++ tailWord_631679) baseStart_631679 baseEnd_631679 := by
    simpa [prefixWord, tailWord_631679, baseEnd_631679] using wordTrace_append hprefix tailTrace_631679
  have hstable : (prefixWord ++ tailWord_631679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631679).length < 2 ^ (prefixWord ++ tailWord_631679).sum := by decide
  have hdescent : baseEnd_631679 < baseStart_631679 := by decide
  rcases family_descends (prefixWord ++ tailWord_631679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631687 : List Nat := [1, 1, 4, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_631687 : Nat := 118140960795 + 631687 * 2 ^ 59
def prefixEnd_631687 : Nat := 4983230072969 + 3 ^ 40 * 631687 * 2
def baseEnd_631687 : Nat := 324359054196775255407431

theorem tailTrace_631687 : CollatzResearch.WordTrace tailWord_631687 prefixEnd_631687 324359054196775255407431 := by
  unfold tailWord_631687
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039517662513357395661315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15359678441675571597107543 23039517662513357395661315)
  ·
    refine ⟨34559276493770036093491973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23039517662513357395661315 34559276493770036093491973)
    ·
      refine ⟨6479864342581881767529745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34559276493770036093491973 6479864342581881767529745)
      ·
        refine ⟨4859898256936411325647309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6479864342581881767529745 4859898256936411325647309)
        ·
          refine ⟨1822461846351154247117741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4859898256936411325647309 1822461846351154247117741)
          ·
            refine ⟨683423192381682842669153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1822461846351154247117741 683423192381682842669153)
            ·
              refine ⟨512567394286262132001865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683423192381682842669153 512567394286262132001865)
              ·
                refine ⟨384425545714696599001399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512567394286262132001865 384425545714696599001399)
                ·
                  refine ⟨576638318572044898502099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384425545714696599001399 576638318572044898502099)
                  ·
                    refine ⟨864957477858067347753149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 576638318572044898502099 864957477858067347753149)
                    ·
                      refine ⟨324359054196775255407431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 864957477858067347753149 324359054196775255407431)
                      ·
                        rfl

theorem cell23_631687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_631687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631687 prefixEnd_631687 := by exact prefixLift 631687
  have htrace : WordTrace (prefixWord ++ tailWord_631687) baseStart_631687 baseEnd_631687 := by
    simpa [prefixWord, tailWord_631687, baseEnd_631687] using wordTrace_append hprefix tailTrace_631687
  have hstable : (prefixWord ++ tailWord_631687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631687).length < 2 ^ (prefixWord ++ tailWord_631687).sum := by decide
  have hdescent : baseEnd_631687 < baseStart_631687 := by decide
  rcases family_descends (prefixWord ++ tailWord_631687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631759 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 2, 6]
def baseStart_631759 : Nat := 118140960795 + 631759 * 2 ^ 59
def prefixEnd_631759 : Nat := 4983230072969 + 3 ^ 40 * 631759 * 2
def baseEnd_631759 : Nat := 108132008267966324569033

theorem tailTrace_631759 : CollatzResearch.WordTrace tailWord_631759 prefixEnd_631759 108132008267966324569033 := by
  unfold tailWord_631759
  simp only [CollatzResearch.WordTrace]
  refine ⟨23042143718252513692282331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15361429145501675794854887 23042143718252513692282331)
  ·
    refine ⟨34563215577378770538423497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23042143718252513692282331 34563215577378770538423497)
    ·
      refine ⟨25922411683034077903817623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34563215577378770538423497 25922411683034077903817623)
      ·
        refine ⟨38883617524551116855726435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25922411683034077903817623 38883617524551116855726435)
        ·
          refine ⟨58325426286826675283589653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38883617524551116855726435 58325426286826675283589653)
          ·
            refine ⟨2734004357195000403918265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58325426286826675283589653 2734004357195000403918265)
            ·
              refine ⟨2050503267896250302938699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734004357195000403918265 2050503267896250302938699)
              ·
                refine ⟨3075754901844375454408049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050503267896250302938699 3075754901844375454408049)
                ·
                  refine ⟨2306816176383281590806037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075754901844375454408049 2306816176383281590806037)
                  ·
                    refine ⟨108132008267966324569033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2306816176383281590806037 108132008267966324569033)
                    ·
                      rfl

theorem cell23_631759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_631759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631759 prefixEnd_631759 := by exact prefixLift 631759
  have htrace : WordTrace (prefixWord ++ tailWord_631759) baseStart_631759 baseEnd_631759 := by
    simpa [prefixWord, tailWord_631759, baseEnd_631759] using wordTrace_append hprefix tailTrace_631759
  have hstable : (prefixWord ++ tailWord_631759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631759).length < 2 ^ (prefixWord ++ tailWord_631759).sum := by decide
  have hdescent : baseEnd_631759 < baseStart_631759 := by decide
  rcases family_descends (prefixWord ++ tailWord_631759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631770 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2]
def baseStart_631770 : Nat := 118140960795 + 631770 * 2 ^ 59
def prefixEnd_631770 : Nat := 4983230072969 + 3 ^ 40 * 631770 * 2
def baseEnd_631770 : Nat := 324401673091098430669549

theorem tailTrace_631770 : CollatzResearch.WordTrace tailWord_631770 prefixEnd_631770 324401673091098430669549 := by
  unfold tailWord_631770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760636230303165642733191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15361696614141775047288509 5760636230303165642733191)
  ·
    refine ⟨8640954345454748464099787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5760636230303165642733191 8640954345454748464099787)
    ·
      refine ⟨12961431518182122696149681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8640954345454748464099787 12961431518182122696149681)
      ·
        refine ⟨9721073638636592022112261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12961431518182122696149681 9721073638636592022112261)
        ·
          refine ⟨1822701307244361004146049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9721073638636592022112261 1822701307244361004146049)
          ·
            refine ⟨1367025980433270753109537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822701307244361004146049 1367025980433270753109537)
            ·
              refine ⟨1025269485324953064832153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367025980433270753109537 1025269485324953064832153)
              ·
                refine ⟨768952113993714798624115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025269485324953064832153 768952113993714798624115)
                ·
                  refine ⟨1153428170990572197936173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768952113993714798624115 1153428170990572197936173)
                  ·
                    refine ⟨432535564121464574226065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153428170990572197936173 432535564121464574226065)
                    ·
                      refine ⟨324401673091098430669549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432535564121464574226065 324401673091098430669549)
                      ·
                        rfl

theorem cell23_631770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_631770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631770 prefixEnd_631770 := by exact prefixLift 631770
  have htrace : WordTrace (prefixWord ++ tailWord_631770) baseStart_631770 baseEnd_631770 := by
    simpa [prefixWord, tailWord_631770, baseEnd_631770] using wordTrace_append hprefix tailTrace_631770
  have hstable : (prefixWord ++ tailWord_631770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631770).length < 2 ^ (prefixWord ++ tailWord_631770).sum := by decide
  have hdescent : baseEnd_631770 < baseStart_631770 := by decide
  rcases family_descends (prefixWord ++ tailWord_631770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631786 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_631786 : Nat := 118140960795 + 631786 * 2 ^ 59
def prefixEnd_631786 : Nat := 4983230072969 + 3 ^ 40 * 631786 * 2
def baseEnd_631786 : Nat := 324409888781570368069475

theorem tailTrace_631786 : CollatzResearch.WordTrace tailWord_631786 prefixEnd_631786 324409888781570368069475 := by
  unfold tailWord_631786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760782122288674325878803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15362085659436464869010141 5760782122288674325878803)
  ·
    refine ⟨8641173183433011488818205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5760782122288674325878803 8641173183433011488818205)
    ·
      refine ⟨3240439943787379308306827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8641173183433011488818205 3240439943787379308306827)
      ·
        refine ⟨4860659915681068962460241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3240439943787379308306827 4860659915681068962460241)
        ·
          refine ⟨3645494936760801721845181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4860659915681068962460241 3645494936760801721845181)
          ·
            refine ⟨1367060601285300645691943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3645494936760801721845181 1367060601285300645691943)
            ·
              refine ⟨2050590901927950968537915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367060601285300645691943 2050590901927950968537915)
              ·
                refine ⟨3075886352891926452806873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050590901927950968537915 3075886352891926452806873)
                ·
                  refine ⟨2306914764668944839605155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075886352891926452806873 2306914764668944839605155)
                  ·
                    refine ⟨3460372147003417259407733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306914764668944839605155 3460372147003417259407733)
                    ·
                      refine ⟨324409888781570368069475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3460372147003417259407733 324409888781570368069475)
                      ·
                        rfl

theorem cell23_631786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_631786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631786 prefixEnd_631786 := by exact prefixLift 631786
  have htrace : WordTrace (prefixWord ++ tailWord_631786) baseStart_631786 baseEnd_631786 := by
    simpa [prefixWord, tailWord_631786, baseEnd_631786] using wordTrace_append hprefix tailTrace_631786
  have hstable : (prefixWord ++ tailWord_631786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631786).length < 2 ^ (prefixWord ++ tailWord_631786).sum := by decide
  have hdescent : baseEnd_631786 < baseStart_631786 := by decide
  rcases family_descends (prefixWord ++ tailWord_631786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631856 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_631856 : Nat := 118140960795 + 631856 * 2 ^ 59
def prefixEnd_631856 : Nat := 4983230072969 + 3 ^ 40 * 631856 * 2
def baseEnd_631856 : Nat := 324445832427385094194153

theorem tailTrace_631856 : CollatzResearch.WordTrace tailWord_631856 prefixEnd_631856 324445832427385094194153 := by
  unfold tailWord_631856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522840799450549629281711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15363787732600732839042281 11522840799450549629281711)
  ·
    refine ⟨17284261199175824443922567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11522840799450549629281711 17284261199175824443922567)
    ·
      refine ⟨25926391798763736665883851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17284261199175824443922567 25926391798763736665883851)
      ·
        refine ⟨38889587698145604998825777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25926391798763736665883851 38889587698145604998825777)
        ·
          refine ⟨29167190773609203749119333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38889587698145604998825777 29167190773609203749119333)
          ·
            refine ⟨5468848270051725702959875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29167190773609203749119333 5468848270051725702959875)
            ·
              refine ⟨8203272405077588554439813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468848270051725702959875 8203272405077588554439813)
              ·
                refine ⟨1538113575952047853957465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8203272405077588554439813 1538113575952047853957465)
                ·
                  refine ⟨1153585181964035890468099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538113575952047853957465 1153585181964035890468099)
                  ·
                    refine ⟨1730377772946053835702149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1153585181964035890468099 1730377772946053835702149)
                    ·
                      refine ⟨324445832427385094194153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1730377772946053835702149 324445832427385094194153)
                      ·
                        rfl

theorem cell23_631856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_631856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631856 prefixEnd_631856 := by exact prefixLift 631856
  have htrace : WordTrace (prefixWord ++ tailWord_631856) baseStart_631856 baseEnd_631856 := by
    simpa [prefixWord, tailWord_631856, baseEnd_631856] using wordTrace_append hprefix tailTrace_631856
  have hstable : (prefixWord ++ tailWord_631856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631856).length < 2 ^ (prefixWord ++ tailWord_631856).sum := by decide
  have hdescent : baseEnd_631856 < baseStart_631856 := by decide
  rcases family_descends (prefixWord ++ tailWord_631856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631859 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5]
def baseStart_631859 : Nat := 118140960795 + 631859 * 2 ^ 59
def prefixEnd_631859 : Nat := 4983230072969 + 3 ^ 40 * 631859 * 2
def baseEnd_631859 : Nat := 324447372869348582456639

theorem tailTrace_631859 : CollatzResearch.WordTrace tailWord_631859 prefixEnd_631859 324447372869348582456639 := by
  unfold tailWord_631859
  simp only [CollatzResearch.WordTrace]
  refine ⟨23045791017890230770922631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15363860678593487180615087 23045791017890230770922631)
  ·
    refine ⟨34568686526835346156383947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23045791017890230770922631 34568686526835346156383947)
    ·
      refine ⟨51853029790253019234575921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34568686526835346156383947 51853029790253019234575921)
      ·
        refine ⟨38889772342689764425931941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51853029790253019234575921 38889772342689764425931941)
        ·
          refine ⟨7291832314254330829862239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38889772342689764425931941 7291832314254330829862239)
          ·
            refine ⟨10937748471381496244793359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291832314254330829862239 10937748471381496244793359)
            ·
              refine ⟨16406622707072244367190039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937748471381496244793359 16406622707072244367190039)
              ·
                refine ⟨24609934060608366550785059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16406622707072244367190039 24609934060608366550785059)
                ·
                  refine ⟨36914901090912549826177589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24609934060608366550785059 36914901090912549826177589)
                  ·
                    refine ⟨3460771977273051546204149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36914901090912549826177589 3460771977273051546204149)
                    ·
                      refine ⟨324447372869348582456639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3460771977273051546204149 324447372869348582456639)
                      ·
                        rfl

theorem cell23_631859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_631859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631859 prefixEnd_631859 := by exact prefixLift 631859
  have htrace : WordTrace (prefixWord ++ tailWord_631859) baseStart_631859 baseEnd_631859 := by
    simpa [prefixWord, tailWord_631859, baseEnd_631859] using wordTrace_append hprefix tailTrace_631859
  have hstable : (prefixWord ++ tailWord_631859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631859).length < 2 ^ (prefixWord ++ tailWord_631859).sum := by decide
  have hdescent : baseEnd_631859 < baseStart_631859 := by decide
  rcases family_descends (prefixWord ++ tailWord_631859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631860 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_631860 : Nat := 118140960795 + 631860 * 2 ^ 59
def prefixEnd_631860 : Nat := 4983230072969 + 3 ^ 40 * 631860 * 2
def baseEnd_631860 : Nat := 324447886350003078544135

theorem tailTrace_631860 : CollatzResearch.WordTrace tailWord_631860 prefixEnd_631860 324447886350003078544135 := by
  unfold tailWord_631860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522913745443303970854517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15363884993924405294472689 11522913745443303970854517)
  ·
    refine ⟨1080273163635309747267611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11522913745443303970854517 1080273163635309747267611)
    ·
      refine ⟨1620409745452964620901417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080273163635309747267611 1620409745452964620901417)
      ·
        refine ⟨1215307309089723465676063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1620409745452964620901417 1215307309089723465676063)
        ·
          refine ⟨1822960963634585198514095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215307309089723465676063 1822960963634585198514095)
          ·
            refine ⟨2734441445451877797771143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822960963634585198514095 2734441445451877797771143)
            ·
              refine ⟨4101662168177816696656715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734441445451877797771143 4101662168177816696656715)
              ·
                refine ⟨6152493252266725044985073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4101662168177816696656715 6152493252266725044985073)
                ·
                  refine ⟨4614369939200043783738805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6152493252266725044985073 4614369939200043783738805)
                  ·
                    refine ⟨432597181800004104725513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4614369939200043783738805 432597181800004104725513)
                    ·
                      refine ⟨324447886350003078544135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432597181800004104725513 324447886350003078544135)
                      ·
                        rfl

theorem cell23_631860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_631860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631860 prefixEnd_631860 := by exact prefixLift 631860
  have htrace : WordTrace (prefixWord ++ tailWord_631860) baseStart_631860 baseEnd_631860 := by
    simpa [prefixWord, tailWord_631860, baseEnd_631860] using wordTrace_append hprefix tailTrace_631860
  have hstable : (prefixWord ++ tailWord_631860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631860).length < 2 ^ (prefixWord ++ tailWord_631860).sum := by decide
  have hdescent : baseEnd_631860 < baseStart_631860 := by decide
  rcases family_descends (prefixWord ++ tailWord_631860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631890 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_631890 : Nat := 118140960795 + 631890 * 2 ^ 59
def prefixEnd_631890 : Nat := 4983230072969 + 3 ^ 40 * 631890 * 2
def baseEnd_631890 : Nat := 324463290769637961168997

theorem tailTrace_631890 : CollatzResearch.WordTrace tailWord_631890 prefixEnd_631890 324463290769637961168997 := by
  unfold tailWord_631890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761730420194480766325281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15364614453851948710200749 5761730420194480766325281)
  ·
    refine ⟨4321297815145860574743961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5761730420194480766325281 4321297815145860574743961)
    ·
      refine ⟨3240973361359395431057971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4321297815145860574743961 3240973361359395431057971)
      ·
        refine ⟨4861460042039093146586957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3240973361359395431057971 4861460042039093146586957)
        ·
          refine ⟨1823047515764659929970109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4861460042039093146586957 1823047515764659929970109)
          ·
            refine ⟨683642818411747473738791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1823047515764659929970109 683642818411747473738791)
            ·
              refine ⟨1025464227617621210608187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683642818411747473738791 1025464227617621210608187)
              ·
                refine ⟨1538196341426431815912281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025464227617621210608187 1538196341426431815912281)
                ·
                  refine ⟨1153647256069823861934211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538196341426431815912281 1153647256069823861934211)
                  ·
                    refine ⟨1730470884104735792901317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1153647256069823861934211 1730470884104735792901317)
                    ·
                      refine ⟨324463290769637961168997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1730470884104735792901317 324463290769637961168997)
                      ·
                        rfl

theorem cell23_631890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_631890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631890 prefixEnd_631890 := by exact prefixLift 631890
  have htrace : WordTrace (prefixWord ++ tailWord_631890) baseStart_631890 baseEnd_631890 := by
    simpa [prefixWord, tailWord_631890, baseEnd_631890] using wordTrace_append hprefix tailTrace_631890
  have hstable : (prefixWord ++ tailWord_631890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631890).length < 2 ^ (prefixWord ++ tailWord_631890).sum := by decide
  have hdescent : baseEnd_631890 < baseStart_631890 := by decide
  rcases family_descends (prefixWord ++ tailWord_631890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631913 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 6]
def baseStart_631913 : Nat := 118140960795 + 631913 * 2 ^ 59
def prefixEnd_631913 : Nat := 4983230072969 + 3 ^ 40 * 631913 * 2
def baseEnd_631913 : Nat := 36052788980521263464599

theorem tailTrace_631913 : CollatzResearch.WordTrace tailWord_631913 prefixEnd_631913 36052788980521263464599 := by
  unfold tailWord_631913
  simp only [CollatzResearch.WordTrace]
  refine ⟨23047760559694597993388393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15365173706463065328925595 23047760559694597993388393)
  ·
    refine ⟨17285820419770948495041295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23047760559694597993388393 17285820419770948495041295)
    ·
      refine ⟨25928730629656422742561943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17285820419770948495041295 25928730629656422742561943)
      ·
        refine ⟨38893095944484634113842915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25928730629656422742561943 38893095944484634113842915)
        ·
          refine ⟨58339643916726951170764373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38893095944484634113842915 58339643916726951170764373)
          ·
            refine ⟨683667702149143959032395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 58339643916726951170764373 683667702149143959032395)
            ·
              refine ⟨1025501553223715938548593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683667702149143959032395 1025501553223715938548593)
              ·
                refine ⟨769126164917786953911445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025501553223715938548593 769126164917786953911445)
                ·
                  refine ⟨36052788980521263464599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 769126164917786953911445 36052788980521263464599)
                  ·
                    rfl

theorem cell23_631913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 6].length) (baseStart_631913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631913 prefixEnd_631913 := by exact prefixLift 631913
  have htrace : WordTrace (prefixWord ++ tailWord_631913) baseStart_631913 baseEnd_631913 := by
    simpa [prefixWord, tailWord_631913, baseEnd_631913] using wordTrace_append hprefix tailTrace_631913
  have hstable : (prefixWord ++ tailWord_631913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631913).length < 2 ^ (prefixWord ++ tailWord_631913).sum := by decide
  have hdescent : baseEnd_631913 < baseStart_631913 := by decide
  rcases family_descends (prefixWord ++ tailWord_631913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631933 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_631933 : Nat := 118140960795 + 631933 * 2 ^ 59
def prefixEnd_631933 : Nat := 4983230072969 + 3 ^ 40 * 631933 * 2
def baseEnd_631933 : Nat := 324485370437781292931299

theorem tailTrace_631933 : CollatzResearch.WordTrace tailWord_631933 prefixEnd_631933 324485370437781292931299 := by
  unfold tailWord_631933
  simp only [CollatzResearch.WordTrace]
  refine ⟨23048490019622141409116453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15365660013081427606077635 23048490019622141409116453)
  ·
    refine ⟨4321591878679151514209335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23048490019622141409116453 4321591878679151514209335)
    ·
      refine ⟨6482387818018727271314003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321591878679151514209335 6482387818018727271314003)
      ·
        refine ⟨9723581727028090906971005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482387818018727271314003 9723581727028090906971005)
        ·
          refine ⟨3646343147635534090114127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9723581727028090906971005 3646343147635534090114127)
          ·
            refine ⟨5469514721453301135171191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646343147635534090114127 5469514721453301135171191)
            ·
              refine ⟨8204272082179951702756787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469514721453301135171191 8204272082179951702756787)
              ·
                refine ⟨12306408123269927554135181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204272082179951702756787 12306408123269927554135181)
                ·
                  refine ⟨4614903046226222832800693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12306408123269927554135181 4614903046226222832800693)
                  ·
                    refine ⟨432647160583708390575065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4614903046226222832800693 432647160583708390575065)
                    ·
                      refine ⟨324485370437781292931299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432647160583708390575065 324485370437781292931299)
                      ·
                        rfl

theorem cell23_631933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_631933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631933 prefixEnd_631933 := by exact prefixLift 631933
  have htrace : WordTrace (prefixWord ++ tailWord_631933) baseStart_631933 baseEnd_631933 := by
    simpa [prefixWord, tailWord_631933, baseEnd_631933] using wordTrace_append hprefix tailTrace_631933
  have hstable : (prefixWord ++ tailWord_631933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631933).length < 2 ^ (prefixWord ++ tailWord_631933).sum := by decide
  have hdescent : baseEnd_631933 < baseStart_631933 := by decide
  rcases family_descends (prefixWord ++ tailWord_631933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631940 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_631940 : Nat := 118140960795 + 631940 * 2 ^ 59
def prefixEnd_631940 : Nat := 4983230072969 + 3 ^ 40 * 631940 * 2
def baseEnd_631940 : Nat := 324488964802362765543767

theorem tailTrace_631940 : CollatzResearch.WordTrace tailWord_631940 prefixEnd_631940 324488964802362765543767 := by
  unfold tailWord_631940
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524372665298390802310637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15365830220397854403080849 11524372665298390802310637)
  ·
    refine ⟨4321639749486896550866489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11524372665298390802310637 4321639749486896550866489)
    ·
      refine ⟨3241229812115172413149867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4321639749486896550866489 3241229812115172413149867)
      ·
        refine ⟨4861844718172758619724801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241229812115172413149867 4861844718172758619724801)
        ·
          refine ⟨3646383538629568964793601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4861844718172758619724801 3646383538629568964793601)
          ·
            refine ⟨2734787653972176723595201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3646383538629568964793601 2734787653972176723595201)
            ·
              refine ⟨2051090740479132542696401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734787653972176723595201 2051090740479132542696401)
              ·
                refine ⟨1538318055359349407022301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051090740479132542696401 1538318055359349407022301)
                ·
                  refine ⟨576869270759756027633363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1538318055359349407022301 576869270759756027633363)
                  ·
                    refine ⟨865303906139634041450045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 576869270759756027633363 865303906139634041450045)
                    ·
                      refine ⟨324488964802362765543767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 865303906139634041450045 324488964802362765543767)
                      ·
                        rfl

theorem cell23_631940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_631940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631940 prefixEnd_631940 := by exact prefixLift 631940
  have htrace : WordTrace (prefixWord ++ tailWord_631940) baseStart_631940 baseEnd_631940 := by
    simpa [prefixWord, tailWord_631940, baseEnd_631940] using wordTrace_append hprefix tailTrace_631940
  have hstable : (prefixWord ++ tailWord_631940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631940).length < 2 ^ (prefixWord ++ tailWord_631940).sum := by decide
  have hdescent : baseEnd_631940 < baseStart_631940 := by decide
  rcases family_descends (prefixWord ++ tailWord_631940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631950 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_631950 : Nat := 118140960795 + 631950 * 2 ^ 59
def prefixEnd_631950 : Nat := 4983230072969 + 3 ^ 40 * 631950 * 2
def baseEnd_631950 : Nat := 324494099608907726418721

theorem tailTrace_631950 : CollatzResearch.WordTrace tailWord_631950 prefixEnd_631950 324494099608907726418721 := by
  unfold tailWord_631950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881138757570069164060663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15366073373707035541656869 2881138757570069164060663)
  ·
    refine ⟨4321708136355103746090995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2881138757570069164060663 4321708136355103746090995)
    ·
      refine ⟨6482562204532655619136493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321708136355103746090995 6482562204532655619136493)
      ·
        refine ⟨2430960826699745857176185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6482562204532655619136493 2430960826699745857176185)
        ·
          refine ⟨1823220620024809392882139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430960826699745857176185 1823220620024809392882139)
          ·
            refine ⟨2734830930037214089323209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823220620024809392882139 2734830930037214089323209)
            ·
              refine ⟨2051123197527910566992407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734830930037214089323209 2051123197527910566992407)
              ·
                refine ⟨3076684796291865850488611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051123197527910566992407 3076684796291865850488611)
                ·
                  refine ⟨4615027194437798775732917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076684796291865850488611 4615027194437798775732917)
                  ·
                    refine ⟨432658799478543635224961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4615027194437798775732917 432658799478543635224961)
                    ·
                      refine ⟨324494099608907726418721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432658799478543635224961 324494099608907726418721)
                      ·
                        rfl

theorem cell23_631950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_631950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631950 prefixEnd_631950 := by exact prefixLift 631950
  have htrace : WordTrace (prefixWord ++ tailWord_631950) baseStart_631950 baseEnd_631950 := by
    simpa [prefixWord, tailWord_631950, baseEnd_631950] using wordTrace_append hprefix tailTrace_631950
  have hstable : (prefixWord ++ tailWord_631950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631950).length < 2 ^ (prefixWord ++ tailWord_631950).sum := by decide
  have hdescent : baseEnd_631950 < baseStart_631950 := by decide
  rcases family_descends (prefixWord ++ tailWord_631950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631967 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 2, 3, 2]
def baseStart_631967 : Nat := 118140960795 + 631967 * 2 ^ 59
def prefixEnd_631967 : Nat := 4983230072969 + 3 ^ 40 * 631967 * 2
def baseEnd_631967 : Nat := 324502828780034159906143

theorem tailTrace_631967 : CollatzResearch.WordTrace tailWord_631967 prefixEnd_631967 324502828780034159906143 := by
  unfold tailWord_631967
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049730101498965215854155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15366486734332643477236103 23049730101498965215854155)
  ·
    refine ⟨34574595152248447823781233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23049730101498965215854155 34574595152248447823781233)
    ·
      refine ⟨25930946364186335867835925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34574595152248447823781233 25930946364186335867835925)
      ·
        refine ⟨1215513110821234493804809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25930946364186335867835925 1215513110821234493804809)
        ·
          refine ⟨911634833115925870353607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1215513110821234493804809 911634833115925870353607)
          ·
            refine ⟨1367452249673888805530411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911634833115925870353607 1367452249673888805530411)
            ·
              refine ⟨2051178374510833208295617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367452249673888805530411 2051178374510833208295617)
              ·
                refine ⟨1538383780883124906221713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051178374510833208295617 1538383780883124906221713)
                ·
                  refine ⟨1153787835662343679666285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538383780883124906221713 1153787835662343679666285)
                  ·
                    refine ⟨432670438373378879874857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153787835662343679666285 432670438373378879874857)
                    ·
                      refine ⟨324502828780034159906143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432670438373378879874857 324502828780034159906143)
                      ·
                        rfl

theorem cell23_631967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_631967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631967 prefixEnd_631967 := by exact prefixLift 631967
  have htrace : WordTrace (prefixWord ++ tailWord_631967) baseStart_631967 baseEnd_631967 := by
    simpa [prefixWord, tailWord_631967, baseEnd_631967] using wordTrace_append hprefix tailTrace_631967
  have hstable : (prefixWord ++ tailWord_631967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631967).length < 2 ^ (prefixWord ++ tailWord_631967).sum := by decide
  have hdescent : baseEnd_631967 < baseStart_631967 := by decide
  rcases family_descends (prefixWord ++ tailWord_631967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631973 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_631973 : Nat := 118140960795 + 631973 * 2 ^ 59
def prefixEnd_631973 : Nat := 4983230072969 + 3 ^ 40 * 631973 * 2
def baseEnd_631973 : Nat := 108168636554653712143705

theorem tailTrace_631973 : CollatzResearch.WordTrace tailWord_631973 prefixEnd_631973 108168636554653712143705 := by
  unfold tailWord_631973
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049948939477228240572573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15366632626318152160381715 23049948939477228240572573)
  ·
    refine ⟨8643730852303960590214715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23049948939477228240572573 8643730852303960590214715)
    ·
      refine ⟨12965596278455940885322073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643730852303960590214715 12965596278455940885322073)
      ·
        refine ⟨9724197208841955663991555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12965596278455940885322073 9724197208841955663991555)
        ·
          refine ⟨14586295813262933495987333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9724197208841955663991555 14586295813262933495987333)
          ·
            refine ⟨2734930464986800030497625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14586295813262933495987333 2734930464986800030497625)
            ·
              refine ⟨2051197848740100022873219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734930464986800030497625 2051197848740100022873219)
              ·
                refine ⟨3076796773110150034309829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051197848740100022873219 3076796773110150034309829)
                ·
                  refine ⟨576899394958153131433093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3076796773110150034309829 576899394958153131433093)
                  ·
                    refine ⟨108168636554653712143705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 576899394958153131433093 108168636554653712143705)
                    ·
                      rfl

theorem cell23_631973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_631973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631973 prefixEnd_631973 := by exact prefixLift 631973
  have htrace : WordTrace (prefixWord ++ tailWord_631973) baseStart_631973 baseEnd_631973 := by
    simpa [prefixWord, tailWord_631973, baseEnd_631973] using wordTrace_append hprefix tailTrace_631973
  have hstable : (prefixWord ++ tailWord_631973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631973).length < 2 ^ (prefixWord ++ tailWord_631973).sum := by decide
  have hdescent : baseEnd_631973 < baseStart_631973 := by decide
  rcases family_descends (prefixWord ++ tailWord_631973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631980 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 3, 2, 2]
def baseStart_631980 : Nat := 118140960795 + 631980 * 2 ^ 59
def prefixEnd_631980 : Nat := 4983230072969 + 3 ^ 40 * 631980 * 2
def baseEnd_631980 : Nat := 324509504028542609043583

theorem tailTrace_631980 : CollatzResearch.WordTrace tailWord_631980 prefixEnd_631980 324509504028542609043583 := by
  unfold tailWord_631980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525102125225934218038697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15366802833634578957384929 11525102125225934218038697)
  ·
    refine ⟨8643826593919450663529023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11525102125225934218038697 8643826593919450663529023)
    ·
      refine ⟨12965739890879175995293535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643826593919450663529023 12965739890879175995293535)
      ·
        refine ⟨19448609836318763992940303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12965739890879175995293535 19448609836318763992940303)
        ·
          refine ⟨29172914754478145989410455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19448609836318763992940303 29172914754478145989410455)
          ·
            refine ⟨43759372131717218984115683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29172914754478145989410455 43759372131717218984115683)
            ·
              refine ⟨65639058197575828476173525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43759372131717218984115683 65639058197575828476173525)
              ·
                refine ⟨1538415426505683479910317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65639058197575828476173525 1538415426505683479910317)
                ·
                  refine ⟨576905784939631304966369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1538415426505683479910317 576905784939631304966369)
                  ·
                    refine ⟨432679338704723478724777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 576905784939631304966369 432679338704723478724777)
                    ·
                      refine ⟨324509504028542609043583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432679338704723478724777 324509504028542609043583)
                      ·
                        rfl

theorem cell23_631980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_631980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631980 prefixEnd_631980 := by exact prefixLift 631980
  have htrace : WordTrace (prefixWord ++ tailWord_631980) baseStart_631980 baseEnd_631980 := by
    simpa [prefixWord, tailWord_631980, baseEnd_631980] using wordTrace_append hprefix tailTrace_631980
  have hstable : (prefixWord ++ tailWord_631980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631980).length < 2 ^ (prefixWord ++ tailWord_631980).sum := by decide
  have hdescent : baseEnd_631980 < baseStart_631980 := by decide
  rcases family_descends (prefixWord ++ tailWord_631980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_631986 : List Nat := [3, 2, 1, 1, 1, 4, 1, 10]
def baseStart_631986 : Nat := 118140960795 + 631986 * 2 ^ 59
def prefixEnd_631986 : Nat := 4983230072969 + 3 ^ 40 * 631986 * 2
def baseEnd_631986 : Nat := 12018984626387762428465

theorem tailTrace_631986 : CollatzResearch.WordTrace tailWord_631986 prefixEnd_631986 12018984626387762428465 := by
  unfold tailWord_631986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762605772107532865198953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15366948725620087640530541 5762605772107532865198953)
  ·
    refine ⟨4321954329080649648899215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5762605772107532865198953 4321954329080649648899215)
    ·
      refine ⟨6482931493620974473348823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321954329080649648899215 6482931493620974473348823)
      ·
        refine ⟨9724397240431461710023235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482931493620974473348823 9724397240431461710023235)
        ·
          refine ⟨14586595860647192565034853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9724397240431461710023235 14586595860647192565034853)
          ·
            refine ⟨2734986723871348605944035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14586595860647192565034853 2734986723871348605944035)
            ·
              refine ⟨4102480085807022908916053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734986723871348605944035 4102480085807022908916053)
              ·
                refine ⟨12018984626387762428465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4102480085807022908916053 12018984626387762428465)
                ·
                  rfl

theorem cell23_631986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 10].length) (baseStart_631986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_631986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_631986 prefixEnd_631986 := by exact prefixLift 631986
  have htrace : WordTrace (prefixWord ++ tailWord_631986) baseStart_631986 baseEnd_631986 := by
    simpa [prefixWord, tailWord_631986, baseEnd_631986] using wordTrace_append hprefix tailTrace_631986
  have hstable : (prefixWord ++ tailWord_631986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_631986).length < 2 ^ (prefixWord ++ tailWord_631986).sum := by decide
  have hdescent : baseEnd_631986 < baseStart_631986 := by decide
  rcases family_descends (prefixWord ++ tailWord_631986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632000 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3]
def baseStart_632000 : Nat := 118140960795 + 632000 * 2 ^ 59
def prefixEnd_632000 : Nat := 4983230072969 + 3 ^ 40 * 632000 * 2
def baseEnd_632000 : Nat := 324519773641632530793491

theorem tailTrace_632000 : CollatzResearch.WordTrace tailWord_632000 prefixEnd_632000 324519773641632530793491 := by
  unfold tailWord_632000
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525466855189705925902727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15367289140252941234536969 11525466855189705925902727)
  ·
    refine ⟨17288200282784558888854091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11525466855189705925902727 17288200282784558888854091)
    ·
      refine ⟨25932300424176838333281137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17288200282784558888854091 25932300424176838333281137)
      ·
        refine ⟨19449225318132628749960853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25932300424176838333281137 19449225318132628749960853)
        ·
          refine ⟨911682436787466972654415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19449225318132628749960853 911682436787466972654415)
          ·
            refine ⟨1367523655181200458981623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911682436787466972654415 1367523655181200458981623)
            ·
              refine ⟨2051285482771800688472435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367523655181200458981623 2051285482771800688472435)
              ·
                refine ⟨3076928224157701032708653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051285482771800688472435 3076928224157701032708653)
                ·
                  refine ⟨1153848084059137887265745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3076928224157701032708653 1153848084059137887265745)
                  ·
                    refine ⟨865386063044353415449309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153848084059137887265745 865386063044353415449309)
                    ·
                      refine ⟨324519773641632530793491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 865386063044353415449309 324519773641632530793491)
                      ·
                        rfl

theorem cell23_632000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_632000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632000 prefixEnd_632000 := by exact prefixLift 632000
  have htrace : WordTrace (prefixWord ++ tailWord_632000) baseStart_632000 baseEnd_632000 := by
    simpa [prefixWord, tailWord_632000, baseEnd_632000] using wordTrace_append hprefix tailTrace_632000
  have hstable : (prefixWord ++ tailWord_632000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632000).length < 2 ^ (prefixWord ++ tailWord_632000).sum := by decide
  have hdescent : baseEnd_632000 < baseStart_632000 := by decide
  rcases family_descends (prefixWord ++ tailWord_632000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632020 : List Nat := [2, 4, 1, 4, 2, 10]
def baseStart_632020 : Nat := 118140960795 + 632020 * 2 ^ 59
def prefixEnd_632020 : Nat := 4983230072969 + 3 ^ 40 * 632020 * 2
def baseEnd_632020 : Nat := 1335514581295154125693

theorem tailTrace_632020 : CollatzResearch.WordTrace tailWord_632020 prefixEnd_632020 1335514581295154125693 := by
  unfold tailWord_632020
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525831585153477633766757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15367775446871303511689009 11525831585153477633766757)
  ·
    refine ⟨2161093422216277056331267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11525831585153477633766757 2161093422216277056331267)
    ·
      refine ⟨3241640133324415584496901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2161093422216277056331267 3241640133324415584496901)
      ·
        refine ⟨607807524998327922093169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3241640133324415584496901 607807524998327922093169)
        ·
          refine ⟨455855643748745941569877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607807524998327922093169 455855643748745941569877)
          ·
            refine ⟨1335514581295154125693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 455855643748745941569877 1335514581295154125693)
            ·
              rfl

theorem cell23_632020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 10].length) (baseStart_632020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632020 prefixEnd_632020 := by exact prefixLift 632020
  have htrace : WordTrace (prefixWord ++ tailWord_632020) baseStart_632020 baseEnd_632020 := by
    simpa [prefixWord, tailWord_632020, baseEnd_632020] using wordTrace_append hprefix tailTrace_632020
  have hstable : (prefixWord ++ tailWord_632020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632020).length < 2 ^ (prefixWord ++ tailWord_632020).sum := by decide
  have hdescent : baseEnd_632020 < baseStart_632020 := by decide
  rcases family_descends (prefixWord ++ tailWord_632020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632040 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_632040 : Nat := 118140960795 + 632040 * 2 ^ 59
def prefixEnd_632040 : Nat := 4983230072969 + 3 ^ 40 * 632040 * 2
def baseEnd_632040 : Nat := 324540312867812374293307

theorem tailTrace_632040 : CollatzResearch.WordTrace tailWord_632040 prefixEnd_632040 324540312867812374293307 := by
  unfold tailWord_632040
  simp only [CollatzResearch.WordTrace]
  refine ⟨11526196315117249341630787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15368261753489665788841049 11526196315117249341630787)
  ·
    refine ⟨17289294472675874012446181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11526196315117249341630787 17289294472675874012446181)
    ·
      refine ⟨3241742713626726377333659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17289294472675874012446181 3241742713626726377333659)
      ·
        refine ⟨4862614070440089566000489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241742713626726377333659 4862614070440089566000489)
        ·
          refine ⟨3646960552830067174500367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4862614070440089566000489 3646960552830067174500367)
          ·
            refine ⟨5470440829245100761750551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646960552830067174500367 5470440829245100761750551)
            ·
              refine ⟨8205661243867651142625827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470440829245100761750551 8205661243867651142625827)
              ·
                refine ⟨12308491865801476713938741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8205661243867651142625827 12308491865801476713938741)
                ·
                  refine ⟨1153921112418888441931757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12308491865801476713938741 1153921112418888441931757)
                  ·
                    refine ⟨432720417157083165724409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1153921112418888441931757 432720417157083165724409)
                    ·
                      refine ⟨324540312867812374293307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432720417157083165724409 324540312867812374293307)
                      ·
                        rfl

theorem cell23_632040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_632040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632040 prefixEnd_632040 := by exact prefixLift 632040
  have htrace : WordTrace (prefixWord ++ tailWord_632040) baseStart_632040 baseEnd_632040 := by
    simpa [prefixWord, tailWord_632040, baseEnd_632040] using wordTrace_append hprefix tailTrace_632040
  have hstable : (prefixWord ++ tailWord_632040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632040).length < 2 ^ (prefixWord ++ tailWord_632040).sum := by decide
  have hdescent : baseEnd_632040 < baseStart_632040 := by decide
  rcases family_descends (prefixWord ++ tailWord_632040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632087 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 4, 2, 2]
def baseStart_632087 : Nat := 118140960795 + 632087 * 2 ^ 59
def prefixEnd_632087 : Nat := 4983230072969 + 3 ^ 40 * 632087 * 2
def baseEnd_632087 : Nat := 324564446458573690405591

theorem tailTrace_632087 : CollatzResearch.WordTrace tailWord_632087 prefixEnd_632087 324564446458573690405591 := by
  unfold tailWord_632087
  simp only [CollatzResearch.WordTrace]
  refine ⟨23054106861064225710222515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15369404574042817140148343 23054106861064225710222515)
  ·
    refine ⟨34581160291596338565333773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23054106861064225710222515 34581160291596338565333773)
    ·
      refine ⟨12967935109348626962000165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34581160291596338565333773 12967935109348626962000165)
      ·
        refine ⟨2431487833002867555375031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12967935109348626962000165 2431487833002867555375031)
        ·
          refine ⟨3647231749504301333062547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431487833002867555375031 3647231749504301333062547)
          ·
            refine ⟨5470847624256451999593821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647231749504301333062547 5470847624256451999593821)
            ·
              refine ⟨2051567859096169499847683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5470847624256451999593821 2051567859096169499847683)
              ·
                refine ⟨3077351788644254249771525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051567859096169499847683 3077351788644254249771525)
                ·
                  refine ⟨577003460370797671832161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3077351788644254249771525 577003460370797671832161)
                  ·
                    refine ⟨432752595278098253874121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 577003460370797671832161 432752595278098253874121)
                    ·
                      refine ⟨324564446458573690405591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432752595278098253874121 324564446458573690405591)
                      ·
                        rfl

theorem cell23_632087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_632087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632087 prefixEnd_632087 := by exact prefixLift 632087
  have htrace : WordTrace (prefixWord ++ tailWord_632087) baseStart_632087 baseEnd_632087 := by
    simpa [prefixWord, tailWord_632087, baseEnd_632087] using wordTrace_append hprefix tailTrace_632087
  have hstable : (prefixWord ++ tailWord_632087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632087).length < 2 ^ (prefixWord ++ tailWord_632087).sum := by decide
  have hdescent : baseEnd_632087 < baseStart_632087 := by decide
  rcases family_descends (prefixWord ++ tailWord_632087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632104 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_632104 : Nat := 118140960795 + 632104 * 2 ^ 59
def prefixEnd_632104 : Nat := 4983230072969 + 3 ^ 40 * 632104 * 2
def baseEnd_632104 : Nat := 324573175629700123893013

theorem tailTrace_632104 : CollatzResearch.WordTrace tailWord_632104 prefixEnd_632104 324573175629700123893013 := by
  unfold tailWord_632104
  simp only [CollatzResearch.WordTrace]
  refine ⟨11527363451001318806795683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15369817934668425075727577 11527363451001318806795683)
  ·
    refine ⟨17291045176501978210193525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11527363451001318806795683 17291045176501978210193525)
    ·
      refine ⟨1621035485297060457205643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17291045176501978210193525 1621035485297060457205643)
      ·
        refine ⟨2431553227945590685808465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621035485297060457205643 2431553227945590685808465)
        ·
          refine ⟨1823664920959193014356349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2431553227945590685808465 1823664920959193014356349)
          ·
            refine ⟨683874345359697380383631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1823664920959193014356349 683874345359697380383631)
            ·
              refine ⟨1025811518039546070575447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683874345359697380383631 1025811518039546070575447)
              ·
                refine ⟨1538717277059319105863171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025811518039546070575447 1538717277059319105863171)
                ·
                  refine ⟨2308075915588978658794757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538717277059319105863171 2308075915588978658794757)
                  ·
                    refine ⟨432764234172933498524017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2308075915588978658794757 432764234172933498524017)
                    ·
                      refine ⟨324573175629700123893013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432764234172933498524017 324573175629700123893013)
                      ·
                        rfl

theorem cell23_632104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_632104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632104 prefixEnd_632104 := by exact prefixLift 632104
  have htrace : WordTrace (prefixWord ++ tailWord_632104) baseStart_632104 baseEnd_632104 := by
    simpa [prefixWord, tailWord_632104, baseEnd_632104] using wordTrace_append hprefix tailTrace_632104
  have hstable : (prefixWord ++ tailWord_632104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632104).length < 2 ^ (prefixWord ++ tailWord_632104).sum := by decide
  have hdescent : baseEnd_632104 < baseStart_632104 := by decide
  rcases family_descends (prefixWord ++ tailWord_632104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632127 : List Nat := [1, 1, 2, 2, 4, 4, 1, 3, 5]
def baseStart_632127 : Nat := 118140960795 + 632127 * 2 ^ 59
def prefixEnd_632127 : Nat := 4983230072969 + 3 ^ 40 * 632127 * 2
def baseEnd_632127 : Nat := 36064998409417059322823

theorem tailTrace_632127 : CollatzResearch.WordTrace tailWord_632127 prefixEnd_632127 36064998409417059322823 := by
  unfold tailWord_632127
  simp only [CollatzResearch.WordTrace]
  refine ⟨23055565780919312541678635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15370377187279541694452423 23055565780919312541678635)
  ·
    refine ⟨34583348671378968812517953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23055565780919312541678635 34583348671378968812517953)
    ·
      refine ⟨25937511503534226609388465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34583348671378968812517953 25937511503534226609388465)
      ·
        refine ⟨19453133627650669957041349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25937511503534226609388465 19453133627650669957041349)
        ·
          refine ⟨3647462555184500616945253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19453133627650669957041349 3647462555184500616945253)
          ·
            refine ⟨683899229097093865677235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3647462555184500616945253 683899229097093865677235)
            ·
              refine ⟨1025848843645640798515853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683899229097093865677235 1025848843645640798515853)
              ·
                refine ⟨384693316367115299443445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1025848843645640798515853 384693316367115299443445)
                ·
                  refine ⟨36064998409417059322823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384693316367115299443445 36064998409417059322823)
                  ·
                    rfl

theorem cell23_632127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 5].length) (baseStart_632127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632127 prefixEnd_632127 := by exact prefixLift 632127
  have htrace : WordTrace (prefixWord ++ tailWord_632127) baseStart_632127 baseEnd_632127 := by
    simpa [prefixWord, tailWord_632127, baseEnd_632127] using wordTrace_append hprefix tailTrace_632127
  have hstable : (prefixWord ++ tailWord_632127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632127).length < 2 ^ (prefixWord ++ tailWord_632127).sum := by decide
  have hdescent : baseEnd_632127 < baseStart_632127 := by decide
  rcases family_descends (prefixWord ++ tailWord_632127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632140 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_632140 : Nat := 118140960795 + 632140 * 2 ^ 59
def prefixEnd_632140 : Nat := 4983230072969 + 3 ^ 40 * 632140 * 2
def baseEnd_632140 : Nat := 108197220311087327680949

theorem tailTrace_632140 : CollatzResearch.WordTrace tailWord_632140 prefixEnd_632140 108197220311087327680949 := by
  unfold tailWord_632140
  simp only [CollatzResearch.WordTrace]
  refine ⟨11528019964936107880950937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15370693286581477174601249 11528019964936107880950937)
  ·
    refine ⟨8646014973702080910713203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11528019964936107880950937 8646014973702080910713203)
    ·
      refine ⟨12969022460553121366069805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8646014973702080910713203 12969022460553121366069805)
      ·
        refine ⟨4863383422707420512276177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12969022460553121366069805 4863383422707420512276177)
        ·
          refine ⟨3647537567030565384207133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4863383422707420512276177 3647537567030565384207133)
          ·
            refine ⟨1367826587636462019077675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3647537567030565384207133 1367826587636462019077675)
            ·
              refine ⟨2051739881454693028616513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367826587636462019077675 2051739881454693028616513)
              ·
                refine ⟨1538804911091019771462385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051739881454693028616513 1538804911091019771462385)
                ·
                  refine ⟨1154103683318264828596789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538804911091019771462385 1154103683318264828596789)
                  ·
                    refine ⟨108197220311087327680949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1154103683318264828596789 108197220311087327680949)
                    ·
                      rfl

theorem cell23_632140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_632140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632140 prefixEnd_632140 := by exact prefixLift 632140
  have htrace : WordTrace (prefixWord ++ tailWord_632140) baseStart_632140 baseEnd_632140 := by
    simpa [prefixWord, tailWord_632140, baseEnd_632140] using wordTrace_append hprefix tailTrace_632140
  have hstable : (prefixWord ++ tailWord_632140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632140).length < 2 ^ (prefixWord ++ tailWord_632140).sum := by decide
  have hdescent : baseEnd_632140 < baseStart_632140 := by decide
  rcases family_descends (prefixWord ++ tailWord_632140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632174 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_632174 : Nat := 118140960795 + 632174 * 2 ^ 59
def prefixEnd_632174 : Nat := 4983230072969 + 3 ^ 40 * 632174 * 2
def baseEnd_632174 : Nat := 108203039758504950005897

theorem tailTrace_632174 : CollatzResearch.WordTrace tailWord_632174 prefixEnd_632174 108203039758504950005897 := by
  unfold tailWord_632174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882160001468629946079947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15371520007832693045759717 2882160001468629946079947)
  ·
    refine ⟨4323240002202944919119921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882160001468629946079947 4323240002202944919119921)
    ·
      refine ⟨3242430001652208689339941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4323240002202944919119921 3242430001652208689339941)
      ·
        refine ⟨607955625309789129251239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3242430001652208689339941 607955625309789129251239)
        ·
          refine ⟨911933437964683693876859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607955625309789129251239 911933437964683693876859)
          ·
            refine ⟨1367900156947025540815289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911933437964683693876859 1367900156947025540815289)
            ·
              refine ⟨1025925117710269155611467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367900156947025540815289 1025925117710269155611467)
              ·
                refine ⟨1538887676565403733417201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025925117710269155611467 1538887676565403733417201)
                ·
                  refine ⟨1154165757424052800062901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538887676565403733417201 1154165757424052800062901)
                  ·
                    refine ⟨108203039758504950005897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1154165757424052800062901 108203039758504950005897)
                    ·
                      rfl

theorem cell23_632174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_632174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632174 prefixEnd_632174 := by exact prefixLift 632174
  have htrace : WordTrace (prefixWord ++ tailWord_632174) baseStart_632174 baseEnd_632174 := by
    simpa [prefixWord, tailWord_632174, baseEnd_632174] using wordTrace_append hprefix tailTrace_632174
  have hstable : (prefixWord ++ tailWord_632174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632174).length < 2 ^ (prefixWord ++ tailWord_632174).sum := by decide
  have hdescent : baseEnd_632174 < baseStart_632174 := by decide
  rcases family_descends (prefixWord ++ tailWord_632174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632187 : List Nat := [1, 1, 1, 1, 1, 6, 2, 5, 1, 4]
def baseStart_632187 : Nat := 118140960795 + 632187 * 2 ^ 59
def prefixEnd_632187 : Nat := 4983230072969 + 3 ^ 40 * 632187 * 2
def baseEnd_632187 : Nat := 108205264841341099718377

theorem tailTrace_632187 : CollatzResearch.WordTrace tailWord_632187 prefixEnd_632187 108205264841341099718377 := by
  unfold tailWord_632187
  simp only [CollatzResearch.WordTrace]
  refine ⟨23057754160701942788862815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15371836107134628525908543 23057754160701942788862815)
  ·
    refine ⟨34586631241052914183294223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23057754160701942788862815 34586631241052914183294223)
    ·
      refine ⟨51879946861579371274941335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34586631241052914183294223 51879946861579371274941335)
      ·
        refine ⟨77819920292369056912412003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51879946861579371274941335 77819920292369056912412003)
        ·
          refine ⟨116729880438553585368618005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77819920292369056912412003 116729880438553585368618005)
          ·
            refine ⟨5471713145557199314153969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116729880438553585368618005 5471713145557199314153969)
            ·
              refine ⟨4103784859167899485615477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5471713145557199314153969 4103784859167899485615477)
              ·
                refine ⟨384729830546990576776451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4103784859167899485615477 384729830546990576776451)
                ·
                  refine ⟨577094745820485865164677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384729830546990576776451 577094745820485865164677)
                  ·
                    refine ⟨108205264841341099718377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 577094745820485865164677 108205264841341099718377)
                    ·
                      rfl

theorem cell23_632187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 4].length) (baseStart_632187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632187 prefixEnd_632187 := by exact prefixLift 632187
  have htrace : WordTrace (prefixWord ++ tailWord_632187) baseStart_632187 baseEnd_632187 := by
    simpa [prefixWord, tailWord_632187, baseEnd_632187] using wordTrace_append hprefix tailTrace_632187
  have hstable : (prefixWord ++ tailWord_632187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632187).length < 2 ^ (prefixWord ++ tailWord_632187).sum := by decide
  have hdescent : baseEnd_632187 < baseStart_632187 := by decide
  rcases family_descends (prefixWord ++ tailWord_632187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632194 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_632194 : Nat := 118140960795 + 632194 * 2 ^ 59
def prefixEnd_632194 : Nat := 4983230072969 + 3 ^ 40 * 632194 * 2
def baseEnd_632194 : Nat := 324619388888604771767599

theorem tailTrace_632194 : CollatzResearch.WordTrace tailWord_632194 prefixEnd_632194 324619388888604771767599 := by
  unfold tailWord_632194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5764502367919145746091909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15372006314451055322911757 5764502367919145746091909)
  ·
    refine ⟨1080844193984839827392233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5764502367919145746091909 1080844193984839827392233)
    ·
      refine ⟨810633145488629870544175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1080844193984839827392233 810633145488629870544175)
      ·
        refine ⟨1215949718232944805816263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810633145488629870544175 1215949718232944805816263)
        ·
          refine ⟨1823924577349417208724395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215949718232944805816263 1823924577349417208724395)
          ·
            refine ⟨2735886866024125813086593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823924577349417208724395 2735886866024125813086593)
            ·
              refine ⟨2051915149518094359814945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735886866024125813086593 2051915149518094359814945)
              ·
                refine ⟨1538936362138570769861209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051915149518094359814945 1538936362138570769861209)
                ·
                  refine ⟨1154202271603928077395907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538936362138570769861209 1154202271603928077395907)
                  ·
                    refine ⟨1731303407405892116093861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154202271603928077395907 1731303407405892116093861)
                    ·
                      refine ⟨324619388888604771767599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1731303407405892116093861 324619388888604771767599)
                      ·
                        rfl

theorem cell23_632194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_632194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632194 prefixEnd_632194 := by exact prefixLift 632194
  have htrace : WordTrace (prefixWord ++ tailWord_632194) baseStart_632194 baseEnd_632194 := by
    simpa [prefixWord, tailWord_632194, baseEnd_632194] using wordTrace_append hprefix tailTrace_632194
  have hstable : (prefixWord ++ tailWord_632194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632194).length < 2 ^ (prefixWord ++ tailWord_632194).sum := by decide
  have hdescent : baseEnd_632194 < baseStart_632194 := by decide
  rcases family_descends (prefixWord ++ tailWord_632194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632200 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 6]
def baseStart_632200 : Nat := 118140960795 + 632200 * 2 ^ 59
def prefixEnd_632200 : Nat := 4983230072969 + 3 ^ 40 * 632200 * 2
def baseEnd_632200 : Nat := 36069163308059083143619

theorem tailTrace_632200 : CollatzResearch.WordTrace tailWord_632200 prefixEnd_632200 36069163308059083143619 := by
  unfold tailWord_632200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11529114154827423004543027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15372152206436564006057369 11529114154827423004543027)
  ·
    refine ⟨17293671232241134506814541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11529114154827423004543027 17293671232241134506814541)
    ·
      refine ⟨6485126712090425440055453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17293671232241134506814541 6485126712090425440055453)
      ·
        refine ⟨2431922517033909540020795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6485126712090425440055453 2431922517033909540020795)
        ·
          refine ⟨3647883775550864310031193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431922517033909540020795 3647883775550864310031193)
          ·
            refine ⟨2735912831663148232523395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3647883775550864310031193 2735912831663148232523395)
            ·
              refine ⟨4103869247494722348785093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735912831663148232523395 4103869247494722348785093)
              ·
                refine ⟨769475483905260440397205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4103869247494722348785093 769475483905260440397205)
                ·
                  refine ⟨36069163308059083143619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 769475483905260440397205 36069163308059083143619)
                  ·
                    rfl

theorem cell23_632200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 6].length) (baseStart_632200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632200 prefixEnd_632200 := by exact prefixLift 632200
  have htrace : WordTrace (prefixWord ++ tailWord_632200) baseStart_632200 baseEnd_632200 := by
    simpa [prefixWord, tailWord_632200, baseEnd_632200] using wordTrace_append hprefix tailTrace_632200
  have hstable : (prefixWord ++ tailWord_632200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632200).length < 2 ^ (prefixWord ++ tailWord_632200).sum := by decide
  have hdescent : baseEnd_632200 < baseStart_632200 := by decide
  rcases family_descends (prefixWord ++ tailWord_632200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632203 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6]
def baseStart_632203 : Nat := 118140960795 + 632203 * 2 ^ 59
def prefixEnd_632203 : Nat := 4983230072969 + 3 ^ 40 * 632203 * 2
def baseEnd_632203 : Nat := 324624010214495236555057

theorem tailTrace_632203 : CollatzResearch.WordTrace tailWord_632203 prefixEnd_632203 324624010214495236555057 := by
  unfold tailWord_632203
  simp only [CollatzResearch.WordTrace]
  refine ⟨23058337728643977521445263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15372225152429318347630175 23058337728643977521445263)
  ·
    refine ⟨34587506592965966282167895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23058337728643977521445263 34587506592965966282167895)
    ·
      refine ⟨51881259889448949423251843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34587506592965966282167895 51881259889448949423251843)
      ·
        refine ⟨77821889834173424134877765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51881259889448949423251843 77821889834173424134877765)
        ·
          refine ⟨14591604343907517025289581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77821889834173424134877765 14591604343907517025289581)
          ·
            refine ⟨5471851628965318884483593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14591604343907517025289581 5471851628965318884483593)
            ·
              refine ⟨4103888721723989163362695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5471851628965318884483593 4103888721723989163362695)
              ·
                refine ⟨6155833082585983745044043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4103888721723989163362695 6155833082585983745044043)
                ·
                  refine ⟨9233749623878975617566065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6155833082585983745044043 9233749623878975617566065)
                  ·
                    refine ⟨6925312217909231713174549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9233749623878975617566065 6925312217909231713174549)
                    ·
                      refine ⟨324624010214495236555057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6925312217909231713174549 324624010214495236555057)
                      ·
                        rfl

theorem cell23_632203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_632203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632203 prefixEnd_632203 := by exact prefixLift 632203
  have htrace : WordTrace (prefixWord ++ tailWord_632203) baseStart_632203 baseEnd_632203 := by
    simpa [prefixWord, tailWord_632203, baseEnd_632203] using wordTrace_append hprefix tailTrace_632203
  have hstable : (prefixWord ++ tailWord_632203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632203).length < 2 ^ (prefixWord ++ tailWord_632203).sum := by decide
  have hdescent : baseEnd_632203 < baseStart_632203 := by decide
  rcases family_descends (prefixWord ++ tailWord_632203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632227 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 3]
def baseStart_632227 : Nat := 118140960795 + 632227 * 2 ^ 59
def prefixEnd_632227 : Nat := 4983230072969 + 3 ^ 40 * 632227 * 2
def baseEnd_632227 : Nat := 324636333750203142654947

theorem tailTrace_632227 : CollatzResearch.WordTrace tailWord_632227 prefixEnd_632227 324636333750203142654947 := by
  unfold tailWord_632227
  simp only [CollatzResearch.WordTrace]
  refine ⟨23059213080557029620318935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15372808720371353080212623 23059213080557029620318935)
  ·
    refine ⟨34588819620835544430478403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23059213080557029620318935 34588819620835544430478403)
    ·
      refine ⟨51883229431253316645717605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34588819620835544430478403 51883229431253316645717605)
      ·
        refine ⟨9728105518359996871072051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51883229431253316645717605 9728105518359996871072051)
        ·
          refine ⟨14592158277539995306608077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9728105518359996871072051 14592158277539995306608077)
          ·
            refine ⟨5472059354077498239978029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14592158277539995306608077 5472059354077498239978029)
            ·
              refine ⟨2052022257779061839991761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5472059354077498239978029 2052022257779061839991761)
              ·
                refine ⟨1539016693334296379993821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052022257779061839991761 1539016693334296379993821)
                ·
                  refine ⟨577131260000361142497683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1539016693334296379993821 577131260000361142497683)
                  ·
                    refine ⟨865696890000541713746525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 577131260000361142497683 865696890000541713746525)
                    ·
                      refine ⟨324636333750203142654947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 865696890000541713746525 324636333750203142654947)
                      ·
                        rfl

theorem cell23_632227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_632227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632227 prefixEnd_632227 := by exact prefixLift 632227
  have htrace : WordTrace (prefixWord ++ tailWord_632227) baseStart_632227 baseEnd_632227 := by
    simpa [prefixWord, tailWord_632227, baseEnd_632227] using wordTrace_append hprefix tailTrace_632227
  have hstable : (prefixWord ++ tailWord_632227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632227).length < 2 ^ (prefixWord ++ tailWord_632227).sum := by decide
  have hdescent : baseEnd_632227 < baseStart_632227 := by decide
  rcases family_descends (prefixWord ++ tailWord_632227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632270 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_632270 : Nat := 118140960795 + 632270 * 2 ^ 59
def prefixEnd_632270 : Nat := 4983230072969 + 3 ^ 40 * 632270 * 2
def baseEnd_632270 : Nat := 324658413418346474417249

theorem tailTrace_632270 : CollatzResearch.WordTrace tailWord_632270 prefixEnd_632270 324658413418346474417249 := by
  unfold tailWord_632270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882597677425155995516783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15373854279600831976089509 2882597677425155995516783)
  ·
    refine ⟨4323896516137733993275175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882597677425155995516783 4323896516137733993275175)
    ·
      refine ⟨6485844774206600989912763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323896516137733993275175 6485844774206600989912763)
      ·
        refine ⟨9728767161309901484869145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6485844774206600989912763 9728767161309901484869145)
        ·
          refine ⟨7296575370982426113651859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9728767161309901484869145 7296575370982426113651859)
          ·
            refine ⟨10944863056473639170477789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7296575370982426113651859 10944863056473639170477789)
            ·
              refine ⟨4104323646177614688929171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10944863056473639170477789 4104323646177614688929171)
              ·
                refine ⟨6156485469266422033393757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104323646177614688929171 6156485469266422033393757)
                ·
                  refine ⟨2308682050974908262522659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6156485469266422033393757 2308682050974908262522659)
                  ·
                    refine ⟨3463023076462362393783989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2308682050974908262522659 3463023076462362393783989)
                    ·
                      refine ⟨324658413418346474417249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3463023076462362393783989 324658413418346474417249)
                      ·
                        rfl

theorem cell23_632270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_632270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632270 prefixEnd_632270 := by exact prefixLift 632270
  have htrace : WordTrace (prefixWord ++ tailWord_632270) baseStart_632270 baseEnd_632270 := by
    simpa [prefixWord, tailWord_632270, baseEnd_632270] using wordTrace_append hprefix tailTrace_632270
  have hstable : (prefixWord ++ tailWord_632270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632270).length < 2 ^ (prefixWord ++ tailWord_632270).sum := by decide
  have hdescent : baseEnd_632270 < baseStart_632270 := by decide
  rcases family_descends (prefixWord ++ tailWord_632270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632283 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7]
def baseStart_632283 : Nat := 118140960795 + 632283 * 2 ^ 59
def prefixEnd_632283 : Nat := 4983230072969 + 3 ^ 40 * 632283 * 2
def baseEnd_632283 : Nat := 324665088666854923554689

theorem tailTrace_632283 : CollatzResearch.WordTrace tailWord_632283 prefixEnd_632283 324665088666854923554689 := by
  unfold tailWord_632283
  simp only [CollatzResearch.WordTrace]
  refine ⟨23061255568354151184357503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15374170378902767456238335 23061255568354151184357503)
  ·
    refine ⟨34591883352531226776536255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23061255568354151184357503 34591883352531226776536255)
    ·
      refine ⟨51887825028796840164804383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34591883352531226776536255 51887825028796840164804383)
      ·
        refine ⟨77831737543195260247206575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51887825028796840164804383 77831737543195260247206575)
        ·
          refine ⟨116747606314792890370809863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77831737543195260247206575 116747606314792890370809863)
          ·
            refine ⟨175121409472189335556214795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116747606314792890370809863 175121409472189335556214795)
            ·
              refine ⟨262682114208284003334322193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175121409472189335556214795 262682114208284003334322193)
              ·
                refine ⟨197011585656213002500741645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262682114208284003334322193 197011585656213002500741645)
                ·
                  refine ⟨73879344621079875937778117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197011585656213002500741645 73879344621079875937778117)
                  ·
                    refine ⟨13852377116452476738333397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73879344621079875937778117 13852377116452476738333397)
                    ·
                      refine ⟨324665088666854923554689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13852377116452476738333397 324665088666854923554689)
                      ·
                        rfl

theorem cell23_632283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_632283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632283 prefixEnd_632283 := by exact prefixLift 632283
  have htrace : WordTrace (prefixWord ++ tailWord_632283) baseStart_632283 baseEnd_632283 := by
    simpa [prefixWord, tailWord_632283, baseEnd_632283] using wordTrace_append hprefix tailTrace_632283
  have hstable : (prefixWord ++ tailWord_632283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632283).length < 2 ^ (prefixWord ++ tailWord_632283).sum := by decide
  have hdescent : baseEnd_632283 < baseStart_632283 := by decide
  rcases family_descends (prefixWord ++ tailWord_632283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632370 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_632370 : Nat := 118140960795 + 632370 * 2 ^ 59
def prefixEnd_632370 : Nat := 4983230072969 + 3 ^ 40 * 632370 * 2
def baseEnd_632370 : Nat := 324709761483796083166789

theorem tailTrace_632370 : CollatzResearch.WordTrace tailWord_632370 prefixEnd_632370 324709761483796083166789 := by
  unfold tailWord_632370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766107179759741260693641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15376285812692643361849709 5766107179759741260693641)
  ·
    refine ⟨4324580384819805945520231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5766107179759741260693641 4324580384819805945520231)
    ·
      refine ⟨6486870577229708918280347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324580384819805945520231 6486870577229708918280347)
      ·
        refine ⟨9730305865844563377420521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6486870577229708918280347 9730305865844563377420521)
        ·
          refine ⟨7297729399383422533065391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9730305865844563377420521 7297729399383422533065391)
          ·
            refine ⟨10946594099075133799598087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297729399383422533065391 10946594099075133799598087)
            ·
              refine ⟨16419891148612700699397131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946594099075133799598087 16419891148612700699397131)
              ·
                refine ⟨24629836722919051049095697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16419891148612700699397131 24629836722919051049095697)
                ·
                  refine ⟨18472377542189288286821773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24629836722919051049095697 18472377542189288286821773)
                  ·
                    refine ⟨6927141578320983107558165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18472377542189288286821773 6927141578320983107558165)
                    ·
                      refine ⟨324709761483796083166789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6927141578320983107558165 324709761483796083166789)
                      ·
                        rfl

theorem cell23_632370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_632370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632370 prefixEnd_632370 := by exact prefixLift 632370
  have htrace : WordTrace (prefixWord ++ tailWord_632370) baseStart_632370 baseEnd_632370 := by
    simpa [prefixWord, tailWord_632370, baseEnd_632370] using wordTrace_append hprefix tailTrace_632370
  have hstable : (prefixWord ++ tailWord_632370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632370).length < 2 ^ (prefixWord ++ tailWord_632370).sum := by decide
  have hdescent : baseEnd_632370 < baseStart_632370 := by decide
  rcases family_descends (prefixWord ++ tailWord_632370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632377 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 3]
def baseStart_632377 : Nat := 118140960795 + 632377 * 2 ^ 59
def prefixEnd_632377 : Nat := 4983230072969 + 3 ^ 40 * 632377 * 2
def baseEnd_632377 : Nat := 324713355848377555779257

theorem tailTrace_632377 : CollatzResearch.WordTrace tailWord_632377 prefixEnd_632377 324713355848377555779257 := by
  unfold tailWord_632377
  simp only [CollatzResearch.WordTrace]
  refine ⟨23064684030013605238279385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15376456020009070158852923 23064684030013605238279385)
  ·
    refine ⟨17298513022510203928709539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23064684030013605238279385 17298513022510203928709539)
    ·
      refine ⟨25947769533765305893064309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17298513022510203928709539 25947769533765305893064309)
      ·
        refine ⟨2432603393790497427474779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25947769533765305893064309 2432603393790497427474779)
        ·
          refine ⟨3648905090685746141212169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432603393790497427474779 3648905090685746141212169)
          ·
            refine ⟨2736678818014309605909127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648905090685746141212169 2736678818014309605909127)
            ·
              refine ⟨4105018227021464408863691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736678818014309605909127 4105018227021464408863691)
              ·
                refine ⟨6157527340532196613295537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105018227021464408863691 6157527340532196613295537)
                ·
                  refine ⟨4618145505399147459971653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157527340532196613295537 4618145505399147459971653)
                  ·
                    refine ⟨865902282262340148744685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618145505399147459971653 865902282262340148744685)
                    ·
                      refine ⟨324713355848377555779257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 865902282262340148744685 324713355848377555779257)
                      ·
                        rfl

theorem cell23_632377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_632377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632377 prefixEnd_632377 := by exact prefixLift 632377
  have htrace : WordTrace (prefixWord ++ tailWord_632377) baseStart_632377 baseEnd_632377 := by
    simpa [prefixWord, tailWord_632377, baseEnd_632377] using wordTrace_append hprefix tailTrace_632377
  have hstable : (prefixWord ++ tailWord_632377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632377).length < 2 ^ (prefixWord ++ tailWord_632377).sum := by decide
  have hdescent : baseEnd_632377 < baseStart_632377 := by decide
  rcases family_descends (prefixWord ++ tailWord_632377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632391 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_632391 : Nat := 118140960795 + 632391 * 2 ^ 59
def prefixEnd_632391 : Nat := 4983230072969 + 3 ^ 40 * 632391 * 2
def baseEnd_632391 : Nat := 324720544577540501004193

theorem tailTrace_632391 : CollatzResearch.WordTrace tailWord_632391 prefixEnd_632391 324720544577540501004193 := by
  unfold tailWord_632391
  simp only [CollatzResearch.WordTrace]
  refine ⟨23065194651962885629289027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15376796434641923752859351 23065194651962885629289027)
  ·
    refine ⟨34597791977944328443933541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23065194651962885629289027 34597791977944328443933541)
    ·
      refine ⟨6487085995864561583237539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34597791977944328443933541 6487085995864561583237539)
      ·
        refine ⟨9730628993796842374856309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487085995864561583237539 9730628993796842374856309)
        ·
          refine ⟨912246468168453972642779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9730628993796842374856309 912246468168453972642779)
          ·
            refine ⟨1368369702252680958964169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912246468168453972642779 1368369702252680958964169)
            ·
              refine ⟨1026277276689510719223127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368369702252680958964169 1026277276689510719223127)
              ·
                refine ⟨1539415915034266078834691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026277276689510719223127 1539415915034266078834691)
                ·
                  refine ⟨2309123872551399118252037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539415915034266078834691 2309123872551399118252037)
                  ·
                    refine ⟨432960726103387334672257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309123872551399118252037 432960726103387334672257)
                    ·
                      refine ⟨324720544577540501004193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 432960726103387334672257 324720544577540501004193)
                      ·
                        rfl

theorem cell23_632391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_632391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632391 prefixEnd_632391 := by exact prefixLift 632391
  have htrace : WordTrace (prefixWord ++ tailWord_632391) baseStart_632391 baseEnd_632391 := by
    simpa [prefixWord, tailWord_632391, baseEnd_632391] using wordTrace_append hprefix tailTrace_632391
  have hstable : (prefixWord ++ tailWord_632391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632391).length < 2 ^ (prefixWord ++ tailWord_632391).sum := by decide
  have hdescent : baseEnd_632391 < baseStart_632391 := by decide
  rcases family_descends (prefixWord ++ tailWord_632391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632424 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_632424 : Nat := 118140960795 + 632424 * 2 ^ 59
def prefixEnd_632424 : Nat := 4983230072969 + 3 ^ 40 * 632424 * 2
def baseEnd_632424 : Nat := 324737489439138871891541

theorem tailTrace_632424 : CollatzResearch.WordTrace tailWord_632424 prefixEnd_632424 324737489439138871891541 := by
  unfold tailWord_632424
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533199130421666132620163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15377598840562221510160217 11533199130421666132620163)
  ·
    refine ⟨17299798695632499198930245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11533199130421666132620163 17299798695632499198930245)
    ·
      refine ⟨3243712255431093599799421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17299798695632499198930245 3243712255431093599799421)
      ·
        refine ⟨1216392095786660099924783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3243712255431093599799421 1216392095786660099924783)
        ·
          refine ⟨1824588143679990149887175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216392095786660099924783 1824588143679990149887175)
          ·
            refine ⟨2736882215519985224830763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824588143679990149887175 2736882215519985224830763)
            ·
              refine ⟨4105323323279977837246145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736882215519985224830763 4105323323279977837246145)
              ·
                refine ⟨3078992492459983377934609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4105323323279977837246145 3078992492459983377934609)
                ·
                  refine ⟨2309244369344987533450957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078992492459983377934609 2309244369344987533450957)
                  ·
                    refine ⟨865966638504370325044109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309244369344987533450957 865966638504370325044109)
                    ·
                      refine ⟨324737489439138871891541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 865966638504370325044109 324737489439138871891541)
                      ·
                        rfl

theorem cell23_632424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_632424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632424 prefixEnd_632424 := by exact prefixLift 632424
  have htrace : WordTrace (prefixWord ++ tailWord_632424) baseStart_632424 baseEnd_632424 := by
    simpa [prefixWord, tailWord_632424, baseEnd_632424] using wordTrace_append hprefix tailTrace_632424
  have hstable : (prefixWord ++ tailWord_632424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632424).length < 2 ^ (prefixWord ++ tailWord_632424).sum := by decide
  have hdescent : baseEnd_632424 < baseStart_632424 := by decide
  rcases family_descends (prefixWord ++ tailWord_632424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632440 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 4, 8]
def baseStart_632440 : Nat := 118140960795 + 632440 * 2 ^ 59
def prefixEnd_632440 : Nat := 4983230072969 + 3 ^ 40 * 632440 * 2
def baseEnd_632440 : Nat := 108248568376536936430489

theorem tailTrace_632440 : CollatzResearch.WordTrace tailWord_632440 prefixEnd_632440 108248568376536936430489 := by
  unfold tailWord_632440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533490914392683498911387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15377987885856911331881849 11533490914392683498911387)
  ·
    refine ⟨17300236371589025248367081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11533490914392683498911387 17300236371589025248367081)
    ·
      refine ⟨12975177278691768936275311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17300236371589025248367081 12975177278691768936275311)
      ·
        refine ⟨19462765918037653404412967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12975177278691768936275311 19462765918037653404412967)
        ·
          refine ⟨29194148877056480106619451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19462765918037653404412967 29194148877056480106619451)
          ·
            refine ⟨43791223315584720159929177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29194148877056480106619451 43791223315584720159929177)
            ·
              refine ⟨32843417486688540119946883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43791223315584720159929177 32843417486688540119946883)
              ·
                refine ⟨49265126230032810179920325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32843417486688540119946883 49265126230032810179920325)
                ·
                  refine ⟨9237211168131151908735061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49265126230032810179920325 9237211168131151908735061)
                  ·
                    refine ⟨108248568376536936430489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9237211168131151908735061 108248568376536936430489)
                    ·
                      rfl

theorem cell23_632440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_632440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632440 prefixEnd_632440 := by exact prefixLift 632440
  have htrace : WordTrace (prefixWord ++ tailWord_632440) baseStart_632440 baseEnd_632440 := by
    simpa [prefixWord, tailWord_632440, baseEnd_632440] using wordTrace_append hprefix tailTrace_632440
  have hstable : (prefixWord ++ tailWord_632440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632440).length < 2 ^ (prefixWord ++ tailWord_632440).sum := by decide
  have hdescent : baseEnd_632440 < baseStart_632440 := by decide
  rcases family_descends (prefixWord ++ tailWord_632440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632484 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_632484 : Nat := 118140960795 + 632484 * 2 ^ 59
def prefixEnd_632484 : Nat := 4983230072969 + 3 ^ 40 * 632484 * 2
def baseEnd_632484 : Nat := 324768298278408637141265

theorem tailTrace_632484 : CollatzResearch.WordTrace tailWord_632484 prefixEnd_632484 324768298278408637141265 := by
  unfold tailWord_632484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534293320312981256212253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15379057760417308341616337 11534293320312981256212253)
  ·
    refine ⟨4325359995117367971079595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11534293320312981256212253 4325359995117367971079595)
    ·
      refine ⟨6488039992676051956619393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325359995117367971079595 6488039992676051956619393)
      ·
        refine ⟨4866029994507038967464545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6488039992676051956619393 4866029994507038967464545)
        ·
          refine ⟨3649522495880279225598409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4866029994507038967464545 3649522495880279225598409)
          ·
            refine ⟨2737141871910209419198807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649522495880279225598409 2737141871910209419198807)
            ·
              refine ⟨4105712807865314128798211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737141871910209419198807 4105712807865314128798211)
              ·
                refine ⟨6158569211797971193197317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105712807865314128798211 6158569211797971193197317)
                ·
                  refine ⟨1154731727212119598724497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6158569211797971193197317 1154731727212119598724497)
                  ·
                    refine ⟨866048795409089699043373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1154731727212119598724497 866048795409089699043373)
                    ·
                      refine ⟨324768298278408637141265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 866048795409089699043373 324768298278408637141265)
                      ·
                        rfl

theorem cell23_632484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_632484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632484 prefixEnd_632484 := by exact prefixLift 632484
  have htrace : WordTrace (prefixWord ++ tailWord_632484) baseStart_632484 baseEnd_632484 := by
    simpa [prefixWord, tailWord_632484, baseEnd_632484] using wordTrace_append hprefix tailTrace_632484
  have hstable : (prefixWord ++ tailWord_632484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632484).length < 2 ^ (prefixWord ++ tailWord_632484).sum := by decide
  have hdescent : baseEnd_632484 < baseStart_632484 := by decide
  rcases family_descends (prefixWord ++ tailWord_632484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632488 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_632488 : Nat := 118140960795 + 632488 * 2 ^ 59
def prefixEnd_632488 : Nat := 4983230072969 + 3 ^ 40 * 632488 * 2
def baseEnd_632488 : Nat := 324770352201026621491247

theorem tailTrace_632488 : CollatzResearch.WordTrace tailWord_632488 prefixEnd_632488 324770352201026621491247 := by
  unfold tailWord_632488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534366266305735597785059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15379155021740980797046745 11534366266305735597785059)
  ·
    refine ⟨17301549399458603396677589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11534366266305735597785059 17301549399458603396677589)
    ·
      refine ⟨405505064049811017109631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17301549399458603396677589 405505064049811017109631)
      ·
        refine ⟨608257596074716525664447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405505064049811017109631 608257596074716525664447)
        ·
          refine ⟨912386394112074788496671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608257596074716525664447 912386394112074788496671)
          ·
            refine ⟨1368579591168112182745007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912386394112074788496671 1368579591168112182745007)
            ·
              refine ⟨2052869386752168274117511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368579591168112182745007 2052869386752168274117511)
              ·
                refine ⟨3079304080128252411176267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052869386752168274117511 3079304080128252411176267)
                ·
                  refine ⟨4618956120192378616764401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079304080128252411176267 4618956120192378616764401)
                  ·
                    refine ⟨3464217090144283962573301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4618956120192378616764401 3464217090144283962573301)
                    ·
                      refine ⟨324770352201026621491247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3464217090144283962573301 324770352201026621491247)
                      ·
                        rfl

theorem cell23_632488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_632488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632488 prefixEnd_632488 := by exact prefixLift 632488
  have htrace : WordTrace (prefixWord ++ tailWord_632488) baseStart_632488 baseEnd_632488 := by
    simpa [prefixWord, tailWord_632488, baseEnd_632488] using wordTrace_append hprefix tailTrace_632488
  have hstable : (prefixWord ++ tailWord_632488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632488).length < 2 ^ (prefixWord ++ tailWord_632488).sum := by decide
  have hdescent : baseEnd_632488 < baseStart_632488 := by decide
  rcases family_descends (prefixWord ++ tailWord_632488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632517 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_632517 : Nat := 118140960795 + 632517 * 2 ^ 59
def prefixEnd_632517 : Nat := 4983230072969 + 3 ^ 40 * 632517 * 2
def baseEnd_632517 : Nat := 108261747713335669342871

theorem tailTrace_632517 : CollatzResearch.WordTrace tailWord_632517 prefixEnd_632517 108261747713335669342871 := by
  unfold tailWord_632517
  simp only [CollatzResearch.WordTrace]
  refine ⟨23069790249506409148375805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15379860166337606098917203 23069790249506409148375805)
  ·
    refine ⟨8651171343564903430640927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23069790249506409148375805 8651171343564903430640927)
    ·
      refine ⟨12976757015347355145961391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8651171343564903430640927 12976757015347355145961391)
      ·
        refine ⟨19465135523021032718942087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12976757015347355145961391 19465135523021032718942087)
        ·
          refine ⟨29197703284531549078413131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19465135523021032718942087 29197703284531549078413131)
          ·
            refine ⟨43796554926797323617619697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29197703284531549078413131 43796554926797323617619697)
            ·
              refine ⟨32847416195097992713214773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43796554926797323617619697 32847416195097992713214773)
              ·
                refine ⟨3079445268290436816863885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32847416195097992713214773 3079445268290436816863885)
                ·
                  refine ⟨1154791975608913806323957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3079445268290436816863885 1154791975608913806323957)
                  ·
                    refine ⟨108261747713335669342871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1154791975608913806323957 108261747713335669342871)
                    ·
                      rfl

theorem cell23_632517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_632517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632517 prefixEnd_632517 := by exact prefixLift 632517
  have htrace : WordTrace (prefixWord ++ tailWord_632517) baseStart_632517 baseEnd_632517 := by
    simpa [prefixWord, tailWord_632517, baseEnd_632517] using wordTrace_append hprefix tailTrace_632517
  have hstable : (prefixWord ++ tailWord_632517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632517).length < 2 ^ (prefixWord ++ tailWord_632517).sum := by decide
  have hdescent : baseEnd_632517 < baseStart_632517 := by decide
  rcases family_descends (prefixWord ++ tailWord_632517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632548 : List Nat := [2, 3, 1, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_632548 : Nat := 118140960795 + 632548 * 2 ^ 59
def prefixEnd_632548 : Nat := 4983230072969 + 3 ^ 40 * 632548 * 2
def baseEnd_632548 : Nat := 324801161040296386740971

theorem tailTrace_632548 : CollatzResearch.WordTrace tailWord_632548 prefixEnd_632548 324801161040296386740971 := by
  unfold tailWord_632548
  simp only [CollatzResearch.WordTrace]
  refine ⟨11535460456197050721377149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15380613941596067628502865 11535460456197050721377149)
  ·
    refine ⟨4325797671073894020516431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11535460456197050721377149 4325797671073894020516431)
    ·
      refine ⟨6488696506610841030774647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325797671073894020516431 6488696506610841030774647)
      ·
        refine ⟨9733044759916261546161971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488696506610841030774647 9733044759916261546161971)
        ·
          refine ⟨14599567139874392319242957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9733044759916261546161971 14599567139874392319242957)
          ·
            refine ⟨5474837677452897119716109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14599567139874392319242957 5474837677452897119716109)
            ·
              refine ⟨2053064129044836419893541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5474837677452897119716109 2053064129044836419893541)
              ·
                refine ⟨384949524195906828730039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2053064129044836419893541 384949524195906828730039)
                ·
                  refine ⟨577424286293860243095059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384949524195906828730039 577424286293860243095059)
                  ·
                    refine ⟨866136429440790364642589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 577424286293860243095059 866136429440790364642589)
                    ·
                      refine ⟨324801161040296386740971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 866136429440790364642589 324801161040296386740971)
                      ·
                        rfl

theorem cell23_632548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_632548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632548 prefixEnd_632548 := by exact prefixLift 632548
  have htrace : WordTrace (prefixWord ++ tailWord_632548) baseStart_632548 baseEnd_632548 := by
    simpa [prefixWord, tailWord_632548, baseEnd_632548] using wordTrace_append hprefix tailTrace_632548
  have hstable : (prefixWord ++ tailWord_632548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632548).length < 2 ^ (prefixWord ++ tailWord_632548).sum := by decide
  have hdescent : baseEnd_632548 < baseStart_632548 := by decide
  rcases family_descends (prefixWord ++ tailWord_632548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632554 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_632554 : Nat := 118140960795 + 632554 * 2 ^ 59
def prefixEnd_632554 : Nat := 4983230072969 + 3 ^ 40 * 632554 * 2
def baseEnd_632554 : Nat := 324804241924223363265943

theorem tailTrace_632554 : CollatzResearch.WordTrace tailWord_632554 prefixEnd_632554 324804241924223363265943 := by
  unfold tailWord_632554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5767784937593091116868179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15380759833581576311648477 5767784937593091116868179)
  ·
    refine ⟨8651677406389636675302269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5767784937593091116868179 8651677406389636675302269)
    ·
      refine ⟨3244379027396113753238351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8651677406389636675302269 3244379027396113753238351)
      ·
        refine ⟨4866568541094170629857527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3244379027396113753238351 4866568541094170629857527)
        ·
          refine ⟨7299852811641255944786291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4866568541094170629857527 7299852811641255944786291)
          ·
            refine ⟨10949779217461883917179437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7299852811641255944786291 10949779217461883917179437)
            ·
              refine ⟨4106167206548206468942289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10949779217461883917179437 4106167206548206468942289)
              ·
                refine ⟨3079625404911154851706717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106167206548206468942289 3079625404911154851706717)
                ·
                  refine ⟨1154859526841683069390019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3079625404911154851706717 1154859526841683069390019)
                  ·
                    refine ⟨1732289290262524604085029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154859526841683069390019 1732289290262524604085029)
                    ·
                      refine ⟨324804241924223363265943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1732289290262524604085029 324804241924223363265943)
                      ·
                        rfl

theorem cell23_632554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_632554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632554 prefixEnd_632554 := by exact prefixLift 632554
  have htrace : WordTrace (prefixWord ++ tailWord_632554) baseStart_632554 baseEnd_632554 := by
    simpa [prefixWord, tailWord_632554, baseEnd_632554] using wordTrace_append hprefix tailTrace_632554
  have hstable : (prefixWord ++ tailWord_632554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632554).length < 2 ^ (prefixWord ++ tailWord_632554).sum := by decide
  have hdescent : baseEnd_632554 < baseStart_632554 := by decide
  rcases family_descends (prefixWord ++ tailWord_632554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632567 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_632567 : Nat := 118140960795 + 632567 * 2 ^ 59
def prefixEnd_632567 : Nat := 4983230072969 + 3 ^ 40 * 632567 * 2
def baseEnd_632567 : Nat := 324810917172731812403383

theorem tailTrace_632567 : CollatzResearch.WordTrace tailWord_632567 prefixEnd_632567 324810917172731812403383 := by
  unfold tailWord_632567
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071613899325267687695955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15381075932883511791797303 23071613899325267687695955)
  ·
    refine ⟨34607420848987901531543933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23071613899325267687695955 34607420848987901531543933)
    ·
      refine ⟨12977782818370463074328975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34607420848987901531543933 12977782818370463074328975)
      ·
        refine ⟨19466674227555694611493463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12977782818370463074328975 19466674227555694611493463)
        ·
          refine ⟨29200011341333541917240195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19466674227555694611493463 29200011341333541917240195)
          ·
            refine ⟨43800017012000312875860293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29200011341333541917240195 43800017012000312875860293)
            ·
              refine ⟨8212503189750058664223805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43800017012000312875860293 8212503189750058664223805)
              ·
                refine ⟨3079688696156271999083927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8212503189750058664223805 3079688696156271999083927)
                ·
                  refine ⟨4619533044234407998625891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079688696156271999083927 4619533044234407998625891)
                  ·
                    refine ⟨6929299566351611997938837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4619533044234407998625891 6929299566351611997938837)
                    ·
                      refine ⟨324810917172731812403383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6929299566351611997938837 324810917172731812403383)
                      ·
                        rfl

theorem cell23_632567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_632567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632567 prefixEnd_632567 := by exact prefixLift 632567
  have htrace : WordTrace (prefixWord ++ tailWord_632567) baseStart_632567 baseEnd_632567 := by
    simpa [prefixWord, tailWord_632567, baseEnd_632567] using wordTrace_append hprefix tailTrace_632567
  have hstable : (prefixWord ++ tailWord_632567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632567).length < 2 ^ (prefixWord ++ tailWord_632567).sum := by decide
  have hdescent : baseEnd_632567 < baseStart_632567 := by decide
  rcases family_descends (prefixWord ++ tailWord_632567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632577 : List Nat := [1, 2, 4, 1, 1, 1, 2, 11]
def baseStart_632577 : Nat := 118140960795 + 632577 * 2 ^ 59
def prefixEnd_632577 : Nat := 4983230072969 + 3 ^ 40 * 632577 * 2
def baseEnd_632577 : Nat := 12030224147380621232531

theorem tailTrace_632577 : CollatzResearch.WordTrace tailWord_632577 prefixEnd_632577 12030224147380621232531 := by
  unfold tailWord_632577
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071978629289039395559985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15381319086192692930373323 23071978629289039395559985)
  ·
    refine ⟨17303983971966779546669989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23071978629289039395559985 17303983971966779546669989)
    ·
      refine ⟨3244496994743771165000623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17303983971966779546669989 3244496994743771165000623)
      ·
        refine ⟨4866745492115656747500935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3244496994743771165000623 4866745492115656747500935)
        ·
          refine ⟨7300118238173485121251403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4866745492115656747500935 7300118238173485121251403)
          ·
            refine ⟨10950177357260227681877105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7300118238173485121251403 10950177357260227681877105)
            ·
              refine ⟨8212633017945170761407829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10950177357260227681877105 8212633017945170761407829)
              ·
                refine ⟨12030224147380621232531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 8212633017945170761407829 12030224147380621232531)
                ·
                  rfl

theorem cell23_632577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 11].length) (baseStart_632577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632577 prefixEnd_632577 := by exact prefixLift 632577
  have htrace : WordTrace (prefixWord ++ tailWord_632577) baseStart_632577 baseEnd_632577 := by
    simpa [prefixWord, tailWord_632577, baseEnd_632577] using wordTrace_append hprefix tailTrace_632577
  have hstable : (prefixWord ++ tailWord_632577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632577).length < 2 ^ (prefixWord ++ tailWord_632577).sum := by decide
  have hdescent : baseEnd_632577 < baseStart_632577 := by decide
  rcases family_descends (prefixWord ++ tailWord_632577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632584 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_632584 : Nat := 118140960795 + 632584 * 2 ^ 59
def prefixEnd_632584 : Nat := 4983230072969 + 3 ^ 40 * 632584 * 2
def baseEnd_632584 : Nat := 324819646343858245890805

theorem tailTrace_632584 : CollatzResearch.WordTrace tailWord_632584 prefixEnd_632584 324819646343858245890805 := by
  unfold tailWord_632584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11536116970131839795532403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15381489293509119727376537 11536116970131839795532403)
  ·
    refine ⟨17304175455197759693298605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11536116970131839795532403 17304175455197759693298605)
    ·
      refine ⟨6489065795699159884986977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17304175455197759693298605 6489065795699159884986977)
      ·
        refine ⟨4866799346774369913740233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6489065795699159884986977 4866799346774369913740233)
        ·
          refine ⟨3650099510080777435305175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4866799346774369913740233 3650099510080777435305175)
          ·
            refine ⟨5475149265121166152957763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650099510080777435305175 5475149265121166152957763)
            ·
              refine ⟨8212723897681749229436645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5475149265121166152957763 8212723897681749229436645)
              ·
                refine ⟨1539885730815327980519371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8212723897681749229436645 1539885730815327980519371)
                ·
                  refine ⟨2309828596222991970779057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539885730815327980519371 2309828596222991970779057)
                  ·
                    refine ⟨1732371447167243978084293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2309828596222991970779057 1732371447167243978084293)
                    ·
                      refine ⟨324819646343858245890805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1732371447167243978084293 324819646343858245890805)
                      ·
                        rfl

theorem cell23_632584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_632584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632584 prefixEnd_632584 := by exact prefixLift 632584
  have htrace : WordTrace (prefixWord ++ tailWord_632584) baseStart_632584 baseEnd_632584 := by
    simpa [prefixWord, tailWord_632584, baseEnd_632584] using wordTrace_append hprefix tailTrace_632584
  have hstable : (prefixWord ++ tailWord_632584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632584).length < 2 ^ (prefixWord ++ tailWord_632584).sum := by decide
  have hdescent : baseEnd_632584 < baseStart_632584 := by decide
  rcases family_descends (prefixWord ++ tailWord_632584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632589 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 6]
def baseStart_632589 : Nat := 118140960795 + 632589 * 2 ^ 59
def prefixEnd_632589 : Nat := 4983230072969 + 3 ^ 40 * 632589 * 2
def baseEnd_632589 : Nat := 36091357083014525147587

theorem tailTrace_632589 : CollatzResearch.WordTrace tailWord_632589 prefixEnd_632589 36091357083014525147587 := by
  unfold tailWord_632589
  simp only [CollatzResearch.WordTrace]
  refine ⟨23072416305245565444996821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15381610870163710296664547 23072416305245565444996821)
  ·
    refine ⟨540759757154192940117113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 23072416305245565444996821 540759757154192940117113)
    ·
      refine ⟨405569817865644705087835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 540759757154192940117113 405569817865644705087835)
      ·
        refine ⟨608354726798467057631753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405569817865644705087835 608354726798467057631753)
        ·
          refine ⟨456266045098850293223815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608354726798467057631753 456266045098850293223815)
          ·
            refine ⟨684399067648275439835723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456266045098850293223815 684399067648275439835723)
            ·
              refine ⟨1026598601472413159753585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684399067648275439835723 1026598601472413159753585)
              ·
                refine ⟨769948951104309869815189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026598601472413159753585 769948951104309869815189)
                ·
                  refine ⟨36091357083014525147587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 769948951104309869815189 36091357083014525147587)
                  ·
                    rfl

theorem cell23_632589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_632589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632589 prefixEnd_632589 := by exact prefixLift 632589
  have htrace : WordTrace (prefixWord ++ tailWord_632589) baseStart_632589 baseEnd_632589 := by
    simpa [prefixWord, tailWord_632589, baseEnd_632589] using wordTrace_append hprefix tailTrace_632589
  have hstable : (prefixWord ++ tailWord_632589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632589).length < 2 ^ (prefixWord ++ tailWord_632589).sum := by decide
  have hdescent : baseEnd_632589 < baseStart_632589 := by decide
  rcases family_descends (prefixWord ++ tailWord_632589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632617 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_632617 : Nat := 118140960795 + 632617 * 2 ^ 59
def prefixEnd_632617 : Nat := 4983230072969 + 3 ^ 40 * 632617 * 2
def baseEnd_632617 : Nat := 324836591205456616778153

theorem tailTrace_632617 : CollatzResearch.WordTrace tailWord_632617 prefixEnd_632617 324836591205456616778153 := by
  unfold tailWord_632617
  simp only [CollatzResearch.WordTrace]
  refine ⟨23073437549144126227016105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15382291699429417484677403 23073437549144126227016105)
  ·
    refine ⟨17305078161858094670262079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23073437549144126227016105 17305078161858094670262079)
    ·
      refine ⟨25957617242787142005393119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17305078161858094670262079 25957617242787142005393119)
      ·
        refine ⟨38936425864180713008089679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25957617242787142005393119 38936425864180713008089679)
        ·
          refine ⟨58404638796271069512134519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38936425864180713008089679 58404638796271069512134519)
          ·
            refine ⟨87606958194406604268201779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58404638796271069512134519 87606958194406604268201779)
            ·
              refine ⟨131410437291609906402302669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87606958194406604268201779 131410437291609906402302669)
              ·
                refine ⟨49278913984353714900863501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131410437291609906402302669 49278913984353714900863501)
                ·
                  refine ⟨18479592744132643087823813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49278913984353714900863501 18479592744132643087823813)
                  ·
                    refine ⟨3464923639524870578966965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18479592744132643087823813 3464923639524870578966965)
                    ·
                      refine ⟨324836591205456616778153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3464923639524870578966965 324836591205456616778153)
                      ·
                        rfl

theorem cell23_632617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_632617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632617 prefixEnd_632617 := by exact prefixLift 632617
  have htrace : WordTrace (prefixWord ++ tailWord_632617) baseStart_632617 baseEnd_632617 := by
    simpa [prefixWord, tailWord_632617, baseEnd_632617] using wordTrace_append hprefix tailTrace_632617
  have hstable : (prefixWord ++ tailWord_632617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632617).length < 2 ^ (prefixWord ++ tailWord_632617).sum := by decide
  have hdescent : baseEnd_632617 < baseStart_632617 := by decide
  rcases family_descends (prefixWord ++ tailWord_632617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632628 : List Nat := [2, 5, 1, 1, 2, 3, 2, 7]
def baseStart_632628 : Nat := 118140960795 + 632628 * 2 ^ 59
def prefixEnd_632628 : Nat := 4983230072969 + 3 ^ 40 * 632628 * 2
def baseEnd_632628 : Nat := 12031194055283558286689

theorem tailTrace_632628 : CollatzResearch.WordTrace tailWord_632628 prefixEnd_632628 12031194055283558286689 := by
  unfold tailWord_632628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11536919376052137552833269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15382559168069516737111025 11536919376052137552833269)
  ·
    refine ⟨1081586191504887895578119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11536919376052137552833269 1081586191504887895578119)
    ·
      refine ⟨1622379287257331843367179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1081586191504887895578119 1622379287257331843367179)
      ·
        refine ⟨2433568930885997765050769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622379287257331843367179 2433568930885997765050769)
        ·
          refine ⟨1825176698164498323788077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433568930885997765050769 1825176698164498323788077)
          ·
            refine ⟨684441261811686871420529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1825176698164498323788077 684441261811686871420529)
            ·
              refine ⟨513330946358765153565397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684441261811686871420529 513330946358765153565397)
              ·
                refine ⟨12031194055283558286689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 513330946358765153565397 12031194055283558286689)
                ·
                  rfl

theorem cell23_632628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 7].length) (baseStart_632628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632628 prefixEnd_632628 := by exact prefixLift 632628
  have htrace : WordTrace (prefixWord ++ tailWord_632628) baseStart_632628 baseEnd_632628 := by
    simpa [prefixWord, tailWord_632628, baseEnd_632628] using wordTrace_append hprefix tailTrace_632628
  have hstable : (prefixWord ++ tailWord_632628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632628).length < 2 ^ (prefixWord ++ tailWord_632628).sum := by decide
  have hdescent : baseEnd_632628 < baseStart_632628 := by decide
  rcases family_descends (prefixWord ++ tailWord_632628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
