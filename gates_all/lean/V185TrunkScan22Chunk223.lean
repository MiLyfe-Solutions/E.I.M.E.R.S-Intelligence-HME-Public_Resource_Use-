import V185TrunkScan22Chunk222

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1988094 : List Nat := [4, 2, 2, 3, 1, 2, 2, 6]
def baseStart_1988094 : Nat := 118140960795 + 1988094 * 2 ^ 59
def prefixEnd_1988094 : Nat := 4983230072969 + 3 ^ 40 * 1988094 * 2
def baseEnd_1988094 : Nat := 75618356171840726428291

theorem tailTrace_1988094 : CollatzResearch.WordTrace tailWord_1988094 prefixEnd_1988094 75618356171840726428291 := by
  unfold tailWord_1988094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063968157435306533524417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48341163506321634845463557 9063968157435306533524417)
  ·
    refine ⟨6797976118076479900143313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9063968157435306533524417 6797976118076479900143313)
    ·
      refine ⟨5098482088557359925107485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6797976118076479900143313 5098482088557359925107485)
      ·
        refine ⟨1911930783209009971915307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5098482088557359925107485 1911930783209009971915307)
        ·
          refine ⟨2867896174813514957872961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911930783209009971915307 2867896174813514957872961)
          ·
            refine ⟨2150922131110136218404721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2867896174813514957872961 2150922131110136218404721)
            ·
              refine ⟨1613191598332602163803541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150922131110136218404721 1613191598332602163803541)
              ·
                refine ⟨75618356171840726428291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1613191598332602163803541 75618356171840726428291)
                ·
                  rfl

theorem cell22_1988094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_1988094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988094 prefixEnd_1988094 := by exact prefixLift 1988094
  have htrace : WordTrace (prefixWord ++ tailWord_1988094) baseStart_1988094 baseEnd_1988094 := by
    simpa [prefixWord, tailWord_1988094, baseEnd_1988094] using wordTrace_append hprefix tailTrace_1988094
  have hstable : (prefixWord ++ tailWord_1988094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988094).length < 2 ^ (prefixWord ++ tailWord_1988094).sum := by decide
  have hdescent : baseEnd_1988094 < baseStart_1988094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988152 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 1, 4]
def baseStart_1988152 : Nat := 118140960795 + 1988152 * 2 ^ 59
def prefixEnd_1988152 : Nat := 4983230072969 + 3 ^ 40 * 1988152 * 2
def baseEnd_1988152 : Nat := 680585060131873719904441

theorem tailTrace_1988152 : CollatzResearch.WordTrace tailWord_1988152 prefixEnd_1988152 680585060131873719904441 := by
  unfold tailWord_1988152
  simp only [CollatzResearch.WordTrace]
  refine ⟨36256930346636164086903355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48342573795514885449204473 36256930346636164086903355)
  ·
    refine ⟨54385395519954246130355033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36256930346636164086903355 54385395519954246130355033)
    ·
      refine ⟨40789046639965684597766275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54385395519954246130355033 40789046639965684597766275)
      ·
        refine ⟨61183569959948526896649413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40789046639965684597766275 61183569959948526896649413)
        ·
          refine ⟨11471919367490348793121765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61183569959948526896649413 11471919367490348793121765)
          ·
            refine ⟨2150984881404440398710331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11471919367490348793121765 2150984881404440398710331)
            ·
              refine ⟨3226477322106660598065497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150984881404440398710331 3226477322106660598065497)
              ·
                refine ⟨2419857991579995448549123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226477322106660598065497 2419857991579995448549123)
                ·
                  refine ⟨3629786987369993172823685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419857991579995448549123 3629786987369993172823685)
                  ·
                    refine ⟨680585060131873719904441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629786987369993172823685 680585060131873719904441)
                    ·
                      rfl

theorem cell22_1988152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_1988152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988152 prefixEnd_1988152 := by exact prefixLift 1988152
  have htrace : WordTrace (prefixWord ++ tailWord_1988152) baseStart_1988152 baseEnd_1988152 := by
    simpa [prefixWord, tailWord_1988152, baseEnd_1988152] using wordTrace_append hprefix tailTrace_1988152
  have hstable : (prefixWord ++ tailWord_1988152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988152).length < 2 ^ (prefixWord ++ tailWord_1988152).sum := by decide
  have hdescent : baseEnd_1988152 < baseStart_1988152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988178 : List Nat := [3, 2, 2, 1, 2, 12]
def baseStart_1988178 : Nat := 118140960795 + 1988178 * 2 ^ 59
def prefixEnd_1988178 : Nat := 4983230072969 + 3 ^ 40 * 1988178 * 2
def baseEnd_1988178 : Nat := 8402394573619979243881

theorem tailTrace_1988178 : CollatzResearch.WordTrace tailWord_1988178 prefixEnd_1988178 8402394573619979243881 := by
  unfold tailWord_1988178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18128702247794533653563297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48343205994118756409502125 18128702247794533653563297)
  ·
    refine ⟨13596526685845900240172473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18128702247794533653563297 13596526685845900240172473)
    ·
      refine ⟨10197395014384425180129355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13596526685845900240172473 10197395014384425180129355)
      ·
        refine ⟨15296092521576637770194033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10197395014384425180129355 15296092521576637770194033)
        ·
          refine ⟨11472069391182478327645525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15296092521576637770194033 11472069391182478327645525)
          ·
            refine ⟨8402394573619979243881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11472069391182478327645525 8402394573619979243881)
            ·
              rfl

theorem cell22_1988178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 12].length) (baseStart_1988178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988178 prefixEnd_1988178 := by exact prefixLift 1988178
  have htrace : WordTrace (prefixWord ++ tailWord_1988178) baseStart_1988178 baseEnd_1988178 := by
    simpa [prefixWord, tailWord_1988178, baseEnd_1988178] using wordTrace_append hprefix tailTrace_1988178
  have hstable : (prefixWord ++ tailWord_1988178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988178).length < 2 ^ (prefixWord ++ tailWord_1988178).sum := by decide
  have hdescent : baseEnd_1988178 < baseStart_1988178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988180 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1988180 : Nat := 118140960795 + 1988180 * 2 ^ 59
def prefixEnd_1988180 : Nat := 4983230072969 + 3 ^ 40 * 1988180 * 2
def baseEnd_1988180 : Nat := 680594645104090980204355

theorem tailTrace_1988180 : CollatzResearch.WordTrace tailWord_1988180 prefixEnd_1988180 680594645104090980204355 := by
  unfold tailWord_1988180
  simp only [CollatzResearch.WordTrace]
  refine ⟨36257440968585444477912997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48343254624780592637217329 36257440968585444477912997)
  ·
    refine ⟨6798270181609770839608687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36257440968585444477912997 6798270181609770839608687)
    ·
      refine ⟨10197405272414656259413031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6798270181609770839608687 10197405272414656259413031)
      ·
        refine ⟨15296107908621984389119547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10197405272414656259413031 15296107908621984389119547)
        ·
          refine ⟨22944161862932976583679321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15296107908621984389119547 22944161862932976583679321)
          ·
            refine ⟨17208121397199732437759491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22944161862932976583679321 17208121397199732437759491)
            ·
              refine ⟨25812182095799598656639237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17208121397199732437759491 25812182095799598656639237)
              ·
                refine ⟨4839784142962424748119857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25812182095799598656639237 4839784142962424748119857)
                ·
                  refine ⟨3629838107221818561089893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839784142962424748119857 3629838107221818561089893)
                  ·
                    refine ⟨680594645104090980204355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629838107221818561089893 680594645104090980204355)
                    ·
                      rfl

theorem cell22_1988180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1988180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988180 prefixEnd_1988180 := by exact prefixLift 1988180
  have htrace : WordTrace (prefixWord ++ tailWord_1988180) baseStart_1988180 baseEnd_1988180 := by
    simpa [prefixWord, tailWord_1988180, baseEnd_1988180] using wordTrace_append hprefix tailTrace_1988180
  have hstable : (prefixWord ++ tailWord_1988180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988180).length < 2 ^ (prefixWord ++ tailWord_1988180).sum := by decide
  have hdescent : baseEnd_1988180 < baseStart_1988180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988195 : List Nat := [1, 1, 1, 5, 1, 5, 1, 7]
def baseStart_1988195 : Nat := 118140960795 + 1988195 * 2 ^ 59
def prefixEnd_1988195 : Nat := 4983230072969 + 3 ^ 40 * 1988195 * 2
def baseEnd_1988195 : Nat := 75622197767848437897701

theorem tailTrace_1988195 : CollatzResearch.WordTrace tailWord_1988195 prefixEnd_1988195 75622197767848437897701 := by
  unfold tailWord_1988195
  simp only [CollatzResearch.WordTrace]
  refine ⟨72515429032116546517622039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48343619354744364345081359 72515429032116546517622039)
  ·
    refine ⟨108773143548174819776433059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72515429032116546517622039 108773143548174819776433059)
    ·
      refine ⟨163159715322262229664649589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108773143548174819776433059 163159715322262229664649589)
      ·
        refine ⟨15296223311462084031060899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163159715322262229664649589 15296223311462084031060899)
        ·
          refine ⟨22944334967193126046591349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15296223311462084031060899 22944334967193126046591349)
          ·
            refine ⟨2151031403174355566867939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22944334967193126046591349 2151031403174355566867939)
            ·
              refine ⟨3226547104761533350301909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151031403174355566867939 3226547104761533350301909)
              ·
                refine ⟨75622197767848437897701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3226547104761533350301909 75622197767848437897701)
                ·
                  rfl

theorem cell22_1988195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 7].length) (baseStart_1988195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988195 prefixEnd_1988195 := by exact prefixLift 1988195
  have htrace : WordTrace (prefixWord ++ tailWord_1988195) baseStart_1988195 baseEnd_1988195 := by
    simpa [prefixWord, tailWord_1988195, baseEnd_1988195] using wordTrace_append hprefix tailTrace_1988195
  have hstable : (prefixWord ++ tailWord_1988195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988195).length < 2 ^ (prefixWord ++ tailWord_1988195).sum := by decide
  have hdescent : baseEnd_1988195 < baseStart_1988195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988214 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_1988214 : Nat := 118140960795 + 1988214 * 2 ^ 59
def prefixEnd_1988214 : Nat := 4983230072969 + 3 ^ 40 * 1988214 * 2
def baseEnd_1988214 : Nat := 680606283998926224854251

theorem tailTrace_1988214 : CollatzResearch.WordTrace tailWord_1988214 prefixEnd_1988214 680606283998926224854251 := by
  unfold tailWord_1988214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532257626190482047660231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48344081346031808508375797 4532257626190482047660231)
  ·
    refine ⟨6798386439285723071490347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4532257626190482047660231 6798386439285723071490347)
    ·
      refine ⟨10197579658928584607235521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6798386439285723071490347 10197579658928584607235521)
      ·
        refine ⟨7648184744196438455426641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10197579658928584607235521 7648184744196438455426641)
        ·
          refine ⟨5736138558147328841569981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7648184744196438455426641 5736138558147328841569981)
          ·
            refine ⟨2151051959305248315588743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5736138558147328841569981 2151051959305248315588743)
            ·
              refine ⟨3226577938957872473383115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151051959305248315588743 3226577938957872473383115)
              ·
                refine ⟨4839866908436808710074673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226577938957872473383115 4839866908436808710074673)
                ·
                  refine ⟨3629900181327606532556005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4839866908436808710074673 3629900181327606532556005)
                  ·
                    refine ⟨680606283998926224854251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629900181327606532556005 680606283998926224854251)
                    ·
                      rfl

theorem cell22_1988214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_1988214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988214 prefixEnd_1988214 := by exact prefixLift 1988214
  have htrace : WordTrace (prefixWord ++ tailWord_1988214) baseStart_1988214 baseEnd_1988214 := by
    simpa [prefixWord, tailWord_1988214, baseEnd_1988214] using wordTrace_append hprefix tailTrace_1988214
  have hstable : (prefixWord ++ tailWord_1988214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988214).length < 2 ^ (prefixWord ++ tailWord_1988214).sum := by decide
  have hdescent : baseEnd_1988214 < baseStart_1988214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988278 : List Nat := [5, 1, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1988278 : Nat := 118140960795 + 1988278 * 2 ^ 59
def prefixEnd_1988278 : Nat := 4983230072969 + 3 ^ 40 * 1988278 * 2
def baseEnd_1988278 : Nat := 680628192506851391254055

theorem tailTrace_1988278 : CollatzResearch.WordTrace tailWord_1988278 prefixEnd_1988278 680628192506851391254055 := by
  unfold tailWord_1988278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532403518175990730805843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48345637527210567795262325 4532403518175990730805843)
  ·
    refine ⟨6798605277263986096208765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4532403518175990730805843 6798605277263986096208765)
    ·
      refine ⟨2549476978973994786078287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6798605277263986096208765 2549476978973994786078287)
      ·
        refine ⟨3824215468460992179117431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549476978973994786078287 3824215468460992179117431)
        ·
          refine ⟨5736323202691488268676147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3824215468460992179117431 5736323202691488268676147)
          ·
            refine ⟨8604484804037232403014221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736323202691488268676147 8604484804037232403014221)
            ·
              refine ⟨3226681801513962151130333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8604484804037232403014221 3226681801513962151130333)
              ·
                refine ⟨1210005675567735806673875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226681801513962151130333 1210005675567735806673875)
                ·
                  refine ⟨1815008513351603710010813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210005675567735806673875 1815008513351603710010813)
                  ·
                    refine ⟨680628192506851391254055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815008513351603710010813 680628192506851391254055)
                    ·
                      rfl

theorem cell22_1988278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1988278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988278 prefixEnd_1988278 := by exact prefixLift 1988278
  have htrace : WordTrace (prefixWord ++ tailWord_1988278) baseStart_1988278 baseEnd_1988278 := by
    simpa [prefixWord, tailWord_1988278, baseEnd_1988278] using wordTrace_append hprefix tailTrace_1988278
  have hstable : (prefixWord ++ tailWord_1988278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988278).length < 2 ^ (prefixWord ++ tailWord_1988278).sum := by decide
  have hdescent : baseEnd_1988278 < baseStart_1988278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988321 : List Nat := [1, 2, 3, 1, 6, 1, 1, 2, 1, 4]
def baseStart_1988321 : Nat := 118140960795 + 1988321 * 2 ^ 59
def prefixEnd_1988321 : Nat := 4983230072969 + 3 ^ 40 * 1988321 * 2
def baseEnd_1988321 : Nat := 680642912285613612428923

theorem tailTrace_1988321 : CollatzResearch.WordTrace tailWord_1988321 prefixEnd_1988321 680642912285613612428923 := by
  unfold tailWord_1988321
  simp only [CollatzResearch.WordTrace]
  refine ⟨72520024629660070036708817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48346683086440046691139211 72520024629660070036708817)
  ·
    refine ⟨54390018472245052527531613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72520024629660070036708817 54390018472245052527531613)
    ·
      refine ⟨20396256927091894697824355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54390018472245052527531613 20396256927091894697824355)
      ·
        refine ⟨30594385390637842046736533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20396256927091894697824355 30594385390637842046736533)
        ·
          refine ⟨1434111815186148845940775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30594385390637842046736533 1434111815186148845940775)
          ·
            refine ⟨2151167722779223268911163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434111815186148845940775 2151167722779223268911163)
            ·
              refine ⟨3226751584168834903366745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151167722779223268911163 3226751584168834903366745)
              ·
                refine ⟨2420063688126626177525059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226751584168834903366745 2420063688126626177525059)
                ·
                  refine ⟨3630095532189939266287589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420063688126626177525059 3630095532189939266287589)
                  ·
                    refine ⟨680642912285613612428923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3630095532189939266287589 680642912285613612428923)
                    ·
                      rfl

theorem cell22_1988321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_1988321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988321 prefixEnd_1988321 := by exact prefixLift 1988321
  have htrace : WordTrace (prefixWord ++ tailWord_1988321) baseStart_1988321 baseEnd_1988321 := by
    simpa [prefixWord, tailWord_1988321, baseEnd_1988321] using wordTrace_append hprefix tailTrace_1988321
  have hstable : (prefixWord ++ tailWord_1988321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988321).length < 2 ^ (prefixWord ++ tailWord_1988321).sum := by decide
  have hdescent : baseEnd_1988321 < baseStart_1988321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988330 : List Nat := [3, 1, 3, 1, 1, 1, 4, 8]
def baseStart_1988330 : Nat := 118140960795 + 1988330 * 2 ^ 59
def prefixEnd_1988330 : Nat := 4983230072969 + 3 ^ 40 * 1988330 * 2
def baseEnd_1988330 : Nat := 75627332574393398772655

theorem tailTrace_1988330 : CollatzResearch.WordTrace tailWord_1988330 prefixEnd_1988330 75627332574393398772655 := by
  unfold tailWord_1988330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18130088221656866143446611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48346901924418309715857629 18130088221656866143446611)
  ·
    refine ⟨27195132332485299215169917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18130088221656866143446611 27195132332485299215169917)
    ·
      refine ⟨10198174624681987205688719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27195132332485299215169917 10198174624681987205688719)
      ·
        refine ⟨15297261937022980808533079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10198174624681987205688719 15297261937022980808533079)
        ·
          refine ⟨22945892905534471212799619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15297261937022980808533079 22945892905534471212799619)
          ·
            refine ⟨34418839358301706819199429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22945892905534471212799619 34418839358301706819199429)
            ·
              refine ⟨6453532379681570028599893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34418839358301706819199429 6453532379681570028599893)
              ·
                refine ⟨75627332574393398772655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6453532379681570028599893 75627332574393398772655)
                ·
                  rfl

theorem cell22_1988330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_1988330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988330 prefixEnd_1988330 := by exact prefixLift 1988330
  have htrace : WordTrace (prefixWord ++ tailWord_1988330) baseStart_1988330 baseEnd_1988330 := by
    simpa [prefixWord, tailWord_1988330, baseEnd_1988330] using wordTrace_append hprefix tailTrace_1988330
  have hstable : (prefixWord ++ tailWord_1988330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988330).length < 2 ^ (prefixWord ++ tailWord_1988330).sum := by decide
  have hdescent : baseEnd_1988330 < baseStart_1988330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988360 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1988360 : Nat := 118140960795 + 1988360 * 2 ^ 59
def prefixEnd_1988360 : Nat := 4983230072969 + 3 ^ 40 * 1988360 * 2
def baseEnd_1988360 : Nat := 680656262782630510703803

theorem tailTrace_1988360 : CollatzResearch.WordTrace tailWord_1988360 prefixEnd_1988360 680656262782630510703803 := by
  unfold tailWord_1988360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36260723538259389848689267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48347631384345853131585689 36260723538259389848689267)
  ·
    refine ⟨54391085307389084773033901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36260723538259389848689267 54391085307389084773033901)
    ·
      refine ⟨20396656990270906789887713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54391085307389084773033901 20396656990270906789887713)
      ·
        refine ⟨15297492742703180092415785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20396656990270906789887713 15297492742703180092415785)
        ·
          refine ⟨11473119557027385069311839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15297492742703180092415785 11473119557027385069311839)
          ·
            refine ⟨17209679335541077603967759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11473119557027385069311839 17209679335541077603967759)
            ·
              refine ⟨25814519003311616405951639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17209679335541077603967759 25814519003311616405951639)
              ·
                refine ⟨38721778504967424608927459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25814519003311616405951639 38721778504967424608927459)
                ·
                  refine ⟨58082667757451136913391189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38721778504967424608927459 58082667757451136913391189)
                  ·
                    refine ⟨680656262782630510703803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58082667757451136913391189 680656262782630510703803)
                    ·
                      rfl

theorem cell22_1988360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1988360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988360 prefixEnd_1988360 := by exact prefixLift 1988360
  have htrace : WordTrace (prefixWord ++ tailWord_1988360) baseStart_1988360 baseEnd_1988360 := by
    simpa [prefixWord, tailWord_1988360, baseEnd_1988360] using wordTrace_append hprefix tailTrace_1988360
  have hstable : (prefixWord ++ tailWord_1988360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988360).length < 2 ^ (prefixWord ++ tailWord_1988360).sum := by decide
  have hdescent : baseEnd_1988360 < baseStart_1988360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988396 : List Nat := [2, 2, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_1988396 : Nat := 118140960795 + 1988396 * 2 ^ 59
def prefixEnd_1988396 : Nat := 4983230072969 + 3 ^ 40 * 1988396 * 2
def baseEnd_1988396 : Nat := 680668586318338416803693

theorem tailTrace_1988396 : CollatzResearch.WordTrace tailWord_1988396 prefixEnd_1988396 680668586318338416803693 := by
  unfold tailWord_1988396
  simp only [CollatzResearch.WordTrace]
  refine ⟨36261380052194178922844521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48348506736258905230459361 36261380052194178922844521)
  ·
    refine ⟨27196035039145634192133391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36261380052194178922844521 27196035039145634192133391)
    ·
      refine ⟨40794052558718451288200087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27196035039145634192133391 40794052558718451288200087)
      ·
        refine ⟨61191078838077676932300131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40794052558718451288200087 61191078838077676932300131)
        ·
          refine ⟨91786618257116515398450197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61191078838077676932300131 91786618257116515398450197)
          ·
            refine ⟨4302497730802336659302353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91786618257116515398450197 4302497730802336659302353)
            ·
              refine ⟨3226873298101752494476765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302497730802336659302353 3226873298101752494476765)
              ·
                refine ⟨1210077486788157185428787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226873298101752494476765 1210077486788157185428787)
                ·
                  refine ⟨1815116230182235778143181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210077486788157185428787 1815116230182235778143181)
                  ·
                    refine ⟨680668586318338416803693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815116230182235778143181 680668586318338416803693)
                    ·
                      rfl

theorem cell22_1988396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_1988396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988396 prefixEnd_1988396 := by exact prefixLift 1988396
  have htrace : WordTrace (prefixWord ++ tailWord_1988396) baseStart_1988396 baseEnd_1988396 := by
    simpa [prefixWord, tailWord_1988396, baseEnd_1988396] using wordTrace_append hprefix tailTrace_1988396
  have hstable : (prefixWord ++ tailWord_1988396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988396).length < 2 ^ (prefixWord ++ tailWord_1988396).sum := by decide
  have hdescent : baseEnd_1988396 < baseStart_1988396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988409 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 7]
def baseStart_1988409 : Nat := 118140960795 + 1988409 * 2 ^ 59
def prefixEnd_1988409 : Nat := 4983230072969 + 3 ^ 40 * 1988409 * 2
def baseEnd_1988409 : Nat := 226891012161336905409551

theorem tailTrace_1988409 : CollatzResearch.WordTrace tailWord_1988409 prefixEnd_1988409 226891012161336905409551 := by
  unfold tailWord_1988409
  simp only [CollatzResearch.WordTrace]
  refine ⟨72523234253341261065912281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48348822835560840710608187 72523234253341261065912281)
  ·
    refine ⟨54392425690005945799434211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72523234253341261065912281 54392425690005945799434211)
    ·
      refine ⟨81588638535008918699151317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54392425690005945799434211 81588638535008918699151317)
      ·
        refine ⟨1912233715664271532011359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 81588638535008918699151317 1912233715664271532011359)
        ·
          refine ⟨2868350573496407298017039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912233715664271532011359 2868350573496407298017039)
          ·
            refine ⟨4302525860244610947025559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868350573496407298017039 4302525860244610947025559)
            ·
              refine ⟨6453788790366916420538339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302525860244610947025559 6453788790366916420538339)
              ·
                refine ⟨9680683185550374630807509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453788790366916420538339 9680683185550374630807509)
                ·
                  refine ⟨226891012161336905409551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9680683185550374630807509 226891012161336905409551)
                  ·
                    rfl

theorem cell22_1988409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_1988409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988409 prefixEnd_1988409 := by exact prefixLift 1988409
  have htrace : WordTrace (prefixWord ++ tailWord_1988409) baseStart_1988409 baseEnd_1988409 := by
    simpa [prefixWord, tailWord_1988409, baseEnd_1988409] using wordTrace_append hprefix tailTrace_1988409
  have hstable : (prefixWord ++ tailWord_1988409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988409).length < 2 ^ (prefixWord ++ tailWord_1988409).sum := by decide
  have hdescent : baseEnd_1988409 < baseStart_1988409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988437 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 6]
def baseStart_1988437 : Nat := 118140960795 + 1988437 * 2 ^ 59
def prefixEnd_1988437 : Nat := 4983230072969 + 3 ^ 40 * 1988437 * 2
def baseEnd_1988437 : Nat := 226894207152075992176189

theorem tailTrace_1988437 : CollatzResearch.WordTrace tailWord_1988437 prefixEnd_1988437 226894207152075992176189 := by
  unfold tailWord_1988437
  simp only [CollatzResearch.WordTrace]
  refine ⟨72524255497239821847931565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48349503664826547898621043 72524255497239821847931565)
  ·
    refine ⟨27196595811464933192974337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72524255497239821847931565 27196595811464933192974337)
    ·
      refine ⟨20397446858598699894730753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27196595811464933192974337 20397446858598699894730753)
      ·
        refine ⟨15298085143949024921048065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20397446858598699894730753 15298085143949024921048065)
        ·
          refine ⟨11473563857961768690786049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15298085143949024921048065 11473563857961768690786049)
          ·
            refine ⟨8605172893471326518089537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11473563857961768690786049 8605172893471326518089537)
            ·
              refine ⟨6453879670103494888567153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8605172893471326518089537 6453879670103494888567153)
              ·
                refine ⟨4840409752577621166425365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6453879670103494888567153 4840409752577621166425365)
                ·
                  refine ⟨226894207152075992176189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4840409752577621166425365 226894207152075992176189)
                  ·
                    rfl

theorem cell22_1988437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_1988437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988437 prefixEnd_1988437 := by exact prefixLift 1988437
  have htrace : WordTrace (prefixWord ++ tailWord_1988437) baseStart_1988437 baseEnd_1988437 := by
    simpa [prefixWord, tailWord_1988437, baseEnd_1988437] using wordTrace_append hprefix tailTrace_1988437
  have hstable : (prefixWord ++ tailWord_1988437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988437).length < 2 ^ (prefixWord ++ tailWord_1988437).sum := by decide
  have hdescent : baseEnd_1988437 < baseStart_1988437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988469 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1988469 : Nat := 118140960795 + 1988469 * 2 ^ 59
def prefixEnd_1988469 : Nat := 4983230072969 + 3 ^ 40 * 1988469 * 2
def baseEnd_1988469 : Nat := 680693575710190559728469

theorem tailTrace_1988469 : CollatzResearch.WordTrace tailWord_1988469 prefixEnd_1988469 680693575710190559728469 := by
  unfold tailWord_1988469
  simp only [CollatzResearch.WordTrace]
  refine ⟨72525422633123891313096461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48350281755415927542064307 72525422633123891313096461)
  ·
    refine ⟨27197033487421459242411173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72525422633123891313096461 27197033487421459242411173)
    ·
      refine ⟨5099443778891523607952095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27197033487421459242411173 5099443778891523607952095)
      ·
        refine ⟨7649165668337285411928143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099443778891523607952095 7649165668337285411928143)
        ·
          refine ⟨11473748502505928117892215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7649165668337285411928143 11473748502505928117892215)
          ·
            refine ⟨17210622753758892176838323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11473748502505928117892215 17210622753758892176838323)
            ·
              refine ⟨25815934130638338265257485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17210622753758892176838323 25815934130638338265257485)
              ·
                refine ⟨9680975298989376849471557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25815934130638338265257485 9680975298989376849471557)
                ·
                  refine ⟨1815182868560508159275917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9680975298989376849471557 1815182868560508159275917)
                  ·
                    refine ⟨680693575710190559728469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815182868560508159275917 680693575710190559728469)
                    ·
                      rfl

theorem cell22_1988469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1988469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988469 prefixEnd_1988469 := by exact prefixLift 1988469
  have htrace : WordTrace (prefixWord ++ tailWord_1988469) baseStart_1988469 baseEnd_1988469 := by
    simpa [prefixWord, tailWord_1988469, baseEnd_1988469] using wordTrace_append hprefix tailTrace_1988469
  have hstable : (prefixWord ++ tailWord_1988469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988469).length < 2 ^ (prefixWord ++ tailWord_1988469).sum := by decide
  have hdescent : baseEnd_1988469 < baseStart_1988469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988520 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1988520 : Nat := 118140960795 + 1988520 * 2 ^ 59
def prefixEnd_1988520 : Nat := 4983230072969 + 3 ^ 40 * 1988520 * 2
def baseEnd_1988520 : Nat := 680711034052443426703313

theorem tailTrace_1988520 : CollatzResearch.WordTrace tailWord_1988520 prefixEnd_1988520 680711034052443426703313 := by
  unfold tailWord_1988520
  simp only [CollatzResearch.WordTrace]
  refine ⟨36263641377969563511601507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48351521837292751348802009 36263641377969563511601507)
  ·
    refine ⟨54395462066954345267402261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36263641377969563511601507 54395462066954345267402261)
    ·
      refine ⟨2549787284388484934409481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54395462066954345267402261 2549787284388484934409481)
      ·
        refine ⟨1912340463291363700807111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2549787284388484934409481 1912340463291363700807111)
        ·
          refine ⟨2868510694937045551210667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912340463291363700807111 2868510694937045551210667)
          ·
            refine ⟨4302766042405568326816001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868510694937045551210667 4302766042405568326816001)
            ·
              refine ⟨3227074531804176245112001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302766042405568326816001 3227074531804176245112001)
              ·
                refine ⟨2420305898853132183834001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227074531804176245112001 2420305898853132183834001)
                ·
                  refine ⟨1815229424139849137875501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2420305898853132183834001 1815229424139849137875501)
                  ·
                    refine ⟨680711034052443426703313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815229424139849137875501 680711034052443426703313)
                    ·
                      rfl

theorem cell22_1988520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1988520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988520 prefixEnd_1988520 := by exact prefixLift 1988520
  have htrace : WordTrace (prefixWord ++ tailWord_1988520) baseStart_1988520 baseEnd_1988520 := by
    simpa [prefixWord, tailWord_1988520, baseEnd_1988520] using wordTrace_append hprefix tailTrace_1988520
  have hstable : (prefixWord ++ tailWord_1988520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988520).length < 2 ^ (prefixWord ++ tailWord_1988520).sum := by decide
  have hdescent : baseEnd_1988520 < baseStart_1988520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988531 : List Nat := [1, 1, 1, 2, 3, 1, 5, 4, 1, 3]
def baseStart_1988531 : Nat := 118140960795 + 1988531 * 2 ^ 59
def prefixEnd_1988531 : Nat := 4983230072969 + 3 ^ 40 * 1988531 * 2
def baseEnd_1988531 : Nat := 680714799577243064678279

theorem tailTrace_1988531 : CollatzResearch.WordTrace tailWord_1988531 prefixEnd_1988531 680714799577243064678279 := by
  unfold tailWord_1988531
  simp only [CollatzResearch.WordTrace]
  refine ⟨72527683958899275901853447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48351789305932850601235631 72527683958899275901853447)
  ·
    refine ⟨108791525938348913852780171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72527683958899275901853447 108791525938348913852780171)
    ·
      refine ⟨163187288907523370779170257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108791525938348913852780171 163187288907523370779170257)
      ·
        refine ⟨122390466680642528084377693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163187288907523370779170257 122390466680642528084377693)
        ·
          refine ⟨45896425005240948031641635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122390466680642528084377693 45896425005240948031641635)
          ·
            refine ⟨68844637507861422047462453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45896425005240948031641635 68844637507861422047462453)
            ·
              refine ⟨6454184766362008316949605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68844637507861422047462453 6454184766362008316949605)
              ·
                refine ⟨1210159643692876559428051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6454184766362008316949605 1210159643692876559428051)
                ·
                  refine ⟨1815239465539314839142077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210159643692876559428051 1815239465539314839142077)
                  ·
                    refine ⟨680714799577243064678279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815239465539314839142077 680714799577243064678279)
                    ·
                      rfl

theorem cell22_1988531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 1, 3].length) (baseStart_1988531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988531 prefixEnd_1988531 := by exact prefixLift 1988531
  have htrace : WordTrace (prefixWord ++ tailWord_1988531) baseStart_1988531 baseEnd_1988531 := by
    simpa [prefixWord, tailWord_1988531, baseEnd_1988531] using wordTrace_append hprefix tailTrace_1988531
  have hstable : (prefixWord ++ tailWord_1988531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988531).length < 2 ^ (prefixWord ++ tailWord_1988531).sum := by decide
  have hdescent : baseEnd_1988531 < baseStart_1988531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988587 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 3, 5]
def baseStart_1988587 : Nat := 118140960795 + 1988587 * 2 ^ 59
def prefixEnd_1988587 : Nat := 4983230072969 + 3 ^ 40 * 1988587 * 2
def baseEnd_1988587 : Nat := 680733969521677585278107

theorem tailTrace_1988587 : CollatzResearch.WordTrace tailWord_1988587 prefixEnd_1988587 680733969521677585278107 := by
  unfold tailWord_1988587
  simp only [CollatzResearch.WordTrace]
  refine ⟨72529726446696397465892015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48353150964464264977261343 72529726446696397465892015)
  ·
    refine ⟨108794589670044596198838023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72529726446696397465892015 108794589670044596198838023)
    ·
      refine ⟨163191884505066894298257035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108794589670044596198838023 163191884505066894298257035)
      ·
        refine ⟨244787826757600341447385553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163191884505066894298257035 244787826757600341447385553)
        ·
          refine ⟨183590870068200256085539165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244787826757600341447385553 183590870068200256085539165)
          ·
            refine ⟨68846576275575096032077187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183590870068200256085539165 68846576275575096032077187)
            ·
              refine ⟨103269864413362644048115781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68846576275575096032077187 103269864413362644048115781)
              ·
                refine ⟨19363099577505495759021709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103269864413362644048115781 19363099577505495759021709)
                ·
                  refine ⟨7261162341564560909633141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19363099577505495759021709 7261162341564560909633141)
                  ·
                    refine ⟨680733969521677585278107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7261162341564560909633141 680733969521677585278107)
                    ·
                      rfl

theorem cell22_1988587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_1988587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988587 prefixEnd_1988587 := by exact prefixLift 1988587
  have htrace : WordTrace (prefixWord ++ tailWord_1988587) baseStart_1988587 baseEnd_1988587 := by
    simpa [prefixWord, tailWord_1988587, baseEnd_1988587] using wordTrace_append hprefix tailTrace_1988587
  have hstable : (prefixWord ++ tailWord_1988587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988587).length < 2 ^ (prefixWord ++ tailWord_1988587).sum := by decide
  have hdescent : baseEnd_1988587 < baseStart_1988587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988606 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1988606 : Nat := 118140960795 + 1988606 * 2 ^ 59
def prefixEnd_1988606 : Nat := 4983230072969 + 3 ^ 40 * 1988606 * 2
def baseEnd_1988606 : Nat := 226913491203322623017683

theorem tailTrace_1988606 : CollatzResearch.WordTrace tailWord_1988606 prefixEnd_1988606 226913491203322623017683 := by
  unfold tailWord_1988606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066302429203445463854209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48353612955751709140555781 9066302429203445463854209)
  ·
    refine ⟨6799726821902584097890657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9066302429203445463854209 6799726821902584097890657)
    ·
      refine ⟨5099795116426938073417993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6799726821902584097890657 5099795116426938073417993)
      ·
        refine ⟨3824846337320203555063495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5099795116426938073417993 3824846337320203555063495)
        ·
          refine ⟨5737269505980305332595243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3824846337320203555063495 5737269505980305332595243)
          ·
            refine ⟨8605904258970457998892865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737269505980305332595243 8605904258970457998892865)
            ·
              refine ⟨6454428194227843499169649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8605904258970457998892865 6454428194227843499169649)
              ·
                refine ⟨4840821145670882624377237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6454428194227843499169649 4840821145670882624377237)
                ·
                  refine ⟨226913491203322623017683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4840821145670882624377237 226913491203322623017683)
                  ·
                    rfl

theorem cell22_1988606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1988606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988606 prefixEnd_1988606 := by exact prefixLift 1988606
  have htrace : WordTrace (prefixWord ++ tailWord_1988606) baseStart_1988606 baseEnd_1988606 := by
    simpa [prefixWord, tailWord_1988606, baseEnd_1988606] using wordTrace_append hprefix tailTrace_1988606
  have hstable : (prefixWord ++ tailWord_1988606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988606).length < 2 ^ (prefixWord ++ tailWord_1988606).sum := by decide
  have hdescent : baseEnd_1988606 < baseStart_1988606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988619 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 2, 4]
def baseStart_1988619 : Nat := 118140960795 + 1988619 * 2 ^ 59
def prefixEnd_1988619 : Nat := 4983230072969 + 3 ^ 40 * 1988619 * 2
def baseEnd_1988619 : Nat := 680744923775640168478009

theorem tailTrace_1988619 : CollatzResearch.WordTrace tailWord_1988619 prefixEnd_1988619 680744923775640168478009 := by
  unfold tailWord_1988619
  simp only [CollatzResearch.WordTrace]
  refine ⟨72530893582580466931056911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48353929055053644620704607 72530893582580466931056911)
  ·
    refine ⟨108796340373870700396585367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72530893582580466931056911 108796340373870700396585367)
    ·
      refine ⟨163194510560806050594878051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108796340373870700396585367 163194510560806050594878051)
      ·
        refine ⟨244791765841209075892317077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163194510560806050594878051 244791765841209075892317077)
        ·
          refine ⟨11474614023806675432452363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244791765841209075892317077 11474614023806675432452363)
          ·
            refine ⟨17211921035710013148678545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11474614023806675432452363 17211921035710013148678545)
            ·
              refine ⟨12908940776782509861508909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17211921035710013148678545 12908940776782509861508909)
              ·
                refine ⟨4840852791293441198065841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12908940776782509861508909 4840852791293441198065841)
                ·
                  refine ⟨3630639593470080898549381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4840852791293441198065841 3630639593470080898549381)
                  ·
                    refine ⟨680744923775640168478009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3630639593470080898549381 680744923775640168478009)
                    ·
                      rfl

theorem cell22_1988619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_1988619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988619 prefixEnd_1988619 := by exact prefixLift 1988619
  have htrace : WordTrace (prefixWord ++ tailWord_1988619) baseStart_1988619 baseEnd_1988619 := by
    simpa [prefixWord, tailWord_1988619, baseEnd_1988619] using wordTrace_append hprefix tailTrace_1988619
  have hstable : (prefixWord ++ tailWord_1988619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988619).length < 2 ^ (prefixWord ++ tailWord_1988619).sum := by decide
  have hdescent : baseEnd_1988619 < baseStart_1988619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988634 : List Nat := [3, 1, 1, 3, 1, 5, 8]
def baseStart_1988634 : Nat := 118140960795 + 1988634 * 2 ^ 59
def prefixEnd_1988634 : Nat := 4983230072969 + 3 ^ 40 * 1988634 * 2
def baseEnd_1988634 : Nat := 25212965132673523309369

theorem tailTrace_1988634 : CollatzResearch.WordTrace tailWord_1988634 prefixEnd_1988634 25212965132673523309369 := by
  unfold tailWord_1988634
  simp only [CollatzResearch.WordTrace]
  refine ⟨18132860169381531123213239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48354293785017416328568637 18132860169381531123213239)
  ·
    refine ⟨27199290254072296684819859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18132860169381531123213239 27199290254072296684819859)
    ·
      refine ⟨40798935381108445027229789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27199290254072296684819859 40798935381108445027229789)
      ·
        refine ⟨15299600767915666885211171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40798935381108445027229789 15299600767915666885211171)
        ·
          refine ⟨22949401151873500327816757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15299600767915666885211171 22949401151873500327816757)
          ·
            refine ⟨2151506357988140655732821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22949401151873500327816757 2151506357988140655732821)
            ·
              refine ⟨25212965132673523309369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2151506357988140655732821 25212965132673523309369)
              ·
                rfl

theorem cell22_1988634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 8].length) (baseStart_1988634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988634 prefixEnd_1988634 := by exact prefixLift 1988634
  have htrace : WordTrace (prefixWord ++ tailWord_1988634) baseStart_1988634 baseEnd_1988634 := by
    simpa [prefixWord, tailWord_1988634, baseEnd_1988634] using wordTrace_append hprefix tailTrace_1988634
  have hstable : (prefixWord ++ tailWord_1988634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988634).length < 2 ^ (prefixWord ++ tailWord_1988634).sum := by decide
  have hdescent : baseEnd_1988634 < baseStart_1988634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988636 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1988636 : Nat := 118140960795 + 1988636 * 2 ^ 59
def prefixEnd_1988636 : Nat := 4983230072969 + 3 ^ 40 * 1988636 * 2
def baseEnd_1988636 : Nat := 680750743223057790802957

theorem tailTrace_1988636 : CollatzResearch.WordTrace tailWord_1988636 prefixEnd_1988636 680750743223057790802957 := by
  unfold tailWord_1988636
  simp only [CollatzResearch.WordTrace]
  refine ⟨36265756811759439417212881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48354342415679252556283841 36265756811759439417212881)
  ·
    refine ⟨27199317608819579562909661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36265756811759439417212881 27199317608819579562909661)
    ·
      refine ⟨10199744103307342336091123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27199317608819579562909661 10199744103307342336091123)
      ·
        refine ⟨15299616154961013504136685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10199744103307342336091123 15299616154961013504136685)
        ·
          refine ⟨5737356058110380064051257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15299616154961013504136685 5737356058110380064051257)
          ·
            refine ⟨4303017043582785048038443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5737356058110380064051257 4303017043582785048038443)
            ·
              refine ⟨6454525565374177572057665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303017043582785048038443 6454525565374177572057665)
              ·
                refine ⟨4840894174030633179043249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6454525565374177572057665 4840894174030633179043249)
                ·
                  refine ⟨3630670630522974884282437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4840894174030633179043249 3630670630522974884282437)
                  ·
                    refine ⟨680750743223057790802957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3630670630522974884282437 680750743223057790802957)
                    ·
                      rfl

theorem cell22_1988636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1988636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988636 prefixEnd_1988636 := by exact prefixLift 1988636
  have htrace : WordTrace (prefixWord ++ tailWord_1988636) baseStart_1988636 baseEnd_1988636 := by
    simpa [prefixWord, tailWord_1988636, baseEnd_1988636] using wordTrace_append hprefix tailTrace_1988636
  have hstable : (prefixWord ++ tailWord_1988636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988636).length < 2 ^ (prefixWord ++ tailWord_1988636).sum := by decide
  have hdescent : baseEnd_1988636 < baseStart_1988636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988696 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 5]
def baseStart_1988696 : Nat := 118140960795 + 1988696 * 2 ^ 59
def prefixEnd_1988696 : Nat := 4983230072969 + 3 ^ 40 * 1988696 * 2
def baseEnd_1988696 : Nat := 226923760816412544767591

theorem tailTrace_1988696 : CollatzResearch.WordTrace tailWord_1988696 prefixEnd_1988696 226923760816412544767591 := by
  unfold tailWord_1988696
  simp only [CollatzResearch.WordTrace]
  refine ⟨36266851001650754540804971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48355801335534339387739961 36266851001650754540804971)
  ·
    refine ⟨54400276502476131811207457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36266851001650754540804971 54400276502476131811207457)
    ·
      refine ⟨40800207376857098858405593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54400276502476131811207457 40800207376857098858405593)
      ·
        refine ⟨30600155532642824143804195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40800207376857098858405593 30600155532642824143804195)
        ·
          refine ⟨45900233298964236215706293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30600155532642824143804195 45900233298964236215706293)
          ·
            refine ⟨4303146871777897145222465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45900233298964236215706293 4303146871777897145222465)
            ·
              refine ⟨3227360153833422858916849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4303146871777897145222465 3227360153833422858916849)
              ·
                refine ⟨2420520115375067144187637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3227360153833422858916849 2420520115375067144187637)
                ·
                  refine ⟨226923760816412544767591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2420520115375067144187637 226923760816412544767591)
                  ·
                    rfl

theorem cell22_1988696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_1988696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988696 prefixEnd_1988696 := by exact prefixLift 1988696
  have htrace : WordTrace (prefixWord ++ tailWord_1988696) baseStart_1988696 baseEnd_1988696 := by
    simpa [prefixWord, tailWord_1988696, baseEnd_1988696] using wordTrace_append hprefix tailTrace_1988696
  have hstable : (prefixWord ++ tailWord_1988696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988696).length < 2 ^ (prefixWord ++ tailWord_1988696).sum := by decide
  have hdescent : baseEnd_1988696 < baseStart_1988696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988700 : List Nat := [2, 2, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1988700 : Nat := 118140960795 + 1988700 * 2 ^ 59
def prefixEnd_1988700 : Nat := 4983230072969 + 3 ^ 40 * 1988700 * 2
def baseEnd_1988700 : Nat := 680772651730982957202761

theorem tailTrace_1988700 : CollatzResearch.WordTrace tailWord_1988700 prefixEnd_1988700 680772651730982957202761 := by
  unfold tailWord_1988700
  simp only [CollatzResearch.WordTrace]
  refine ⟨36266923947643508882377777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48355898596858011843170369 36266923947643508882377777)
  ·
    refine ⟨27200192960732631661783333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36266923947643508882377777 27200192960732631661783333)
    ·
      refine ⟨5100036180137368436584375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27200192960732631661783333 5100036180137368436584375)
      ·
        refine ⟨7650054270206052654876563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100036180137368436584375 7650054270206052654876563)
        ·
          refine ⟨11475081405309078982314845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7650054270206052654876563 11475081405309078982314845)
          ·
            refine ⟨4303155526990904618368067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11475081405309078982314845 4303155526990904618368067)
            ·
              refine ⟨6454733290486356927552101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303155526990904618368067 6454733290486356927552101)
              ·
                refine ⟨1210262491966191923916019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6454733290486356927552101 1210262491966191923916019)
                ·
                  refine ⟨1815393737949287885874029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210262491966191923916019 1815393737949287885874029)
                  ·
                    refine ⟨680772651730982957202761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815393737949287885874029 680772651730982957202761)
                    ·
                      rfl

theorem cell22_1988700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1988700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988700 prefixEnd_1988700 := by exact prefixLift 1988700
  have htrace : WordTrace (prefixWord ++ tailWord_1988700) baseStart_1988700 baseEnd_1988700 := by
    simpa [prefixWord, tailWord_1988700, baseEnd_1988700] using wordTrace_append hprefix tailTrace_1988700
  have hstable : (prefixWord ++ tailWord_1988700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988700).length < 2 ^ (prefixWord ++ tailWord_1988700).sum := by decide
  have hdescent : baseEnd_1988700 < baseStart_1988700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988702 : List Nat := [4, 4, 1, 1, 3, 1, 1, 7]
def baseStart_1988702 : Nat := 118140960795 + 1988702 * 2 ^ 59
def prefixEnd_1988702 : Nat := 4983230072969 + 3 ^ 40 * 1988702 * 2
def baseEnd_1988702 : Nat := 75641481819095068739195

theorem tailTrace_1988702 : CollatzResearch.WordTrace tailWord_1988702 prefixEnd_1988702 75641481819095068739195 := by
  unfold tailWord_1988702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066740105159971513291045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48355947227519848070885573 9066740105159971513291045)
  ·
    refine ⟨1700013769717494658742071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9066740105159971513291045 1700013769717494658742071)
    ·
      refine ⟨2550020654576241988113107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700013769717494658742071 2550020654576241988113107)
      ·
        refine ⟨3825030981864362982169661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550020654576241988113107 3825030981864362982169661)
        ·
          refine ⟨1434386618199136118313623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3825030981864362982169661 1434386618199136118313623)
          ·
            refine ⟨2151579927298704177470435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434386618199136118313623 2151579927298704177470435)
            ·
              refine ⟨3227369890948056266205653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151579927298704177470435 3227369890948056266205653)
              ·
                refine ⟨75641481819095068739195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3227369890948056266205653 75641481819095068739195)
                ·
                  rfl

theorem cell22_1988702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_1988702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988702 prefixEnd_1988702 := by exact prefixLift 1988702
  have htrace : WordTrace (prefixWord ++ tailWord_1988702) baseStart_1988702 baseEnd_1988702 := by
    simpa [prefixWord, tailWord_1988702, baseEnd_1988702] using wordTrace_append hprefix tailTrace_1988702
  have hstable : (prefixWord ++ tailWord_1988702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988702).length < 2 ^ (prefixWord ++ tailWord_1988702).sum := by decide
  have hdescent : baseEnd_1988702 < baseStart_1988702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988743 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 1, 4]
def baseStart_1988743 : Nat := 118140960795 + 1988743 * 2 ^ 59
def prefixEnd_1988743 : Nat := 4983230072969 + 3 ^ 40 * 1988743 * 2
def baseEnd_1988743 : Nat := 680787371509745178377629

theorem tailTrace_1988743 : CollatzResearch.WordTrace tailWord_1988743 prefixEnd_1988743 680787371509745178377629 := by
  unfold tailWord_1988743
  simp only [CollatzResearch.WordTrace]
  refine ⟨72535416234131236108570883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48356944156087490739047255 72535416234131236108570883)
  ·
    refine ⟨108803124351196854162856325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72535416234131236108570883 108803124351196854162856325)
    ·
      refine ⟨20400585815849410155535561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108803124351196854162856325 20400585815849410155535561)
      ·
        refine ⟨15300439361887057616651671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20400585815849410155535561 15300439361887057616651671)
        ·
          refine ⟨22950659042830586424977507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15300439361887057616651671 22950659042830586424977507)
          ·
            refine ⟨34425988564245879637466261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22950659042830586424977507 34425988564245879637466261)
            ·
              refine ⟨1613718213949025608006231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34425988564245879637466261 1613718213949025608006231)
              ·
                refine ⟨2420577320923538412009347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613718213949025608006231 2420577320923538412009347)
                ·
                  refine ⟨3630865981385307618014021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420577320923538412009347 3630865981385307618014021)
                  ·
                    refine ⟨680787371509745178377629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3630865981385307618014021 680787371509745178377629)
                    ·
                      rfl

theorem cell22_1988743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_1988743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988743 prefixEnd_1988743 := by exact prefixLift 1988743
  have htrace : WordTrace (prefixWord ++ tailWord_1988743) baseStart_1988743 baseEnd_1988743 := by
    simpa [prefixWord, tailWord_1988743, baseEnd_1988743] using wordTrace_append hprefix tailTrace_1988743
  have hstable : (prefixWord ++ tailWord_1988743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988743).length < 2 ^ (prefixWord ++ tailWord_1988743).sum := by decide
  have hdescent : baseEnd_1988743 < baseStart_1988743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988799 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 8]
def baseStart_1988799 : Nat := 118140960795 + 1988799 * 2 ^ 59
def prefixEnd_1988799 : Nat := 4983230072969 + 3 ^ 40 * 1988799 * 2
def baseEnd_1988799 : Nat := 680806541454179698977457

theorem tailTrace_1988799 : CollatzResearch.WordTrace tailWord_1988799 prefixEnd_1988799 680806541454179698977457 := by
  unfold tailWord_1988799
  simp only [CollatzResearch.WordTrace]
  refine ⟨72537458721928357672609451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48358305814618905115072967 72537458721928357672609451)
  ·
    refine ⟨108806188082892536508914177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72537458721928357672609451 108806188082892536508914177)
    ·
      refine ⟨81604641062169402381685633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108806188082892536508914177 81604641062169402381685633)
      ·
        refine ⟨61203480796627051786264225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81604641062169402381685633 61203480796627051786264225)
        ·
          refine ⟨45902610597470288839698169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61203480796627051786264225 45902610597470288839698169)
          ·
            refine ⟨34426957948102716629773627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45902610597470288839698169 34426957948102716629773627)
            ·
              refine ⟨51640436922154074944660441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34426957948102716629773627 51640436922154074944660441)
              ·
                refine ⟨38730327691615556208495331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51640436922154074944660441 38730327691615556208495331)
                ·
                  refine ⟨58095491537423334312742997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38730327691615556208495331 58095491537423334312742997)
                  ·
                    refine ⟨680806541454179698977457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58095491537423334312742997 680806541454179698977457)
                    ·
                      rfl

theorem cell22_1988799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_1988799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988799 prefixEnd_1988799 := by exact prefixLift 1988799
  have htrace : WordTrace (prefixWord ++ tailWord_1988799) baseStart_1988799 baseEnd_1988799 := by
    simpa [prefixWord, tailWord_1988799, baseEnd_1988799] using wordTrace_append hprefix tailTrace_1988799
  have hstable : (prefixWord ++ tailWord_1988799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988799).length < 2 ^ (prefixWord ++ tailWord_1988799).sum := by decide
  have hdescent : baseEnd_1988799 < baseStart_1988799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988846 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1988846 : Nat := 118140960795 + 1988846 * 2 ^ 59
def prefixEnd_1988846 : Nat := 4983230072969 + 3 ^ 40 * 1988846 * 2
def baseEnd_1988846 : Nat := 680822630514687243052313

theorem tailTrace_1988846 : CollatzResearch.WordTrace tailWord_1988846 prefixEnd_1988846 680822630514687243052313 := by
  unfold tailWord_1988846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067396619094760587446299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48359448635172056466380261 9067396619094760587446299)
  ·
    refine ⟨13601094928642140881169449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9067396619094760587446299 13601094928642140881169449)
    ·
      refine ⟨10200821196481605660877087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13601094928642140881169449 10200821196481605660877087)
      ·
        refine ⟨15301231794722408491315631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200821196481605660877087 15301231794722408491315631)
        ·
          refine ⟨22951847692083612736973447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15301231794722408491315631 22951847692083612736973447)
          ·
            refine ⟨34427771538125419105460171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22951847692083612736973447 34427771538125419105460171)
            ·
              refine ⟨51641657307188128658190257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34427771538125419105460171 51641657307188128658190257)
              ·
                refine ⟨38731242980391096493642693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51641657307188128658190257 38731242980391096493642693)
                ·
                  refine ⟨7262108058823330592558005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38731242980391096493642693 7262108058823330592558005)
                  ·
                    refine ⟨680822630514687243052313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7262108058823330592558005 680822630514687243052313)
                    ·
                      rfl

theorem cell22_1988846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1988846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988846 prefixEnd_1988846 := by exact prefixLift 1988846
  have htrace : WordTrace (prefixWord ++ tailWord_1988846) baseStart_1988846 baseEnd_1988846 := by
    simpa [prefixWord, tailWord_1988846, baseEnd_1988846] using wordTrace_append hprefix tailTrace_1988846
  have hstable : (prefixWord ++ tailWord_1988846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988846).length < 2 ^ (prefixWord ++ tailWord_1988846).sum := by decide
  have hdescent : baseEnd_1988846 < baseStart_1988846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988876 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 6]
def baseStart_1988876 : Nat := 118140960795 + 1988876 * 2 ^ 59
def prefixEnd_1988876 : Nat := 4983230072969 + 3 ^ 40 * 1988876 * 2
def baseEnd_1988876 : Nat := 226944300042592388267407

theorem tailTrace_1988876 : CollatzResearch.WordTrace tailWord_1988876 prefixEnd_1988876 226944300042592388267407 := by
  unfold tailWord_1988876
  simp only [CollatzResearch.WordTrace]
  refine ⟨36270133571324699911581241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48360178095099599882108321 36270133571324699911581241)
  ·
    refine ⟨27202600178493524933685931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36270133571324699911581241 27202600178493524933685931)
    ·
      refine ⟨40803900267740287400528897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27202600178493524933685931 40803900267740287400528897)
      ·
        refine ⟨30602925200805215550396673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40803900267740287400528897 30602925200805215550396673)
        ·
          refine ⟨22952193900603911662797505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30602925200805215550396673 22952193900603911662797505)
          ·
            refine ⟨17214145425452933747098129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22952193900603911662797505 17214145425452933747098129)
            ·
              refine ⟨12910609069089700310323597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17214145425452933747098129 12910609069089700310323597)
              ·
                refine ⟨4841478400908637616371349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12910609069089700310323597 4841478400908637616371349)
                ·
                  refine ⟨226944300042592388267407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4841478400908637616371349 226944300042592388267407)
                  ·
                    rfl

theorem cell22_1988876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_1988876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988876 prefixEnd_1988876 := by exact prefixLift 1988876
  have htrace : WordTrace (prefixWord ++ tailWord_1988876) baseStart_1988876 baseEnd_1988876 := by
    simpa [prefixWord, tailWord_1988876, baseEnd_1988876] using wordTrace_append hprefix tailTrace_1988876
  have hstable : (prefixWord ++ tailWord_1988876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988876).length < 2 ^ (prefixWord ++ tailWord_1988876).sum := by decide
  have hdescent : baseEnd_1988876 < baseStart_1988876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988891 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 1, 5]
def baseStart_1988891 : Nat := 118140960795 + 1988891 * 2 ^ 59
def prefixEnd_1988891 : Nat := 4983230072969 + 3 ^ 40 * 1988891 * 2
def baseEnd_1988891 : Nat := 680838034934322125677175

theorem tailTrace_1988891 : CollatzResearch.WordTrace tailWord_1988891 prefixEnd_1988891 680838034934322125677175 := by
  unfold tailWord_1988891
  simp only [CollatzResearch.WordTrace]
  refine ⟨72540814237595057384958527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48360542825063371589972351 72540814237595057384958527)
  ·
    refine ⟨108811221356392586077437791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72540814237595057384958527 108811221356392586077437791)
    ·
      refine ⟨163216832034588879116156687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108811221356392586077437791 163216832034588879116156687)
      ·
        refine ⟨244825248051883318674235031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163216832034588879116156687 244825248051883318674235031)
        ·
          refine ⟨367237872077824978011352547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244825248051883318674235031 367237872077824978011352547)
          ·
            refine ⟨550856808116737467017028821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367237872077824978011352547 550856808116737467017028821)
            ·
              refine ⟨12910706440236034383211613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 550856808116737467017028821 12910706440236034383211613)
              ·
                refine ⟨4841514915088512893704355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12910706440236034383211613 4841514915088512893704355)
                ·
                  refine ⟨7262272372632769340556533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4841514915088512893704355 7262272372632769340556533)
                  ·
                    refine ⟨680838034934322125677175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7262272372632769340556533 680838034934322125677175)
                    ·
                      rfl

theorem cell22_1988891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_1988891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988891 prefixEnd_1988891 := by exact prefixLift 1988891
  have htrace : WordTrace (prefixWord ++ tailWord_1988891) baseStart_1988891 baseEnd_1988891 := by
    simpa [prefixWord, tailWord_1988891, baseEnd_1988891] using wordTrace_append hprefix tailTrace_1988891
  have hstable : (prefixWord ++ tailWord_1988891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988891).length < 2 ^ (prefixWord ++ tailWord_1988891).sum := by decide
  have hdescent : baseEnd_1988891 < baseStart_1988891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989156 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1989156 : Nat := 118140960795 + 1989156 * 2 ^ 59
def prefixEnd_1989156 : Nat := 4983230072969 + 3 ^ 40 * 1989156 * 2
def baseEnd_1989156 : Nat := 680928749849949767801363

theorem tailTrace_1989156 : CollatzResearch.WordTrace tailWord_1989156 prefixEnd_1989156 680928749849949767801363 := by
  unfold tailWord_1989156
  simp only [CollatzResearch.WordTrace]
  refine ⟨36275239790817503821677661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48366986387756671762236881 36275239790817503821677661)
  ·
    refine ⟨13603214921556563933129123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36275239790817503821677661 13603214921556563933129123)
    ·
      refine ⟨20404822382334845899693685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13603214921556563933129123 20404822382334845899693685)
      ·
        refine ⟨1912952098343891803096283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20404822382334845899693685 1912952098343891803096283)
        ·
          refine ⟨2869428147515837704644425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912952098343891803096283 2869428147515837704644425)
          ·
            refine ⟨2152071110636878278483319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869428147515837704644425 2152071110636878278483319)
            ·
              refine ⟨3228106665955317417724979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152071110636878278483319 3228106665955317417724979)
              ·
                refine ⟨4842159998932976126587469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228106665955317417724979 4842159998932976126587469)
                ·
                  refine ⟨1815809999599866047470301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4842159998932976126587469 1815809999599866047470301)
                  ·
                    refine ⟨680928749849949767801363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815809999599866047470301 680928749849949767801363)
                    ·
                      rfl

theorem cell22_1989156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1989156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989156 prefixEnd_1989156 := by exact prefixLift 1989156
  have htrace : WordTrace (prefixWord ++ tailWord_1989156) baseStart_1989156 baseEnd_1989156 := by
    simpa [prefixWord, tailWord_1989156, baseEnd_1989156] using wordTrace_append hprefix tailTrace_1989156
  have hstable : (prefixWord ++ tailWord_1989156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989156).length < 2 ^ (prefixWord ++ tailWord_1989156).sum := by decide
  have hdescent : baseEnd_1989156 < baseStart_1989156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989195 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 6, 3]
def baseStart_1989195 : Nat := 118140960795 + 1989195 * 2 ^ 59
def prefixEnd_1989195 : Nat := 4983230072969 + 3 ^ 40 * 1989195 * 2
def baseEnd_1989195 : Nat := 680942100346966666076243

theorem tailTrace_1989195 : CollatzResearch.WordTrace tailWord_1989195 prefixEnd_1989195 680942100346966666076243 := by
  unfold tailWord_1989195
  simp only [CollatzResearch.WordTrace]
  refine ⟨72551902028493717304025039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48367934685662478202683359 72551902028493717304025039)
  ·
    refine ⟨108827853042740575956037559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72551902028493717304025039 108827853042740575956037559)
    ·
      refine ⟨163241779564110863934056339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108827853042740575956037559 163241779564110863934056339)
      ·
        refine ⟨244862669346166295901084509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163241779564110863934056339 244862669346166295901084509)
        ·
          refine ⟨91823501004812360962906691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244862669346166295901084509 91823501004812360962906691)
          ·
            refine ⟨137735251507218541444360037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91823501004812360962906691 137735251507218541444360037)
            ·
              refine ⟨25825359657603476520817507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137735251507218541444360037 25825359657603476520817507)
              ·
                refine ⟨38738039486405214781226261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25825359657603476520817507 38738039486405214781226261)
                ·
                  refine ⟨1815845600925244442869981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38738039486405214781226261 1815845600925244442869981)
                  ·
                    refine ⟨680942100346966666076243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815845600925244442869981 680942100346966666076243)
                    ·
                      rfl

theorem cell22_1989195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 3].length) (baseStart_1989195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989195 prefixEnd_1989195 := by exact prefixLift 1989195
  have htrace : WordTrace (prefixWord ++ tailWord_1989195) baseStart_1989195 baseEnd_1989195 := by
    simpa [prefixWord, tailWord_1989195, baseEnd_1989195] using wordTrace_append hprefix tailTrace_1989195
  have hstable : (prefixWord ++ tailWord_1989195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989195).length < 2 ^ (prefixWord ++ tailWord_1989195).sum := by decide
  have hdescent : baseEnd_1989195 < baseStart_1989195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989229 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1989229 : Nat := 118140960795 + 1989229 * 2 ^ 59
def prefixEnd_1989229 : Nat := 4983230072969 + 3 ^ 40 * 1989229 * 2
def baseEnd_1989229 : Nat := 680953739241801910726139

theorem tailTrace_1989229 : CollatzResearch.WordTrace tailWord_1989229 prefixEnd_1989229 680953739241801910726139 := by
  unfold tailWord_1989229
  simp only [CollatzResearch.WordTrace]
  refine ⟨72553142110370541110762741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48368761406913694073841827 72553142110370541110762741)
  ·
    refine ⟨6801857072847238229134007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72553142110370541110762741 6801857072847238229134007)
    ·
      refine ⟨10202785609270857343701011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6801857072847238229134007 10202785609270857343701011)
      ·
        refine ⟨15304178413906286015551517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10202785609270857343701011 15304178413906286015551517)
        ·
          refine ⟨5739066905214857255831819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15304178413906286015551517 5739066905214857255831819)
          ·
            refine ⟨8608600357822285883747729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739066905214857255831819 8608600357822285883747729)
            ·
              refine ⟨6456450268366714412810797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8608600357822285883747729 6456450268366714412810797)
              ·
                refine ⟨2421168850637517904804049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6456450268366714412810797 2421168850637517904804049)
                ·
                  refine ⟨1815876637978138428603037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2421168850637517904804049 1815876637978138428603037)
                  ·
                    refine ⟨680953739241801910726139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815876637978138428603037 680953739241801910726139)
                    ·
                      rfl

theorem cell22_1989229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1989229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989229 prefixEnd_1989229 := by exact prefixLift 1989229
  have htrace : WordTrace (prefixWord ++ tailWord_1989229) baseStart_1989229 baseEnd_1989229 := by
    simpa [prefixWord, tailWord_1989229, baseEnd_1989229] using wordTrace_append hprefix tailTrace_1989229
  have hstable : (prefixWord ++ tailWord_1989229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989229).length < 2 ^ (prefixWord ++ tailWord_1989229).sum := by decide
  have hdescent : baseEnd_1989229 < baseStart_1989229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989325 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1989325 : Nat := 118140960795 + 1989325 * 2 ^ 59
def prefixEnd_1989325 : Nat := 4983230072969 + 3 ^ 40 * 1989325 * 2
def baseEnd_1989325 : Nat := 680986602003689660325845

theorem tailTrace_1989325 : CollatzResearch.WordTrace tailWord_1989325 prefixEnd_1989325 680986602003689660325845 := by
  unfold tailWord_1989325
  simp only [CollatzResearch.WordTrace]
  refine ⟨72556643518022749506257429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48371095678681833004171619 72556643518022749506257429)
  ·
    refine ⟨3401092664907316383105817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72556643518022749506257429 3401092664907316383105817)
    ·
      refine ⟨2550819498680487287329363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3401092664907316383105817 2550819498680487287329363)
      ·
        refine ⟨3826229248020730930994045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550819498680487287329363 3826229248020730930994045)
        ·
          refine ⟨1434835968007774099122767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3826229248020730930994045 1434835968007774099122767)
          ·
            refine ⟨2152253952011661148684151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434835968007774099122767 2152253952011661148684151)
            ·
              refine ⟨3228380928017491723026227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152253952011661148684151 3228380928017491723026227)
              ·
                refine ⟨4842571392026237584539341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228380928017491723026227 4842571392026237584539341)
                ·
                  refine ⟨1815964272009839094202253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4842571392026237584539341 1815964272009839094202253)
                  ·
                    refine ⟨680986602003689660325845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815964272009839094202253 680986602003689660325845)
                    ·
                      rfl

theorem cell22_1989325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1989325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989325 prefixEnd_1989325 := by exact prefixLift 1989325
  have htrace : WordTrace (prefixWord ++ tailWord_1989325) baseStart_1989325 baseEnd_1989325 := by
    simpa [prefixWord, tailWord_1989325, baseEnd_1989325] using wordTrace_append hprefix tailTrace_1989325
  have hstable : (prefixWord ++ tailWord_1989325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989325).length < 2 ^ (prefixWord ++ tailWord_1989325).sum := by decide
  have hdescent : baseEnd_1989325 < baseStart_1989325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989360 : List Nat := [2, 1, 1, 1, 3, 1, 3, 10]
def baseStart_1989360 : Nat := 118140960795 + 1989360 * 2 ^ 59
def prefixEnd_1989360 : Nat := 4983230072969 + 3 ^ 40 * 1989360 * 2
def baseEnd_1989360 : Nat := 75666509246551248411193

theorem tailTrace_1989360 : CollatzResearch.WordTrace tailWord_1989360 prefixEnd_1989360 75666509246551248411193 := by
  unfold tailWord_1989360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36278960036447975241890767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48371946715263966989187689 36278960036447975241890767)
  ·
    refine ⟨54418440054671962862836151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36278960036447975241890767 54418440054671962862836151)
    ·
      refine ⟨81627660082007944294254227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54418440054671962862836151 81627660082007944294254227)
      ·
        refine ⟨122441490123011916441381341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81627660082007944294254227 122441490123011916441381341)
        ·
          refine ⟨45915558796129468665518003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122441490123011916441381341 45915558796129468665518003)
          ·
            refine ⟨68873338194194202998277005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45915558796129468665518003 68873338194194202998277005)
            ·
              refine ⟨25827501822822826124353877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68873338194194202998277005 25827501822822826124353877)
              ·
                refine ⟨75666509246551248411193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25827501822822826124353877 75666509246551248411193)
                ·
                  rfl

theorem cell22_1989360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_1989360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989360 prefixEnd_1989360 := by exact prefixLift 1989360
  have htrace : WordTrace (prefixWord ++ tailWord_1989360) baseStart_1989360 baseEnd_1989360 := by
    simpa [prefixWord, tailWord_1989360, baseEnd_1989360] using wordTrace_append hprefix tailTrace_1989360
  have hstable : (prefixWord ++ tailWord_1989360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989360).length < 2 ^ (prefixWord ++ tailWord_1989360).sum := by decide
  have hdescent : baseEnd_1989360 < baseStart_1989360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989383 : List Nat := [1, 1, 4, 4, 1, 3, 2, 2, 4]
def baseStart_1989383 : Nat := 118140960795 + 1989383 * 2 ^ 59
def prefixEnd_1989383 : Nat := 4983230072969 + 3 ^ 40 * 1989383 * 2
def baseEnd_1989383 : Nat := 227002152196332280791889

theorem tailTrace_1989383 : CollatzResearch.WordTrace tailWord_1989383 prefixEnd_1989383 227002152196332280791889 := by
  unfold tailWord_1989383
  simp only [CollatzResearch.WordTrace]
  refine ⟨72558758951812625411868803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48372505967875083607912535 72558758951812625411868803)
  ·
    refine ⟨108838138427718938117803205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72558758951812625411868803 108838138427718938117803205)
    ·
      refine ⟨20407150955197300897088101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108838138427718938117803205 20407150955197300897088101)
      ·
        refine ⟨3826340804099493918204019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20407150955197300897088101 3826340804099493918204019)
        ·
          refine ⟨5739511206149240877306029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826340804099493918204019 5739511206149240877306029)
          ·
            refine ⟨2152316702305965328989761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5739511206149240877306029 2152316702305965328989761)
            ·
              refine ⟨1614237526729473996742321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152316702305965328989761 1614237526729473996742321)
              ·
                refine ⟨1210678145047105497556741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614237526729473996742321 1210678145047105497556741)
                ·
                  refine ⟨227002152196332280791889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1210678145047105497556741 227002152196332280791889)
                  ·
                    rfl

theorem cell22_1989383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 4].length) (baseStart_1989383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989383 prefixEnd_1989383 := by exact prefixLift 1989383
  have htrace : WordTrace (prefixWord ++ tailWord_1989383) baseStart_1989383 baseEnd_1989383 := by
    simpa [prefixWord, tailWord_1989383, baseEnd_1989383] using wordTrace_append hprefix tailTrace_1989383
  have hstable : (prefixWord ++ tailWord_1989383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989383).length < 2 ^ (prefixWord ++ tailWord_1989383).sum := by decide
  have hdescent : baseEnd_1989383 < baseStart_1989383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989409 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1989409 : Nat := 118140960795 + 1989409 * 2 ^ 59
def prefixEnd_1989409 : Nat := 4983230072969 + 3 ^ 40 * 1989409 * 2
def baseEnd_1989409 : Nat := 681015356920341441225587

theorem tailTrace_1989409 : CollatzResearch.WordTrace tailWord_1989409 prefixEnd_1989409 681015356920341441225587 := by
  unfold tailWord_1989409
  simp only [CollatzResearch.WordTrace]
  refine ⟨72559707249718431852315281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48373138166478954568210187 72559707249718431852315281)
  ·
    refine ⟨54419780437288823889236461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72559707249718431852315281 54419780437288823889236461)
    ·
      refine ⟨20407417663983308958463673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54419780437288823889236461 20407417663983308958463673)
      ·
        refine ⟨15305563247987481718847755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20407417663983308958463673 15305563247987481718847755)
        ·
          refine ⟨22958344871981222578271633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15305563247987481718847755 22958344871981222578271633)
          ·
            refine ⟨17218758653985916933703725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22958344871981222578271633 17218758653985916933703725)
            ·
              refine ⟨6457034495244718850138897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17218758653985916933703725 6457034495244718850138897)
              ·
                refine ⟨4842775871433539137604173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6457034495244718850138897 4842775871433539137604173)
                ·
                  refine ⟨1816040951787577176601565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4842775871433539137604173 1816040951787577176601565)
                  ·
                    refine ⟨681015356920341441225587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816040951787577176601565 681015356920341441225587)
                    ·
                      rfl

theorem cell22_1989409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1989409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989409 prefixEnd_1989409 := by exact prefixLift 1989409
  have htrace : WordTrace (prefixWord ++ tailWord_1989409) baseStart_1989409 baseEnd_1989409 := by
    simpa [prefixWord, tailWord_1989409, baseEnd_1989409] using wordTrace_append hprefix tailTrace_1989409
  have hstable : (prefixWord ++ tailWord_1989409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989409).length < 2 ^ (prefixWord ++ tailWord_1989409).sum := by decide
  have hdescent : baseEnd_1989409 < baseStart_1989409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989439 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 5]
def baseStart_1989439 : Nat := 118140960795 + 1989439 * 2 ^ 59
def prefixEnd_1989439 : Nat := 4983230072969 + 3 ^ 40 * 1989439 * 2
def baseEnd_1989439 : Nat := 227008542177810454325165

theorem tailTrace_1989439 : CollatzResearch.WordTrace tailWord_1989439 prefixEnd_1989439 227008542177810454325165 := by
  unfold tailWord_1989439
  simp only [CollatzResearch.WordTrace]
  refine ⟨72560801439609746975907371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48373867626406497983938247 72560801439609746975907371)
  ·
    refine ⟨108841202159414620463861057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72560801439609746975907371 108841202159414620463861057)
    ·
      refine ⟨81630901619560965347895793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108841202159414620463861057 81630901619560965347895793)
      ·
        refine ⟨61223176214670724010921845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81630901619560965347895793 61223176214670724010921845)
        ·
          refine ⟨5739672770125380376023923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61223176214670724010921845 5739672770125380376023923)
          ·
            refine ⟨8609509155188070564035885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739672770125380376023923 8609509155188070564035885)
            ·
              refine ⟨3228565933195526461513457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8609509155188070564035885 3228565933195526461513457)
              ·
                refine ⟨2421424449896644846135093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3228565933195526461513457 2421424449896644846135093)
                ·
                  refine ⟨227008542177810454325165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2421424449896644846135093 227008542177810454325165)
                  ·
                    rfl

theorem cell22_1989439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 5].length) (baseStart_1989439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989439 prefixEnd_1989439 := by exact prefixLift 1989439
  have htrace : WordTrace (prefixWord ++ tailWord_1989439) baseStart_1989439 baseEnd_1989439 := by
    simpa [prefixWord, tailWord_1989439, baseEnd_1989439] using wordTrace_append hprefix tailTrace_1989439
  have hstable : (prefixWord ++ tailWord_1989439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989439).length < 2 ^ (prefixWord ++ tailWord_1989439).sum := by decide
  have hdescent : baseEnd_1989439 < baseStart_1989439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989499 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 4, 3]
def baseStart_1989499 : Nat := 118140960795 + 1989499 * 2 ^ 59
def prefixEnd_1989499 : Nat := 4983230072969 + 3 ^ 40 * 1989499 * 2
def baseEnd_1989499 : Nat := 681046165759611206475311

theorem tailTrace_1989499 : CollatzResearch.WordTrace tailWord_1989499 prefixEnd_1989499 681046165759611206475311 := by
  unfold tailWord_1989499
  simp only [CollatzResearch.WordTrace]
  refine ⟨72562989819392377223091551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48375326546261584815394367 72562989819392377223091551)
  ·
    refine ⟨108844484729088565834637327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72562989819392377223091551 108844484729088565834637327)
    ·
      refine ⟨163266727093632848751955991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108844484729088565834637327 163266727093632848751955991)
      ·
        refine ⟨244900090640449273127933987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163266727093632848751955991 244900090640449273127933987)
        ·
          refine ⟨367350135960673909691900981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244900090640449273127933987 367350135960673909691900981)
          ·
            refine ⟨34439075246313179033615717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 367350135960673909691900981 34439075246313179033615717)
            ·
              refine ⟨6457326608683721068802947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34439075246313179033615717 6457326608683721068802947)
              ·
                refine ⟨9685989913025581603204421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457326608683721068802947 9685989913025581603204421)
                ·
                  refine ⟨1816123108692296550600829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9685989913025581603204421 1816123108692296550600829)
                  ·
                    refine ⟨681046165759611206475311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816123108692296550600829 681046165759611206475311)
                    ·
                      rfl

theorem cell22_1989499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 3].length) (baseStart_1989499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989499 prefixEnd_1989499 := by exact prefixLift 1989499
  have htrace : WordTrace (prefixWord ++ tailWord_1989499) baseStart_1989499 baseEnd_1989499 := by
    simpa [prefixWord, tailWord_1989499, baseEnd_1989499] using wordTrace_append hprefix tailTrace_1989499
  have hstable : (prefixWord ++ tailWord_1989499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989499).length < 2 ^ (prefixWord ++ tailWord_1989499).sum := by decide
  have hdescent : baseEnd_1989499 < baseStart_1989499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989604 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1989604 : Nat := 118140960795 + 1989604 * 2 ^ 59
def prefixEnd_1989604 : Nat := 4983230072969 + 3 ^ 40 * 1989604 * 2
def baseEnd_1989604 : Nat := 681082109405425932599989

theorem tailTrace_1989604 : CollatzResearch.WordTrace tailWord_1989604 prefixEnd_1989604 681082109405425932599989 := by
  unfold tailWord_1989604
  simp only [CollatzResearch.WordTrace]
  refine ⟨36283409742005990077831933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48377879656007986770442577 36283409742005990077831933)
  ·
    refine ⟨13606278653252246279186975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36283409742005990077831933 13606278653252246279186975)
    ·
      refine ⟨20409417979878369418780463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13606278653252246279186975 20409417979878369418780463)
      ·
        refine ⟨30614126969817554128170695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409417979878369418780463 30614126969817554128170695)
        ·
          refine ⟨45921190454726331192256043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30614126969817554128170695 45921190454726331192256043)
          ·
            refine ⟨68881785682089496788384065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45921190454726331192256043 68881785682089496788384065)
            ·
              refine ⟨51661339261567122591288049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68881785682089496788384065 51661339261567122591288049)
              ·
                refine ⟨38746004446175341943466037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51661339261567122591288049 38746004446175341943466037)
                ·
                  refine ⟨3632437916828938307199941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38746004446175341943466037 3632437916828938307199941)
                  ·
                    refine ⟨681082109405425932599989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3632437916828938307199941 681082109405425932599989)
                    ·
                      rfl

theorem cell22_1989604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1989604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989604 prefixEnd_1989604 := by exact prefixLift 1989604
  have htrace : WordTrace (prefixWord ++ tailWord_1989604) baseStart_1989604 baseEnd_1989604 := by
    simpa [prefixWord, tailWord_1989604, baseEnd_1989604] using wordTrace_append hprefix tailTrace_1989604
  have hstable : (prefixWord ++ tailWord_1989604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989604).length < 2 ^ (prefixWord ++ tailWord_1989604).sum := by decide
  have hdescent : baseEnd_1989604 < baseStart_1989604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989649 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1989649 : Nat := 118140960795 + 1989649 * 2 ^ 59
def prefixEnd_1989649 : Nat := 4983230072969 + 3 ^ 40 * 1989649 * 2
def baseEnd_1989649 : Nat := 681097513825060815224851

theorem tailTrace_1989649 : CollatzResearch.WordTrace tailWord_1989649 prefixEnd_1989649 681097513825060815224851 := by
  unfold tailWord_1989649
  simp only [CollatzResearch.WordTrace]
  refine ⟨72568460768848952841052001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48378973845899301894034667 72568460768848952841052001)
  ·
    refine ⟨54426345576636714630789001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72568460768848952841052001 54426345576636714630789001)
    ·
      refine ⟨40819759182477535973091751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54426345576636714630789001 40819759182477535973091751)
      ·
        refine ⟨61229638773716303959637627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40819759182477535973091751 61229638773716303959637627)
        ·
          refine ⟨91844458160574455939456441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61229638773716303959637627 91844458160574455939456441)
          ·
            refine ⟨68883343620430841954592331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91844458160574455939456441 68883343620430841954592331)
            ·
              refine ⟨103325015430646262931888497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68883343620430841954592331 103325015430646262931888497)
              ·
                refine ⟨77493761572984697198916373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103325015430646262931888497 77493761572984697198916373)
                ·
                  refine ⟨3632520073733657681199205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77493761572984697198916373 3632520073733657681199205)
                  ·
                    refine ⟨681097513825060815224851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3632520073733657681199205 681097513825060815224851)
                    ·
                      rfl

theorem cell22_1989649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1989649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989649 prefixEnd_1989649 := by exact prefixLift 1989649
  have htrace : WordTrace (prefixWord ++ tailWord_1989649) baseStart_1989649 baseEnd_1989649 := by
    simpa [prefixWord, tailWord_1989649, baseEnd_1989649] using wordTrace_append hprefix tailTrace_1989649
  have hstable : (prefixWord ++ tailWord_1989649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989649).length < 2 ^ (prefixWord ++ tailWord_1989649).sum := by decide
  have hdescent : baseEnd_1989649 < baseStart_1989649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989653 : List Nat := [1, 3, 2, 1, 4, 1, 3, 3, 4]
def baseStart_1989653 : Nat := 118140960795 + 1989653 * 2 ^ 59
def prefixEnd_1989653 : Nat := 4983230072969 + 3 ^ 40 * 1989653 * 2
def baseEnd_1989653 : Nat := 227032961035602046041613

theorem tailTrace_1989653 : CollatzResearch.WordTrace tailWord_1989653 prefixEnd_1989653 227032961035602046041613 := by
  unfold tailWord_1989653
  simp only [CollatzResearch.WordTrace]
  refine ⟨72568606660834461524197613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48379071107222974349465075 72568606660834461524197613)
  ·
    refine ⟨27213227497812923071574105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72568606660834461524197613 27213227497812923071574105)
    ·
      refine ⟨20409920623359692303680579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27213227497812923071574105 20409920623359692303680579)
      ·
        refine ⟨30614880935039538455520869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20409920623359692303680579 30614880935039538455520869)
        ·
          refine ⟨5740290175319913460410163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30614880935039538455520869 5740290175319913460410163)
          ·
            refine ⟨8610435262979870190615245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740290175319913460410163 8610435262979870190615245)
            ·
              refine ⟨3228913223617451321480717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8610435262979870190615245 3228913223617451321480717)
              ·
                refine ⟨1210842458856544245555269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3228913223617451321480717 1210842458856544245555269)
                ·
                  refine ⟨227032961035602046041613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1210842458856544245555269 227032961035602046041613)
                  ·
                    rfl

theorem cell22_1989653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_1989653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989653 prefixEnd_1989653 := by exact prefixLift 1989653
  have htrace : WordTrace (prefixWord ++ tailWord_1989653) baseStart_1989653 baseEnd_1989653 := by
    simpa [prefixWord, tailWord_1989653, baseEnd_1989653] using wordTrace_append hprefix tailTrace_1989653
  have hstable : (prefixWord ++ tailWord_1989653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989653).length < 2 ^ (prefixWord ++ tailWord_1989653).sum := by decide
  have hdescent : baseEnd_1989653 < baseStart_1989653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989666 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1989666 : Nat := 118140960795 + 1989666 * 2 ^ 59
def prefixEnd_1989666 : Nat := 4983230072969 + 3 ^ 40 * 1989666 * 2
def baseEnd_1989666 : Nat := 681103333272478437549799

theorem tailTrace_1989666 : CollatzResearch.WordTrace tailWord_1989666 prefixEnd_1989666 681103333272478437549799 := by
  unfold tailWord_1989666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18142270202446841186105213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48379387206524909829613901 18142270202446841186105213)
  ·
    refine ⟨6803351325917565444789455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18142270202446841186105213 6803351325917565444789455)
    ·
      refine ⟨10205026988876348167184183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803351325917565444789455 10205026988876348167184183)
      ·
        refine ⟨15307540483314522250776275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205026988876348167184183 15307540483314522250776275)
        ·
          refine ⟨22961310724971783376164413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15307540483314522250776275 22961310724971783376164413)
          ·
            refine ⟨8610491521864418766061655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22961310724971783376164413 8610491521864418766061655)
            ·
              refine ⟨12915737282796628149092483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610491521864418766061655 12915737282796628149092483)
              ·
                refine ⟨19373605924194942223638725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915737282796628149092483 19373605924194942223638725)
                ·
                  refine ⟨3632551110786551666932261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19373605924194942223638725 3632551110786551666932261)
                  ·
                    refine ⟨681103333272478437549799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3632551110786551666932261 681103333272478437549799)
                    ·
                      rfl

theorem cell22_1989666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1989666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989666 prefixEnd_1989666 := by exact prefixLift 1989666
  have htrace : WordTrace (prefixWord ++ tailWord_1989666) baseStart_1989666 baseEnd_1989666 := by
    simpa [prefixWord, tailWord_1989666, baseEnd_1989666] using wordTrace_append hprefix tailTrace_1989666
  have hstable : (prefixWord ++ tailWord_1989666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989666).length < 2 ^ (prefixWord ++ tailWord_1989666).sum := by decide
  have hdescent : baseEnd_1989666 < baseStart_1989666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989668 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1989668 : Nat := 118140960795 + 1989668 * 2 ^ 59
def prefixEnd_1989668 : Nat := 4983230072969 + 3 ^ 40 * 1989668 * 2
def baseEnd_1989668 : Nat := 681104017913351098999793

theorem tailTrace_1989668 : CollatzResearch.WordTrace tailWord_1989668 prefixEnd_1989668 681104017913351098999793 := by
  unfold tailWord_1989668
  simp only [CollatzResearch.WordTrace]
  refine ⟨36284576877890059542996829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48379435837186746057329105 36284576877890059542996829)
  ·
    refine ⟨13606716329208772328623811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36284576877890059542996829 13606716329208772328623811)
    ·
      refine ⟨20410074493813158492935717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13606716329208772328623811 20410074493813158492935717)
      ·
        refine ⟨3826888967589967217425447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20410074493813158492935717 3826888967589967217425447)
        ·
          refine ⟨5740333451384950826138171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3826888967589967217425447 5740333451384950826138171)
          ·
            refine ⟨8610500177077426239207257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5740333451384950826138171 8610500177077426239207257)
            ·
              refine ⟨6457875132808069679405443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8610500177077426239207257 6457875132808069679405443)
              ·
                refine ⟨9686812699212104519108165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457875132808069679405443 9686812699212104519108165)
                ·
                  refine ⟨1816277381102269597332781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9686812699212104519108165 1816277381102269597332781)
                  ·
                    refine ⟨681104017913351098999793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816277381102269597332781 681104017913351098999793)
                    ·
                      rfl

theorem cell22_1989668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1989668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989668 prefixEnd_1989668 := by exact prefixLift 1989668
  have htrace : WordTrace (prefixWord ++ tailWord_1989668) baseStart_1989668 baseEnd_1989668 := by
    simpa [prefixWord, tailWord_1989668, baseEnd_1989668] using wordTrace_append hprefix tailTrace_1989668
  have hstable : (prefixWord ++ tailWord_1989668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989668).length < 2 ^ (prefixWord ++ tailWord_1989668).sum := by decide
  have hdescent : baseEnd_1989668 < baseStart_1989668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989696 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 5, 3]
def baseStart_1989696 : Nat := 118140960795 + 1989696 * 2 ^ 59
def prefixEnd_1989696 : Nat := 4983230072969 + 3 ^ 40 * 1989696 * 2
def baseEnd_1989696 : Nat := 681113602885568359299707

theorem tailTrace_1989696 : CollatzResearch.WordTrace tailWord_1989696 prefixEnd_1989696 681113602885568359299707 := by
  unfold tailWord_1989696
  simp only [CollatzResearch.WordTrace]
  refine ⟨36285087499839339934006471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48380116666452453245341961 36285087499839339934006471)
  ·
    refine ⟨54427631249759009901009707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36285087499839339934006471 54427631249759009901009707)
    ·
      refine ⟨81641446874638514851514561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54427631249759009901009707 81641446874638514851514561)
      ·
        refine ⟨61231085155978886138635921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81641446874638514851514561 61231085155978886138635921)
        ·
          refine ⟨45923313866984164603976941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61231085155978886138635921 45923313866984164603976941)
          ·
            refine ⟨17221242700119061726491353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45923313866984164603976941 17221242700119061726491353)
            ·
              refine ⟨12915932025089296294868515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17221242700119061726491353 12915932025089296294868515)
              ·
                refine ⟨19373898037633944442302773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12915932025089296294868515 19373898037633944442302773)
                ·
                  refine ⟨1816302941028182291465885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19373898037633944442302773 1816302941028182291465885)
                  ·
                    refine ⟨681113602885568359299707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816302941028182291465885 681113602885568359299707)
                    ·
                      rfl

theorem cell22_1989696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_1989696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989696 prefixEnd_1989696 := by exact prefixLift 1989696
  have htrace : WordTrace (prefixWord ++ tailWord_1989696) baseStart_1989696 baseEnd_1989696 := by
    simpa [prefixWord, tailWord_1989696, baseEnd_1989696] using wordTrace_append hprefix tailTrace_1989696
  have hstable : (prefixWord ++ tailWord_1989696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989696).length < 2 ^ (prefixWord ++ tailWord_1989696).sum := by decide
  have hdescent : baseEnd_1989696 < baseStart_1989696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989741 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1989741 : Nat := 118140960795 + 1989741 * 2 ^ 59
def prefixEnd_1989741 : Nat := 4983230072969 + 3 ^ 40 * 1989741 * 2
def baseEnd_1989741 : Nat := 681129007305203241924569

theorem tailTrace_1989741 : CollatzResearch.WordTrace tailWord_1989741 prefixEnd_1989741 681129007305203241924569 := by
  unfold tailWord_1989741
  simp only [CollatzResearch.WordTrace]
  refine ⟨72571816284515652553401077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48381210856343768368934051 72571816284515652553401077)
  ·
    refine ⟨6803607776673342426881351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72571816284515652553401077 6803607776673342426881351)
    ·
      refine ⟨10205411665010013640322027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803607776673342426881351 10205411665010013640322027)
      ·
        refine ⟨15308117497515020460483041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205411665010013640322027 15308117497515020460483041)
        ·
          refine ⟨11481088123136265345362281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15308117497515020460483041 11481088123136265345362281)
          ·
            refine ⟨8610816092352199009021711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11481088123136265345362281 8610816092352199009021711)
            ·
              refine ⟨12916224138528298513532567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610816092352199009021711 12916224138528298513532567)
              ·
                refine ⟨19374336207792447770298851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12916224138528298513532567 19374336207792447770298851)
                ·
                  refine ⟨29061504311688671655448277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19374336207792447770298851 29061504311688671655448277)
                  ·
                    refine ⟨681129007305203241924569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29061504311688671655448277 681129007305203241924569)
                    ·
                      rfl

theorem cell22_1989741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1989741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989741 prefixEnd_1989741 := by exact prefixLift 1989741
  have htrace : WordTrace (prefixWord ++ tailWord_1989741) baseStart_1989741 baseEnd_1989741 := by
    simpa [prefixWord, tailWord_1989741, baseEnd_1989741] using wordTrace_append hprefix tailTrace_1989741
  have hstable : (prefixWord ++ tailWord_1989741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989741).length < 2 ^ (prefixWord ++ tailWord_1989741).sum := by decide
  have hdescent : baseEnd_1989741 < baseStart_1989741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989756 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1989756 : Nat := 118140960795 + 1989756 * 2 ^ 59
def prefixEnd_1989756 : Nat := 4983230072969 + 3 ^ 40 * 1989756 * 2
def baseEnd_1989756 : Nat := 681134142111748202799523

theorem tailTrace_1989756 : CollatzResearch.WordTrace tailWord_1989756 prefixEnd_1989756 681134142111748202799523 := by
  unfold tailWord_1989756
  simp only [CollatzResearch.WordTrace]
  refine ⟨36286181689730655057598561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48381575586307540076798081 36286181689730655057598561)
  ·
    refine ⟨27214636267297991293198921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36286181689730655057598561 27214636267297991293198921)
    ·
      refine ⟨20410977200473493469899191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27214636267297991293198921 20410977200473493469899191)
      ·
        refine ⟨30616465800710240204848787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20410977200473493469899191 30616465800710240204848787)
        ·
          refine ⟨45924698701065360307273181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30616465800710240204848787 45924698701065360307273181)
          ·
            refine ⟨17221762012899510115227443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45924698701065360307273181 17221762012899510115227443)
            ·
              refine ⟨25832643019349265172841165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17221762012899510115227443 25832643019349265172841165)
              ·
                refine ⟨9687241132255974439815437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25832643019349265172841165 9687241132255974439815437)
                ·
                  refine ⟨3632715424595990414930789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9687241132255974439815437 3632715424595990414930789)
                  ·
                    refine ⟨681134142111748202799523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3632715424595990414930789 681134142111748202799523)
                    ·
                      rfl

theorem cell22_1989756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1989756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989756 prefixEnd_1989756 := by exact prefixLift 1989756
  have htrace : WordTrace (prefixWord ++ tailWord_1989756) baseStart_1989756 baseEnd_1989756 := by
    simpa [prefixWord, tailWord_1989756, baseEnd_1989756] using wordTrace_append hprefix tailTrace_1989756
  have hstable : (prefixWord ++ tailWord_1989756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989756).length < 2 ^ (prefixWord ++ tailWord_1989756).sum := by decide
  have hdescent : baseEnd_1989756 < baseStart_1989756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989788 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 6]
def baseStart_1989788 : Nat := 118140960795 + 1989788 * 2 ^ 59
def prefixEnd_1989788 : Nat := 4983230072969 + 3 ^ 40 * 1989788 * 2
def baseEnd_1989788 : Nat := 227048365455236928666475

theorem tailTrace_1989788 : CollatzResearch.WordTrace tailWord_1989788 prefixEnd_1989788 227048365455236928666475 := by
  unfold tailWord_1989788
  simp only [CollatzResearch.WordTrace]
  refine ⟨36286765257672689790181009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48382353676896919720241345 36286765257672689790181009)
  ·
    refine ⟨27215073943254517342635757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36286765257672689790181009 27215073943254517342635757)
    ·
      refine ⟨10205652728720444003488409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27215073943254517342635757 10205652728720444003488409)
      ·
        refine ⟨7654239546540333002616307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10205652728720444003488409 7654239546540333002616307)
        ·
          refine ⟨11481359319810499503924461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7654239546540333002616307 11481359319810499503924461)
          ·
            refine ⟨4305509744928937313971673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11481359319810499503924461 4305509744928937313971673)
            ·
              refine ⟨3229132308696702985478755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4305509744928937313971673 3229132308696702985478755)
              ·
                refine ⟨4843698463045054478218133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229132308696702985478755 4843698463045054478218133)
                ·
                  refine ⟨227048365455236928666475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4843698463045054478218133 227048365455236928666475)
                  ·
                    rfl

theorem cell22_1989788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_1989788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989788 prefixEnd_1989788 := by exact prefixLift 1989788
  have htrace : WordTrace (prefixWord ++ tailWord_1989788) baseStart_1989788 baseEnd_1989788 := by
    simpa [prefixWord, tailWord_1989788, baseEnd_1989788] using wordTrace_append hprefix tailTrace_1989788
  have hstable : (prefixWord ++ tailWord_1989788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989788).length < 2 ^ (prefixWord ++ tailWord_1989788).sum := by decide
  have hdescent : baseEnd_1989788 < baseStart_1989788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989822 : List Nat := [4, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1989822 : Nat := 118140960795 + 1989822 * 2 ^ 59
def prefixEnd_1989822 : Nat := 4983230072969 + 3 ^ 40 * 1989822 * 2
def baseEnd_1989822 : Nat := 227052245086848676883107

theorem tailTrace_1989822 : CollatzResearch.WordTrace tailWord_1989822 prefixEnd_1989822 227052245086848676883107 := by
  unfold tailWord_1989822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9071846324652775423387465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48383180398148135591399813 9071846324652775423387465)
  ·
    refine ⟨6803884743489581567540599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9071846324652775423387465 6803884743489581567540599)
    ·
      refine ⟨10205827115234372351310899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803884743489581567540599 10205827115234372351310899)
      ·
        refine ⟨15308740672851558526966349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10205827115234372351310899 15308740672851558526966349)
        ·
          refine ⟨5740777752319334447612381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15308740672851558526966349 5740777752319334447612381)
          ·
            refine ⟨2152791657119750417854643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5740777752319334447612381 2152791657119750417854643)
            ·
              refine ⟨3229187485679625626781965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152791657119750417854643 3229187485679625626781965)
              ·
                refine ⟨1210945307129859610043237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3229187485679625626781965 1210945307129859610043237)
                ·
                  refine ⟨227052245086848676883107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1210945307129859610043237 227052245086848676883107)
                  ·
                    rfl

theorem cell22_1989822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1989822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989822 prefixEnd_1989822 := by exact prefixLift 1989822
  have htrace : WordTrace (prefixWord ++ tailWord_1989822) baseStart_1989822 baseEnd_1989822 := by
    simpa [prefixWord, tailWord_1989822, baseEnd_1989822] using wordTrace_append hprefix tailTrace_1989822
  have hstable : (prefixWord ++ tailWord_1989822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989822).length < 2 ^ (prefixWord ++ tailWord_1989822).sum := by decide
  have hdescent : baseEnd_1989822 < baseStart_1989822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989899 : List Nat := [1, 1, 1, 1, 5, 5, 2, 2, 1, 3]
def baseStart_1989899 : Nat := 118140960795 + 1989899 * 2 ^ 59
def prefixEnd_1989899 : Nat := 4983230072969 + 3 ^ 40 * 1989899 * 2
def baseEnd_1989899 : Nat := 681183093934143496474085

theorem tailTrace_1989899 : CollatzResearch.WordTrace tailWord_1989899 prefixEnd_1989899 681183093934143496474085 := by
  unfold tailWord_1989899
  simp only [CollatzResearch.WordTrace]
  refine ⟨72577579017943245537652751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48385052678628830358435167 72577579017943245537652751)
  ·
    refine ⟨108866368526914868306479127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72577579017943245537652751 108866368526914868306479127)
    ·
      refine ⟨163299552790372302459718691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108866368526914868306479127 163299552790372302459718691)
      ·
        refine ⟨244949329185558453689578037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163299552790372302459718691 244949329185558453689578037)
        ·
          refine ⟨22963999611146105033397941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244949329185558453689578037 22963999611146105033397941)
          ·
            refine ⟨2152874963544947346881057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22963999611146105033397941 2152874963544947346881057)
            ·
              refine ⟨1614656222658710510160793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2152874963544947346881057 1614656222658710510160793)
              ·
                refine ⟨1210992166994032882620595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614656222658710510160793 1210992166994032882620595)
                ·
                  refine ⟨1816488250491049323930893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210992166994032882620595 1816488250491049323930893)
                  ·
                    refine ⟨681183093934143496474085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816488250491049323930893 681183093934143496474085)
                    ·
                      rfl

theorem cell22_1989899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 3].length) (baseStart_1989899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989899 prefixEnd_1989899 := by exact prefixLift 1989899
  have htrace : WordTrace (prefixWord ++ tailWord_1989899) baseStart_1989899 baseEnd_1989899 := by
    simpa [prefixWord, tailWord_1989899, baseEnd_1989899] using wordTrace_append hprefix tailTrace_1989899
  have hstable : (prefixWord ++ tailWord_1989899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989899).length < 2 ^ (prefixWord ++ tailWord_1989899).sum := by decide
  have hdescent : baseEnd_1989899 < baseStart_1989899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989923 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 6]
def baseStart_1989923 : Nat := 118140960795 + 1989923 * 2 ^ 59
def prefixEnd_1989923 : Nat := 4983230072969 + 3 ^ 40 * 1989923 * 2
def baseEnd_1989923 : Nat := 227063769874871811291337

theorem tailTrace_1989923 : CollatzResearch.WordTrace tailWord_1989923 prefixEnd_1989923 227063769874871811291337 := by
  unfold tailWord_1989923
  simp only [CollatzResearch.WordTrace]
  refine ⟨72578454369856297636526423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48385636246570865091017615 72578454369856297636526423)
  ·
    refine ⟨108867681554784446454789635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72578454369856297636526423 108867681554784446454789635)
    ·
      refine ⟨163301522332176669682184453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108867681554784446454789635 163301522332176669682184453)
      ·
        refine ⟨30619035437283125565409585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163301522332176669682184453 30619035437283125565409585)
        ·
          refine ⟨22964276577962344174057189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30619035437283125565409585 22964276577962344174057189)
          ·
            refine ⟨4305801858367939532635723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22964276577962344174057189 4305801858367939532635723)
            ·
              refine ⟨6458702787551909298953585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305801858367939532635723 6458702787551909298953585)
              ·
                refine ⟨4844027090663931974215189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6458702787551909298953585 4844027090663931974215189)
                ·
                  refine ⟨227063769874871811291337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4844027090663931974215189 227063769874871811291337)
                  ·
                    rfl

theorem cell22_1989923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 6].length) (baseStart_1989923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1989923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1989923 prefixEnd_1989923 := by exact prefixLift 1989923
  have htrace : WordTrace (prefixWord ++ tailWord_1989923) baseStart_1989923 baseEnd_1989923 := by
    simpa [prefixWord, tailWord_1989923, baseEnd_1989923] using wordTrace_append hprefix tailTrace_1989923
  have hstable : (prefixWord ++ tailWord_1989923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989923).length < 2 ^ (prefixWord ++ tailWord_1989923).sum := by decide
  have hdescent : baseEnd_1989923 < baseStart_1989923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990013 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 7]
def baseStart_1990013 : Nat := 118140960795 + 1990013 * 2 ^ 59
def prefixEnd_1990013 : Nat := 4983230072969 + 3 ^ 40 * 1990013 * 2
def baseEnd_1990013 : Nat := 227074039487961733041245

theorem tailTrace_1990013 : CollatzResearch.WordTrace tailWord_1990013 prefixEnd_1990013 227074039487961733041245 := by
  unfold tailWord_1990013
  simp only [CollatzResearch.WordTrace]
  refine ⟨72581736939530243007302693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48387824626353495338201795 72581736939530243007302693)
  ·
    refine ⟨13609075676161920563869255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72581736939530243007302693 13609075676161920563869255)
    ·
      refine ⟨20413613514242880845803883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13609075676161920563869255 20413613514242880845803883)
      ·
        refine ⟨30620420271364321268705825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20413613514242880845803883 30620420271364321268705825)
        ·
          refine ⟨22965315203523240951529369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30620420271364321268705825 22965315203523240951529369)
          ·
            refine ⟨17223986402642430713647027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22965315203523240951529369 17223986402642430713647027)
            ·
              refine ⟨25835979603963646070470541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17223986402642430713647027 25835979603963646070470541)
              ·
                refine ⟨9688492351486367276426453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25835979603963646070470541 9688492351486367276426453)
                ·
                  refine ⟨227074039487961733041245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9688492351486367276426453 227074039487961733041245)
                  ·
                    rfl

theorem cell22_1990013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_1990013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990013 prefixEnd_1990013 := by exact prefixLift 1990013
  have htrace : WordTrace (prefixWord ++ tailWord_1990013) baseStart_1990013 baseEnd_1990013 := by
    simpa [prefixWord, tailWord_1990013, baseEnd_1990013] using wordTrace_append hprefix tailTrace_1990013
  have hstable : (prefixWord ++ tailWord_1990013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990013).length < 2 ^ (prefixWord ++ tailWord_1990013).sum := by decide
  have hdescent : baseEnd_1990013 < baseStart_1990013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990028 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_1990028 : Nat := 118140960795 + 1990028 * 2 ^ 59
def prefixEnd_1990028 : Nat := 4983230072969 + 3 ^ 40 * 1990028 * 2
def baseEnd_1990028 : Nat := 681227253270430159998689

theorem tailTrace_1990028 : CollatzResearch.WordTrace tailWord_1990028 prefixEnd_1990028 681227253270430159998689 := by
  unfold tailWord_1990028
  simp only [CollatzResearch.WordTrace]
  refine ⟨36291142017237950284549369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48388189356317267046065825 36291142017237950284549369)
  ·
    refine ⟨27218356512928462713412027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36291142017237950284549369 27218356512928462713412027)
    ·
      refine ⟨40827534769392694070118041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27218356512928462713412027 40827534769392694070118041)
      ·
        refine ⟨30620651077044520552588531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40827534769392694070118041 30620651077044520552588531)
        ·
          refine ⟨45930976615566780828882797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30620651077044520552588531 45930976615566780828882797)
          ·
            refine ⟨17224116230837542810831049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45930976615566780828882797 17224116230837542810831049)
            ·
              refine ⟨12918087173128157108123287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17224116230837542810831049 12918087173128157108123287)
              ·
                refine ⟨19377130759692235662184931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12918087173128157108123287 19377130759692235662184931)
                ·
                  refine ⟨29065696139538353493277397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19377130759692235662184931 29065696139538353493277397)
                  ·
                    refine ⟨681227253270430159998689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29065696139538353493277397 681227253270430159998689)
                    ·
                      rfl

theorem cell22_1990028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_1990028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990028 prefixEnd_1990028 := by exact prefixLift 1990028
  have htrace : WordTrace (prefixWord ++ tailWord_1990028) baseStart_1990028 baseEnd_1990028 := by
    simpa [prefixWord, tailWord_1990028, baseEnd_1990028] using wordTrace_append hprefix tailTrace_1990028
  have hstable : (prefixWord ++ tailWord_1990028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990028).length < 2 ^ (prefixWord ++ tailWord_1990028).sum := by decide
  have hdescent : baseEnd_1990028 < baseStart_1990028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990043 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 9, 4]
def baseStart_1990043 : Nat := 118140960795 + 1990043 * 2 ^ 59
def prefixEnd_1990043 : Nat := 4983230072969 + 3 ^ 40 * 1990043 * 2
def baseEnd_1990043 : Nat := 681232388076975120873643

theorem tailTrace_1990043 : CollatzResearch.WordTrace tailWord_1990043 prefixEnd_1990043 681232388076975120873643 := by
  unfold tailWord_1990043
  simp only [CollatzResearch.WordTrace]
  refine ⟨72582831129421558130894783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48388554086281038753929855 72582831129421558130894783)
  ·
    refine ⟨108874246694132337196342175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72582831129421558130894783 108874246694132337196342175)
    ·
      refine ⟨163311370041198505794513263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108874246694132337196342175 163311370041198505794513263)
      ·
        refine ⟨244967055061797758691769895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163311370041198505794513263 244967055061797758691769895)
        ·
          refine ⟨367450582592696638037654843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244967055061797758691769895 367450582592696638037654843)
          ·
            refine ⟨551175873889044957056482265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367450582592696638037654843 551175873889044957056482265)
            ·
              refine ⟨413381905416783717792361699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551175873889044957056482265 413381905416783717792361699)
              ·
                refine ⟨620072858125175576688542549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413381905416783717792361699 620072858125175576688542549)
                ·
                  refine ⟨3633239403077200644659429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 620072858125175576688542549 3633239403077200644659429)
                  ·
                    refine ⟨681232388076975120873643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633239403077200644659429 681232388076975120873643)
                    ·
                      rfl

theorem cell22_1990043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_1990043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990043 prefixEnd_1990043 := by exact prefixLift 1990043
  have htrace : WordTrace (prefixWord ++ tailWord_1990043) baseStart_1990043 baseEnd_1990043 := by
    simpa [prefixWord, tailWord_1990043, baseEnd_1990043] using wordTrace_append hprefix tailTrace_1990043
  have hstable : (prefixWord ++ tailWord_1990043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990043).length < 2 ^ (prefixWord ++ tailWord_1990043).sum := by decide
  have hdescent : baseEnd_1990043 < baseStart_1990043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990060 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_1990060 : Nat := 118140960795 + 1990060 * 2 ^ 59
def prefixEnd_1990060 : Nat := 4983230072969 + 3 ^ 40 * 1990060 * 2
def baseEnd_1990060 : Nat := 681238207524392743198591

theorem tailTrace_1990060 : CollatzResearch.WordTrace tailWord_1990060 prefixEnd_1990060 681238207524392743198591 := by
  unfold tailWord_1990060
  simp only [CollatzResearch.WordTrace]
  refine ⟨36291725585179985017131817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48388967446906646689509089 36291725585179985017131817)
  ·
    refine ⟨27218794188884988762848863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36291725585179985017131817 27218794188884988762848863)
    ·
      refine ⟨40828191283327483144273295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27218794188884988762848863 40828191283327483144273295)
      ·
        refine ⟨61242286924991224716409943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40828191283327483144273295 61242286924991224716409943)
        ·
          refine ⟨91863430387486837074614915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61242286924991224716409943 91863430387486837074614915)
          ·
            refine ⟨137795145581230255611922373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91863430387486837074614915 137795145581230255611922373)
            ·
              refine ⟨25836589796480672927235445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137795145581230255611922373 25836589796480672927235445)
              ·
                refine ⟨2422180293420063086928323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25836589796480672927235445 2422180293420063086928323)
                ·
                  refine ⟨3633270440130094630392485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422180293420063086928323 3633270440130094630392485)
                  ·
                    refine ⟨681238207524392743198591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633270440130094630392485 681238207524392743198591)
                    ·
                      rfl

theorem cell22_1990060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_1990060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990060 prefixEnd_1990060 := by exact prefixLift 1990060
  have htrace : WordTrace (prefixWord ++ tailWord_1990060) baseStart_1990060 baseEnd_1990060 := by
    simpa [prefixWord, tailWord_1990060, baseEnd_1990060] using wordTrace_append hprefix tailTrace_1990060
  have hstable : (prefixWord ++ tailWord_1990060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990060).length < 2 ^ (prefixWord ++ tailWord_1990060).sum := by decide
  have hdescent : baseEnd_1990060 < baseStart_1990060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990090 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_1990090 : Nat := 118140960795 + 1990090 * 2 ^ 59
def prefixEnd_1990090 : Nat := 4983230072969 + 3 ^ 40 * 1990090 * 2
def baseEnd_1990090 : Nat := 681248477137482664948499

theorem tailTrace_1990090 : CollatzResearch.WordTrace tailWord_1990090 prefixEnd_1990090 681248477137482664948499 := by
  unfold tailWord_1990090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18146136340062821289463931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48389696906834190105237149 18146136340062821289463931)
  ·
    refine ⟨27219204510094231934195897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18146136340062821289463931 27219204510094231934195897)
    ·
      refine ⟨20414403382570673950646923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27219204510094231934195897 20414403382570673950646923)
      ·
        refine ⟨30621605073856010925970385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20414403382570673950646923 30621605073856010925970385)
        ·
          refine ⟨22966203805392008194477789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30621605073856010925970385 22966203805392008194477789)
          ·
            refine ⟨8612326427022003072929171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22966203805392008194477789 8612326427022003072929171)
            ·
              refine ⟨12918489640533004609393757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612326427022003072929171 12918489640533004609393757)
              ·
                refine ⟨4844433615199876728522659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12918489640533004609393757 4844433615199876728522659)
                ·
                  refine ⟨7266650422799815092783989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4844433615199876728522659 7266650422799815092783989)
                  ·
                    refine ⟨681248477137482664948499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7266650422799815092783989 681248477137482664948499)
                    ·
                      rfl

theorem cell22_1990090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_1990090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990090 prefixEnd_1990090 := by exact prefixLift 1990090
  have htrace : WordTrace (prefixWord ++ tailWord_1990090) baseStart_1990090 baseEnd_1990090 := by
    simpa [prefixWord, tailWord_1990090, baseEnd_1990090] using wordTrace_append hprefix tailTrace_1990090
  have hstable : (prefixWord ++ tailWord_1990090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990090).length < 2 ^ (prefixWord ++ tailWord_1990090).sum := by decide
  have hdescent : baseEnd_1990090 < baseStart_1990090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990103 : List Nat := [1, 1, 3, 2, 1, 1, 1, 12]
def baseStart_1990103 : Nat := 118140960795 + 1990103 * 2 ^ 59
def prefixEnd_1990103 : Nat := 4983230072969 + 3 ^ 40 * 1990103 * 2
def baseEnd_1990103 : Nat := 75694769700350551597051

theorem tailTrace_1990103 : CollatzResearch.WordTrace tailWord_1990103 prefixEnd_1990103 75694769700350551597051 := by
  unfold tailWord_1990103
  simp only [CollatzResearch.WordTrace]
  refine ⟨72585019509204188378078963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48390013006136125585385975 72585019509204188378078963)
  ·
    refine ⟨108877529263806282567118445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72585019509204188378078963 108877529263806282567118445)
    ·
      refine ⟨40829073473927355962669417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108877529263806282567118445 40829073473927355962669417)
      ·
        refine ⟨30621805105445516972002063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40829073473927355962669417 30621805105445516972002063)
        ·
          refine ⟨45932707658168275458003095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30621805105445516972002063 45932707658168275458003095)
          ·
            refine ⟨68899061487252413187004643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45932707658168275458003095 68899061487252413187004643)
            ·
              refine ⟨103348592230878619780506965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68899061487252413187004643 103348592230878619780506965)
              ·
                refine ⟨75694769700350551597051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 103348592230878619780506965 75694769700350551597051)
                ·
                  rfl

theorem cell22_1990103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 12].length) (baseStart_1990103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990103 prefixEnd_1990103 := by exact prefixLift 1990103
  have htrace : WordTrace (prefixWord ++ tailWord_1990103) baseStart_1990103 baseEnd_1990103 := by
    simpa [prefixWord, tailWord_1990103, baseEnd_1990103] using wordTrace_append hprefix tailTrace_1990103
  have hstable : (prefixWord ++ tailWord_1990103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990103).length < 2 ^ (prefixWord ++ tailWord_1990103).sum := by decide
  have hdescent : baseEnd_1990103 < baseStart_1990103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990105 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_1990105 : Nat := 118140960795 + 1990105 * 2 ^ 59
def prefixEnd_1990105 : Nat := 4983230072969 + 3 ^ 40 * 1990105 * 2
def baseEnd_1990105 : Nat := 681253611944027625823453

theorem tailTrace_1990105 : CollatzResearch.WordTrace tailWord_1990105 prefixEnd_1990105 681253611944027625823453 := by
  unfold tailWord_1990105
  simp only [CollatzResearch.WordTrace]
  refine ⟨72585092455196942719651769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48390061636797961813101179 72585092455196942719651769)
  ·
    refine ⟨54438819341397707039738827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72585092455196942719651769 54438819341397707039738827)
    ·
      refine ⟨81658229012096560559608241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54438819341397707039738827 81658229012096560559608241)
      ·
        refine ⟨61243671759072420419706181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81658229012096560559608241 61243671759072420419706181)
        ·
          refine ⟨11483188454826078828694909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61243671759072420419706181 11483188454826078828694909)
          ·
            refine ⟨4306195670559779560760591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11483188454826078828694909 4306195670559779560760591)
            ·
              refine ⟨6459293505839669341140887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306195670559779560760591 6459293505839669341140887)
              ·
                refine ⟨9688940258759504011711331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6459293505839669341140887 9688940258759504011711331)
                ·
                  refine ⟨14533410388139256017566997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9688940258759504011711331 14533410388139256017566997)
                  ·
                    refine ⟨681253611944027625823453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14533410388139256017566997 681253611944027625823453)
                    ·
                      rfl

theorem cell22_1990105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_1990105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990105 prefixEnd_1990105 := by exact prefixLift 1990105
  have htrace : WordTrace (prefixWord ++ tailWord_1990105) baseStart_1990105 baseEnd_1990105 := by
    simpa [prefixWord, tailWord_1990105, baseEnd_1990105] using wordTrace_append hprefix tailTrace_1990105
  have hstable : (prefixWord ++ tailWord_1990105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990105).length < 2 ^ (prefixWord ++ tailWord_1990105).sum := by decide
  have hdescent : baseEnd_1990105 < baseStart_1990105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990109 : List Nat := [1, 4, 3, 1, 1, 3, 2, 3, 4]
def baseStart_1990109 : Nat := 118140960795 + 1990109 * 2 ^ 59
def prefixEnd_1990109 : Nat := 4983230072969 + 3 ^ 40 * 1990109 * 2
def baseEnd_1990109 : Nat := 227084993741924316241147

theorem tailTrace_1990109 : CollatzResearch.WordTrace tailWord_1990109 prefixEnd_1990109 227084993741924316241147 := by
  unfold tailWord_1990109
  simp only [CollatzResearch.WordTrace]
  refine ⟨72585238347182451402797381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48390158898121634268531587 72585238347182451402797381)
  ·
    refine ⟨13609732190096709638024509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72585238347182451402797381 13609732190096709638024509)
    ·
      refine ⟨5103649571286266114259191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13609732190096709638024509 5103649571286266114259191)
      ·
        refine ⟨7655474356929399171388787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5103649571286266114259191 7655474356929399171388787)
        ·
          refine ⟨11483211535394098757083181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655474356929399171388787 11483211535394098757083181)
          ·
            refine ⟨4306204325772787033906193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11483211535394098757083181 4306204325772787033906193)
            ·
              refine ⟨3229653244329590275429645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306204325772787033906193 3229653244329590275429645)
              ·
                refine ⟨1211119966623596353286117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3229653244329590275429645 1211119966623596353286117)
                ·
                  refine ⟨227084993741924316241147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211119966623596353286117 227084993741924316241147)
                  ·
                    rfl

theorem cell22_1990109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_1990109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990109 prefixEnd_1990109 := by exact prefixLift 1990109
  have htrace : WordTrace (prefixWord ++ tailWord_1990109) baseStart_1990109 baseEnd_1990109 := by
    simpa [prefixWord, tailWord_1990109, baseEnd_1990109] using wordTrace_append hprefix tailTrace_1990109
  have hstable : (prefixWord ++ tailWord_1990109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990109).length < 2 ^ (prefixWord ++ tailWord_1990109).sum := by decide
  have hdescent : baseEnd_1990109 < baseStart_1990109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990152 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 3, 3]
def baseStart_1990152 : Nat := 118140960795 + 1990152 * 2 ^ 59
def prefixEnd_1990152 : Nat := 4983230072969 + 3 ^ 40 * 1990152 * 2
def baseEnd_1990152 : Nat := 681269701004535169898309

theorem tailTrace_1990152 : CollatzResearch.WordTrace tailWord_1990152 prefixEnd_1990152 681269701004535169898309 := by
  unfold tailWord_1990152
  simp only [CollatzResearch.WordTrace]
  refine ⟨36293403343013334873306355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48391204457351113164408473 36293403343013334873306355)
  ·
    refine ⟨54440105014520002309959533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36293403343013334873306355 54440105014520002309959533)
    ·
      refine ⟨20415039380445000866234825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54440105014520002309959533 20415039380445000866234825)
      ·
        refine ⟨15311279535333750649676119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20415039380445000866234825 15311279535333750649676119)
        ·
          refine ⟨22966919303000625974514179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311279535333750649676119 22966919303000625974514179)
          ·
            refine ⟨34450378954500938961771269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22966919303000625974514179 34450378954500938961771269)
            ·
              refine ⟨6459446053968926055332113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34450378954500938961771269 6459446053968926055332113)
              ·
                refine ⟨4844584540476694541499085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6459446053968926055332113 4844584540476694541499085)
                ·
                  refine ⟨1816719202678760453062157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4844584540476694541499085 1816719202678760453062157)
                  ·
                    refine ⟨681269701004535169898309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816719202678760453062157 681269701004535169898309)
                    ·
                      rfl

theorem cell22_1990152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_1990152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990152 prefixEnd_1990152 := by exact prefixLift 1990152
  have htrace : WordTrace (prefixWord ++ tailWord_1990152) baseStart_1990152 baseEnd_1990152 := by
    simpa [prefixWord, tailWord_1990152, baseEnd_1990152] using wordTrace_append hprefix tailTrace_1990152
  have hstable : (prefixWord ++ tailWord_1990152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990152).length < 2 ^ (prefixWord ++ tailWord_1990152).sum := by decide
  have hdescent : baseEnd_1990152 < baseStart_1990152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990165 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 7]
def baseStart_1990165 : Nat := 118140960795 + 1990165 * 2 ^ 59
def prefixEnd_1990165 : Nat := 4983230072969 + 3 ^ 40 * 1990165 * 2
def baseEnd_1990165 : Nat := 227091383723402489774423

theorem tailTrace_1990165 : CollatzResearch.WordTrace tailWord_1990165 prefixEnd_1990165 227091383723402489774423 := by
  unfold tailWord_1990165
  simp only [CollatzResearch.WordTrace]
  refine ⟨72587280834979572966835949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48391520556653048644557299 72587280834979572966835949)
  ·
    refine ⟨27220230313117339862563481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72587280834979572966835949 27220230313117339862563481)
    ·
      refine ⟨20415172734838004896922611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27220230313117339862563481 20415172734838004896922611)
      ·
        refine ⟨30622759102257007345383917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20415172734838004896922611 30622759102257007345383917)
        ·
          refine ⟨11483534663346377754518969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30622759102257007345383917 11483534663346377754518969)
          ·
            refine ⟨8612650997509783315889227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11483534663346377754518969 8612650997509783315889227)
            ·
              refine ⟨12918976496264674973833841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8612650997509783315889227 12918976496264674973833841)
              ·
                refine ⟨9689232372198506230375381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12918976496264674973833841 9689232372198506230375381)
                ·
                  refine ⟨227091383723402489774423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9689232372198506230375381 227091383723402489774423)
                  ·
                    rfl

theorem cell22_1990165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_1990165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990165 prefixEnd_1990165 := by exact prefixLift 1990165
  have htrace : WordTrace (prefixWord ++ tailWord_1990165) baseStart_1990165 baseEnd_1990165 := by
    simpa [prefixWord, tailWord_1990165, baseEnd_1990165] using wordTrace_append hprefix tailTrace_1990165
  have hstable : (prefixWord ++ tailWord_1990165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990165).length < 2 ^ (prefixWord ++ tailWord_1990165).sum := by decide
  have hdescent : baseEnd_1990165 < baseStart_1990165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990199 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 5]
def baseStart_1990199 : Nat := 118140960795 + 1990199 * 2 ^ 59
def prefixEnd_1990199 : Nat := 4983230072969 + 3 ^ 40 * 1990199 * 2
def baseEnd_1990199 : Nat := 227095263355014237991055

theorem tailTrace_1990199 : CollatzResearch.WordTrace tailWord_1990199 prefixEnd_1990199 227095263355014237991055 := by
  unfold tailWord_1990199
  simp only [CollatzResearch.WordTrace]
  refine ⟨72588520916856396773573651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48392347277904264515715767 72588520916856396773573651)
  ·
    refine ⟨108882781375284595160360477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72588520916856396773573651 108882781375284595160360477)
    ·
      refine ⟨40831043015731723185135179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108882781375284595160360477 40831043015731723185135179)
      ·
        refine ⟨61246564523597584777702769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40831043015731723185135179 61246564523597584777702769)
        ·
          refine ⟨45934923392698188583277077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61246564523597584777702769 45934923392698188583277077)
          ·
            refine ⟨2153199534032727589841113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45934923392698188583277077 2153199534032727589841113)
            ·
              refine ⟨1614899650524545692380835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153199534032727589841113 1614899650524545692380835)
              ·
                refine ⟨2422349475786818538571253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614899650524545692380835 2422349475786818538571253)
                ·
                  refine ⟨227095263355014237991055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422349475786818538571253 227095263355014237991055)
                  ·
                    rfl

theorem cell22_1990199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 5].length) (baseStart_1990199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990199 prefixEnd_1990199 := by exact prefixLift 1990199
  have htrace : WordTrace (prefixWord ++ tailWord_1990199) baseStart_1990199 baseEnd_1990199 := by
    simpa [prefixWord, tailWord_1990199, baseEnd_1990199] using wordTrace_append hprefix tailTrace_1990199
  have hstable : (prefixWord ++ tailWord_1990199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990199).length < 2 ^ (prefixWord ++ tailWord_1990199).sum := by decide
  have hdescent : baseEnd_1990199 < baseStart_1990199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990237 : List Nat := [1, 4, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1990237 : Nat := 118140960795 + 1990237 * 2 ^ 59
def prefixEnd_1990237 : Nat := 4983230072969 + 3 ^ 40 * 1990237 * 2
def baseEnd_1990237 : Nat := 681298798241623281523049

theorem tailTrace_1990237 : CollatzResearch.WordTrace tailWord_1990237 prefixEnd_1990237 681298798241623281523049 := by
  unfold tailWord_1990237
  simp only [CollatzResearch.WordTrace]
  refine ⟨72589906890718729263456965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48393271260479152842304643 72589906890718729263456965)
  ·
    refine ⟨13610607542009761736898181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72589906890718729263456965 13610607542009761736898181)
    ·
      refine ⟨2551988914126830325668409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13610607542009761736898181 2551988914126830325668409)
      ·
        refine ⟨1913991685595122744251307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2551988914126830325668409 1913991685595122744251307)
        ·
          refine ⟨2870987528392684116376961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913991685595122744251307 2870987528392684116376961)
          ·
            refine ⟨2153240646294513087282721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870987528392684116376961 2153240646294513087282721)
            ·
              refine ⟨1614930484720884815462041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153240646294513087282721 1614930484720884815462041)
              ·
                refine ⟨1211197863540663611596531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1614930484720884815462041 1211197863540663611596531)
                ·
                  refine ⟨1816796795310995417394797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211197863540663611596531 1816796795310995417394797)
                  ·
                    refine ⟨681298798241623281523049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816796795310995417394797 681298798241623281523049)
                    ·
                      rfl

theorem cell22_1990237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1990237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990237 prefixEnd_1990237 := by exact prefixLift 1990237
  have htrace : WordTrace (prefixWord ++ tailWord_1990237) baseStart_1990237 baseEnd_1990237 := by
    simpa [prefixWord, tailWord_1990237, baseEnd_1990237] using wordTrace_append hprefix tailTrace_1990237
  have hstable : (prefixWord ++ tailWord_1990237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990237).length < 2 ^ (prefixWord ++ tailWord_1990237).sum := by decide
  have hdescent : baseEnd_1990237 < baseStart_1990237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990240 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_1990240 : Nat := 118140960795 + 1990240 * 2 ^ 59
def prefixEnd_1990240 : Nat := 4983230072969 + 3 ^ 40 * 1990240 * 2
def baseEnd_1990240 : Nat := 681299825202932273698039

theorem tailTrace_1990240 : CollatzResearch.WordTrace tailWord_1990240 prefixEnd_1990240 681299825202932273698039 := by
  unfold tailWord_1990240
  simp only [CollatzResearch.WordTrace]
  refine ⟨36295008154853930387908087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48393344206471907183877449 36295008154853930387908087)
  ·
    refine ⟨54442512232280895581862131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36295008154853930387908087 54442512232280895581862131)
    ·
      refine ⟨81663768348421343372793197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54442512232280895581862131 81663768348421343372793197)
      ·
        refine ⟨30623913130658003764797449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81663768348421343372793197 30623913130658003764797449)
        ·
          refine ⟨22967934847993502823598087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30623913130658003764797449 22967934847993502823598087)
          ·
            refine ⟨34451902271990254235397131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22967934847993502823598087 34451902271990254235397131)
            ·
              refine ⟨51677853407985381353095697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34451902271990254235397131 51677853407985381353095697)
              ·
                refine ⟨38758390055989036014821773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51677853407985381353095697 38758390055989036014821773)
                ·
                  refine ⟨14534396270995888505558165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38758390055989036014821773 14534396270995888505558165)
                  ·
                    refine ⟨681299825202932273698039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14534396270995888505558165 681299825202932273698039)
                    ·
                      rfl

theorem cell22_1990240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_1990240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990240 prefixEnd_1990240 := by exact prefixLift 1990240
  have htrace : WordTrace (prefixWord ++ tailWord_1990240) baseStart_1990240 baseEnd_1990240 := by
    simpa [prefixWord, tailWord_1990240, baseEnd_1990240] using wordTrace_append hprefix tailTrace_1990240
  have hstable : (prefixWord ++ tailWord_1990240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990240).length < 2 ^ (prefixWord ++ tailWord_1990240).sum := by decide
  have hdescent : baseEnd_1990240 < baseStart_1990240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990244 : List Nat := [2, 3, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1990244 : Nat := 118140960795 + 1990244 * 2 ^ 59
def prefixEnd_1990244 : Nat := 4983230072969 + 3 ^ 40 * 1990244 * 2
def baseEnd_1990244 : Nat := 227100398161559198866009

theorem tailTrace_1990244 : CollatzResearch.WordTrace tailWord_1990244 prefixEnd_1990244 227100398161559198866009 := by
  unfold tailWord_1990244
  simp only [CollatzResearch.WordTrace]
  refine ⟨36295081100846684729480893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48393441467795579639307857 36295081100846684729480893)
  ·
    refine ⟨13610655412817506773555335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36295081100846684729480893 13610655412817506773555335)
    ·
      refine ⟨20415983119226260160333003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13610655412817506773555335 20415983119226260160333003)
      ·
        refine ⟨30623974678839390240499505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20415983119226260160333003 30623974678839390240499505)
        ·
          refine ⟨22967981009129542680374629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30623974678839390240499505 22967981009129542680374629)
          ·
            refine ⟨4306496439211789252570243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22967981009129542680374629 4306496439211789252570243)
            ·
              refine ⟨6459744658817683878855365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306496439211789252570243 6459744658817683878855365)
              ·
                refine ⟨1211202123528315727285381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6459744658817683878855365 1211202123528315727285381)
                ·
                  refine ⟨227100398161559198866009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211202123528315727285381 227100398161559198866009)
                  ·
                    rfl

theorem cell22_1990244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1990244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990244 prefixEnd_1990244 := by exact prefixLift 1990244
  have htrace : WordTrace (prefixWord ++ tailWord_1990244) baseStart_1990244 baseEnd_1990244 := by
    simpa [prefixWord, tailWord_1990244, baseEnd_1990244] using wordTrace_append hprefix tailTrace_1990244
  have hstable : (prefixWord ++ tailWord_1990244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990244).length < 2 ^ (prefixWord ++ tailWord_1990244).sum := by decide
  have hdescent : baseEnd_1990244 < baseStart_1990244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990272 : List Nat := [2, 1, 1, 2, 1, 4, 5, 6]
def baseStart_1990272 : Nat := 118140960795 + 1990272 * 2 ^ 59
def prefixEnd_1990272 : Nat := 4983230072969 + 3 ^ 40 * 1990272 * 2
def baseEnd_1990272 : Nat := 75701197717432761877549

theorem tailTrace_1990272 : CollatzResearch.WordTrace tailWord_1990272 prefixEnd_1990272 75701197717432761877549 := by
  unfold tailWord_1990272
  simp only [CollatzResearch.WordTrace]
  refine ⟨36295591722795965120490535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48394122297061286827320713 36295591722795965120490535)
  ·
    refine ⟨54443387584193947680735803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36295591722795965120490535 54443387584193947680735803)
    ·
      refine ⟨81665081376290921521103705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54443387584193947680735803 81665081376290921521103705)
      ·
        refine ⟨61248811032218191140827779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81665081376290921521103705 61248811032218191140827779)
        ·
          refine ⟨91873216548327286711241669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61248811032218191140827779 91873216548327286711241669)
          ·
            refine ⟨17226228102811366258357813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91873216548327286711241669 17226228102811366258357813)
            ·
              refine ⟨1614958884638565586721045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17226228102811366258357813 1614958884638565586721045)
              ·
                refine ⟨75701197717432761877549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1614958884638565586721045 75701197717432761877549)
                ·
                  rfl

theorem cell22_1990272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 6].length) (baseStart_1990272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990272 prefixEnd_1990272 := by exact prefixLift 1990272
  have htrace : WordTrace (prefixWord ++ tailWord_1990272) baseStart_1990272 baseEnd_1990272 := by
    simpa [prefixWord, tailWord_1990272, baseEnd_1990272] using wordTrace_append hprefix tailTrace_1990272
  have hstable : (prefixWord ++ tailWord_1990272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990272).length < 2 ^ (prefixWord ++ tailWord_1990272).sum := by decide
  have hdescent : baseEnd_1990272 < baseStart_1990272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990280 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 1, 4]
def baseStart_1990280 : Nat := 118140960795 + 1990280 * 2 ^ 59
def prefixEnd_1990280 : Nat := 4983230072969 + 3 ^ 40 * 1990280 * 2
def baseEnd_1990280 : Nat := 681313518020385502697917

theorem tailTrace_1990280 : CollatzResearch.WordTrace tailWord_1990280 prefixEnd_1990280 681313518020385502697917 := by
  unfold tailWord_1990280
  simp only [CollatzResearch.WordTrace]
  refine ⟨36295737614781473803636147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48394316819708631738181529 36295737614781473803636147)
  ·
    refine ⟨54443606422172210705454221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36295737614781473803636147 54443606422172210705454221)
    ·
      refine ⟨20416352408314579014545333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54443606422172210705454221 20416352408314579014545333)
      ·
        refine ⟨1914033038279491782613625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20416352408314579014545333 1914033038279491782613625)
        ·
          refine ⟨1435524778709618836960219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1914033038279491782613625 1435524778709618836960219)
          ·
            refine ⟨2153287168064428255440329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435524778709618836960219 2153287168064428255440329)
            ·
              refine ⟨1614965376048321191580247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153287168064428255440329 1614965376048321191580247)
              ·
                refine ⟨2422448064072481787370371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614965376048321191580247 2422448064072481787370371)
                ·
                  refine ⟨3633672096108722681055557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422448064072481787370371 3633672096108722681055557)
                  ·
                    refine ⟨681313518020385502697917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633672096108722681055557 681313518020385502697917)
                    ·
                      rfl

theorem cell22_1990280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_1990280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990280 prefixEnd_1990280 := by exact prefixLift 1990280
  have htrace : WordTrace (prefixWord ++ tailWord_1990280) baseStart_1990280 baseEnd_1990280 := by
    simpa [prefixWord, tailWord_1990280, baseEnd_1990280] using wordTrace_append hprefix tailTrace_1990280
  have hstable : (prefixWord ++ tailWord_1990280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990280).length < 2 ^ (prefixWord ++ tailWord_1990280).sum := by decide
  have hdescent : baseEnd_1990280 < baseStart_1990280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990304 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 3, 3]
def baseStart_1990304 : Nat := 118140960795 + 1990304 * 2 ^ 59
def prefixEnd_1990304 : Nat := 4983230072969 + 3 ^ 40 * 1990304 * 2
def baseEnd_1990304 : Nat := 681321733710857440097843

theorem tailTrace_1990304 : CollatzResearch.WordTrace tailWord_1990304 prefixEnd_1990304 681321733710857440097843 := by
  unfold tailWord_1990304
  simp only [CollatzResearch.WordTrace]
  refine ⟨36296175290737999853072983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48394900387650666470763977 36296175290737999853072983)
  ·
    refine ⟨54444262936106999779609475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36296175290737999853072983 54444262936106999779609475)
    ·
      refine ⟨81666394404160499669414213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54444262936106999779609475 81666394404160499669414213)
      ·
        refine ⟨15312448950780093688015165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81666394404160499669414213 15312448950780093688015165)
        ·
          refine ⟨5742168356542535133005687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15312448950780093688015165 5742168356542535133005687)
          ·
            refine ⟨8613252534813802699508531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742168356542535133005687 8613252534813802699508531)
            ·
              refine ⟨12919878802220704049262797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613252534813802699508531 12919878802220704049262797)
              ·
                refine ⟨4844954550832764018473549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12919878802220704049262797 4844954550832764018473549)
                ·
                  refine ⟨1816857956562286506927581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4844954550832764018473549 1816857956562286506927581)
                  ·
                    refine ⟨681321733710857440097843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816857956562286506927581 681321733710857440097843)
                    ·
                      rfl

theorem cell22_1990304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_1990304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990304 prefixEnd_1990304 := by exact prefixLift 1990304
  have htrace : WordTrace (prefixWord ++ tailWord_1990304) baseStart_1990304 baseEnd_1990304 := by
    simpa [prefixWord, tailWord_1990304, baseEnd_1990304] using wordTrace_append hprefix tailTrace_1990304
  have hstable : (prefixWord ++ tailWord_1990304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990304).length < 2 ^ (prefixWord ++ tailWord_1990304).sum := by decide
  have hdescent : baseEnd_1990304 < baseStart_1990304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990377 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_1990377 : Nat := 118140960795 + 1990377 * 2 ^ 59
def prefixEnd_1990377 : Nat := 4983230072969 + 3 ^ 40 * 1990377 * 2
def baseEnd_1990377 : Nat := 681346723102709583022619

theorem tailTrace_1990377 : CollatzResearch.WordTrace tailWord_1990377 prefixEnd_1990377 681346723102709583022619 := by
  unfold tailWord_1990377
  simp only [CollatzResearch.WordTrace]
  refine ⟨72595013110211533173553385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48396675406807688782368923 72595013110211533173553385)
  ·
    refine ⟨54446259832658649880165039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72595013110211533173553385 54446259832658649880165039)
    ·
      refine ⟨81669389748987974820247559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54446259832658649880165039 81669389748987974820247559)
      ·
        refine ⟨122504084623481962230371339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81669389748987974820247559 122504084623481962230371339)
        ·
          refine ⟨183756126935222943345557009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122504084623481962230371339 183756126935222943345557009)
          ·
            refine ⟨137817095201417207509167757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183756126935222943345557009 137817095201417207509167757)
            ·
              refine ⟨51681410700531452815937909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137817095201417207509167757 51681410700531452815937909)
              ·
                refine ⟨4845132253174823701494179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51681410700531452815937909 4845132253174823701494179)
                ·
                  refine ⟨7267698379762235552241269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4845132253174823701494179 7267698379762235552241269)
                  ·
                    refine ⟨681346723102709583022619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7267698379762235552241269 681346723102709583022619)
                    ·
                      rfl

theorem cell22_1990377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_1990377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990377 prefixEnd_1990377 := by exact prefixLift 1990377
  have htrace : WordTrace (prefixWord ++ tailWord_1990377) baseStart_1990377 baseEnd_1990377 := by
    simpa [prefixWord, tailWord_1990377, baseEnd_1990377] using wordTrace_append hprefix tailTrace_1990377
  have hstable : (prefixWord ++ tailWord_1990377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990377).length < 2 ^ (prefixWord ++ tailWord_1990377).sum := by decide
  have hdescent : baseEnd_1990377 < baseStart_1990377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990381 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1990381 : Nat := 118140960795 + 1990381 * 2 ^ 59
def prefixEnd_1990381 : Nat := 4983230072969 + 3 ^ 40 * 1990381 * 2
def baseEnd_1990381 : Nat := 681348092384454905922607

theorem tailTrace_1990381 : CollatzResearch.WordTrace tailWord_1990381 prefixEnd_1990381 681348092384454905922607 := by
  unfold tailWord_1990381
  simp only [CollatzResearch.WordTrace]
  refine ⟨72595159002197041856698997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48396772668131361237799331 72595159002197041856698997)
  ·
    refine ⟨6805796156455972674065531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72595159002197041856698997 6805796156455972674065531)
    ·
      refine ⟨10208694234683959011098297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6805796156455972674065531 10208694234683959011098297)
      ·
        refine ⟨7656520676012969258323723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10208694234683959011098297 7656520676012969258323723)
        ·
          refine ⟨11484781014019453887485585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656520676012969258323723 11484781014019453887485585)
          ·
            refine ⟨8613585760514590415614189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11484781014019453887485585 8613585760514590415614189)
            ·
              refine ⟨3230094660192971405855321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8613585760514590415614189 3230094660192971405855321)
              ·
                refine ⟨2422570995144728554391491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230094660192971405855321 2422570995144728554391491)
                ·
                  refine ⟨3633856492717092831587237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422570995144728554391491 3633856492717092831587237)
                  ·
                    refine ⟨681348092384454905922607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3633856492717092831587237 681348092384454905922607)
                    ·
                      rfl

theorem cell22_1990381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1990381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990381 prefixEnd_1990381 := by exact prefixLift 1990381
  have htrace : WordTrace (prefixWord ++ tailWord_1990381) baseStart_1990381 baseEnd_1990381 := by
    simpa [prefixWord, tailWord_1990381, baseEnd_1990381] using wordTrace_append hprefix tailTrace_1990381
  have hstable : (prefixWord ++ tailWord_1990381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990381).length < 2 ^ (prefixWord ++ tailWord_1990381).sum := by decide
  have hdescent : baseEnd_1990381 < baseStart_1990381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990406 : List Nat := [6, 2, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1990406 : Nat := 118140960795 + 1990406 * 2 ^ 59
def prefixEnd_1990406 : Nat := 4983230072969 + 3 ^ 40 * 1990406 * 2
def baseEnd_1990406 : Nat := 681356650395363174047531

theorem tailTrace_1990406 : CollatzResearch.WordTrace tailWord_1990406 prefixEnd_1990406 681356650395363174047531 := by
  unfold tailWord_1990406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268627213347077222698721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48397380551404314084239381 2268627213347077222698721)
  ·
    refine ⟨1701470410010307917024041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2268627213347077222698721 1701470410010307917024041)
    ·
      refine ⟨1276102807507730937768031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1701470410010307917024041 1276102807507730937768031)
      ·
        refine ⟨1914154211261596406652047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276102807507730937768031 1914154211261596406652047)
        ·
          refine ⟨2871231316892394609978071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914154211261596406652047 2871231316892394609978071)
          ·
            refine ⟨4306846975338591914967107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871231316892394609978071 4306846975338591914967107)
            ·
              refine ⟨6460270463007887872450661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4306846975338591914967107 6460270463007887872450661)
              ·
                refine ⟨1211300711813978976084499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6460270463007887872450661 1211300711813978976084499)
                ·
                  refine ⟨1816951067720968464126749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211300711813978976084499 1816951067720968464126749)
                  ·
                    refine ⟨681356650395363174047531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816951067720968464126749 681356650395363174047531)
                    ·
                      rfl

theorem cell22_1990406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1990406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990406 prefixEnd_1990406 := by exact prefixLift 1990406
  have htrace : WordTrace (prefixWord ++ tailWord_1990406) baseStart_1990406 baseEnd_1990406 := by
    simpa [prefixWord, tailWord_1990406, baseEnd_1990406] using wordTrace_append hprefix tailTrace_1990406
  have hstable : (prefixWord ++ tailWord_1990406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990406).length < 2 ^ (prefixWord ++ tailWord_1990406).sum := by decide
  have hdescent : baseEnd_1990406 < baseStart_1990406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990407 : List Nat := [1, 1, 4, 4, 12]
def baseStart_1990407 : Nat := 118140960795 + 1990407 * 2 ^ 59
def prefixEnd_1990407 : Nat := 4983230072969 + 3 ^ 40 * 1990407 * 2
def baseEnd_1990407 : Nat := 2803938241628804546389

theorem tailTrace_1990407 : CollatzResearch.WordTrace tailWord_1990407 prefixEnd_1990407 2803938241628804546389 := by
  unfold tailWord_1990407
  simp only [CollatzResearch.WordTrace]
  refine ⟨72596107300102848297145475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48397404866735232198096983 72596107300102848297145475)
  ·
    refine ⟨108894160950154272445718213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72596107300102848297145475 108894160950154272445718213)
    ·
      refine ⟨20417655178153926083572165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108894160950154272445718213 20417655178153926083572165)
      ·
        refine ⟨3828310345903861140669781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20417655178153926083572165 3828310345903861140669781)
        ·
          refine ⟨2803938241628804546389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3828310345903861140669781 2803938241628804546389)
          ·
            rfl

theorem cell22_1990407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 12].length) (baseStart_1990407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990407 prefixEnd_1990407 := by exact prefixLift 1990407
  have htrace : WordTrace (prefixWord ++ tailWord_1990407) baseStart_1990407 baseEnd_1990407 := by
    simpa [prefixWord, tailWord_1990407, baseEnd_1990407] using wordTrace_append hprefix tailTrace_1990407
  have hstable : (prefixWord ++ tailWord_1990407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990407).length < 2 ^ (prefixWord ++ tailWord_1990407).sum := by decide
  have hdescent : baseEnd_1990407 < baseStart_1990407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990531 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 6]
def baseStart_1990531 : Nat := 118140960795 + 1990531 * 2 ^ 59
def prefixEnd_1990531 : Nat := 4983230072969 + 3 ^ 40 * 1990531 * 2
def baseEnd_1990531 : Nat := 227133146816634838224049

theorem tailTrace_1990531 : CollatzResearch.WordTrace tailWord_1990531 prefixEnd_1990531 227133146816634838224049 := by
  unfold tailWord_1990531
  simp only [CollatzResearch.WordTrace]
  refine ⟨72600629951653617474659447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48400419967769078316439631 72600629951653617474659447)
  ·
    refine ⟨108900944927480426211989171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72600629951653617474659447 108900944927480426211989171)
    ·
      refine ⟨163351417391220639317983757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108900944927480426211989171 163351417391220639317983757)
      ·
        refine ⟨61256781521707739744243909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163351417391220639317983757 61256781521707739744243909)
        ·
          refine ⟨11485646535320201202045733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61256781521707739744243909 11485646535320201202045733)
          ·
            refine ⟨2153558725372537725383575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11485646535320201202045733 2153558725372537725383575)
            ·
              refine ⟨3230338088058806588075363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153558725372537725383575 3230338088058806588075363)
              ·
                refine ⟨4845507132088209882113045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230338088058806588075363 4845507132088209882113045)
                ·
                  refine ⟨227133146816634838224049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4845507132088209882113045 227133146816634838224049)
                  ·
                    rfl

theorem cell22_1990531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 6].length) (baseStart_1990531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990531 prefixEnd_1990531 := by exact prefixLift 1990531
  have htrace : WordTrace (prefixWord ++ tailWord_1990531) baseStart_1990531 baseEnd_1990531 := by
    simpa [prefixWord, tailWord_1990531, baseEnd_1990531] using wordTrace_append hprefix tailTrace_1990531
  have hstable : (prefixWord ++ tailWord_1990531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990531).length < 2 ^ (prefixWord ++ tailWord_1990531).sum := by decide
  have hdescent : baseEnd_1990531 < baseStart_1990531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990591 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 3, 3]
def baseStart_1990591 : Nat := 118140960795 + 1990591 * 2 ^ 59
def prefixEnd_1990591 : Nat := 4983230072969 + 3 ^ 40 * 1990591 * 2
def baseEnd_1990591 : Nat := 681419979676084358171963

theorem tailTrace_1990591 : CollatzResearch.WordTrace tailWord_1990591 prefixEnd_1990591 681419979676084358171963 := by
  unfold tailWord_1990591
  simp only [CollatzResearch.WordTrace]
  refine ⟨72602818331436247721843627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48401878887624165147895751 72602818331436247721843627)
  ·
    refine ⟨108904227497154371582765441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72602818331436247721843627 108904227497154371582765441)
    ·
      refine ⟨81678170622865778687074081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108904227497154371582765441 81678170622865778687074081)
      ·
        refine ⟨61258627967149334015305561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81678170622865778687074081 61258627967149334015305561)
        ·
          refine ⟨45943970975362000511479171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61258627967149334015305561 45943970975362000511479171)
          ·
            refine ⟨68915956463043000767218757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45943970975362000511479171 68915956463043000767218757)
            ·
              refine ⟨12921741836820562643853517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68915956463043000767218757 12921741836820562643853517)
              ·
                refine ⟨4845653188807710991445069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12921741836820562643853517 4845653188807710991445069)
                ·
                  refine ⟨1817119945802891621791901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4845653188807710991445069 1817119945802891621791901)
                  ·
                    refine ⟨681419979676084358171963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817119945802891621791901 681419979676084358171963)
                    ·
                      rfl

theorem cell22_1990591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_1990591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990591 prefixEnd_1990591 := by exact prefixLift 1990591
  have htrace : WordTrace (prefixWord ++ tailWord_1990591) baseStart_1990591 baseEnd_1990591 := by
    simpa [prefixWord, tailWord_1990591, baseEnd_1990591] using wordTrace_append hprefix tailTrace_1990591
  have hstable : (prefixWord ++ tailWord_1990591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990591).length < 2 ^ (prefixWord ++ tailWord_1990591).sum := by decide
  have hdescent : baseEnd_1990591 < baseStart_1990591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990638 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_1990638 : Nat := 118140960795 + 1990638 * 2 ^ 59
def prefixEnd_1990638 : Nat := 4983230072969 + 3 ^ 40 * 1990638 * 2
def baseEnd_1990638 : Nat := 227145356245530634082273

theorem tailTrace_1990638 : CollatzResearch.WordTrace tailWord_1990638 prefixEnd_1990638 227145356245530634082273 := by
  unfold tailWord_1990638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075566570283246843600571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48403021708177316499203045 9075566570283246843600571)
  ·
    refine ⟨13613349855424870265400857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9075566570283246843600571 13613349855424870265400857)
    ·
      refine ⟨10210012391568652699050643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13613349855424870265400857 10210012391568652699050643)
      ·
        refine ⟨15315018587352979048575965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10210012391568652699050643 15315018587352979048575965)
        ·
          refine ⟨5743131970257367143215987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15315018587352979048575965 5743131970257367143215987)
          ·
            refine ⟨8614697955386050714823981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743131970257367143215987 8614697955386050714823981)
            ·
              refine ⟨3230511733269769018058993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8614697955386050714823981 3230511733269769018058993)
              ·
                refine ⟨2422883799952326763544245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230511733269769018058993 2422883799952326763544245)
                ·
                  refine ⟨227145356245530634082273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422883799952326763544245 227145356245530634082273)
                  ·
                    rfl

theorem cell22_1990638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_1990638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990638 prefixEnd_1990638 := by exact prefixLift 1990638
  have htrace : WordTrace (prefixWord ++ tailWord_1990638) baseStart_1990638 baseEnd_1990638 := by
    simpa [prefixWord, tailWord_1990638, baseEnd_1990638] using wordTrace_append hprefix tailTrace_1990638
  have hstable : (prefixWord ++ tailWord_1990638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990638).length < 2 ^ (prefixWord ++ tailWord_1990638).sum := by decide
  have hdescent : baseEnd_1990638 < baseStart_1990638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990668 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_1990668 : Nat := 118140960795 + 1990668 * 2 ^ 59
def prefixEnd_1990668 : Nat := 4983230072969 + 3 ^ 40 * 1990668 * 2
def baseEnd_1990668 : Nat := 681446338349681823996727

theorem tailTrace_1990668 : CollatzResearch.WordTrace tailWord_1990668 prefixEnd_1990668 681446338349681823996727 := by
  unfold tailWord_1990668
  simp only [CollatzResearch.WordTrace]
  refine ⟨36302813376078644936198329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48403751168104859914931105 36302813376078644936198329)
  ·
    refine ⟨27227110032058983702148747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36302813376078644936198329 27227110032058983702148747)
    ·
      refine ⟨40840665048088475553223121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27227110032058983702148747 40840665048088475553223121)
      ·
        refine ⟨30630498786066356664917341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40840665048088475553223121 30630498786066356664917341)
        ·
          refine ⟨11486437044774883749344003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30630498786066356664917341 11486437044774883749344003)
          ·
            refine ⟨17229655567162325624016005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11486437044774883749344003 17229655567162325624016005)
            ·
              refine ⟨3230560418842936054503001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17229655567162325624016005 3230560418842936054503001)
              ·
                refine ⟨2422920314132202040877251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230560418842936054503001 2422920314132202040877251)
                ·
                  refine ⟨3634380471198303061315877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422920314132202040877251 3634380471198303061315877)
                  ·
                    refine ⟨681446338349681823996727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3634380471198303061315877 681446338349681823996727)
                    ·
                      rfl

theorem cell22_1990668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_1990668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990668 prefixEnd_1990668 := by exact prefixLift 1990668
  have htrace : WordTrace (prefixWord ++ tailWord_1990668) baseStart_1990668 baseEnd_1990668 := by
    simpa [prefixWord, tailWord_1990668, baseEnd_1990668] using wordTrace_append hprefix tailTrace_1990668
  have hstable : (prefixWord ++ tailWord_1990668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990668).length < 2 ^ (prefixWord ++ tailWord_1990668).sum := by decide
  have hdescent : baseEnd_1990668 < baseStart_1990668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990676 : List Nat := [2, 4, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1990676 : Nat := 118140960795 + 1990676 * 2 ^ 59
def prefixEnd_1990676 : Nat := 4983230072969 + 3 ^ 40 * 1990676 * 2
def baseEnd_1990676 : Nat := 681449076913172469796703

theorem tailTrace_1990676 : CollatzResearch.WordTrace tailWord_1990676 prefixEnd_1990676 681449076913172469796703 := by
  unfold tailWord_1990676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36302959268064153619343941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48403945690752204825791921 36302959268064153619343941)
  ·
    refine ⟨6806804862762028803626989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36302959268064153619343941 6806804862762028803626989)
    ·
      refine ⟨2552551823535760801360121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6806804862762028803626989 2552551823535760801360121)
      ·
        refine ⟨1914413867651820601020091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2552551823535760801360121 1914413867651820601020091)
        ·
          refine ⟨2871620801477730901530137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914413867651820601020091 2871620801477730901530137)
          ·
            refine ⟨2153715601108298176147603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2871620801477730901530137 2153715601108298176147603)
            ·
              refine ⟨3230573401662447264221405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153715601108298176147603 3230573401662447264221405)
              ·
                refine ⟨1211465025623417724083027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3230573401662447264221405 1211465025623417724083027)
                ·
                  refine ⟨1817197538435126586124541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211465025623417724083027 1817197538435126586124541)
                  ·
                    refine ⟨681449076913172469796703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817197538435126586124541 681449076913172469796703)
                    ·
                      rfl

theorem cell22_1990676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1990676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990676 prefixEnd_1990676 := by exact prefixLift 1990676
  have htrace : WordTrace (prefixWord ++ tailWord_1990676) baseStart_1990676 baseEnd_1990676 := by
    simpa [prefixWord, tailWord_1990676, baseEnd_1990676] using wordTrace_append hprefix tailTrace_1990676
  have hstable : (prefixWord ++ tailWord_1990676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990676).length < 2 ^ (prefixWord ++ tailWord_1990676).sum := by decide
  have hdescent : baseEnd_1990676 < baseStart_1990676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990756 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1990756 : Nat := 118140960795 + 1990756 * 2 ^ 59
def prefixEnd_1990756 : Nat := 4983230072969 + 3 ^ 40 * 1990756 * 2
def baseEnd_1990756 : Nat := 227158820849359642598819

theorem tailTrace_1990756 : CollatzResearch.WordTrace tailWord_1990756 prefixEnd_1990756 227158820849359642598819 := by
  unfold tailWord_1990756
  simp only [CollatzResearch.WordTrace]
  refine ⟨36304418187919240450800061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48405890917225653934400081 36304418187919240450800061)
  ·
    refine ⟨13614156820469715169050023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36304418187919240450800061 13614156820469715169050023)
    ·
      refine ⟨20421235230704572753575035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13614156820469715169050023 20421235230704572753575035)
      ·
        refine ⟨30631852846056859130362553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20421235230704572753575035 30631852846056859130362553)
        ·
          refine ⟨22973889634542644347771915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30631852846056859130362553 22973889634542644347771915)
          ·
            refine ⟨34460834451813966521657873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22973889634542644347771915 34460834451813966521657873)
            ·
              refine ⟨25845625838860474891243405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34460834451813966521657873 25845625838860474891243405)
              ·
                refine ⟨9692109689572678084216277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25845625838860474891243405 9692109689572678084216277)
                ·
                  refine ⟨227158820849359642598819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9692109689572678084216277 227158820849359642598819)
                  ·
                    rfl

theorem cell22_1990756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1990756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990756 prefixEnd_1990756 := by exact prefixLift 1990756
  have htrace : WordTrace (prefixWord ++ tailWord_1990756) baseStart_1990756 baseEnd_1990756 := by
    simpa [prefixWord, tailWord_1990756, baseEnd_1990756] using wordTrace_append hprefix tailTrace_1990756
  have hstable : (prefixWord ++ tailWord_1990756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990756).length < 2 ^ (prefixWord ++ tailWord_1990756).sum := by decide
  have hdescent : baseEnd_1990756 < baseStart_1990756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990807 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 5]
def baseStart_1990807 : Nat := 118140960795 + 1990807 * 2 ^ 59
def prefixEnd_1990807 : Nat := 4983230072969 + 3 ^ 40 * 1990807 * 2
def baseEnd_1990807 : Nat := 227164640296777264923767

theorem tailTrace_1990807 : CollatzResearch.WordTrace tailWord_1990807 prefixEnd_1990807 227164640296777264923767 := by
  unfold tailWord_1990807
  simp only [CollatzResearch.WordTrace]
  refine ⟨72610696498653716611706675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48407130999102477741137783 72610696498653716611706675)
  ·
    refine ⟨108916044747980574917560013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72610696498653716611706675 108916044747980574917560013)
    ·
      refine ⟨40843516780492715594085005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108916044747980574917560013 40843516780492715594085005)
      ·
        refine ⟨15316318792684768347781877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40843516780492715594085005 15316318792684768347781877)
        ·
          refine ⟨1435904886814197032604551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15316318792684768347781877 1435904886814197032604551)
          ·
            refine ⟨2153857330221295548906827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435904886814197032604551 2153857330221295548906827)
            ·
              refine ⟨3230785995331943323360241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153857330221295548906827 3230785995331943323360241)
              ·
                refine ⟨2423089496498957492520181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3230785995331943323360241 2423089496498957492520181)
                ·
                  refine ⟨227164640296777264923767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2423089496498957492520181 227164640296777264923767)
                  ·
                    rfl

theorem cell22_1990807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 5].length) (baseStart_1990807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990807 prefixEnd_1990807 := by exact prefixLift 1990807
  have htrace : WordTrace (prefixWord ++ tailWord_1990807) baseStart_1990807 baseEnd_1990807 := by
    simpa [prefixWord, tailWord_1990807, baseEnd_1990807] using wordTrace_append hprefix tailTrace_1990807
  have hstable : (prefixWord ++ tailWord_1990807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990807).length < 2 ^ (prefixWord ++ tailWord_1990807).sum := by decide
  have hdescent : baseEnd_1990807 < baseStart_1990807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990848 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_1990848 : Nat := 118140960795 + 1990848 * 2 ^ 59
def prefixEnd_1990848 : Nat := 4983230072969 + 3 ^ 40 * 1990848 * 2
def baseEnd_1990848 : Nat := 681507956028221354496175

theorem tailTrace_1990848 : CollatzResearch.WordTrace tailWord_1990848 prefixEnd_1990848 681507956028221354496175 := by
  unfold tailWord_1990848
  simp only [CollatzResearch.WordTrace]
  refine ⟨36306095945752590306974599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48408127927670120409299465 36306095945752590306974599)
  ·
    refine ⟨54459143918628885460461899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36306095945752590306974599 54459143918628885460461899)
    ·
      refine ⟨81688715877943328190692849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54459143918628885460461899 81688715877943328190692849)
      ·
        refine ⟨61266536908457496143019637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81688715877943328190692849 61266536908457496143019637)
        ·
          refine ⟨5743737835167890263408091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61266536908457496143019637 5743737835167890263408091)
          ·
            refine ⟨8615606752751835395112137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743737835167890263408091 8615606752751835395112137)
            ·
              refine ⟨6461705064563876546334103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8615606752751835395112137 6461705064563876546334103)
              ·
                refine ⟨9692557596845814819501155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6461705064563876546334103 9692557596845814819501155)
                ·
                  refine ⟨14538836395268722229251733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9692557596845814819501155 14538836395268722229251733)
                  ·
                    refine ⟨681507956028221354496175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14538836395268722229251733 681507956028221354496175)
                    ·
                      rfl

theorem cell22_1990848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_1990848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990848 prefixEnd_1990848 := by exact prefixLift 1990848
  have htrace : WordTrace (prefixWord ++ tailWord_1990848) baseStart_1990848 baseEnd_1990848 := by
    simpa [prefixWord, tailWord_1990848, baseEnd_1990848] using wordTrace_append hprefix tailTrace_1990848
  have hstable : (prefixWord ++ tailWord_1990848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990848).length < 2 ^ (prefixWord ++ tailWord_1990848).sum := by decide
  have hdescent : baseEnd_1990848 < baseStart_1990848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990852 : List Nat := [2, 3, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1990852 : Nat := 118140960795 + 1990852 * 2 ^ 59
def prefixEnd_1990852 : Nat := 4983230072969 + 3 ^ 40 * 1990852 * 2
def baseEnd_1990852 : Nat := 227169775103322225798721

theorem tailTrace_1990852 : CollatzResearch.WordTrace tailWord_1990852 prefixEnd_1990852 227169775103322225798721 := by
  unfold tailWord_1990852
  simp only [CollatzResearch.WordTrace]
  refine ⟨36306168891745344648547405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48408225188993792864729873 36306168891745344648547405)
  ·
    refine ⟨13614813334404504243205277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36306168891745344648547405 13614813334404504243205277)
    ·
      refine ⟨5105555000401689091201979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13614813334404504243205277 5105555000401689091201979)
      ·
        refine ⟨7658332500602533636802969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105555000401689091201979 7658332500602533636802969)
        ·
          refine ⟨5743749375451900227602227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7658332500602533636802969 5743749375451900227602227)
          ·
            refine ⟨8615624063177850341403341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743749375451900227602227 8615624063177850341403341)
            ·
              refine ⟨3230859023691693878026253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8615624063177850341403341 3230859023691693878026253)
              ·
                refine ⟨1211572133884385204259845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3230859023691693878026253 1211572133884385204259845)
                ·
                  refine ⟨227169775103322225798721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211572133884385204259845 227169775103322225798721)
                  ·
                    rfl

theorem cell22_1990852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1990852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990852 prefixEnd_1990852 := by exact prefixLift 1990852
  have htrace : WordTrace (prefixWord ++ tailWord_1990852) baseStart_1990852 baseEnd_1990852 := by
    simpa [prefixWord, tailWord_1990852, baseEnd_1990852] using wordTrace_append hprefix tailTrace_1990852
  have hstable : (prefixWord ++ tailWord_1990852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990852).length < 2 ^ (prefixWord ++ tailWord_1990852).sum := by decide
  have hdescent : baseEnd_1990852 < baseStart_1990852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990869 : List Nat := [1, 3, 2, 4, 2, 1, 3, 2, 4]
def baseStart_1990869 : Nat := 118140960795 + 1990869 * 2 ^ 59
def prefixEnd_1990869 : Nat := 4983230072969 + 3 ^ 40 * 1990869 * 2
def baseEnd_1990869 : Nat := 227171714919128099907037

theorem tailTrace_1990869 : CollatzResearch.WordTrace tailWord_1990869 prefixEnd_1990869 227171714919128099907037 := by
  unfold tailWord_1990869
  simp only [CollatzResearch.WordTrace]
  refine ⟨72612957824429101200463661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48408638549619400800309107 72612957824429101200463661)
  ·
    refine ⟨27229859184160912950173873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72612957824429101200463661 27229859184160912950173873)
    ·
      refine ⟨20422394388120684712630405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27229859184160912950173873 20422394388120684712630405)
      ·
        refine ⟨3829198947772628383618201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20422394388120684712630405 3829198947772628383618201)
        ·
          refine ⟨2871899210829471287713651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3829198947772628383618201 2871899210829471287713651)
          ·
            refine ⟨4307848816244206931570477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871899210829471287713651 4307848816244206931570477)
            ·
              refine ⟨1615443306091577599338929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4307848816244206931570477 1615443306091577599338929)
              ·
                refine ⟨1211582479568683199504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615443306091577599338929 1211582479568683199504197)
                ·
                  refine ⟨227171714919128099907037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211582479568683199504197 227171714919128099907037)
                  ·
                    rfl

theorem cell22_1990869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_1990869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990869 prefixEnd_1990869 := by exact prefixLift 1990869
  have htrace : WordTrace (prefixWord ++ tailWord_1990869) baseStart_1990869 baseEnd_1990869 := by
    simpa [prefixWord, tailWord_1990869, baseEnd_1990869] using wordTrace_append hprefix tailTrace_1990869
  have hstable : (prefixWord ++ tailWord_1990869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990869).length < 2 ^ (prefixWord ++ tailWord_1990869).sum := by decide
  have hdescent : baseEnd_1990869 < baseStart_1990869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990923 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 2, 5]
def baseStart_1990923 : Nat := 118140960795 + 1990923 * 2 ^ 59
def prefixEnd_1990923 : Nat := 4983230072969 + 3 ^ 40 * 1990923 * 2
def baseEnd_1990923 : Nat := 681533630060946158870945

theorem tailTrace_1990923 : CollatzResearch.WordTrace tailWord_1990923 prefixEnd_1990923 681533630060946158870945 := by
  unfold tailWord_1990923
  simp only [CollatzResearch.WordTrace]
  refine ⟨72614927366233468422929423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48409951577488978948619615 72614927366233468422929423)
  ·
    refine ⟨108922391049350202634394135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72614927366233468422929423 108922391049350202634394135)
    ·
      refine ⟨163383586574025303951591203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108922391049350202634394135 163383586574025303951591203)
      ·
        refine ⟨245075379861037955927386805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163383586574025303951591203 245075379861037955927386805)
        ·
          refine ⟨22975816861972308368192513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245075379861037955927386805 22975816861972308368192513)
          ·
            refine ⟨17231862646479231276144385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22975816861972308368192513 17231862646479231276144385)
            ·
              refine ⟨12923896984859423457108289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17231862646479231276144385 12923896984859423457108289)
              ·
                refine ⟨9692922738644567592831217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12923896984859423457108289 9692922738644567592831217)
                ·
                  refine ⟨7269692053983425694623413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9692922738644567592831217 7269692053983425694623413)
                  ·
                    refine ⟨681533630060946158870945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7269692053983425694623413 681533630060946158870945)
                    ·
                      rfl

theorem cell22_1990923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_1990923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990923 prefixEnd_1990923 := by exact prefixLift 1990923
  have htrace : WordTrace (prefixWord ++ tailWord_1990923) baseStart_1990923 baseEnd_1990923 := by
    simpa [prefixWord, tailWord_1990923, baseEnd_1990923] using wordTrace_append hprefix tailTrace_1990923
  have hstable : (prefixWord ++ tailWord_1990923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990923).length < 2 ^ (prefixWord ++ tailWord_1990923).sum := by decide
  have hdescent : baseEnd_1990923 < baseStart_1990923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990929 : List Nat := [1, 2, 2, 1, 1, 5, 4, 2, 1, 3]
def baseStart_1990929 : Nat := 118140960795 + 1990929 * 2 ^ 59
def prefixEnd_1990929 : Nat := 4983230072969 + 3 ^ 40 * 1990929 * 2
def baseEnd_1990929 : Nat := 681535683983564143220927

theorem tailTrace_1990929 : CollatzResearch.WordTrace tailWord_1990929 prefixEnd_1990929 681535683983564143220927 := by
  unfold tailWord_1990929
  simp only [CollatzResearch.WordTrace]
  refine ⟨72615146204211731447647841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48410097469474487631765227 72615146204211731447647841)
  ·
    refine ⟨54461359653158798585735881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72615146204211731447647841 54461359653158798585735881)
    ·
      refine ⟨40846019739869098939301911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54461359653158798585735881 40846019739869098939301911)
      ·
        refine ⟨61269029609803648408952867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40846019739869098939301911 61269029609803648408952867)
        ·
          refine ⟨91903544414705472613429301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61269029609803648408952867 91903544414705472613429301)
          ·
            refine ⟨8615957288878638057508997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91903544414705472613429301 8615957288878638057508997)
            ·
              refine ⟨1615491991664744635782937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8615957288878638057508997 1615491991664744635782937)
              ·
                refine ⟨1211618993748558476837203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615491991664744635782937 1211618993748558476837203)
                ·
                  refine ⟨1817428490622837715255805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211618993748558476837203 1817428490622837715255805)
                  ·
                    refine ⟨681535683983564143220927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817428490622837715255805 681535683983564143220927)
                    ·
                      rfl

theorem cell22_1990929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_1990929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1990929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1990929 prefixEnd_1990929 := by exact prefixLift 1990929
  have htrace : WordTrace (prefixWord ++ tailWord_1990929) baseStart_1990929 baseEnd_1990929 := by
    simpa [prefixWord, tailWord_1990929, baseEnd_1990929] using wordTrace_append hprefix tailTrace_1990929
  have hstable : (prefixWord ++ tailWord_1990929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990929).length < 2 ^ (prefixWord ++ tailWord_1990929).sum := by decide
  have hdescent : baseEnd_1990929 < baseStart_1990929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991015 : List Nat := [1, 1, 5, 1, 3, 2, 1, 8]
def baseStart_1991015 : Nat := 118140960795 + 1991015 * 2 ^ 59
def prefixEnd_1991015 : Nat := 4983230072969 + 3 ^ 40 * 1991015 * 2
def baseEnd_1991015 : Nat := 75729458171232065063407

theorem tailTrace_1991015 : CollatzResearch.WordTrace tailWord_1991015 prefixEnd_1991015 75729458171232065063407 := by
  unfold tailWord_1991015
  simp only [CollatzResearch.WordTrace]
  refine ⟨72618282881900168135278499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48412188587933445423518999 72618282881900168135278499)
  ·
    refine ⟨108927424322850252202917749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72618282881900168135278499 108927424322850252202917749)
    ·
      refine ⟨10211946030267211144023539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108927424322850252202917749 10211946030267211144023539)
      ·
        refine ⟨15317919045400816716035309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10211946030267211144023539 15317919045400816716035309)
        ·
          refine ⟨5744219642025306268513241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15317919045400816716035309 5744219642025306268513241)
          ·
            refine ⟨4308164731518979701384931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5744219642025306268513241 4308164731518979701384931)
            ·
              refine ⟨6462247097278469552077397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308164731518979701384931 6462247097278469552077397)
              ·
                refine ⟨75729458171232065063407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6462247097278469552077397 75729458171232065063407)
                ·
                  rfl

theorem cell22_1991015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 8].length) (baseStart_1991015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991015 prefixEnd_1991015 := by exact prefixLift 1991015
  have htrace : WordTrace (prefixWord ++ tailWord_1991015) baseStart_1991015 baseEnd_1991015 := by
    simpa [prefixWord, tailWord_1991015, baseEnd_1991015] using wordTrace_append hprefix tailTrace_1991015
  have hstable : (prefixWord ++ tailWord_1991015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991015).length < 2 ^ (prefixWord ++ tailWord_1991015).sum := by decide
  have hdescent : baseEnd_1991015 < baseStart_1991015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991137 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1991137 : Nat := 118140960795 + 1991137 * 2 ^ 59
def prefixEnd_1991137 : Nat := 4983230072969 + 3 ^ 40 * 1991137 * 2
def baseEnd_1991137 : Nat := 681606886634320934020289

theorem tailTrace_1991137 : CollatzResearch.WordTrace tailWord_1991137 prefixEnd_1991137 681606886634320934020289 := by
  unfold tailWord_1991137
  simp only [CollatzResearch.WordTrace]
  refine ⟨72622732587458182971219665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48415155058305455314146443 72622732587458182971219665)
  ·
    refine ⟨54467049440593637228414749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72622732587458182971219665 54467049440593637228414749)
    ·
      refine ⟨20425143540222613960655531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54467049440593637228414749 20425143540222613960655531)
      ·
        refine ⟨30637715310333920940983297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20425143540222613960655531 30637715310333920940983297)
        ·
          refine ⟨22978286482750440705737473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30637715310333920940983297 22978286482750440705737473)
          ·
            refine ⟨17233714862062830529303105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22978286482750440705737473 17233714862062830529303105)
            ·
              refine ⟨12925286146547122896977329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17233714862062830529303105 12925286146547122896977329)
              ·
                refine ⟨9693964609910342172732997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12925286146547122896977329 9693964609910342172732997)
                ·
                  refine ⟨1817618364358189157387437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9693964609910342172732997 1817618364358189157387437)
                  ·
                    refine ⟨681606886634320934020289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817618364358189157387437 681606886634320934020289)
                    ·
                      rfl

theorem cell22_1991137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1991137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991137 prefixEnd_1991137 := by exact prefixLift 1991137
  have htrace : WordTrace (prefixWord ++ tailWord_1991137) baseStart_1991137 baseEnd_1991137 := by
    simpa [prefixWord, tailWord_1991137, baseEnd_1991137] using wordTrace_append hprefix tailTrace_1991137
  have hstable : (prefixWord ++ tailWord_1991137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991137).length < 2 ^ (prefixWord ++ tailWord_1991137).sum := by decide
  have hdescent : baseEnd_1991137 < baseStart_1991137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991229 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1991229 : Nat := 118140960795 + 1991229 * 2 ^ 59
def prefixEnd_1991229 : Nat := 4983230072969 + 3 ^ 40 * 1991229 * 2
def baseEnd_1991229 : Nat := 227212793371487786906669

theorem tailTrace_1991229 : CollatzResearch.WordTrace tailWord_1991229 prefixEnd_1991229 227212793371487786906669 := by
  unfold tailWord_1991229
  simp only [CollatzResearch.WordTrace]
  refine ⟨72626088103124882683568741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48417392068749921789045827 72626088103124882683568741)
  ·
    refine ⟨13617391519335915503169139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72626088103124882683568741 13617391519335915503169139)
    ·
      refine ⟨20426087279003873254753709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13617391519335915503169139 20426087279003873254753709)
      ·
        refine ⟨7659782729626452470532641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20426087279003873254753709 7659782729626452470532641)
        ·
          refine ⟨5744837047219839352899481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7659782729626452470532641 5744837047219839352899481)
          ·
            refine ⟨4308627785414879514674611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5744837047219839352899481 4308627785414879514674611)
            ·
              refine ⟨6462941678122319272011917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308627785414879514674611 6462941678122319272011917)
              ·
                refine ⟨2423603129295869727004469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6462941678122319272011917 2423603129295869727004469)
                ·
                  refine ⟨227212793371487786906669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2423603129295869727004469 227212793371487786906669)
                  ·
                    rfl

theorem cell22_1991229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1991229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991229 prefixEnd_1991229 := by exact prefixLift 1991229
  have htrace : WordTrace (prefixWord ++ tailWord_1991229) baseStart_1991229 baseEnd_1991229 := by
    simpa [prefixWord, tailWord_1991229, baseEnd_1991229] using wordTrace_append hprefix tailTrace_1991229
  have hstable : (prefixWord ++ tailWord_1991229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991229).length < 2 ^ (prefixWord ++ tailWord_1991229).sum := by decide
  have hdescent : baseEnd_1991229 < baseStart_1991229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991287 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1991287 : Nat := 118140960795 + 1991287 * 2 ^ 59
def prefixEnd_1991287 : Nat := 4983230072969 + 3 ^ 40 * 1991287 * 2
def baseEnd_1991287 : Nat := 681658234699770542769829

theorem tailTrace_1991287 : CollatzResearch.WordTrace tailWord_1991287 prefixEnd_1991287 681658234699770542769829 := by
  unfold tailWord_1991287
  simp only [CollatzResearch.WordTrace]
  refine ⟨72628203536914758589180115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48418802357943172392786743 72628203536914758589180115)
  ·
    refine ⟨108942305305372137883770173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72628203536914758589180115 108942305305372137883770173)
    ·
      refine ⟨40853364489514551706413815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108942305305372137883770173 40853364489514551706413815)
      ·
        refine ⟨61280046734271827559620723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40853364489514551706413815 61280046734271827559620723)
        ·
          refine ⟨91920070101407741339431085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61280046734271827559620723 91920070101407741339431085)
          ·
            refine ⟨34470026288027903002286657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91920070101407741339431085 34470026288027903002286657)
            ·
              refine ⟨25852519716020927251714993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34470026288027903002286657 25852519716020927251714993)
              ·
                refine ⟨19389389787015695438786245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25852519716020927251714993 19389389787015695438786245)
                ·
                  refine ⟨3635510585065442894772421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19389389787015695438786245 3635510585065442894772421)
                  ·
                    refine ⟨681658234699770542769829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3635510585065442894772421 681658234699770542769829)
                    ·
                      rfl

theorem cell22_1991287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1991287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991287 prefixEnd_1991287 := by exact prefixLift 1991287
  have htrace : WordTrace (prefixWord ++ tailWord_1991287) baseStart_1991287 baseEnd_1991287 := by
    simpa [prefixWord, tailWord_1991287, baseEnd_1991287] using wordTrace_append hprefix tailTrace_1991287
  have hstable : (prefixWord ++ tailWord_1991287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991287).length < 2 ^ (prefixWord ++ tailWord_1991287).sum := by decide
  have hdescent : baseEnd_1991287 < baseStart_1991287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991289 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_1991289 : Nat := 118140960795 + 1991289 * 2 ^ 59
def prefixEnd_1991289 : Nat := 4983230072969 + 3 ^ 40 * 1991289 * 2
def baseEnd_1991289 : Nat := 681658919340643204219823

theorem tailTrace_1991289 : CollatzResearch.WordTrace tailWord_1991289 prefixEnd_1991289 681658919340643204219823 := by
  unfold tailWord_1991289
  simp only [CollatzResearch.WordTrace]
  refine ⟨72628276482907512930752921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48418850988605008620501947 72628276482907512930752921)
  ·
    refine ⟨54471207362180634698064691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72628276482907512930752921 54471207362180634698064691)
    ·
      refine ⟨81706811043270952047097037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54471207362180634698064691 81706811043270952047097037)
      ·
        refine ⟨30640054141226607017661389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81706811043270952047097037 30640054141226607017661389)
        ·
          refine ⟨11490020302959977631623021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30640054141226607017661389 11490020302959977631623021)
          ·
            refine ⟨4308757613609991611858633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11490020302959977631623021 4308757613609991611858633)
            ·
              refine ⟨3231568210207493708893975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4308757613609991611858633 3231568210207493708893975)
              ·
                refine ⟨4847352315311240563340963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231568210207493708893975 4847352315311240563340963)
                ·
                  refine ⟨7271028472966860845011445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4847352315311240563340963 7271028472966860845011445)
                  ·
                    refine ⟨681658919340643204219823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7271028472966860845011445 681658919340643204219823)
                    ·
                      rfl

theorem cell22_1991289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_1991289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991289 prefixEnd_1991289 := by exact prefixLift 1991289
  have htrace : WordTrace (prefixWord ++ tailWord_1991289) baseStart_1991289 baseEnd_1991289 := by
    simpa [prefixWord, tailWord_1991289, baseEnd_1991289] using wordTrace_append hprefix tailTrace_1991289
  have hstable : (prefixWord ++ tailWord_1991289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991289).length < 2 ^ (prefixWord ++ tailWord_1991289).sum := by decide
  have hdescent : baseEnd_1991289 < baseStart_1991289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991364 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 7]
def baseStart_1991364 : Nat := 118140960795 + 1991364 * 2 ^ 59
def prefixEnd_1991364 : Nat := 4983230072969 + 3 ^ 40 * 1991364 * 2
def baseEnd_1991364 : Nat := 227228197791122669531531

theorem tailTrace_1991364 : CollatzResearch.WordTrace tailWord_1991364 prefixEnd_1991364 227228197791122669531531 := by
  unfold tailWord_1991364
  simp only [CollatzResearch.WordTrace]
  refine ⟨36315505978817900369866573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48420674638423867159822097 36315505978817900369866573)
  ·
    refine ⟨13618314742056712638699965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36315505978817900369866573 13618314742056712638699965)
    ·
      refine ⟨5106868028271267239512487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13618314742056712638699965 5106868028271267239512487)
      ·
        refine ⟨7660302042406900859268731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106868028271267239512487 7660302042406900859268731)
        ·
          refine ⟨11490453063610351288903097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660302042406900859268731 11490453063610351288903097)
          ·
            refine ⟨8617839797707763466677323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11490453063610351288903097 8617839797707763466677323)
            ·
              refine ⟨12926759696561645200015985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8617839797707763466677323 12926759696561645200015985)
              ·
                refine ⟨9695069772421233900011989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12926759696561645200015985 9695069772421233900011989)
                ·
                  refine ⟨227228197791122669531531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9695069772421233900011989 227228197791122669531531)
                  ·
                    rfl

theorem cell22_1991364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_1991364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991364 prefixEnd_1991364 := by exact prefixLift 1991364
  have htrace : WordTrace (prefixWord ++ tailWord_1991364) baseStart_1991364 baseEnd_1991364 := by
    simpa [prefixWord, tailWord_1991364, baseEnd_1991364] using wordTrace_append hprefix tailTrace_1991364
  have hstable : (prefixWord ++ tailWord_1991364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991364).length < 2 ^ (prefixWord ++ tailWord_1991364).sum := by decide
  have hdescent : baseEnd_1991364 < baseStart_1991364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991368 : List Nat := [2, 1, 3, 1, 2, 3, 3, 3, 1, 3]
def baseStart_1991368 : Nat := 118140960795 + 1991368 * 2 ^ 59
def prefixEnd_1991368 : Nat := 4983230072969 + 3 ^ 40 * 1991368 * 2
def baseEnd_1991368 : Nat := 681685962655113331494581

theorem tailTrace_1991368 : CollatzResearch.WordTrace tailWord_1991368 prefixEnd_1991368 681685962655113331494581 := by
  unfold tailWord_1991368
  simp only [CollatzResearch.WordTrace]
  refine ⟨36315578924810654711439379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48420771899747539615252505 36315578924810654711439379)
  ·
    refine ⟨54473368387215982067159069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36315578924810654711439379 54473368387215982067159069)
    ·
      refine ⟨20427513145205993275184651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54473368387215982067159069 20427513145205993275184651)
      ·
        refine ⟨30641269717808989912776977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20427513145205993275184651 30641269717808989912776977)
        ·
          refine ⟨22980952288356742434582733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30641269717808989912776977 22980952288356742434582733)
          ·
            refine ⟨8617857108133778412968525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22980952288356742434582733 8617857108133778412968525)
            ·
              refine ⟨3231696415550166904863197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8617857108133778412968525 3231696415550166904863197)
              ·
                refine ⟨1211886155831312589323699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3231696415550166904863197 1211886155831312589323699)
                ·
                  refine ⟨1817829233746968883985549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211886155831312589323699 1817829233746968883985549)
                  ·
                    refine ⟨681685962655113331494581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817829233746968883985549 681685962655113331494581)
                    ·
                      rfl

theorem cell22_1991368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_1991368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991368 prefixEnd_1991368 := by exact prefixLift 1991368
  have htrace : WordTrace (prefixWord ++ tailWord_1991368) baseStart_1991368 baseEnd_1991368 := by
    simpa [prefixWord, tailWord_1991368, baseEnd_1991368] using wordTrace_append hprefix tailTrace_1991368
  have hstable : (prefixWord ++ tailWord_1991368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991368).length < 2 ^ (prefixWord ++ tailWord_1991368).sum := by decide
  have hdescent : baseEnd_1991368 < baseStart_1991368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991428 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1991428 : Nat := 118140960795 + 1991428 * 2 ^ 59
def prefixEnd_1991428 : Nat := 4983230072969 + 3 ^ 40 * 1991428 * 2
def baseEnd_1991428 : Nat := 681706501881293174994397

theorem tailTrace_1991428 : CollatzResearch.WordTrace tailWord_1991428 prefixEnd_1991428 681706501881293174994397 := by
  unfold tailWord_1991428
  simp only [CollatzResearch.WordTrace]
  refine ⟨36316673114701969835031469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48422230819602626446708625 36316673114701969835031469)
  ·
    refine ⟨13618752418013238688136801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36316673114701969835031469 13618752418013238688136801)
    ·
      refine ⟨10214064313509929016102601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13618752418013238688136801 10214064313509929016102601)
      ·
        refine ⟨7660548235132446762076951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10214064313509929016102601 7660548235132446762076951)
        ·
          refine ⟨11490822352698670143115427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7660548235132446762076951 11490822352698670143115427)
          ·
            refine ⟨17236233529048005214673141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11490822352698670143115427 17236233529048005214673141)
            ·
              refine ⟨1615896893348250488875607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17236233529048005214673141 1615896893348250488875607)
              ·
                refine ⟨2423845340022375733313411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615896893348250488875607 2423845340022375733313411)
                ·
                  refine ⟨3635768010033563599970117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423845340022375733313411 3635768010033563599970117)
                  ·
                    refine ⟨681706501881293174994397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3635768010033563599970117 681706501881293174994397)
                    ·
                      rfl

theorem cell22_1991428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1991428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991428 prefixEnd_1991428 := by exact prefixLift 1991428
  have htrace : WordTrace (prefixWord ++ tailWord_1991428) baseStart_1991428 baseEnd_1991428 := by
    simpa [prefixWord, tailWord_1991428, baseEnd_1991428] using wordTrace_append hprefix tailTrace_1991428
  have hstable : (prefixWord ++ tailWord_1991428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991428).length < 2 ^ (prefixWord ++ tailWord_1991428).sum := by decide
  have hdescent : baseEnd_1991428 < baseStart_1991428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991439 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 2, 4]
def baseStart_1991439 : Nat := 118140960795 + 1991439 * 2 ^ 59
def prefixEnd_1991439 : Nat := 4983230072969 + 3 ^ 40 * 1991439 * 2
def baseEnd_1991439 : Nat := 681710267406092812969363

theorem tailTrace_1991439 : CollatzResearch.WordTrace tailWord_1991439 prefixEnd_1991439 681710267406092812969363 := by
  unfold tailWord_1991439
  simp only [CollatzResearch.WordTrace]
  refine ⟨72633747432364088548713371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48422498288242725699142247 72633747432364088548713371)
  ·
    refine ⟨108950621148546132823070057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72633747432364088548713371 108950621148546132823070057)
    ·
      refine ⟨81712965861409599617302543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108950621148546132823070057 81712965861409599617302543)
      ·
        refine ⟨122569448792114399425953815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81712965861409599617302543 122569448792114399425953815)
        ·
          refine ⟨183854173188171599138930723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122569448792114399425953815 183854173188171599138930723)
          ·
            refine ⟨275781259782257398708396085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183854173188171599138930723 275781259782257398708396085)
            ·
              refine ⟨25854493104586631128912133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275781259782257398708396085 25854493104586631128912133)
              ·
                refine ⟨4847717457109993336671025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25854493104586631128912133 4847717457109993336671025)
                ·
                  refine ⟨3635788092832495002503269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4847717457109993336671025 3635788092832495002503269)
                  ·
                    refine ⟨681710267406092812969363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3635788092832495002503269 681710267406092812969363)
                    ·
                      rfl

theorem cell22_1991439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_1991439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991439 prefixEnd_1991439 := by exact prefixLift 1991439
  have htrace : WordTrace (prefixWord ++ tailWord_1991439) baseStart_1991439 baseEnd_1991439 := by
    simpa [prefixWord, tailWord_1991439, baseEnd_1991439] using wordTrace_append hprefix tailTrace_1991439
  have hstable : (prefixWord ++ tailWord_1991439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991439).length < 2 ^ (prefixWord ++ tailWord_1991439).sum := by decide
  have hdescent : baseEnd_1991439 < baseStart_1991439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991441 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 2, 3]
def baseStart_1991441 : Nat := 118140960795 + 1991441 * 2 ^ 59
def prefixEnd_1991441 : Nat := 4983230072969 + 3 ^ 40 * 1991441 * 2
def baseEnd_1991441 : Nat := 681710952046965474419357

theorem tailTrace_1991441 : CollatzResearch.WordTrace tailWord_1991441 prefixEnd_1991441 681710952046965474419357 := by
  unfold tailWord_1991441
  simp only [CollatzResearch.WordTrace]
  refine ⟨72633820378356842890286177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48422546918904561926857451 72633820378356842890286177)
  ·
    refine ⟨54475365283767632167714633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72633820378356842890286177 54475365283767632167714633)
    ·
      refine ⟨40856523962825724125785975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54475365283767632167714633 40856523962825724125785975)
      ·
        refine ⟨61284785944238586188678963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40856523962825724125785975 61284785944238586188678963)
        ·
          refine ⟨91927178916357879283018445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61284785944238586188678963 91927178916357879283018445)
          ·
            refine ⟨34472692093634204731131917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91927178916357879283018445 34472692093634204731131917)
            ·
              refine ⟨12927259535112826774174469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34472692093634204731131917 12927259535112826774174469)
              ·
                refine ⟨2423861162833655020157713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12927259535112826774174469 2423861162833655020157713)
                ·
                  refine ⟨1817895872125241265118285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2423861162833655020157713 1817895872125241265118285)
                  ·
                    refine ⟨681710952046965474419357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817895872125241265118285 681710952046965474419357)
                    ·
                      rfl

theorem cell22_1991441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_1991441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991441 prefixEnd_1991441 := by exact prefixLift 1991441
  have htrace : WordTrace (prefixWord ++ tailWord_1991441) baseStart_1991441 baseEnd_1991441 := by
    simpa [prefixWord, tailWord_1991441, baseEnd_1991441] using wordTrace_append hprefix tailTrace_1991441
  have hstable : (prefixWord ++ tailWord_1991441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991441).length < 2 ^ (prefixWord ++ tailWord_1991441).sum := by decide
  have hdescent : baseEnd_1991441 < baseStart_1991441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991458 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1991458 : Nat := 118140960795 + 1991458 * 2 ^ 59
def prefixEnd_1991458 : Nat := 4983230072969 + 3 ^ 40 * 1991458 * 2
def baseEnd_1991458 : Nat := 681716771494383096744305

theorem tailTrace_1991458 : CollatzResearch.WordTrace tailWord_1991458 prefixEnd_1991458 681716771494383096744305 := by
  unfold tailWord_1991458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18158610104823813698413757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48422960279530169862436685 18158610104823813698413757)
  ·
    refine ⟨6809478789308930136905159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18158610104823813698413757 6809478789308930136905159)
    ·
      refine ⟨10214218183963395205357739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809478789308930136905159 10214218183963395205357739)
      ·
        refine ⟨15321327275945092808036609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10214218183963395205357739 15321327275945092808036609)
        ·
          refine ⟨11490995456958819606027457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15321327275945092808036609 11490995456958819606027457)
          ·
            refine ⟨8618246592719114704520593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11490995456958819606027457 8618246592719114704520593)
            ·
              refine ⟨6463684944539336028390445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618246592719114704520593 6463684944539336028390445)
              ·
                refine ⟨2423881854202251010646417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6463684944539336028390445 2423881854202251010646417)
                ·
                  refine ⟨1817911390651688257984813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2423881854202251010646417 1817911390651688257984813)
                  ·
                    refine ⟨681716771494383096744305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817911390651688257984813 681716771494383096744305)
                    ·
                      rfl

theorem cell22_1991458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1991458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991458 prefixEnd_1991458 := by exact prefixLift 1991458
  have htrace : WordTrace (prefixWord ++ tailWord_1991458) baseStart_1991458 baseEnd_1991458 := by
    simpa [prefixWord, tailWord_1991458, baseEnd_1991458] using wordTrace_append hprefix tailTrace_1991458
  have hstable : (prefixWord ++ tailWord_1991458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991458).length < 2 ^ (prefixWord ++ tailWord_1991458).sum := by decide
  have hdescent : baseEnd_1991458 < baseStart_1991458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991554 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1991554 : Nat := 118140960795 + 1991554 * 2 ^ 59
def prefixEnd_1991554 : Nat := 4983230072969 + 3 ^ 40 * 1991554 * 2
def baseEnd_1991554 : Nat := 681749634256270846344011

theorem tailTrace_1991554 : CollatzResearch.WordTrace tailWord_1991554 prefixEnd_1991554 681749634256270846344011 := by
  unfold tailWord_1991554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18159485456736865797287429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48425294551298308792766477 18159485456736865797287429)
  ·
    refine ⟨3404903523138162336991393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18159485456736865797287429 3404903523138162336991393)
    ·
      refine ⟨2553677642353621752743545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3404903523138162336991393 2553677642353621752743545)
      ·
        refine ⟨1915258231765216314557659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553677642353621752743545 1915258231765216314557659)
        ·
          refine ⟨2872887347647824471836489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915258231765216314557659 2872887347647824471836489)
          ·
            refine ⟨2154665510735868353877367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2872887347647824471836489 2154665510735868353877367)
            ·
              refine ⟨3231998266103802530816051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154665510735868353877367 3231998266103802530816051)
              ·
                refine ⟨4847997399155703796224077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3231998266103802530816051 4847997399155703796224077)
                ·
                  refine ⟨1817999024683388923584029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4847997399155703796224077 1817999024683388923584029)
                  ·
                    refine ⟨681749634256270846344011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1817999024683388923584029 681749634256270846344011)
                    ·
                      rfl

theorem cell22_1991554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1991554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991554 prefixEnd_1991554 := by exact prefixLift 1991554
  have htrace : WordTrace (prefixWord ++ tailWord_1991554) baseStart_1991554 baseEnd_1991554 := by
    simpa [prefixWord, tailWord_1991554, baseEnd_1991554] using wordTrace_append hprefix tailTrace_1991554
  have hstable : (prefixWord ++ tailWord_1991554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991554).length < 2 ^ (prefixWord ++ tailWord_1991554).sum := by decide
  have hdescent : baseEnd_1991554 < baseStart_1991554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991561 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 6]
def baseStart_1991561 : Nat := 118140960795 + 1991561 * 2 ^ 59
def prefixEnd_1991561 : Nat := 4983230072969 + 3 ^ 40 * 1991561 * 2
def baseEnd_1991561 : Nat := 227250676833108387139663

theorem tailTrace_1991561 : CollatzResearch.WordTrace tailWord_1991561 prefixEnd_1991561 227250676833108387139663 := by
  unfold tailWord_1991561
  simp only [CollatzResearch.WordTrace]
  refine ⟨72638197137922103384654537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48425464758614735589769691 72638197137922103384654537)
  ·
    refine ⟨54478647853441577538490903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72638197137922103384654537 54478647853441577538490903)
    ·
      refine ⟨81717971780162366307736355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54478647853441577538490903 81717971780162366307736355)
      ·
        refine ⟨122576957670243549461604533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81717971780162366307736355 122576957670243549461604533)
        ·
          refine ⟨11491589781585332762025425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122576957670243549461604533 11491589781585332762025425)
          ·
            refine ⟨8618692336188999571519069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11491589781585332762025425 8618692336188999571519069)
            ·
              refine ⟨3232009626070874839319651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8618692336188999571519069 3232009626070874839319651)
              ·
                refine ⟨4848014439106312258979477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232009626070874839319651 4848014439106312258979477)
                ·
                  refine ⟨227250676833108387139663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4848014439106312258979477 227250676833108387139663)
                  ·
                    rfl

theorem cell22_1991561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_1991561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991561 prefixEnd_1991561 := by exact prefixLift 1991561
  have htrace : WordTrace (prefixWord ++ tailWord_1991561) baseStart_1991561 baseEnd_1991561 := by
    simpa [prefixWord, tailWord_1991561, baseEnd_1991561] using wordTrace_append hprefix tailTrace_1991561
  have hstable : (prefixWord ++ tailWord_1991561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991561).length < 2 ^ (prefixWord ++ tailWord_1991561).sum := by decide
  have hdescent : baseEnd_1991561 < baseStart_1991561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991651 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 7]
def baseStart_1991651 : Nat := 118140960795 + 1991651 * 2 ^ 59
def prefixEnd_1991651 : Nat := 4983230072969 + 3 ^ 40 * 1991651 * 2
def baseEnd_1991651 : Nat := 227260946446198308889571

theorem tailTrace_1991651 : CollatzResearch.WordTrace tailWord_1991651 prefixEnd_1991651 227260946446198308889571 := by
  unfold tailWord_1991651
  simp only [CollatzResearch.WordTrace]
  refine ⟨72641479707596048755430807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48427653138397365836953871 72641479707596048755430807)
  ·
    refine ⟨108962219561394073133146211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72641479707596048755430807 108962219561394073133146211)
    ·
      refine ⟨163443329342091109699719317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108962219561394073133146211 163443329342091109699719317)
      ·
        refine ⟨7661406062910520767174343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163443329342091109699719317 7661406062910520767174343)
        ·
          refine ⟨11492109094365781150761515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7661406062910520767174343 11492109094365781150761515)
          ·
            refine ⟨17238163641548671726142273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11492109094365781150761515 17238163641548671726142273)
            ·
              refine ⟨12928622731161503794606705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17238163641548671726142273 12928622731161503794606705)
              ·
                refine ⟨9696467048371127845955029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12928622731161503794606705 9696467048371127845955029)
                ·
                  refine ⟨227260946446198308889571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9696467048371127845955029 227260946446198308889571)
                  ·
                    rfl

theorem cell22_1991651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_1991651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991651 prefixEnd_1991651 := by exact prefixLift 1991651
  have htrace : WordTrace (prefixWord ++ tailWord_1991651) baseStart_1991651 baseEnd_1991651 := by
    simpa [prefixWord, tailWord_1991651, baseEnd_1991651] using wordTrace_append hprefix tailTrace_1991651
  have hstable : (prefixWord ++ tailWord_1991651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991651).length < 2 ^ (prefixWord ++ tailWord_1991651).sum := by decide
  have hdescent : baseEnd_1991651 < baseStart_1991651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991728 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 4, 3]
def baseStart_1991728 : Nat := 118140960795 + 1991728 * 2 ^ 59
def prefixEnd_1991728 : Nat := 4983230072969 + 3 ^ 40 * 1991728 * 2
def baseEnd_1991728 : Nat := 681809198012192392493477

theorem tailTrace_1991728 : CollatzResearch.WordTrace tailWord_1991728 prefixEnd_1991728 681809198012192392493477 := by
  unfold tailWord_1991728
  simp only [CollatzResearch.WordTrace]
  refine ⟨36322144064158545452991919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48429525418878060603989225 36322144064158545452991919)
  ·
    refine ⟨54483216096237818179487879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36322144064158545452991919 54483216096237818179487879)
    ·
      refine ⟨81724824144356727269231819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54483216096237818179487879 81724824144356727269231819)
      ·
        refine ⟨122587236216535090903847729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81724824144356727269231819 122587236216535090903847729)
        ·
          refine ⟨91940427162401318177885797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122587236216535090903847729 91940427162401318177885797)
          ·
            refine ⟨17238830092950247158353587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91940427162401318177885797 17238830092950247158353587)
            ·
              refine ⟨25858245139425370737530381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17238830092950247158353587 25858245139425370737530381)
              ·
                refine ⟨9696841927284514026573893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25858245139425370737530381 9696841927284514026573893)
                ·
                  refine ⟨1818157861365846379982605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9696841927284514026573893 1818157861365846379982605)
                  ·
                    refine ⟨681809198012192392493477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818157861365846379982605 681809198012192392493477)
                    ·
                      rfl

theorem cell22_1991728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_1991728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991728 prefixEnd_1991728 := by exact prefixLift 1991728
  have htrace : WordTrace (prefixWord ++ tailWord_1991728) baseStart_1991728 baseEnd_1991728 := by
    simpa [prefixWord, tailWord_1991728, baseEnd_1991728] using wordTrace_append hprefix tailTrace_1991728
  have hstable : (prefixWord ++ tailWord_1991728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991728).length < 2 ^ (prefixWord ++ tailWord_1991728).sum := by decide
  have hdescent : baseEnd_1991728 < baseStart_1991728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991766 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1991766 : Nat := 118140960795 + 1991766 * 2 ^ 59
def prefixEnd_1991766 : Nat := 4983230072969 + 3 ^ 40 * 1991766 * 2
def baseEnd_1991766 : Nat := 681822206188772960043361

theorem tailTrace_1991766 : CollatzResearch.WordTrace tailWord_1991766 prefixEnd_1991766 681822206188772960043361 := by
  unfold tailWord_1991766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540354631386213962241697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48430449401452948930578101 4540354631386213962241697)
  ·
    refine ⟨3405265973539660471681273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4540354631386213962241697 3405265973539660471681273)
    ·
      refine ⟨2553949480154745353760955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3405265973539660471681273 2553949480154745353760955)
      ·
        refine ⟨3830924220232118030641433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553949480154745353760955 3830924220232118030641433)
        ·
          refine ⟨2873193165174088522981075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3830924220232118030641433 2873193165174088522981075)
          ·
            refine ⟨4309789747761132784471613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873193165174088522981075 4309789747761132784471613)
            ·
              refine ⟨1616171155410424794176855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4309789747761132784471613 1616171155410424794176855)
              ·
                refine ⟨2424256733115637191265283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616171155410424794176855 2424256733115637191265283)
                ·
                  refine ⟨3636385099673455786897925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424256733115637191265283 3636385099673455786897925)
                  ·
                    refine ⟨681822206188772960043361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3636385099673455786897925 681822206188772960043361)
                    ·
                      rfl

theorem cell22_1991766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1991766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991766 prefixEnd_1991766 := by exact prefixLift 1991766
  have htrace : WordTrace (prefixWord ++ tailWord_1991766) baseStart_1991766 baseEnd_1991766 := by
    simpa [prefixWord, tailWord_1991766, baseEnd_1991766] using wordTrace_append hprefix tailTrace_1991766
  have hstable : (prefixWord ++ tailWord_1991766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991766).length < 2 ^ (prefixWord ++ tailWord_1991766).sum := by decide
  have hdescent : baseEnd_1991766 < baseStart_1991766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991818 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_1991818 : Nat := 118140960795 + 1991818 * 2 ^ 59
def prefixEnd_1991818 : Nat := 4983230072969 + 3 ^ 40 * 1991818 * 2
def baseEnd_1991818 : Nat := 681840006851462157743201

theorem tailTrace_1991818 : CollatzResearch.WordTrace tailWord_1991818 prefixEnd_1991818 681840006851462157743201 := by
  unfold tailWord_1991818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18161892674497759069190027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48431713798660690851173405 18161892674497759069190027)
  ·
    refine ⟨27242839011746638603785041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18161892674497759069190027 27242839011746638603785041)
    ·
      refine ⟨20432129258809978952838781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27242839011746638603785041 20432129258809978952838781)
      ·
        refine ⟨7662048472053742107314543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20432129258809978952838781 7662048472053742107314543)
        ·
          refine ⟨11493072708080613160971815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7662048472053742107314543 11493072708080613160971815)
          ·
            refine ⟨17239609062120919741457723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11493072708080613160971815 17239609062120919741457723)
            ·
              refine ⟨25859413593181379612186585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17239609062120919741457723 25859413593181379612186585)
              ·
                refine ⟨19394560194886034709139939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25859413593181379612186585 19394560194886034709139939)
                ·
                  refine ⟨29091840292329052063709909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19394560194886034709139939 29091840292329052063709909)
                  ·
                    refine ⟨681840006851462157743201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29091840292329052063709909 681840006851462157743201)
                    ·
                      rfl

theorem cell22_1991818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_1991818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991818 prefixEnd_1991818 := by exact prefixLift 1991818
  have htrace : WordTrace (prefixWord ++ tailWord_1991818) baseStart_1991818 baseEnd_1991818 := by
    simpa [prefixWord, tailWord_1991818, baseEnd_1991818] using wordTrace_append hprefix tailTrace_1991818
  have hstable : (prefixWord ++ tailWord_1991818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991818).length < 2 ^ (prefixWord ++ tailWord_1991818).sum := by decide
  have hdescent : baseEnd_1991818 < baseStart_1991818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991880 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 4, 3]
def baseStart_1991880 : Nat := 118140960795 + 1991880 * 2 ^ 59
def prefixEnd_1991880 : Nat := 4983230072969 + 3 ^ 40 * 1991880 * 2
def baseEnd_1991880 : Nat := 681861230718514662693011

theorem tailTrace_1991880 : CollatzResearch.WordTrace tailWord_1991880 prefixEnd_1991880 681861230718514662693011 := by
  unfold tailWord_1991880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36324916011883210432758547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48433221349177613910344729 36324916011883210432758547)
  ·
    refine ⟨54487374017824815649137821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36324916011883210432758547 54487374017824815649137821)
    ·
      refine ⟨20432765256684305868426683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54487374017824815649137821 20432765256684305868426683)
      ·
        refine ⟨30649147885026458802640025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20432765256684305868426683 30649147885026458802640025)
        ·
          refine ⟨22986860913769844101980019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30649147885026458802640025 22986860913769844101980019)
          ·
            refine ⟨34480291370654766152970029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22986860913769844101980019 34480291370654766152970029)
            ·
              refine ⟨12930109263995537307363761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34480291370654766152970029 12930109263995537307363761)
              ·
                refine ⟨9697581947996652980522821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12930109263995537307363761 9697581947996652980522821)
                ·
                  refine ⟨1818296615249372433848029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9697581947996652980522821 1818296615249372433848029)
                  ·
                    refine ⟨681861230718514662693011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818296615249372433848029 681861230718514662693011)
                    ·
                      rfl

theorem cell22_1991880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_1991880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991880 prefixEnd_1991880 := by exact prefixLift 1991880
  have htrace : WordTrace (prefixWord ++ tailWord_1991880) baseStart_1991880 baseEnd_1991880 := by
    simpa [prefixWord, tailWord_1991880, baseEnd_1991880] using wordTrace_append hprefix tailTrace_1991880
  have hstable : (prefixWord ++ tailWord_1991880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991880).length < 2 ^ (prefixWord ++ tailWord_1991880).sum := by decide
  have hdescent : baseEnd_1991880 < baseStart_1991880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991882 : List Nat := [3, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_1991882 : Nat := 118140960795 + 1991882 * 2 ^ 59
def prefixEnd_1991882 : Nat := 4983230072969 + 3 ^ 40 * 1991882 * 2
def baseEnd_1991882 : Nat := 227287305119795774714335

theorem tailTrace_1991882 : CollatzResearch.WordTrace tailWord_1991882 prefixEnd_1991882 227287305119795774714335 := by
  unfold tailWord_1991882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162476242439793801772475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48433269979839450138059933 18162476242439793801772475)
  ·
    refine ⟨27243714363659690702658713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18162476242439793801772475 27243714363659690702658713)
    ·
      refine ⟨20432785772744768026994035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27243714363659690702658713 20432785772744768026994035)
      ·
        refine ⟨30649178659117152040491053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20432785772744768026994035 30649178659117152040491053)
        ·
          refine ⟨11493441997168932015184145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30649178659117152040491053 11493441997168932015184145)
          ·
            refine ⟨8620081497876699011388109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11493441997168932015184145 8620081497876699011388109)
            ·
              refine ⟨3232530561703762129270541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8620081497876699011388109 3232530561703762129270541)
              ·
                refine ⟨1212198960638910798476453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3232530561703762129270541 1212198960638910798476453)
                ·
                  refine ⟨227287305119795774714335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212198960638910798476453 227287305119795774714335)
                  ·
                    rfl

theorem cell22_1991882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_1991882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991882 prefixEnd_1991882 := by exact prefixLift 1991882
  have htrace : WordTrace (prefixWord ++ tailWord_1991882) baseStart_1991882 baseEnd_1991882 := by
    simpa [prefixWord, tailWord_1991882, baseEnd_1991882] using wordTrace_append hprefix tailTrace_1991882
  have hstable : (prefixWord ++ tailWord_1991882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991882).length < 2 ^ (prefixWord ++ tailWord_1991882).sum := by decide
  have hdescent : baseEnd_1991882 < baseStart_1991882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991914 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_1991914 : Nat := 118140960795 + 1991914 * 2 ^ 59
def prefixEnd_1991914 : Nat := 4983230072969 + 3 ^ 40 * 1991914 * 2
def baseEnd_1991914 : Nat := 681872869613349907342907

theorem tailTrace_1991914 : CollatzResearch.WordTrace tailWord_1991914 prefixEnd_1991914 681872869613349907342907 := by
  unfold tailWord_1991914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162768026410811168063699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48434048070428829781503197 18162768026410811168063699)
  ·
    refine ⟨27244152039616216752095549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18162768026410811168063699 27244152039616216752095549)
    ·
      refine ⟨10216557014856081282035831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27244152039616216752095549 10216557014856081282035831)
      ·
        refine ⟨15324835522284121923053747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216557014856081282035831 15324835522284121923053747)
        ·
          refine ⟨22987253283426182884580621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15324835522284121923053747 22987253283426182884580621)
          ·
            refine ⟨8620219981284818581717733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22987253283426182884580621 8620219981284818581717733)
            ·
              refine ⟨1616291246490903484072075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8620219981284818581717733 1616291246490903484072075)
              ·
                refine ⟨2424436869736355226108113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616291246490903484072075 2424436869736355226108113)
                ·
                  refine ⟨1818327652302266419581085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2424436869736355226108113 1818327652302266419581085)
                  ·
                    refine ⟨681872869613349907342907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818327652302266419581085 681872869613349907342907)
                    ·
                      rfl

theorem cell22_1991914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_1991914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991914 prefixEnd_1991914 := by exact prefixLift 1991914
  have htrace : WordTrace (prefixWord ++ tailWord_1991914) baseStart_1991914 baseEnd_1991914 := by
    simpa [prefixWord, tailWord_1991914, baseEnd_1991914] using wordTrace_append hprefix tailTrace_1991914
  have hstable : (prefixWord ++ tailWord_1991914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991914).length < 2 ^ (prefixWord ++ tailWord_1991914).sum := by decide
  have hdescent : baseEnd_1991914 < baseStart_1991914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991959 : List Nat := [1, 1, 3, 4, 1, 1, 3, 4, 1, 3]
def baseStart_1991959 : Nat := 118140960795 + 1991959 * 2 ^ 59
def prefixEnd_1991959 : Nat := 4983230072969 + 3 ^ 40 * 1991959 * 2
def baseEnd_1991959 : Nat := 681888274032984789967769

theorem tailTrace_1991959 : CollatzResearch.WordTrace tailWord_1991959 prefixEnd_1991959 681888274032984789967769 := by
  unfold tailWord_1991959
  simp only [CollatzResearch.WordTrace]
  refine ⟨72652713390480217357642931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48435142260320144905095287 72652713390480217357642931)
  ·
    refine ⟨108979070085720326036464397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72652713390480217357642931 108979070085720326036464397)
    ·
      refine ⟨40867151282145122263674149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108979070085720326036464397 40867151282145122263674149)
      ·
        refine ⟨7662590865402210424438903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40867151282145122263674149 7662590865402210424438903)
        ·
          refine ⟨11493886298103315636658355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7662590865402210424438903 11493886298103315636658355)
          ·
            refine ⟨17240829447154973454987533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11493886298103315636658355 17240829447154973454987533)
            ·
              refine ⟨6465311042683115045620325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17240829447154973454987533 6465311042683115045620325)
              ·
                refine ⟨1212245820503084071053811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6465311042683115045620325 1212245820503084071053811)
                ·
                  refine ⟨1818368730754626106580717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212245820503084071053811 1818368730754626106580717)
                  ·
                    refine ⟨681888274032984789967769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818368730754626106580717 681888274032984789967769)
                    ·
                      rfl

theorem cell22_1991959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_1991959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1991959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1991959 prefixEnd_1991959 := by exact prefixLift 1991959
  have htrace : WordTrace (prefixWord ++ tailWord_1991959) baseStart_1991959 baseEnd_1991959 := by
    simpa [prefixWord, tailWord_1991959, baseEnd_1991959] using wordTrace_append hprefix tailTrace_1991959
  have hstable : (prefixWord ++ tailWord_1991959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991959).length < 2 ^ (prefixWord ++ tailWord_1991959).sum := by decide
  have hdescent : baseEnd_1991959 < baseStart_1991959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992006 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1992006 : Nat := 118140960795 + 1992006 * 2 ^ 59
def prefixEnd_1992006 : Nat := 4983230072969 + 3 ^ 40 * 1992006 * 2
def baseEnd_1992006 : Nat := 227301454364497444680875

theorem tailTrace_1992006 : CollatzResearch.WordTrace tailWord_1992006 prefixEnd_1992006 227301454364497444680875 := by
  unfold tailWord_1992006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270450863165935762018871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48436285080873296256402581 2270450863165935762018871)
  ·
    refine ⟨3405676294748903643028307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2270450863165935762018871 3405676294748903643028307)
    ·
      refine ⟨5108514442123355464542461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405676294748903643028307 5108514442123355464542461)
      ·
        refine ⟨1915692915796258299203423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5108514442123355464542461 1915692915796258299203423)
        ·
          refine ⟨2873539373694387448805135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915692915796258299203423 2873539373694387448805135)
          ·
            refine ⟨4310309060541581173207703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873539373694387448805135 4310309060541581173207703)
            ·
              refine ⟨6465463590812371759811555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310309060541581173207703 6465463590812371759811555)
              ·
                refine ⟨9698195386218557639717333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465463590812371759811555 9698195386218557639717333)
                ·
                  refine ⟨227301454364497444680875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9698195386218557639717333 227301454364497444680875)
                  ·
                    rfl

theorem cell22_1992006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1992006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992006 prefixEnd_1992006 := by exact prefixLift 1992006
  have htrace : WordTrace (prefixWord ++ tailWord_1992006) baseStart_1992006 baseEnd_1992006 := by
    simpa [prefixWord, tailWord_1992006, baseEnd_1992006] using wordTrace_append hprefix tailTrace_1992006
  have hstable : (prefixWord ++ tailWord_1992006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992006).length < 2 ^ (prefixWord ++ tailWord_1992006).sum := by decide
  have hdescent : baseEnd_1992006 < baseStart_1992006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992017 : List Nat := [1, 2, 2, 1, 4, 1, 1, 6, 4]
def baseStart_1992017 : Nat := 118140960795 + 1992017 * 2 ^ 59
def prefixEnd_1992017 : Nat := 4983230072969 + 3 ^ 40 * 1992017 * 2
def baseEnd_1992017 : Nat := 227302709539430657339197

theorem tailTrace_1992017 : CollatzResearch.WordTrace tailWord_1992017 prefixEnd_1992017 227302709539430657339197 := by
  unfold tailWord_1992017
  simp only [CollatzResearch.WordTrace]
  refine ⟨72654828824270093263254305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48436552549513395508836203 72654828824270093263254305)
  ·
    refine ⟨54491121618202569947440729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72654828824270093263254305 54491121618202569947440729)
    ·
      refine ⟨40868341213651927460580547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54491121618202569947440729 40868341213651927460580547)
      ·
        refine ⟨61302511820477891190870821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40868341213651927460580547 61302511820477891190870821)
        ·
          refine ⟨11494220966339604598288279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61302511820477891190870821 11494220966339604598288279)
          ·
            refine ⟨17241331449509406897432419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11494220966339604598288279 17241331449509406897432419)
            ·
              refine ⟨25861997174264110346148629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17241331449509406897432419 25861997174264110346148629)
              ·
                refine ⟨1212281117543630172475717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25861997174264110346148629 1212281117543630172475717)
                ·
                  refine ⟨227302709539430657339197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212281117543630172475717 227302709539430657339197)
                  ·
                    rfl

theorem cell22_1992017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_1992017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992017 prefixEnd_1992017 := by exact prefixLift 1992017
  have htrace : WordTrace (prefixWord ++ tailWord_1992017) baseStart_1992017 baseEnd_1992017 := by
    simpa [prefixWord, tailWord_1992017, baseEnd_1992017] using wordTrace_append hprefix tailTrace_1992017
  have hstable : (prefixWord ++ tailWord_1992017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992017).length < 2 ^ (prefixWord ++ tailWord_1992017).sum := by decide
  have hdescent : baseEnd_1992017 < baseStart_1992017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992032 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_1992032 : Nat := 118140960795 + 1992032 * 2 ^ 59
def prefixEnd_1992032 : Nat := 4983230072969 + 3 ^ 40 * 1992032 * 2
def baseEnd_1992032 : Nat := 681913263424836932892545

theorem tailTrace_1992032 : CollatzResearch.WordTrace tailWord_1992032 prefixEnd_1992032 681913263424836932892545 := by
  unfold tailWord_1992032
  simp only [CollatzResearch.WordTrace]
  refine ⟨36327687959607875412525175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48436917279477167216700233 36327687959607875412525175)
  ·
    refine ⟨54491531939411813118787763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36327687959607875412525175 54491531939411813118787763)
    ·
      refine ⟨81737297909117719678181645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54491531939411813118787763 81737297909117719678181645)
      ·
        refine ⟨30651486715919144879318117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81737297909117719678181645 30651486715919144879318117)
        ·
          refine ⟨5747153759234839664872147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30651486715919144879318117 5747153759234839664872147)
          ·
            refine ⟨8620730638852259497308221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747153759234839664872147 8620730638852259497308221)
            ·
              refine ⟨3232773989569597311490583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8620730638852259497308221 3232773989569597311490583)
              ·
                refine ⟨4849160984354395967235875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232773989569597311490583 4849160984354395967235875)
                ·
                  refine ⟨7273741476531593950853813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849160984354395967235875 7273741476531593950853813)
                  ·
                    refine ⟨681913263424836932892545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7273741476531593950853813 681913263424836932892545)
                    ·
                      rfl

theorem cell22_1992032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_1992032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992032 prefixEnd_1992032 := by exact prefixLift 1992032
  have htrace : WordTrace (prefixWord ++ tailWord_1992032) baseStart_1992032 baseEnd_1992032 := by
    simpa [prefixWord, tailWord_1992032, baseEnd_1992032] using wordTrace_append hprefix tailTrace_1992032
  have hstable : (prefixWord ++ tailWord_1992032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992032).length < 2 ^ (prefixWord ++ tailWord_1992032).sum := by decide
  have hdescent : baseEnd_1992032 < baseStart_1992032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992066 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1992066 : Nat := 118140960795 + 1992066 * 2 ^ 59
def prefixEnd_1992066 : Nat := 4983230072969 + 3 ^ 40 * 1992066 * 2
def baseEnd_1992066 : Nat := 681924902319672177542441

theorem tailTrace_1992066 : CollatzResearch.WordTrace tailWord_1992066 prefixEnd_1992066 681924902319672177542441 := by
  unfold tailWord_1992066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18164154000273143657947013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48437744000728383087858701 18164154000273143657947013)
  ·
    refine ⟨3405778875051214435865065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18164154000273143657947013 3405778875051214435865065)
    ·
      refine ⟨2554334156288410826898799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3405778875051214435865065 2554334156288410826898799)
      ·
        refine ⟨3831501234432616240348199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554334156288410826898799 3831501234432616240348199)
        ·
          refine ⟨5747251851648924360522299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831501234432616240348199 5747251851648924360522299)
          ·
            refine ⟨8620877777473386540783449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747251851648924360522299 8620877777473386540783449)
            ·
              refine ⟨6465658333105039905587587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8620877777473386540783449 6465658333105039905587587)
              ·
                refine ⟨9698487499657559858381381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6465658333105039905587587 9698487499657559858381381)
                ·
                  refine ⟨1818466406185792473446509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9698487499657559858381381 1818466406185792473446509)
                  ·
                    refine ⟨681924902319672177542441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818466406185792473446509 681924902319672177542441)
                    ·
                      rfl

theorem cell22_1992066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1992066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992066 prefixEnd_1992066 := by exact prefixLift 1992066
  have htrace : WordTrace (prefixWord ++ tailWord_1992066) baseStart_1992066 baseEnd_1992066 := by
    simpa [prefixWord, tailWord_1992066, baseEnd_1992066] using wordTrace_append hprefix tailTrace_1992066
  have hstable : (prefixWord ++ tailWord_1992066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992066).length < 2 ^ (prefixWord ++ tailWord_1992066).sum := by decide
  have hdescent : baseEnd_1992066 < baseStart_1992066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992075 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 2, 6]
def baseStart_1992075 : Nat := 118140960795 + 1992075 * 2 ^ 59
def prefixEnd_1992075 : Nat := 4983230072969 + 3 ^ 40 * 1992075 * 2
def baseEnd_1992075 : Nat := 681927983203599154067413

theorem tailTrace_1992075 : CollatzResearch.WordTrace tailWord_1992075 prefixEnd_1992075 681927983203599154067413 := by
  unfold tailWord_1992075
  simp only [CollatzResearch.WordTrace]
  refine ⟨72656944258059969168865679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48437962838706646112577119 72656944258059969168865679)
  ·
    refine ⟨108985416387089953753298519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72656944258059969168865679 108985416387089953753298519)
    ·
      refine ⟨163478124580634930629947779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108985416387089953753298519 163478124580634930629947779)
      ·
        refine ⟨245217186870952395944921669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163478124580634930629947779 245217186870952395944921669)
        ·
          refine ⟨45978222538303574239672813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245217186870952395944921669 45978222538303574239672813)
          ·
            refine ⟨17241833451863840339877305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45978222538303574239672813 17241833451863840339877305)
            ·
              refine ⟨12931375088897880254907979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17241833451863840339877305 12931375088897880254907979)
              ·
                refine ⟨19397062633346820382361969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12931375088897880254907979 19397062633346820382361969)
                ·
                  refine ⟨14547796975010115286771477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19397062633346820382361969 14547796975010115286771477)
                  ·
                    refine ⟨681927983203599154067413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14547796975010115286771477 681927983203599154067413)
                    ·
                      rfl

theorem cell22_1992075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_1992075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992075 prefixEnd_1992075 := by exact prefixLift 1992075
  have htrace : WordTrace (prefixWord ++ tailWord_1992075) baseStart_1992075 baseEnd_1992075 := by
    simpa [prefixWord, tailWord_1992075, baseEnd_1992075] using wordTrace_append hprefix tailTrace_1992075
  have hstable : (prefixWord ++ tailWord_1992075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992075).length < 2 ^ (prefixWord ++ tailWord_1992075).sum := by decide
  have hdescent : baseEnd_1992075 < baseStart_1992075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992105 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_1992105 : Nat := 118140960795 + 1992105 * 2 ^ 59
def prefixEnd_1992105 : Nat := 4983230072969 + 3 ^ 40 * 1992105 * 2
def baseEnd_1992105 : Nat := 681938252816689075817321

theorem tailTrace_1992105 : CollatzResearch.WordTrace tailWord_1992105 prefixEnd_1992105 681938252816689075817321 := by
  unfold tailWord_1992105
  simp only [CollatzResearch.WordTrace]
  refine ⟨72658038447951284292457769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48438692298634189528305179 72658038447951284292457769)
  ·
    refine ⟨54493528835963463219343327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72658038447951284292457769 54493528835963463219343327)
    ·
      refine ⟨81740293253945194829014991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54493528835963463219343327 81740293253945194829014991)
      ·
        refine ⟨122610439880917792243522487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81740293253945194829014991 122610439880917792243522487)
        ·
          refine ⟨183915659821376688365283731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122610439880917792243522487 183915659821376688365283731)
          ·
            refine ⟨275873489732065032547925597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183915659821376688365283731 275873489732065032547925597)
            ·
              refine ⟨103452558649524387205472099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275873489732065032547925597 103452558649524387205472099)
              ·
                refine ⟨155178837974286580808208149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103452558649524387205472099 155178837974286580808208149)
                ·
                  refine ⟨7274008030044683475384757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155178837974286580808208149 7274008030044683475384757)
                  ·
                    refine ⟨681938252816689075817321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7274008030044683475384757 681938252816689075817321)
                    ·
                      rfl

theorem cell22_1992105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_1992105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992105 prefixEnd_1992105 := by exact prefixLift 1992105
  have htrace : WordTrace (prefixWord ++ tailWord_1992105) baseStart_1992105 baseEnd_1992105 := by
    simpa [prefixWord, tailWord_1992105, baseEnd_1992105] using wordTrace_append hprefix tailTrace_1992105
  have hstable : (prefixWord ++ tailWord_1992105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992105).length < 2 ^ (prefixWord ++ tailWord_1992105).sum := by decide
  have hdescent : baseEnd_1992105 < baseStart_1992105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992130 : List Nat := [3, 5, 2, 1, 1, 2, 1, 7]
def baseStart_1992130 : Nat := 118140960795 + 1992130 * 2 ^ 59
def prefixEnd_1992130 : Nat := 4983230072969 + 3 ^ 40 * 1992130 * 2
def baseEnd_1992130 : Nat := 75771867869733038215805

theorem tailTrace_1992130 : CollatzResearch.WordTrace tailWord_1992130 prefixEnd_1992130 75771867869733038215805 := by
  unfold tailWord_1992130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18164737568215178390529461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48439300181907142374745229 18164737568215178390529461)
  ·
    refine ⟨1702944147020172974112137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18164737568215178390529461 1702944147020172974112137)
    ·
      refine ⟨1277208110265129730584103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1702944147020172974112137 1277208110265129730584103)
      ·
        refine ⟨1915812165397694595876155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277208110265129730584103 1915812165397694595876155)
        ·
          refine ⟨2873718248096541893814233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915812165397694595876155 2873718248096541893814233)
          ·
            refine ⟨2155288686072406420360675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2873718248096541893814233 2155288686072406420360675)
            ·
              refine ⟨3232933029108609630541013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155288686072406420360675 3232933029108609630541013)
              ·
                refine ⟨75771867869733038215805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3232933029108609630541013 75771867869733038215805)
                ·
                  rfl

theorem cell22_1992130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_1992130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992130 prefixEnd_1992130 := by exact prefixLift 1992130
  have htrace : WordTrace (prefixWord ++ tailWord_1992130) baseStart_1992130 baseEnd_1992130 := by
    simpa [prefixWord, tailWord_1992130, baseEnd_1992130] using wordTrace_append hprefix tailTrace_1992130
  have hstable : (prefixWord ++ tailWord_1992130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992130).length < 2 ^ (prefixWord ++ tailWord_1992130).sum := by decide
  have hdescent : baseEnd_1992130 < baseStart_1992130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992184 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 4, 3]
def baseStart_1992184 : Nat := 118140960795 + 1992184 * 2 ^ 59
def prefixEnd_1992184 : Nat := 4983230072969 + 3 ^ 40 * 1992184 * 2
def baseEnd_1992184 : Nat := 681965296131159203092079

theorem tailTrace_1992184 : CollatzResearch.WordTrace tailWord_1992184 prefixEnd_1992184 681965296131159203092079 := by
  unfold tailWord_1992184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36330459907332540392291803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48440613209776720523055737 36330459907332540392291803)
  ·
    refine ⟨54495689860998810588437705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36330459907332540392291803 54495689860998810588437705)
    ·
      refine ⟨40871767395749107941328279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54495689860998810588437705 40871767395749107941328279)
      ·
        refine ⟨61307651093623661911992419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40871767395749107941328279 61307651093623661911992419)
        ·
          refine ⟨91961476640435492867988629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61307651093623661911992419 91961476640435492867988629)
          ·
            refine ⟨4310694217520413728186967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91961476640435492867988629 4310694217520413728186967)
            ·
              refine ⟨6466041326280620592280451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310694217520413728186967 6466041326280620592280451)
              ·
                refine ⟨9699061989420930888420677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6466041326280620592280451 9699061989420930888420677)
                ·
                  refine ⟨1818574123016424541578877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9699061989420930888420677 1818574123016424541578877)
                  ·
                    refine ⟨681965296131159203092079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818574123016424541578877 681965296131159203092079)
                    ·
                      rfl

theorem cell22_1992184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_1992184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992184 prefixEnd_1992184 := by exact prefixLift 1992184
  have htrace : WordTrace (prefixWord ++ tailWord_1992184) baseStart_1992184 baseEnd_1992184 := by
    simpa [prefixWord, tailWord_1992184, baseEnd_1992184] using wordTrace_append hprefix tailTrace_1992184
  have hstable : (prefixWord ++ tailWord_1992184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992184).length < 2 ^ (prefixWord ++ tailWord_1992184).sum := by decide
  have hdescent : baseEnd_1992184 < baseStart_1992184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992201 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 2, 3]
def baseStart_1992201 : Nat := 118140960795 + 1992201 * 2 ^ 59
def prefixEnd_1992201 : Nat := 4983230072969 + 3 ^ 40 * 1992201 * 2
def baseEnd_1992201 : Nat := 681971115578576825417027

theorem tailTrace_1992201 : CollatzResearch.WordTrace tailWord_1992201 prefixEnd_1992201 681971115578576825417027 := by
  unfold tailWord_1992201
  simp only [CollatzResearch.WordTrace]
  refine ⟨72661539855603492687952457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48441026570402328458634971 72661539855603492687952457)
  ·
    refine ⟨54496154891702619515964343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72661539855603492687952457 54496154891702619515964343)
    ·
      refine ⟨81744232337553929273946515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54496154891702619515964343 81744232337553929273946515)
      ·
        refine ⟨122616348506330893910919773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81744232337553929273946515 122616348506330893910919773)
        ·
          refine ⟨45981130689874085216594915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122616348506330893910919773 45981130689874085216594915)
          ·
            refine ⟨68971696034811127824892373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45981130689874085216594915 68971696034811127824892373)
            ·
              refine ⟨1616524125815885808395915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 68971696034811127824892373 1616524125815885808395915)
              ·
                refine ⟨2424786188723828712593873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616524125815885808395915 2424786188723828712593873)
                ·
                  refine ⟨1818589641542871534445405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2424786188723828712593873 1818589641542871534445405)
                  ·
                    refine ⟨681971115578576825417027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818589641542871534445405 681971115578576825417027)
                    ·
                      rfl

theorem cell22_1992201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_1992201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992201 prefixEnd_1992201 := by exact prefixLift 1992201
  have htrace : WordTrace (prefixWord ++ tailWord_1992201) baseStart_1992201 baseEnd_1992201 := by
    simpa [prefixWord, tailWord_1992201, baseEnd_1992201] using wordTrace_append hprefix tailTrace_1992201
  have hstable : (prefixWord ++ tailWord_1992201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992201).length < 2 ^ (prefixWord ++ tailWord_1992201).sum := by decide
  have hdescent : baseEnd_1992201 < baseStart_1992201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992205 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1992205 : Nat := 118140960795 + 1992205 * 2 ^ 59
def prefixEnd_1992205 : Nat := 4983230072969 + 3 ^ 40 * 1992205 * 2
def baseEnd_1992205 : Nat := 681972484860322148317015

theorem tailTrace_1992205 : CollatzResearch.WordTrace tailWord_1992205 prefixEnd_1992205 681972484860322148317015 := by
  unfold tailWord_1992205
  simp only [CollatzResearch.WordTrace]
  refine ⟨72661685747589001371098069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48441123831726000914065379 72661685747589001371098069)
  ·
    refine ⟨1703008259709117219635111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 72661685747589001371098069 1703008259709117219635111)
    ·
      refine ⟨2554512389563675829452667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1703008259709117219635111 2554512389563675829452667)
      ·
        refine ⟨3831768584345513744179001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554512389563675829452667 3831768584345513744179001)
        ·
          refine ⟨2873826438259135308134251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3831768584345513744179001 2873826438259135308134251)
          ·
            refine ⟨4310739657388702962201377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873826438259135308134251 4310739657388702962201377)
            ·
              refine ⟨3233054743041527221651033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310739657388702962201377 3233054743041527221651033)
              ·
                refine ⟨2424791057281145416238275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233054743041527221651033 2424791057281145416238275)
                ·
                  refine ⟨3637186585921718124357413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2424791057281145416238275 3637186585921718124357413)
                  ·
                    refine ⟨681972484860322148317015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3637186585921718124357413 681972484860322148317015)
                    ·
                      rfl

theorem cell22_1992205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1992205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992205 prefixEnd_1992205 := by exact prefixLift 1992205
  have htrace : WordTrace (prefixWord ++ tailWord_1992205) baseStart_1992205 baseEnd_1992205 := by
    simpa [prefixWord, tailWord_1992205, baseEnd_1992205] using wordTrace_append hprefix tailTrace_1992205
  have hstable : (prefixWord ++ tailWord_1992205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992205).length < 2 ^ (prefixWord ++ tailWord_1992205).sum := by decide
  have hdescent : baseEnd_1992205 < baseStart_1992205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992353 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1992353 : Nat := 118140960795 + 1992353 * 2 ^ 59
def prefixEnd_1992353 : Nat := 4983230072969 + 3 ^ 40 * 1992353 * 2
def baseEnd_1992353 : Nat := 682023148284899095616561

theorem tailTrace_1992353 : CollatzResearch.WordTrace tailWord_1992353 prefixEnd_1992353 682023148284899095616561 := by
  unfold tailWord_1992353
  simp only [CollatzResearch.WordTrace]
  refine ⟨72667083751052822647485713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48444722500701881764990475 72667083751052822647485713)
  ·
    refine ⟨54500312813289616985614285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72667083751052822647485713 54500312813289616985614285)
    ·
      refine ⟨20437617304983606369605357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54500312813289616985614285 20437617304983606369605357)
      ·
        refine ⟨7664106489368852388602009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20437617304983606369605357 7664106489368852388602009)
        ·
          refine ⟨5748079867026639291451507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7664106489368852388602009 5748079867026639291451507)
          ·
            refine ⟨8622119800539958937177261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748079867026639291451507 8622119800539958937177261)
            ·
              refine ⟨3233294925202484601441473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8622119800539958937177261 3233294925202484601441473)
              ·
                refine ⟨2424971193901863451081105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233294925202484601441473 2424971193901863451081105)
                ·
                  refine ⟨1818728395426397588310829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2424971193901863451081105 1818728395426397588310829)
                  ·
                    refine ⟨682023148284899095616561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818728395426397588310829 682023148284899095616561)
                    ·
                      rfl

theorem cell22_1992353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1992353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992353 prefixEnd_1992353 := by exact prefixLift 1992353
  have htrace : WordTrace (prefixWord ++ tailWord_1992353) baseStart_1992353 baseEnd_1992353 := by
    simpa [prefixWord, tailWord_1992353, baseEnd_1992353] using wordTrace_append hprefix tailTrace_1992353
  have hstable : (prefixWord ++ tailWord_1992353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992353).length < 2 ^ (prefixWord ++ tailWord_1992353).sum := by decide
  have hdescent : baseEnd_1992353 < baseStart_1992353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992381 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1992381 : Nat := 118140960795 + 1992381 * 2 ^ 59
def prefixEnd_1992381 : Nat := 4983230072969 + 3 ^ 40 * 1992381 * 2
def baseEnd_1992381 : Nat := 682032733257116355916475

theorem tailTrace_1992381 : CollatzResearch.WordTrace tailWord_1992381 prefixEnd_1992381 682032733257116355916475 := by
  unfold tailWord_1992381
  simp only [CollatzResearch.WordTrace]
  refine ⟨72668104994951383429504997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48445403329967588953003331 72668104994951383429504997)
  ·
    refine ⟨13625269686553384393032187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72668104994951383429504997 13625269686553384393032187)
    ·
      refine ⟨20437904529830076589548281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13625269686553384393032187 20437904529830076589548281)
      ·
        refine ⟨15328428397372557442161211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20437904529830076589548281 15328428397372557442161211)
        ·
          refine ⟨22992642596058836163241817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15328428397372557442161211 22992642596058836163241817)
          ·
            refine ⟨17244481947044127122431363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22992642596058836163241817 17244481947044127122431363)
            ·
              refine ⟨25866722920566190683647045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17244481947044127122431363 25866722920566190683647045)
              ·
                refine ⟨4850010547606160753183821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25866722920566190683647045 4850010547606160753183821)
                ·
                  refine ⟨1818753955352310282443933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4850010547606160753183821 1818753955352310282443933)
                  ·
                    refine ⟨682032733257116355916475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818753955352310282443933 682032733257116355916475)
                    ·
                      rfl

theorem cell22_1992381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1992381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992381 prefixEnd_1992381 := by exact prefixLift 1992381
  have htrace : WordTrace (prefixWord ++ tailWord_1992381) baseStart_1992381 baseEnd_1992381 := by
    simpa [prefixWord, tailWord_1992381, baseEnd_1992381] using wordTrace_append hprefix tailTrace_1992381
  have hstable : (prefixWord ++ tailWord_1992381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992381).length < 2 ^ (prefixWord ++ tailWord_1992381).sum := by decide
  have hdescent : baseEnd_1992381 < baseStart_1992381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992415 : List Nat := [1, 1, 2, 3, 2, 2, 5, 2, 1, 3]
def baseStart_1992415 : Nat := 118140960795 + 1992415 * 2 ^ 59
def prefixEnd_1992415 : Nat := 4983230072969 + 3 ^ 40 * 1992415 * 2
def baseEnd_1992415 : Nat := 682044372151951600566371

theorem tailTrace_1992415 : CollatzResearch.WordTrace tailWord_1992415 prefixEnd_1992415 682044372151951600566371 := by
  unfold tailWord_1992415
  simp only [CollatzResearch.WordTrace]
  refine ⟨72669345076828207236242699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48446230051218804824161799 72669345076828207236242699)
  ·
    refine ⟨109004017615242310854364049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72669345076828207236242699 109004017615242310854364049)
    ·
      refine ⟨81753013211431733140773037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109004017615242310854364049 81753013211431733140773037)
      ·
        refine ⟨30657379954286899927789889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81753013211431733140773037 30657379954286899927789889)
        ·
          refine ⟨22993034965715174945842417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30657379954286899927789889 22993034965715174945842417)
          ·
            refine ⟨17244776224286381209381813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22993034965715174945842417 17244776224286381209381813)
            ·
              refine ⟨1616697771026848238379545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17244776224286381209381813 1616697771026848238379545)
              ·
                refine ⟨1212523328270136178784659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616697771026848238379545 1212523328270136178784659)
                ·
                  refine ⟨1818784992405204268176989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212523328270136178784659 1818784992405204268176989)
                  ·
                    refine ⟨682044372151951600566371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818784992405204268176989 682044372151951600566371)
                    ·
                      rfl

theorem cell22_1992415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 3].length) (baseStart_1992415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992415 prefixEnd_1992415 := by exact prefixLift 1992415
  have htrace : WordTrace (prefixWord ++ tailWord_1992415) baseStart_1992415 baseEnd_1992415 := by
    simpa [prefixWord, tailWord_1992415, baseEnd_1992415] using wordTrace_append hprefix tailTrace_1992415
  have hstable : (prefixWord ++ tailWord_1992415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992415).length < 2 ^ (prefixWord ++ tailWord_1992415).sum := by decide
  have hdescent : baseEnd_1992415 < baseStart_1992415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992439 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 6]
def baseStart_1992439 : Nat := 118140960795 + 1992439 * 2 ^ 59
def prefixEnd_1992439 : Nat := 4983230072969 + 3 ^ 40 * 1992439 * 2
def baseEnd_1992439 : Nat := 227350862614141179322099

theorem tailTrace_1992439 : CollatzResearch.WordTrace tailWord_1992439 prefixEnd_1992439 227350862614141179322099 := by
  unfold tailWord_1992439
  simp only [CollatzResearch.WordTrace]
  refine ⟨72670220428741259335116371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48446813619160839556744247 72670220428741259335116371)
  ·
    refine ⟨109005330643111889002674557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72670220428741259335116371 109005330643111889002674557)
    ·
      refine ⟨40876998991166958376002959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109005330643111889002674557 40876998991166958376002959)
      ·
        refine ⟨61315498486750437564004439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40876998991166958376002959 61315498486750437564004439)
        ·
          refine ⟨91973247730125656346006659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61315498486750437564004439 91973247730125656346006659)
          ·
            refine ⟨137959871595188484519009989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91973247730125656346006659 137959871595188484519009989)
            ·
              refine ⟨25867475924097840847314373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137959871595188484519009989 25867475924097840847314373)
              ·
                refine ⟨4850151735768345158871445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25867475924097840847314373 4850151735768345158871445)
                ·
                  refine ⟨227350862614141179322099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4850151735768345158871445 227350862614141179322099)
                  ·
                    rfl

theorem cell22_1992439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 6].length) (baseStart_1992439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992439 prefixEnd_1992439 := by exact prefixLift 1992439
  have htrace : WordTrace (prefixWord ++ tailWord_1992439) baseStart_1992439 baseEnd_1992439 := by
    simpa [prefixWord, tailWord_1992439, baseEnd_1992439] using wordTrace_append hprefix tailTrace_1992439
  have hstable : (prefixWord ++ tailWord_1992439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992439).length < 2 ^ (prefixWord ++ tailWord_1992439).sum := by decide
  have hdescent : baseEnd_1992439 < baseStart_1992439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992488 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1992488 : Nat := 118140960795 + 1992488 * 2 ^ 59
def prefixEnd_1992488 : Nat := 4983230072969 + 3 ^ 40 * 1992488 * 2
def baseEnd_1992488 : Nat := 682069361543803743491147

theorem tailTrace_1992488 : CollatzResearch.WordTrace tailWord_1992488 prefixEnd_1992488 682069361543803743491147 := by
  unfold tailWord_1992488
  simp only [CollatzResearch.WordTrace]
  refine ⟨36336003802781870351825059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48448005070375827135766745 36336003802781870351825059)
  ·
    refine ⟨54504005704172805527737589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36336003802781870351825059 54504005704172805527737589)
    ·
      refine ⟨5109750534766200518225399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54504005704172805527737589 5109750534766200518225399)
      ·
        refine ⟨7664625802149300777338099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109750534766200518225399 7664625802149300777338099)
        ·
          refine ⟨11496938703223951166007149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664625802149300777338099 11496938703223951166007149)
          ·
            refine ⟨4311352013708981687252681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11496938703223951166007149 4311352013708981687252681)
            ·
              refine ⟨3233514010281736265439511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4311352013708981687252681 3233514010281736265439511)
              ·
                refine ⟨4850271015422604398159267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233514010281736265439511 4850271015422604398159267)
                ·
                  refine ⟨7275406523133906597238901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850271015422604398159267 7275406523133906597238901)
                  ·
                    refine ⟨682069361543803743491147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7275406523133906597238901 682069361543803743491147)
                    ·
                      rfl

theorem cell22_1992488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1992488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992488 prefixEnd_1992488 := by exact prefixLift 1992488
  have htrace : WordTrace (prefixWord ++ tailWord_1992488) baseStart_1992488 baseEnd_1992488 := by
    simpa [prefixWord, tailWord_1992488, baseEnd_1992488] using wordTrace_append hprefix tailTrace_1992488
  have hstable : (prefixWord ++ tailWord_1992488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992488).length < 2 ^ (prefixWord ++ tailWord_1992488).sum := by decide
  have hdescent : baseEnd_1992488 < baseStart_1992488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992533 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_1992533 : Nat := 118140960795 + 1992533 * 2 ^ 59
def prefixEnd_1992533 : Nat := 4983230072969 + 3 ^ 40 * 1992533 * 2
def baseEnd_1992533 : Nat := 682084765963438626116009

theorem tailTrace_1992533 : CollatzResearch.WordTrace tailWord_1992533 prefixEnd_1992533 682084765963438626116009 := by
  unfold tailWord_1992533
  simp only [CollatzResearch.WordTrace]
  refine ⟨72673648890400713389038253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48449099260267142259358835 72673648890400713389038253)
  ·
    refine ⟨27252618333900267520889345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72673648890400713389038253 27252618333900267520889345)
    ·
      refine ⟨20439463750425200640667009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27252618333900267520889345 20439463750425200640667009)
      ·
        refine ⟨15329597812818900480500257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20439463750425200640667009 15329597812818900480500257)
        ·
          refine ⟨11497198359614175360375193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15329597812818900480500257 11497198359614175360375193)
          ·
            refine ⟨8622898769710631520281395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11497198359614175360375193 8622898769710631520281395)
            ·
              refine ⟨12934348154565947280422093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622898769710631520281395 12934348154565947280422093)
              ·
                refine ⟨4850380557962230230158285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12934348154565947280422093 4850380557962230230158285)
                ·
                  refine ⟨1818892709235836336309357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4850380557962230230158285 1818892709235836336309357)
                  ·
                    refine ⟨682084765963438626116009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818892709235836336309357 682084765963438626116009)
                    ·
                      rfl

theorem cell22_1992533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_1992533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992533 prefixEnd_1992533 := by exact prefixLift 1992533
  have htrace : WordTrace (prefixWord ++ tailWord_1992533) baseStart_1992533 baseEnd_1992533 := by
    simpa [prefixWord, tailWord_1992533, baseEnd_1992533] using wordTrace_append hprefix tailTrace_1992533
  have hstable : (prefixWord ++ tailWord_1992533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992533).length < 2 ^ (prefixWord ++ tailWord_1992533).sum := by decide
  have hdescent : baseEnd_1992533 < baseStart_1992533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992584 : List Nat := [2, 1, 3, 3, 3, 1, 3, 2, 1, 3]
def baseStart_1992584 : Nat := 118140960795 + 1992584 * 2 ^ 59
def prefixEnd_1992584 : Nat := 4983230072969 + 3 ^ 40 * 1992584 * 2
def baseEnd_1992584 : Nat := 682102224305691493090853

theorem tailTrace_1992584 : CollatzResearch.WordTrace tailWord_1992584 prefixEnd_1992584 682102224305691493090853 := by
  unfold tailWord_1992584
  simp only [CollatzResearch.WordTrace]
  refine ⟨36337754506607974549572403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48450339342143966066096537 36337754506607974549572403)
  ·
    refine ⟨54506631759911961824358605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36337754506607974549572403 54506631759911961824358605)
    ·
      refine ⟨20439986909966985684134477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54506631759911961824358605 20439986909966985684134477)
      ·
        refine ⟨7664995091237619631550429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20439986909966985684134477 7664995091237619631550429)
        ·
          refine ⟨2874373159214107361831411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7664995091237619631550429 2874373159214107361831411)
          ·
            refine ⟨4311559738821161042747117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874373159214107361831411 4311559738821161042747117)
            ·
              refine ⟨1616834902057935391030169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4311559738821161042747117 1616834902057935391030169)
              ·
                refine ⟨1212626176543451543272627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616834902057935391030169 1212626176543451543272627)
                ·
                  refine ⟨1818939264815177314908941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212626176543451543272627 1818939264815177314908941)
                  ·
                    refine ⟨682102224305691493090853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818939264815177314908941 682102224305691493090853)
                    ·
                      rfl

theorem cell22_1992584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_1992584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992584 prefixEnd_1992584 := by exact prefixLift 1992584
  have htrace : WordTrace (prefixWord ++ tailWord_1992584) baseStart_1992584 baseEnd_1992584 := by
    simpa [prefixWord, tailWord_1992584, baseEnd_1992584] using wordTrace_append hprefix tailTrace_1992584
  have hstable : (prefixWord ++ tailWord_1992584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992584).length < 2 ^ (prefixWord ++ tailWord_1992584).sum := by decide
  have hdescent : baseEnd_1992584 < baseStart_1992584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992610 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1992610 : Nat := 118140960795 + 1992610 * 2 ^ 59
def prefixEnd_1992610 : Nat := 4983230072969 + 3 ^ 40 * 1992610 * 2
def baseEnd_1992610 : Nat := 682111124637036091940773

theorem tailTrace_1992610 : CollatzResearch.WordTrace tailWord_1992610 prefixEnd_1992610 682111124637036091940773 := by
  unfold tailWord_1992610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18169114327780438884897821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48450971540747837026394189 18169114327780438884897821)
  ·
    refine ⟨6813417872917664581836683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18169114327780438884897821 6813417872917664581836683)
    ·
      refine ⟨10220126809376496872755025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813417872917664581836683 10220126809376496872755025)
      ·
        refine ⟨7665095107032372654566269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10220126809376496872755025 7665095107032372654566269)
        ·
          refine ⟨2874410665137139745462351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7665095107032372654566269 2874410665137139745462351)
          ·
            refine ⟨4311615997705709618193527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874410665137139745462351 4311615997705709618193527)
            ·
              refine ⟨6467423996558564427290291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311615997705709618193527 6467423996558564427290291)
              ·
                refine ⟨9701135994837846640935437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6467423996558564427290291 9701135994837846640935437)
                ·
                  refine ⟨3637925998064192490350789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9701135994837846640935437 3637925998064192490350789)
                  ·
                    refine ⟨682111124637036091940773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3637925998064192490350789 682111124637036091940773)
                    ·
                      rfl

theorem cell22_1992610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1992610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992610 prefixEnd_1992610 := by exact prefixLift 1992610
  have htrace : WordTrace (prefixWord ++ tailWord_1992610) baseStart_1992610 baseEnd_1992610 := by
    simpa [prefixWord, tailWord_1992610, baseEnd_1992610] using wordTrace_append hprefix tailTrace_1992610
  have hstable : (prefixWord ++ tailWord_1992610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992610).length < 2 ^ (prefixWord ++ tailWord_1992610).sum := by decide
  have hdescent : baseEnd_1992610 < baseStart_1992610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992640 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 2, 3]
def baseStart_1992640 : Nat := 118140960795 + 1992640 * 2 ^ 59
def prefixEnd_1992640 : Nat := 4983230072969 + 3 ^ 40 * 1992640 * 2
def baseEnd_1992640 : Nat := 682121394250126013690681

theorem tailTrace_1992640 : CollatzResearch.WordTrace tailWord_1992640 prefixEnd_1992640 682121394250126013690681 := by
  unfold tailWord_1992640
  simp only [CollatzResearch.WordTrace]
  refine ⟨36338775750506535331591687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48451701000675380442122249 36338775750506535331591687)
  ·
    refine ⟨54508163625759802997387531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36338775750506535331591687 54508163625759802997387531)
    ·
      refine ⟨81762245438639704496081297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54508163625759802997387531 81762245438639704496081297)
      ·
        refine ⟨61321684078979778372060973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81762245438639704496081297 61321684078979778372060973)
        ·
          refine ⟨22995631529617416889522865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61321684078979778372060973 22995631529617416889522865)
          ·
            refine ⟨17246723647213062667142149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22995631529617416889522865 17246723647213062667142149)
            ·
              refine ⟨3233760683852449250089153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17246723647213062667142149 3233760683852449250089153)
              ·
                refine ⟨2425320512889336937566865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233760683852449250089153 2425320512889336937566865)
                ·
                  refine ⟨1818990384667002703175149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2425320512889336937566865 1818990384667002703175149)
                  ·
                    refine ⟨682121394250126013690681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1818990384667002703175149 682121394250126013690681)
                    ·
                      rfl

theorem cell22_1992640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_1992640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992640 prefixEnd_1992640 := by exact prefixLift 1992640
  have htrace : WordTrace (prefixWord ++ tailWord_1992640) baseStart_1992640 baseEnd_1992640 := by
    simpa [prefixWord, tailWord_1992640, baseEnd_1992640] using wordTrace_append hprefix tailTrace_1992640
  have hstable : (prefixWord ++ tailWord_1992640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992640).length < 2 ^ (prefixWord ++ tailWord_1992640).sum := by decide
  have hdescent : baseEnd_1992640 < baseStart_1992640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992702 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1992702 : Nat := 118140960795 + 1992702 * 2 ^ 59
def prefixEnd_1992702 : Nat := 4983230072969 + 3 ^ 40 * 1992702 * 2
def baseEnd_1992702 : Nat := 682142618117178518640491

theorem tailTrace_1992702 : CollatzResearch.WordTrace tailWord_1992702 prefixEnd_1992702 682142618117178518640491 := by
  unfold tailWord_1992702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084976603348556906492545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48453208551192303501293573 9084976603348556906492545)
  ·
    refine ⟨6813732452511417679869409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9084976603348556906492545 6813732452511417679869409)
    ·
      refine ⟨5110299339383563259902057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6813732452511417679869409 5110299339383563259902057)
      ·
        refine ⟨3832724504537672444926543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110299339383563259902057 3832724504537672444926543)
        ·
          refine ⟨5749086756806508667389815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832724504537672444926543 5749086756806508667389815)
          ·
            refine ⟨8623630135209763001084723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749086756806508667389815 8623630135209763001084723)
            ·
              refine ⟨12935445202814644501627085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623630135209763001084723 12935445202814644501627085)
              ·
                refine ⟨4850791951055491688110157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12935445202814644501627085 4850791951055491688110157)
                ·
                  refine ⟨1819046981645809383041309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4850791951055491688110157 1819046981645809383041309)
                  ·
                    refine ⟨682142618117178518640491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819046981645809383041309 682142618117178518640491)
                    ·
                      rfl

theorem cell22_1992702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1992702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992702 prefixEnd_1992702 := by exact prefixLift 1992702
  have htrace : WordTrace (prefixWord ++ tailWord_1992702) baseStart_1992702 baseEnd_1992702 := by
    simpa [prefixWord, tailWord_1992702, baseEnd_1992702] using wordTrace_append hprefix tailTrace_1992702
  have hstable : (prefixWord ++ tailWord_1992702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992702).length < 2 ^ (prefixWord ++ tailWord_1992702).sum := by decide
  have hdescent : baseEnd_1992702 < baseStart_1992702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992715 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 5]
def baseStart_1992715 : Nat := 118140960795 + 1992715 * 2 ^ 59
def prefixEnd_1992715 : Nat := 4983230072969 + 3 ^ 40 * 1992715 * 2
def baseEnd_1992715 : Nat := 227382356094283606021817

theorem tailTrace_1992715 : CollatzResearch.WordTrace tailWord_1992715 prefixEnd_1992715 227382356094283606021817 := by
  unfold tailWord_1992715
  simp only [CollatzResearch.WordTrace]
  refine ⟨72680286975741358472163599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48453524650494238981442399 72680286975741358472163599)
  ·
    refine ⟨109020430463612037708245399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72680286975741358472163599 109020430463612037708245399)
    ·
      refine ⟨163530645695418056562368099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109020430463612037708245399 163530645695418056562368099)
      ·
        refine ⟨245295968543127084843552149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163530645695418056562368099 245295968543127084843552149)
        ·
          refine ⟨11498248525459082102041507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 245295968543127084843552149 11498248525459082102041507)
          ·
            refine ⟨17247372788188623153062261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11498248525459082102041507 17247372788188623153062261)
            ·
              refine ⟨1616941198892683420599587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17247372788188623153062261 1616941198892683420599587)
              ·
                refine ⟨2425411798339025130899381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616941198892683420599587 2425411798339025130899381)
                ·
                  refine ⟨227382356094283606021817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2425411798339025130899381 227382356094283606021817)
                  ·
                    rfl

theorem cell22_1992715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 5].length) (baseStart_1992715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992715 prefixEnd_1992715 := by exact prefixLift 1992715
  have htrace : WordTrace (prefixWord ++ tailWord_1992715) baseStart_1992715 baseEnd_1992715 := by
    simpa [prefixWord, tailWord_1992715, baseEnd_1992715] using wordTrace_append hprefix tailTrace_1992715
  have hstable : (prefixWord ++ tailWord_1992715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992715).length < 2 ^ (prefixWord ++ tailWord_1992715).sum := by decide
  have hdescent : baseEnd_1992715 < baseStart_1992715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992766 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1992766 : Nat := 118140960795 + 1992766 * 2 ^ 59
def prefixEnd_1992766 : Nat := 4983230072969 + 3 ^ 40 * 1992766 * 2
def baseEnd_1992766 : Nat := 227388175541701228346765

theorem tailTrace_1992766 : CollatzResearch.WordTrace tailWord_1992766 prefixEnd_1992766 227388175541701228346765 := by
  unfold tailWord_1992766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085268387319574272783769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48454764732371062788180101 9085268387319574272783769)
  ·
    refine ⟨6813951290489680704587827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9085268387319574272783769 6813951290489680704587827)
    ·
      refine ⟨10220926935734521056881741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6813951290489680704587827 10220926935734521056881741)
      ·
        refine ⟨3832847600900445396330653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10220926935734521056881741 3832847600900445396330653)
        ·
          refine ⟨1437317850337667023623995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3832847600900445396330653 1437317850337667023623995)
          ·
            refine ⟨2155976775506500535435993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437317850337667023623995 2155976775506500535435993)
            ·
              refine ⟨1616982581629875401576995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155976775506500535435993 1616982581629875401576995)
              ·
                refine ⟨2425473872444813102365493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616982581629875401576995 2425473872444813102365493)
                ·
                  refine ⟨227388175541701228346765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2425473872444813102365493 227388175541701228346765)
                  ·
                    rfl

theorem cell22_1992766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1992766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992766 prefixEnd_1992766 := by exact prefixLift 1992766
  have htrace : WordTrace (prefixWord ++ tailWord_1992766) baseStart_1992766 baseEnd_1992766 := by
    simpa [prefixWord, tailWord_1992766, baseEnd_1992766] using wordTrace_append hprefix tailTrace_1992766
  have hstable : (prefixWord ++ tailWord_1992766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992766).length < 2 ^ (prefixWord ++ tailWord_1992766).sum := by decide
  have hdescent : baseEnd_1992766 < baseStart_1992766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992773 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1992773 : Nat := 118140960795 + 1992773 * 2 ^ 59
def prefixEnd_1992773 : Nat := 4983230072969 + 3 ^ 40 * 1992773 * 2
def baseEnd_1992773 : Nat := 682166922868158000115273

theorem tailTrace_1992773 : CollatzResearch.WordTrace tailWord_1992773 prefixEnd_1992773 682166922868158000115273 := by
  unfold tailWord_1992773
  simp only [CollatzResearch.WordTrace]
  refine ⟨72682402409531234377774973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48454934939687489585183315 72682402409531234377774973)
  ·
    refine ⟨27255900903574212891665615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72682402409531234377774973 27255900903574212891665615)
    ·
      refine ⟨40883851355361319337498423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27255900903574212891665615 40883851355361319337498423)
      ·
        refine ⟨61325777033041979006247635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40883851355361319337498423 61325777033041979006247635)
        ·
          refine ⟨91988665549562968509371453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61325777033041979006247635 91988665549562968509371453)
          ·
            refine ⟨34495749581086113191014295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91988665549562968509371453 34495749581086113191014295)
            ·
              refine ⟨51743624371629169786521443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34495749581086113191014295 51743624371629169786521443)
              ·
                refine ⟨77615436557443754679782165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51743624371629169786521443 77615436557443754679782165)
                ·
                  refine ⟨3638223588630176000614789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77615436557443754679782165 3638223588630176000614789)
                  ·
                    refine ⟨682166922868158000115273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638223588630176000614789 682166922868158000115273)
                    ·
                      rfl

theorem cell22_1992773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1992773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992773 prefixEnd_1992773 := by exact prefixLift 1992773
  have htrace : WordTrace (prefixWord ++ tailWord_1992773) baseStart_1992773 baseEnd_1992773 := by
    simpa [prefixWord, tailWord_1992773, baseEnd_1992773] using wordTrace_append hprefix tailTrace_1992773
  have hstable : (prefixWord ++ tailWord_1992773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992773).length < 2 ^ (prefixWord ++ tailWord_1992773).sum := by decide
  have hdescent : baseEnd_1992773 < baseStart_1992773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992822 : List Nat := [5, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1992822 : Nat := 118140960795 + 1992822 * 2 ^ 59
def prefixEnd_1992822 : Nat := 4983230072969 + 3 ^ 40 * 1992822 * 2
def baseEnd_1992822 : Nat := 75798188507726467293347

theorem tailTrace_1992822 : CollatzResearch.WordTrace tailWord_1992822 prefixEnd_1992822 75798188507726467293347 := by
  unfold tailWord_1992822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4542761849147107234144295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48456126390902477164205813 4542761849147107234144295)
  ·
    refine ⟨6814142773720660851216443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4542761849147107234144295 6814142773720660851216443)
    ·
      refine ⟨10221214160580991276824665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6814142773720660851216443 10221214160580991276824665)
      ·
        refine ⟨7665910620435743457618499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10221214160580991276824665 7665910620435743457618499)
        ·
          refine ⟨11498865930653615186427749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665910620435743457618499 11498865930653615186427749)
          ·
            refine ⟨2156037361997552847455203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11498865930653615186427749 2156037361997552847455203)
            ·
              refine ⟨3234056042996329271182805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156037361997552847455203 3234056042996329271182805)
              ·
                refine ⟨75798188507726467293347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3234056042996329271182805 75798188507726467293347)
                ·
                  rfl

theorem cell22_1992822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1992822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992822 prefixEnd_1992822 := by exact prefixLift 1992822
  have htrace : WordTrace (prefixWord ++ tailWord_1992822) baseStart_1992822 baseEnd_1992822 := by
    simpa [prefixWord, tailWord_1992822, baseEnd_1992822] using wordTrace_append hprefix tailTrace_1992822
  have hstable : (prefixWord ++ tailWord_1992822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992822).length < 2 ^ (prefixWord ++ tailWord_1992822).sum := by decide
  have hdescent : baseEnd_1992822 < baseStart_1992822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992837 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_1992837 : Nat := 118140960795 + 1992837 * 2 ^ 59
def prefixEnd_1992837 : Nat := 4983230072969 + 3 ^ 40 * 1992837 * 2
def baseEnd_1992837 : Nat := 682188831376083166515077

theorem tailTrace_1992837 : CollatzResearch.WordTrace tailWord_1992837 prefixEnd_1992837 682188831376083166515077 := by
  unfold tailWord_1992837
  simp only [CollatzResearch.WordTrace]
  refine ⟨72684736681299373308104765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48456491120866248872069843 72684736681299373308104765)
  ·
    refine ⟨27256776255487264990539287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72684736681299373308104765 27256776255487264990539287)
    ·
      refine ⟨40885164383230897485808931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27256776255487264990539287 40885164383230897485808931)
      ·
        refine ⟨61327746574846346228713397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40885164383230897485808931 61327746574846346228713397)
        ·
          refine ⟨5749476241391844958941881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61327746574846346228713397 5749476241391844958941881)
          ·
            refine ⟨4312107181043883719206411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5749476241391844958941881 4312107181043883719206411)
            ·
              refine ⟨6468160771565825578809617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312107181043883719206411 6468160771565825578809617)
              ·
                refine ⟨4851120578674369184107213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468160771565825578809617 4851120578674369184107213)
                ·
                  refine ⟨1819170217002888444040205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4851120578674369184107213 1819170217002888444040205)
                  ·
                    refine ⟨682188831376083166515077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819170217002888444040205 682188831376083166515077)
                    ·
                      rfl

theorem cell22_1992837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_1992837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992837 prefixEnd_1992837 := by exact prefixLift 1992837
  have htrace : WordTrace (prefixWord ++ tailWord_1992837) baseStart_1992837 baseEnd_1992837 := by
    simpa [prefixWord, tailWord_1992837, baseEnd_1992837] using wordTrace_append hprefix tailTrace_1992837
  have hstable : (prefixWord ++ tailWord_1992837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992837).length < 2 ^ (prefixWord ++ tailWord_1992837).sum := by decide
  have hdescent : baseEnd_1992837 < baseStart_1992837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992848 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_1992848 : Nat := 118140960795 + 1992848 * 2 ^ 59
def prefixEnd_1992848 : Nat := 4983230072969 + 3 ^ 40 * 1992848 * 2
def baseEnd_1992848 : Nat := 682192596900882804490043

theorem tailTrace_1992848 : CollatzResearch.WordTrace tailWord_1992848 prefixEnd_1992848 682192596900882804490043 := by
  unfold tailWord_1992848
  simp only [CollatzResearch.WordTrace]
  refine ⟨36342568942129761093377599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48456758589506348124503465 36342568942129761093377599)
  ·
    refine ⟨54513853413194641640066399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36342568942129761093377599 54513853413194641640066399)
    ·
      refine ⟨81770780119791962460099599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54513853413194641640066399 81770780119791962460099599)
      ·
        refine ⟨122656170179687943690149399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81770780119791962460099599 122656170179687943690149399)
        ·
          refine ⟨183984255269531915535224099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122656170179687943690149399 183984255269531915535224099)
          ·
            refine ⟨275976382904297873302836149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183984255269531915535224099 275976382904297873302836149)
            ·
              refine ⟨25872785897277925622140889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275976382904297873302836149 25872785897277925622140889)
              ·
                refine ⟨19404589422958444216605667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25872785897277925622140889 19404589422958444216605667)
                ·
                  refine ⟨29106884134437666324908501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19404589422958444216605667 29106884134437666324908501)
                  ·
                    refine ⟨682192596900882804490043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29106884134437666324908501 682192596900882804490043)
                    ·
                      rfl

theorem cell22_1992848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_1992848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992848 prefixEnd_1992848 := by exact prefixLift 1992848
  have htrace : WordTrace (prefixWord ++ tailWord_1992848) baseStart_1992848 baseEnd_1992848 := by
    simpa [prefixWord, tailWord_1992848, baseEnd_1992848] using wordTrace_append hprefix tailTrace_1992848
  have hstable : (prefixWord ++ tailWord_1992848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992848).length < 2 ^ (prefixWord ++ tailWord_1992848).sum := by decide
  have hdescent : baseEnd_1992848 < baseStart_1992848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992850 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1992850 : Nat := 118140960795 + 1992850 * 2 ^ 59
def prefixEnd_1992850 : Nat := 4983230072969 + 3 ^ 40 * 1992850 * 2
def baseEnd_1992850 : Nat := 227397760513918488646679

theorem tailTrace_1992850 : CollatzResearch.WordTrace tailWord_1992850 prefixEnd_1992850 227397760513918488646679 := by
  unfold tailWord_1992850
  simp only [CollatzResearch.WordTrace]
  refine ⟨18171302707563069132082001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48456807220168184352218669 18171302707563069132082001)
  ·
    refine ⟨13628477030672301849061501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18171302707563069132082001 13628477030672301849061501)
    ·
      refine ⟨5110678886502113193398063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13628477030672301849061501 5110678886502113193398063)
      ·
        refine ⟨7666018329753169790097095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110678886502113193398063 7666018329753169790097095)
        ·
          refine ⟨11499027494629754685145643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7666018329753169790097095 11499027494629754685145643)
          ·
            refine ⟨17248541241944632027718465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11499027494629754685145643 17248541241944632027718465)
            ·
              refine ⟨12936405931458474020788849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17248541241944632027718465 12936405931458474020788849)
              ·
                refine ⟨9702304448593855515591637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12936405931458474020788849 9702304448593855515591637)
                ·
                  refine ⟨227397760513918488646679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9702304448593855515591637 227397760513918488646679)
                  ·
                    rfl

theorem cell22_1992850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1992850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992850 prefixEnd_1992850 := by exact prefixLift 1992850
  have htrace : WordTrace (prefixWord ++ tailWord_1992850) baseStart_1992850 baseEnd_1992850 := by
    simpa [prefixWord, tailWord_1992850, baseEnd_1992850] using wordTrace_append hprefix tailTrace_1992850
  have hstable : (prefixWord ++ tailWord_1992850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992850).length < 2 ^ (prefixWord ++ tailWord_1992850).sum := by decide
  have hdescent : baseEnd_1992850 < baseStart_1992850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992865 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1992865 : Nat := 118140960795 + 1992865 * 2 ^ 59
def prefixEnd_1992865 : Nat := 4983230072969 + 3 ^ 40 * 1992865 * 2
def baseEnd_1992865 : Nat := 682198416348300426814991

theorem tailTrace_1992865 : CollatzResearch.WordTrace tailWord_1992865 prefixEnd_1992865 682198416348300426814991 := by
  unfold tailWord_1992865
  simp only [CollatzResearch.WordTrace]
  refine ⟨72685757925197934090124049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48457171950131956060082699 72685757925197934090124049)
  ·
    refine ⟨54514318443898450567593037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72685757925197934090124049 54514318443898450567593037)
    ·
      refine ⟨20442869416461918962847389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54514318443898450567593037 20442869416461918962847389)
      ·
        refine ⟨7666076031173219611067771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20442869416461918962847389 7666076031173219611067771)
        ·
          refine ⟨11499114046759829416601657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7666076031173219611067771 11499114046759829416601657)
          ·
            refine ⟨8624335535069872062451243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11499114046759829416601657 8624335535069872062451243)
            ·
              refine ⟨12936503302604808093676865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624335535069872062451243 12936503302604808093676865)
              ·
                refine ⟨9702377476953606070257649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12936503302604808093676865 9702377476953606070257649)
                ·
                  refine ⟨7276783107715204552693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9702377476953606070257649 7276783107715204552693237)
                  ·
                    refine ⟨682198416348300426814991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7276783107715204552693237 682198416348300426814991)
                    ·
                      rfl

theorem cell22_1992865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1992865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992865 prefixEnd_1992865 := by exact prefixLift 1992865
  have htrace : WordTrace (prefixWord ++ tailWord_1992865) baseStart_1992865 baseEnd_1992865 := by
    simpa [prefixWord, tailWord_1992865, baseEnd_1992865] using wordTrace_append hprefix tailTrace_1992865
  have hstable : (prefixWord ++ tailWord_1992865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992865).length < 2 ^ (prefixWord ++ tailWord_1992865).sum := by decide
  have hdescent : baseEnd_1992865 < baseStart_1992865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992927 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 2, 3]
def baseStart_1992927 : Nat := 118140960795 + 1992927 * 2 ^ 59
def prefixEnd_1992927 : Nat := 4983230072969 + 3 ^ 40 * 1992927 * 2
def baseEnd_1992927 : Nat := 682219640215352931764801

theorem tailTrace_1992927 : CollatzResearch.WordTrace tailWord_1992927 prefixEnd_1992927 682219640215352931764801 := by
  unfold tailWord_1992927
  simp only [CollatzResearch.WordTrace]
  refine ⟨72688019250973318678881035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48458679500648879119254023 72688019250973318678881035)
  ·
    refine ⟨109032028876459978018321553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72688019250973318678881035 109032028876459978018321553)
    ·
      refine ⟨81774021657344983513741165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109032028876459978018321553 81774021657344983513741165)
      ·
        refine ⟨30665258121504368817652937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81774021657344983513741165 30665258121504368817652937)
        ·
          refine ⟨22998943591128276613239703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30665258121504368817652937 22998943591128276613239703)
          ·
            refine ⟨34498415386692414919859555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22998943591128276613239703 34498415386692414919859555)
            ·
              refine ⟨51747623080038622379789333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34498415386692414919859555 51747623080038622379789333)
              ·
                refine ⟨2425669831876810424052625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51747623080038622379789333 2425669831876810424052625)
                ·
                  refine ⟨1819252373907607818039469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2425669831876810424052625 1819252373907607818039469)
                  ·
                    refine ⟨682219640215352931764801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819252373907607818039469 682219640215352931764801)
                    ·
                      rfl

theorem cell22_1992927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_1992927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992927 prefixEnd_1992927 := by exact prefixLift 1992927
  have htrace : WordTrace (prefixWord ++ tailWord_1992927) baseStart_1992927 baseEnd_1992927 := by
    simpa [prefixWord, tailWord_1992927, baseEnd_1992927] using wordTrace_append hprefix tailTrace_1992927
  have hstable : (prefixWord ++ tailWord_1992927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992927).length < 2 ^ (prefixWord ++ tailWord_1992927).sum := by decide
  have hdescent : baseEnd_1992927 < baseStart_1992927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992929 : List Nat := [1, 2, 3, 1, 3, 1, 5, 2, 4]
def baseStart_1992929 : Nat := 118140960795 + 1992929 * 2 ^ 59
def prefixEnd_1992929 : Nat := 4983230072969 + 3 ^ 40 * 1992929 * 2
def baseEnd_1992929 : Nat := 227406774952075197738265

theorem tailTrace_1992929 : CollatzResearch.WordTrace tailWord_1992929 prefixEnd_1992929 227406774952075197738265 := by
  unfold tailWord_1992929
  simp only [CollatzResearch.WordTrace]
  refine ⟨72688092196966073020453841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48458728131310715346969227 72688092196966073020453841)
  ·
    refine ⟨54516069147724554765340381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72688092196966073020453841 54516069147724554765340381)
    ·
      refine ⟨20443525930396708037002643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54516069147724554765340381 20443525930396708037002643)
      ·
        refine ⟨30665288895595062055503965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20443525930396708037002643 30665288895595062055503965)
        ·
          refine ⟨11499483335848148270813987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30665288895595062055503965 11499483335848148270813987)
          ·
            refine ⟨17249225003772222406220981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11499483335848148270813987 17249225003772222406220981)
            ·
              refine ⟨1617114844103645850583217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17249225003772222406220981 1617114844103645850583217)
              ·
                refine ⟨1212836133077734387937413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617114844103645850583217 1212836133077734387937413)
                ·
                  refine ⟨227406774952075197738265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212836133077734387937413 227406774952075197738265)
                  ·
                    rfl

theorem cell22_1992929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_1992929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992929 prefixEnd_1992929 := by exact prefixLift 1992929
  have htrace : WordTrace (prefixWord ++ tailWord_1992929) baseStart_1992929 baseEnd_1992929 := by
    simpa [prefixWord, tailWord_1992929, baseEnd_1992929] using wordTrace_append hprefix tailTrace_1992929
  have hstable : (prefixWord ++ tailWord_1992929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992929).length < 2 ^ (prefixWord ++ tailWord_1992929).sum := by decide
  have hdescent : baseEnd_1992929 < baseStart_1992929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992940 : List Nat := [2, 2, 1, 1, 2, 3, 4, 7]
def baseStart_1992940 : Nat := 118140960795 + 1992940 * 2 ^ 59
def prefixEnd_1992940 : Nat := 4983230072969 + 3 ^ 40 * 1992940 * 2
def baseEnd_1992940 : Nat := 75802676709002803465529

theorem tailTrace_1992940 : CollatzResearch.WordTrace tailWord_1992940 prefixEnd_1992940 75802676709002803465529 := by
  unfold tailWord_1992940
  simp only [CollatzResearch.WordTrace]
  refine ⟨36344246699963110949552137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48458995599950814599402849 36344246699963110949552137)
  ·
    refine ⟨27258185024972333212164103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36344246699963110949552137 27258185024972333212164103)
    ·
      refine ⟨40887277537458499818246155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27258185024972333212164103 40887277537458499818246155)
      ·
        refine ⟨61330916306187749727369233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40887277537458499818246155 61330916306187749727369233)
        ·
          refine ⟨45998187229640812295526925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61330916306187749727369233 45998187229640812295526925)
          ·
            refine ⟨17249320211115304610822597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45998187229640812295526925 17249320211115304610822597)
            ·
              refine ⟨3234247539584119614529237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17249320211115304610822597 3234247539584119614529237)
              ·
                refine ⟨75802676709002803465529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3234247539584119614529237 75802676709002803465529)
                ·
                  rfl

theorem cell22_1992940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 7].length) (baseStart_1992940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1992940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1992940 prefixEnd_1992940 := by exact prefixLift 1992940
  have htrace : WordTrace (prefixWord ++ tailWord_1992940) baseStart_1992940 baseEnd_1992940 := by
    simpa [prefixWord, tailWord_1992940, baseEnd_1992940] using wordTrace_append hprefix tailTrace_1992940
  have hstable : (prefixWord ++ tailWord_1992940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992940).length < 2 ^ (prefixWord ++ tailWord_1992940).sum := by decide
  have hdescent : baseEnd_1992940 < baseStart_1992940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993047 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 6]
def baseStart_1993047 : Nat := 118140960795 + 1993047 * 2 ^ 59
def prefixEnd_1993047 : Nat := 4983230072969 + 3 ^ 40 * 1993047 * 2
def baseEnd_1993047 : Nat := 227420239555904206254811

theorem tailTrace_1993047 : CollatzResearch.WordTrace tailWord_1993047 prefixEnd_1993047 227420239555904206254811 := by
  unfold tailWord_1993047
  simp only [CollatzResearch.WordTrace]
  refine ⟨72692396010538579173249395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48461597340359052782166263 72692396010538579173249395)
  ·
    refine ⟨109038594015807868759874093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72692396010538579173249395 109038594015807868759874093)
    ·
      refine ⟨40889472755927950784952785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109038594015807868759874093 40889472755927950784952785)
      ·
        refine ⟨30667104566945963088714589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40889472755927950784952785 30667104566945963088714589)
        ·
          refine ⟨11500164212604736158267971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30667104566945963088714589 11500164212604736158267971)
          ·
            refine ⟨17250246318907104237401957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11500164212604736158267971 17250246318907104237401957)
            ·
              refine ⟨3234421184795082044512867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17250246318907104237401957 3234421184795082044512867)
              ·
                refine ⟨4851631777192623066769301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234421184795082044512867 4851631777192623066769301)
                ·
                  refine ⟨227420239555904206254811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4851631777192623066769301 227420239555904206254811)
                  ·
                    rfl

theorem cell22_1993047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 6].length) (baseStart_1993047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993047 prefixEnd_1993047 := by exact prefixLift 1993047
  have htrace : WordTrace (prefixWord ++ tailWord_1993047) baseStart_1993047 baseEnd_1993047 := by
    simpa [prefixWord, tailWord_1993047, baseEnd_1993047] using wordTrace_append hprefix tailTrace_1993047
  have hstable : (prefixWord ++ tailWord_1993047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993047).length < 2 ^ (prefixWord ++ tailWord_1993047).sum := by decide
  have hdescent : baseEnd_1993047 < baseStart_1993047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993066 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1993066 : Nat := 118140960795 + 1993066 * 2 ^ 59
def prefixEnd_1993066 : Nat := 4983230072969 + 3 ^ 40 * 1993066 * 2
def baseEnd_1993066 : Nat := 682267222756002902539375

theorem tailTrace_1993066 : CollatzResearch.WordTrace tailWord_1993066 prefixEnd_1993066 682267222756002902539375 := by
  unfold tailWord_1993066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18173272249367436354547763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48462059331646496945460701 18173272249367436354547763)
  ·
    refine ⟨27259908374051154531821645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18173272249367436354547763 27259908374051154531821645)
    ·
      refine ⟨10222465640269182949433117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27259908374051154531821645 10222465640269182949433117)
      ·
        refine ⟨3833424615100943606037419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10222465640269182949433117 3833424615100943606037419)
        ·
          refine ⟨5750136922651415409056129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833424615100943606037419 5750136922651415409056129)
          ·
            refine ⟨4312602691988561556792097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5750136922651415409056129 4312602691988561556792097)
            ·
              refine ⟨3234452018991421167594073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312602691988561556792097 3234452018991421167594073)
              ·
                refine ⟨2425839014243565875695555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234452018991421167594073 2425839014243565875695555)
                ·
                  refine ⟨3638758521365348813543333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425839014243565875695555 3638758521365348813543333)
                  ·
                    refine ⟨682267222756002902539375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638758521365348813543333 682267222756002902539375)
                    ·
                      rfl

theorem cell22_1993066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1993066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993066 prefixEnd_1993066 := by exact prefixLift 1993066
  have htrace : WordTrace (prefixWord ++ tailWord_1993066) baseStart_1993066 baseEnd_1993066 := by
    simpa [prefixWord, tailWord_1993066, baseEnd_1993066] using wordTrace_append hprefix tailTrace_1993066
  have hstable : (prefixWord ++ tailWord_1993066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993066).length < 2 ^ (prefixWord ++ tailWord_1993066).sum := by decide
  have hdescent : baseEnd_1993066 < baseStart_1993066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993075 : List Nat := [1, 1, 1, 2, 2, 1, 2, 12]
def baseStart_1993075 : Nat := 118140960795 + 1993075 * 2 ^ 59
def prefixEnd_1993075 : Nat := 4983230072969 + 3 ^ 40 * 1993075 * 2
def baseEnd_1993075 : Nat := 75807811515547764340483

theorem tailTrace_1993075 : CollatzResearch.WordTrace tailWord_1993075 prefixEnd_1993075 75807811515547764340483 := by
  unfold tailWord_1993075
  simp only [CollatzResearch.WordTrace]
  refine ⟨72693417254437139955268679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48462278169624759970179119 72693417254437139955268679)
  ·
    refine ⟨109040125881655709932903019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72693417254437139955268679 109040125881655709932903019)
    ·
      refine ⟨163560188822483564899354529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109040125881655709932903019 163560188822483564899354529)
      ·
        refine ⟨122670141616862673674515897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163560188822483564899354529 122670141616862673674515897)
        ·
          refine ⟨92002606212647005255886923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122670141616862673674515897 92002606212647005255886923)
          ·
            refine ⟨138003909318970507883830385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92002606212647005255886923 138003909318970507883830385)
            ·
              refine ⟨103502931989227880912872789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138003909318970507883830385 103502931989227880912872789)
              ·
                refine ⟨75807811515547764340483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 103502931989227880912872789 75807811515547764340483)
                ·
                  rfl

theorem cell22_1993075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 12].length) (baseStart_1993075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993075 prefixEnd_1993075 := by exact prefixLift 1993075
  have htrace : WordTrace (prefixWord ++ tailWord_1993075) baseStart_1993075 baseEnd_1993075 := by
    simpa [prefixWord, tailWord_1993075, baseEnd_1993075] using wordTrace_append hprefix tailTrace_1993075
  have hstable : (prefixWord ++ tailWord_1993075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993075).length < 2 ^ (prefixWord ++ tailWord_1993075).sum := by decide
  have hdescent : baseEnd_1993075 < baseStart_1993075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993098 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_1993098 : Nat := 118140960795 + 1993098 * 2 ^ 59
def prefixEnd_1993098 : Nat := 4983230072969 + 3 ^ 40 * 1993098 * 2
def baseEnd_1993098 : Nat := 227426059003321828579759

theorem tailTrace_1993098 : CollatzResearch.WordTrace tailWord_1993098 prefixEnd_1993098 227426059003321828579759 := by
  unfold tailWord_1993098
  simp only [CollatzResearch.WordTrace]
  refine ⟨18173564033338453720838987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48462837422235876588903965 18173564033338453720838987)
  ·
    refine ⟨27260346050007680581258481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18173564033338453720838987 27260346050007680581258481)
    ·
      refine ⟨20445259537505760435943861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27260346050007680581258481 20445259537505760435943861)
      ·
        refine ⟨1916743081641165040869737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20445259537505760435943861 1916743081641165040869737)
        ·
          refine ⟨1437557311230873780652303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916743081641165040869737 1437557311230873780652303)
          ·
            refine ⟨2156335966846310670978455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437557311230873780652303 2156335966846310670978455)
            ·
              refine ⟨3234503950269466006467683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156335966846310670978455 3234503950269466006467683)
              ·
                refine ⟨4851755925404199009701525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234503950269466006467683 4851755925404199009701525)
                ·
                  refine ⟨227426059003321828579759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4851755925404199009701525 227426059003321828579759)
                  ·
                    rfl

theorem cell22_1993098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_1993098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993098 prefixEnd_1993098 := by exact prefixLift 1993098
  have htrace : WordTrace (prefixWord ++ tailWord_1993098) baseStart_1993098 baseEnd_1993098 := by
    simpa [prefixWord, tailWord_1993098, baseEnd_1993098] using wordTrace_append hprefix tailTrace_1993098
  have hstable : (prefixWord ++ tailWord_1993098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993098).length < 2 ^ (prefixWord ++ tailWord_1993098).sum := by decide
  have hdescent : baseEnd_1993098 < baseStart_1993098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993124 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1993124 : Nat := 118140960795 + 1993124 * 2 ^ 59
def prefixEnd_1993124 : Nat := 4983230072969 + 3 ^ 40 * 1993124 * 2
def baseEnd_1993124 : Nat := 682287077341310084589197

theorem tailTrace_1993124 : CollatzResearch.WordTrace tailWord_1993124 prefixEnd_1993124 682287077341310084589197 := by
  unfold tailWord_1993124
  simp only [CollatzResearch.WordTrace]
  refine ⟨36347602215629810661901213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48463469620839747549201617 36347602215629810661901213)
  ·
    refine ⟨13630350830861178998212955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36347602215629810661901213 13630350830861178998212955)
    ·
      refine ⟨20445526246291768497319433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13630350830861178998212955 20445526246291768497319433)
      ·
        refine ⟨15334144684718826372989575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20445526246291768497319433 15334144684718826372989575)
        ·
          refine ⟨23001217027078239559484363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15334144684718826372989575 23001217027078239559484363)
          ·
            refine ⟨34501825540617359339226545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23001217027078239559484363 34501825540617359339226545)
            ·
              refine ⟨25876369155463019504419909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34501825540617359339226545 25876369155463019504419909)
              ·
                refine ⟨4851819216649316157078733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25876369155463019504419909 4851819216649316157078733)
                ·
                  refine ⟨1819432206243493558904525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4851819216649316157078733 1819432206243493558904525)
                  ·
                    refine ⟨682287077341310084589197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819432206243493558904525 682287077341310084589197)
                    ·
                      rfl

theorem cell22_1993124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1993124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993124 prefixEnd_1993124 := by exact prefixLift 1993124
  have htrace : WordTrace (prefixWord ++ tailWord_1993124) baseStart_1993124 baseEnd_1993124 := by
    simpa [prefixWord, tailWord_1993124, baseEnd_1993124] using wordTrace_append hprefix tailTrace_1993124
  have hstable : (prefixWord ++ tailWord_1993124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993124).length < 2 ^ (prefixWord ++ tailWord_1993124).sum := by decide
  have hdescent : baseEnd_1993124 < baseStart_1993124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993152 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_1993152 : Nat := 118140960795 + 1993152 * 2 ^ 59
def prefixEnd_1993152 : Nat := 4983230072969 + 3 ^ 40 * 1993152 * 2
def baseEnd_1993152 : Nat := 682296662313527344889111

theorem tailTrace_1993152 : CollatzResearch.WordTrace tailWord_1993152 prefixEnd_1993152 682296662313527344889111 := by
  unfold tailWord_1993152
  simp only [CollatzResearch.WordTrace]
  refine ⟨36348112837579091052910855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48464150450105454737214473 36348112837579091052910855)
  ·
    refine ⟨54522169256368636579366283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36348112837579091052910855 54522169256368636579366283)
    ·
      refine ⟨81783253884552954869049425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54522169256368636579366283 81783253884552954869049425)
      ·
        refine ⟨61337440413414716151787069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81783253884552954869049425 61337440413414716151787069)
        ·
          refine ⟨23001540155030518556920151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61337440413414716151787069 23001540155030518556920151)
          ·
            refine ⟨34502310232545777835380227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23001540155030518556920151 34502310232545777835380227)
            ·
              refine ⟨51753465348818666753070341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34502310232545777835380227 51753465348818666753070341)
              ·
                refine ⟨9703774752903500016200689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51753465348818666753070341 9703774752903500016200689)
                ·
                  refine ⟨7277831064677625012150517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9703774752903500016200689 7277831064677625012150517)
                  ·
                    refine ⟨682296662313527344889111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7277831064677625012150517 682296662313527344889111)
                    ·
                      rfl

theorem cell22_1993152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_1993152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993152 prefixEnd_1993152 := by exact prefixLift 1993152
  have htrace : WordTrace (prefixWord ++ tailWord_1993152) baseStart_1993152 baseEnd_1993152 := by
    simpa [prefixWord, tailWord_1993152, baseEnd_1993152] using wordTrace_append hprefix tailTrace_1993152
  have hstable : (prefixWord ++ tailWord_1993152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993152).length < 2 ^ (prefixWord ++ tailWord_1993152).sum := by decide
  have hdescent : baseEnd_1993152 < baseStart_1993152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993184 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_1993184 : Nat := 118140960795 + 1993184 * 2 ^ 59
def prefixEnd_1993184 : Nat := 4983230072969 + 3 ^ 40 * 1993184 * 2
def baseEnd_1993184 : Nat := 682307616567489928089013

theorem tailTrace_1993184 : CollatzResearch.WordTrace tailWord_1993184 prefixEnd_1993184 682307616567489928089013 := by
  unfold tailWord_1993184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36348696405521125785493303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48464928540694834380657737 36348696405521125785493303)
  ·
    refine ⟨54523044608281688678239955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36348696405521125785493303 54523044608281688678239955)
    ·
      refine ⟨81784566912422533017359933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54523044608281688678239955 81784566912422533017359933)
      ·
        refine ⟨30669212592158449881509975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81784566912422533017359933 30669212592158449881509975)
        ·
          refine ⟨46003818888237674822264963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30669212592158449881509975 46003818888237674822264963)
          ·
            refine ⟨69005728332356512233397445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46003818888237674822264963 69005728332356512233397445)
            ·
              refine ⟨12938574062316846043762021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69005728332356512233397445 12938574062316846043762021)
              ·
                refine ⟨2425982636684408633205379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12938574062316846043762021 2425982636684408633205379)
                ·
                  refine ⟨3638973955026612949808069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425982636684408633205379 3638973955026612949808069)
                  ·
                    refine ⟨682307616567489928089013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638973955026612949808069 682307616567489928089013)
                    ·
                      rfl

theorem cell22_1993184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_1993184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993184 prefixEnd_1993184 := by exact prefixLift 1993184
  have htrace : WordTrace (prefixWord ++ tailWord_1993184) baseStart_1993184 baseEnd_1993184 := by
    simpa [prefixWord, tailWord_1993184, baseEnd_1993184] using wordTrace_append hprefix tailTrace_1993184
  have hstable : (prefixWord ++ tailWord_1993184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993184).length < 2 ^ (prefixWord ++ tailWord_1993184).sum := by decide
  have hdescent : baseEnd_1993184 < baseStart_1993184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993205 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 5]
def baseStart_1993205 : Nat := 118140960795 + 1993205 * 2 ^ 59
def prefixEnd_1993205 : Nat := 4983230072969 + 3 ^ 40 * 1993205 * 2
def baseEnd_1993205 : Nat := 227438268432217624437983

theorem tailTrace_1993205 : CollatzResearch.WordTrace tailWord_1993205 prefixEnd_1993205 227438268432217624437983 := by
  unfold tailWord_1993205
  simp only [CollatzResearch.WordTrace]
  refine ⟨72698158743966172157501069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48465439162644114771667379 72698158743966172157501069)
  ·
    refine ⟨27261809528987314559062901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72698158743966172157501069 27261809528987314559062901)
    ·
      refine ⟨2555794643342560739912147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27261809528987314559062901 2555794643342560739912147)
      ·
        refine ⟨3833691965013841109868221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555794643342560739912147 3833691965013841109868221)
        ·
          refine ⟨1437634486880190416200583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3833691965013841109868221 1437634486880190416200583)
          ·
            refine ⟨2156451730320285624300875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437634486880190416200583 2156451730320285624300875)
            ·
              refine ⟨3234677595480428436451313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156451730320285624300875 3234677595480428436451313)
              ·
                refine ⟨2426008196610321327338485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234677595480428436451313 2426008196610321327338485)
                ·
                  refine ⟨227438268432217624437983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2426008196610321327338485 227438268432217624437983)
                  ·
                    rfl

theorem cell22_1993205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_1993205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993205 prefixEnd_1993205 := by exact prefixLift 1993205
  have htrace : WordTrace (prefixWord ++ tailWord_1993205) baseStart_1993205 baseEnd_1993205 := by
    simpa [prefixWord, tailWord_1993205, baseEnd_1993205] using wordTrace_append hprefix tailTrace_1993205
  have hstable : (prefixWord ++ tailWord_1993205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993205).length < 2 ^ (prefixWord ++ tailWord_1993205).sum := by decide
  have hdescent : baseEnd_1993205 < baseStart_1993205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993222 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1993222 : Nat := 118140960795 + 1993222 * 2 ^ 59
def prefixEnd_1993222 : Nat := 4983230072969 + 3 ^ 40 * 1993222 * 2
def baseEnd_1993222 : Nat := 227440208248023498546299

theorem tailTrace_1993222 : CollatzResearch.WordTrace tailWord_1993222 prefixEnd_1993222 227440208248023498546299 := by
  unfold tailWord_1993222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271836837028268251902185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48465852523269722707246613 2271836837028268251902185)
  ·
    refine ⟨1703877627771201188926639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2271836837028268251902185 1703877627771201188926639)
    ·
      refine ⟨2555816441656801783389959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1703877627771201188926639 2555816441656801783389959)
      ·
        refine ⟨3833724662485202675084939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555816441656801783389959 3833724662485202675084939)
        ·
          refine ⟨5750586993727804012627409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833724662485202675084939 5750586993727804012627409)
          ·
            refine ⟨4312940245295853009470557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5750586993727804012627409 4312940245295853009470557)
            ·
              refine ⟨1617352591985944878551459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4312940245295853009470557 1617352591985944878551459)
              ·
                refine ⟨2426028887978917317827189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617352591985944878551459 2426028887978917317827189)
                ·
                  refine ⟨227440208248023498546299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2426028887978917317827189 227440208248023498546299)
                  ·
                    rfl

theorem cell22_1993222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1993222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993222 prefixEnd_1993222 := by exact prefixLift 1993222
  have htrace : WordTrace (prefixWord ++ tailWord_1993222) baseStart_1993222 baseEnd_1993222 := by
    simpa [prefixWord, tailWord_1993222, baseEnd_1993222] using wordTrace_append hprefix tailTrace_1993222
  have hstable : (prefixWord ++ tailWord_1993222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993222).length < 2 ^ (prefixWord ++ tailWord_1993222).sum := by decide
  have hdescent : baseEnd_1993222 < baseStart_1993222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993244 : List Nat := [2, 2, 3, 1, 2, 3, 1, 8]
def baseStart_1993244 : Nat := 118140960795 + 1993244 * 2 ^ 59
def prefixEnd_1993244 : Nat := 4983230072969 + 3 ^ 40 * 1993244 * 2
def baseEnd_1993244 : Nat := 75814239532629974620981

theorem tailTrace_1993244 : CollatzResearch.WordTrace tailWord_1993244 prefixEnd_1993244 75814239532629974620981 := by
  unfold tailWord_1993244
  simp only [CollatzResearch.WordTrace]
  refine ⟨36349790595412440909085393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48466387460549921212113857 36349790595412440909085393)
  ·
    refine ⟨27262342946559330681814045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36349790595412440909085393 27262342946559330681814045)
    ·
      refine ⟨10223378604959749005680267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27262342946559330681814045 10223378604959749005680267)
      ·
        refine ⟨15335067907439623508520401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10223378604959749005680267 15335067907439623508520401)
        ·
          refine ⟨11501300930579717631390301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15335067907439623508520401 11501300930579717631390301)
          ·
            refine ⟨4312987848967394111771363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11501300930579717631390301 4312987848967394111771363)
            ·
              refine ⟨6469481773451091167657045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312987848967394111771363 6469481773451091167657045)
              ·
                refine ⟨75814239532629974620981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6469481773451091167657045 75814239532629974620981)
                ·
                  rfl

theorem cell22_1993244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 8].length) (baseStart_1993244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993244 prefixEnd_1993244 := by exact prefixLift 1993244
  have htrace : WordTrace (prefixWord ++ tailWord_1993244) baseStart_1993244 baseEnd_1993244 := by
    simpa [prefixWord, tailWord_1993244, baseEnd_1993244] using wordTrace_append hprefix tailTrace_1993244
  have hstable : (prefixWord ++ tailWord_1993244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993244).length < 2 ^ (prefixWord ++ tailWord_1993244).sum := by decide
  have hdescent : baseEnd_1993244 < baseStart_1993244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993259 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 5, 3]
def baseStart_1993259 : Nat := 118140960795 + 1993259 * 2 ^ 59
def prefixEnd_1993259 : Nat := 4983230072969 + 3 ^ 40 * 1993259 * 2
def baseEnd_1993259 : Nat := 682333290600214732463783

theorem tailTrace_1993259 : CollatzResearch.WordTrace tailWord_1993259 prefixEnd_1993259 682333290600214732463783 := by
  unfold tailWord_1993259
  simp only [CollatzResearch.WordTrace]
  refine ⟨72700128285770539379966831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48466752190513692919977887 72700128285770539379966831)
  ·
    refine ⟨109050192428655809069950247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72700128285770539379966831 109050192428655809069950247)
    ·
      refine ⟨163575288642983713604925371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109050192428655809069950247 163575288642983713604925371)
      ·
        refine ⟨245362932964475570407388057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163575288642983713604925371 245362932964475570407388057)
        ·
          refine ⟨184022199723356677805541043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245362932964475570407388057 184022199723356677805541043)
          ·
            refine ⟨276033299585035016708311565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184022199723356677805541043 276033299585035016708311565)
            ·
              refine ⟨103512487344388131265616837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276033299585035016708311565 103512487344388131265616837)
              ·
                refine ⟨19408591377072774612303157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103512487344388131265616837 19408591377072774612303157)
                ·
                  refine ⟨1819555441600572619903421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19408591377072774612303157 1819555441600572619903421)
                  ·
                    refine ⟨682333290600214732463783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819555441600572619903421 682333290600214732463783)
                    ·
                      rfl

theorem cell22_1993259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 3].length) (baseStart_1993259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993259 prefixEnd_1993259 := by exact prefixLift 1993259
  have htrace : WordTrace (prefixWord ++ tailWord_1993259) baseStart_1993259 baseEnd_1993259 := by
    simpa [prefixWord, tailWord_1993259, baseEnd_1993259] using wordTrace_append hprefix tailTrace_1993259
  have hstable : (prefixWord ++ tailWord_1993259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993259).length < 2 ^ (prefixWord ++ tailWord_1993259).sum := by decide
  have hdescent : baseEnd_1993259 < baseStart_1993259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993278 : List Nat := [4, 2, 1, 4, 1, 1, 2, 7]
def baseStart_1993278 : Nat := 118140960795 + 1993278 * 2 ^ 59
def prefixEnd_1993278 : Nat := 4983230072969 + 3 ^ 40 * 1993278 * 2
def baseEnd_1993278 : Nat := 75815532743167224026525

theorem tailTrace_1993278 : CollatzResearch.WordTrace tailWord_1993278 prefixEnd_1993278 75815532743167224026525 := by
  unfold tailWord_1993278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087602659087713203113561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48467214181801137083272325 9087602659087713203113561)
  ·
    refine ⟨6815701994315784902335171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9087602659087713203113561 6815701994315784902335171)
    ·
      refine ⟨10223552991473677353502757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6815701994315784902335171 10223552991473677353502757)
      ·
        refine ⟨1916916185901314503781767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10223552991473677353502757 1916916185901314503781767)
        ·
          refine ⟨2875374278851971755672651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916916185901314503781767 2875374278851971755672651)
          ·
            refine ⟨4313061418277957633508977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875374278851971755672651 4313061418277957633508977)
            ·
              refine ⟨3234796063708468225131733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4313061418277957633508977 3234796063708468225131733)
              ·
                refine ⟨75815532743167224026525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3234796063708468225131733 75815532743167224026525)
                ·
                  rfl

theorem cell22_1993278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_1993278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993278 prefixEnd_1993278 := by exact prefixLift 1993278
  have htrace : WordTrace (prefixWord ++ tailWord_1993278) baseStart_1993278 baseEnd_1993278 := by
    simpa [prefixWord, tailWord_1993278, baseEnd_1993278] using wordTrace_append hprefix tailTrace_1993278
  have hstable : (prefixWord ++ tailWord_1993278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993278).length < 2 ^ (prefixWord ++ tailWord_1993278).sum := by decide
  have hdescent : baseEnd_1993278 < baseStart_1993278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993368 : List Nat := [2, 1, 2, 4, 1, 1, 4, 3, 4]
def baseStart_1993368 : Nat := 118140960795 + 1993368 * 2 ^ 59
def prefixEnd_1993368 : Nat := 4983230072969 + 3 ^ 40 * 1993368 * 2
def baseEnd_1993368 : Nat := 227456867842591593829483

theorem tailTrace_1993368 : CollatzResearch.WordTrace tailWord_1993368 prefixEnd_1993368 227456867842591593829483 := by
  unfold tailWord_1993368
  simp only [CollatzResearch.WordTrace]
  refine ⟨36352051921187825497842379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48469402561583767330456505 36352051921187825497842379)
  ·
    refine ⟨54528077881781738246763569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36352051921187825497842379 54528077881781738246763569)
    ·
      refine ⟨40896058411336303685072677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54528077881781738246763569 40896058411336303685072677)
      ·
        refine ⟨7668010952125556940951127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40896058411336303685072677 7668010952125556940951127)
        ·
          refine ⟨11502016428188335411426691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668010952125556940951127 11502016428188335411426691)
          ·
            refine ⟨17253024642282503117140037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11502016428188335411426691 17253024642282503117140037)
            ·
              refine ⟨3234942120427969334463757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17253024642282503117140037 3234942120427969334463757)
              ·
                refine ⟨1213103295160488500423909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3234942120427969334463757 1213103295160488500423909)
                ·
                  refine ⟨227456867842591593829483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213103295160488500423909 227456867842591593829483)
                  ·
                    rfl

theorem cell22_1993368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_1993368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993368 prefixEnd_1993368 := by exact prefixLift 1993368
  have htrace : WordTrace (prefixWord ++ tailWord_1993368) baseStart_1993368 baseEnd_1993368 := by
    simpa [prefixWord, tailWord_1993368, baseEnd_1993368] using wordTrace_append hprefix tailTrace_1993368
  have hstable : (prefixWord ++ tailWord_1993368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993368).length < 2 ^ (prefixWord ++ tailWord_1993368).sum := by decide
  have hdescent : baseEnd_1993368 < baseStart_1993368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993370 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_1993370 : Nat := 118140960795 + 1993370 * 2 ^ 59
def prefixEnd_1993370 : Nat := 4983230072969 + 3 ^ 40 * 1993370 * 2
def baseEnd_1993370 : Nat := 682371288168647442938443

theorem tailTrace_1993370 : CollatzResearch.WordTrace tailWord_1993370 prefixEnd_1993370 682371288168647442938443 := by
  unfold tailWord_1993370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176044197092101334314391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48469451192245603558171709 18176044197092101334314391)
  ·
    refine ⟨27264066295638152001471587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18176044197092101334314391 27264066295638152001471587)
    ·
      refine ⟨40896099443457228002207381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27264066295638152001471587 40896099443457228002207381)
      ·
        refine ⟨1917004661412057562603471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40896099443457228002207381 1917004661412057562603471)
        ·
          refine ⟨2875506992118086343905207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917004661412057562603471 2875506992118086343905207)
          ·
            refine ⟨4313260488177129515857811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875506992118086343905207 4313260488177129515857811)
            ·
              refine ⟨6469890732265694273786717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313260488177129515857811 6469890732265694273786717)
              ·
                refine ⟨2426209024599635352670019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6469890732265694273786717 2426209024599635352670019)
                ·
                  refine ⟨3639313536899453029005029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426209024599635352670019 3639313536899453029005029)
                  ·
                    refine ⟨682371288168647442938443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3639313536899453029005029 682371288168647442938443)
                    ·
                      rfl

theorem cell22_1993370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_1993370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993370 prefixEnd_1993370 := by exact prefixLift 1993370
  have htrace : WordTrace (prefixWord ++ tailWord_1993370) baseStart_1993370 baseEnd_1993370 := by
    simpa [prefixWord, tailWord_1993370, baseEnd_1993370] using wordTrace_append hprefix tailTrace_1993370
  have hstable : (prefixWord ++ tailWord_1993370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993370).length < 2 ^ (prefixWord ++ tailWord_1993370).sum := by decide
  have hdescent : baseEnd_1993370 < baseStart_1993370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993441 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 7]
def baseStart_1993441 : Nat := 118140960795 + 1993441 * 2 ^ 59
def prefixEnd_1993441 : Nat := 4983230072969 + 3 ^ 40 * 1993441 * 2
def baseEnd_1993441 : Nat := 227465197639875641471075

theorem tailTrace_1993441 : CollatzResearch.WordTrace tailWord_1993441 prefixEnd_1993441 227465197639875641471075 := by
  unfold tailWord_1993441
  simp only [CollatzResearch.WordTrace]
  refine ⟨72706766371111184463092177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48471177580740789642061451 72706766371111184463092177)
  ·
    refine ⟨54530074778333388347319133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72706766371111184463092177 54530074778333388347319133)
    ·
      refine ⟨20448778041875020630244675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54530074778333388347319133 20448778041875020630244675)
      ·
        refine ⟨30673167062812530945367013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20448778041875020630244675 30673167062812530945367013)
        ·
          refine ⟨5751218824277349552256315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30673167062812530945367013 5751218824277349552256315)
          ·
            refine ⟨8626828236416024328384473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751218824277349552256315 8626828236416024328384473)
            ·
              refine ⟨6470121177312018246288355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8626828236416024328384473 6470121177312018246288355)
              ·
                refine ⟨9705181765968027369432533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6470121177312018246288355 9705181765968027369432533)
                ·
                  refine ⟨227465197639875641471075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9705181765968027369432533 227465197639875641471075)
                  ·
                    rfl

theorem cell22_1993441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_1993441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993441 prefixEnd_1993441 := by exact prefixLift 1993441
  have htrace : WordTrace (prefixWord ++ tailWord_1993441) baseStart_1993441 baseEnd_1993441 := by
    simpa [prefixWord, tailWord_1993441, baseEnd_1993441] using wordTrace_append hprefix tailTrace_1993441
  have hstable : (prefixWord ++ tailWord_1993441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993441).length < 2 ^ (prefixWord ++ tailWord_1993441).sum := by decide
  have hdescent : baseEnd_1993441 < baseStart_1993441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993445 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_1993445 : Nat := 118140960795 + 1993445 * 2 ^ 59
def prefixEnd_1993445 : Nat := 4983230072969 + 3 ^ 40 * 1993445 * 2
def baseEnd_1993445 : Nat := 682396962201372247313213

theorem tailTrace_1993445 : CollatzResearch.WordTrace tailWord_1993445 prefixEnd_1993445 682396962201372247313213 := by
  unfold tailWord_1993445
  simp only [CollatzResearch.WordTrace]
  refine ⟨72706912263096693146237789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48471274842064462097491859 72706912263096693146237789)
  ·
    refine ⟨27265092098661259929839171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72706912263096693146237789 27265092098661259929839171)
    ·
      refine ⟨40897638147991889894758757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27265092098661259929839171 40897638147991889894758757)
      ·
        refine ⟨7668307152748479355267267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40897638147991889894758757 7668307152748479355267267)
        ·
          refine ⟨11502460729122719032900901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668307152748479355267267 11502460729122719032900901)
          ·
            refine ⟨2156711386710509818668919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11502460729122719032900901 2156711386710509818668919)
            ·
              refine ⟨3235067080065764728003379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156711386710509818668919 3235067080065764728003379)
              ·
                refine ⟨4852600620098647092005069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235067080065764728003379 4852600620098647092005069)
                ·
                  refine ⟨1819725232536992659501901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4852600620098647092005069 1819725232536992659501901)
                  ·
                    refine ⟨682396962201372247313213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819725232536992659501901 682396962201372247313213)
                    ·
                      rfl

theorem cell22_1993445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_1993445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993445 prefixEnd_1993445 := by exact prefixLift 1993445
  have htrace : WordTrace (prefixWord ++ tailWord_1993445) baseStart_1993445 baseEnd_1993445 := by
    simpa [prefixWord, tailWord_1993445, baseEnd_1993445] using wordTrace_append hprefix tailTrace_1993445
  have hstable : (prefixWord ++ tailWord_1993445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993445).length < 2 ^ (prefixWord ++ tailWord_1993445).sum := by decide
  have hdescent : baseEnd_1993445 < baseStart_1993445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993458 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1993458 : Nat := 118140960795 + 1993458 * 2 ^ 59
def prefixEnd_1993458 : Nat := 4983230072969 + 3 ^ 40 * 1993458 * 2
def baseEnd_1993458 : Nat := 227467137455681515579391

theorem tailTrace_1993458 : CollatzResearch.WordTrace tailWord_1993458 prefixEnd_1993458 227467137455681515579391 := by
  unfold tailWord_1993458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176846603012399091615257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48471590941366397577640685 18176846603012399091615257)
  ·
    refine ⟨13632634952259299318711443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18176846603012399091615257 13632634952259299318711443)
    ·
      refine ⟨20448952428388948978067165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13632634952259299318711443 20448952428388948978067165)
      ·
        refine ⟨7668357160645855866775187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20448952428388948978067165 7668357160645855866775187)
        ·
          refine ⟨11502535740968783800162781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668357160645855866775187 11502535740968783800162781)
          ·
            refine ⟨4313450902863293925061043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11502535740968783800162781 4313450902863293925061043)
            ·
              refine ⟨6470176354294940887591565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313450902863293925061043 6470176354294940887591565)
              ·
                refine ⟨2426316132860602832846837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6470176354294940887591565 2426316132860602832846837)
                ·
                  refine ⟨227467137455681515579391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2426316132860602832846837 227467137455681515579391)
                  ·
                    rfl

theorem cell22_1993458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1993458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993458 prefixEnd_1993458 := by exact prefixLift 1993458
  have htrace : WordTrace (prefixWord ++ tailWord_1993458) baseStart_1993458 baseEnd_1993458 := by
    simpa [prefixWord, tailWord_1993458, baseEnd_1993458] using wordTrace_append hprefix tailTrace_1993458
  have hstable : (prefixWord ++ tailWord_1993458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993458).length < 2 ^ (prefixWord ++ tailWord_1993458).sum := by decide
  have hdescent : baseEnd_1993458 < baseStart_1993458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993516 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_1993516 : Nat := 118140960795 + 1993516 * 2 ^ 59
def prefixEnd_1993516 : Nat := 4983230072969 + 3 ^ 40 * 1993516 * 2
def baseEnd_1993516 : Nat := 682421266952351728787995

theorem tailTrace_1993516 : CollatzResearch.WordTrace tailWord_1993516 prefixEnd_1993516 682421266952351728787995 := by
  unfold tailWord_1993516
  simp only [CollatzResearch.WordTrace]
  refine ⟨36354750922919736136036201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48473001230559648181381601 36354750922919736136036201)
  ·
    refine ⟨27266063192189802102027151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36354750922919736136036201 27266063192189802102027151)
    ·
      refine ⟨40899094788284703153040727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27266063192189802102027151 40899094788284703153040727)
      ·
        refine ⟨61348642182427054729561091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40899094788284703153040727 61348642182427054729561091)
        ·
          refine ⟨92022963273640582094341637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61348642182427054729561091 92022963273640582094341637)
          ·
            refine ⟨17254305613807609142689057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92022963273640582094341637 17254305613807609142689057)
            ·
              refine ⟨12940729210355706857016793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17254305613807609142689057 12940729210355706857016793)
              ·
                refine ⟨9705546907766780142762595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12940729210355706857016793 9705546907766780142762595)
                ·
                  refine ⟨14558320361650170214143893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705546907766780142762595 14558320361650170214143893)
                  ·
                    refine ⟨682421266952351728787995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14558320361650170214143893 682421266952351728787995)
                    ·
                      rfl

theorem cell22_1993516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_1993516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993516 prefixEnd_1993516 := by exact prefixLift 1993516
  have htrace : WordTrace (prefixWord ++ tailWord_1993516) baseStart_1993516 baseEnd_1993516 := by
    simpa [prefixWord, tailWord_1993516, baseEnd_1993516] using wordTrace_append hprefix tailTrace_1993516
  have hstable : (prefixWord ++ tailWord_1993516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993516).length < 2 ^ (prefixWord ++ tailWord_1993516).sum := by decide
  have hdescent : baseEnd_1993516 < baseStart_1993516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993582 : List Nat := [4, 1, 2, 3, 2, 2, 2, 6]
def baseStart_1993582 : Nat := 118140960795 + 1993582 * 2 ^ 59
def prefixEnd_1993582 : Nat := 4983230072969 + 3 ^ 40 * 1993582 * 2
def baseEnd_1993582 : Nat := 75827095566794395181977

theorem tailTrace_1993582 : CollatzResearch.WordTrace tailWord_1993582 prefixEnd_1993582 75827095566794395181977 := by
  unfold tailWord_1993582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9088988632950045692996875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48474606042400243695983333 9088988632950045692996875)
  ·
    refine ⟨13633482949425068539495313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9088988632950045692996875 13633482949425068539495313)
    ·
      refine ⟨10225112212068801404621485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13633482949425068539495313 10225112212068801404621485)
      ·
        refine ⟨3834417079525800526733057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10225112212068801404621485 3834417079525800526733057)
        ·
          refine ⟨2875812809644350395049793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3834417079525800526733057 2875812809644350395049793)
          ·
            refine ⟨2156859607233262796287345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2875812809644350395049793 2156859607233262796287345)
            ·
              refine ⟨1617644705424947097215509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156859607233262796287345 1617644705424947097215509)
              ·
                refine ⟨75827095566794395181977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1617644705424947097215509 75827095566794395181977)
                ·
                  rfl

theorem cell22_1993582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_1993582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993582 prefixEnd_1993582 := by exact prefixLift 1993582
  have htrace : WordTrace (prefixWord ++ tailWord_1993582) baseStart_1993582 baseEnd_1993582 := by
    simpa [prefixWord, tailWord_1993582, baseEnd_1993582] using wordTrace_append hprefix tailTrace_1993582
  have hstable : (prefixWord ++ tailWord_1993582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993582).length < 2 ^ (prefixWord ++ tailWord_1993582).sum := by decide
  have hdescent : baseEnd_1993582 < baseStart_1993582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993591 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1993591 : Nat := 118140960795 + 1993591 * 2 ^ 59
def prefixEnd_1993591 : Nat := 4983230072969 + 3 ^ 40 * 1993591 * 2
def baseEnd_1993591 : Nat := 682446940985076533162765

theorem tailTrace_1993591 : CollatzResearch.WordTrace tailWord_1993591 prefixEnd_1993591 682446940985076533162765 := by
  unfold tailWord_1993591
  simp only [CollatzResearch.WordTrace]
  refine ⟨72712237320567760081052627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48474824880378506720701751 72712237320567760081052627)
  ·
    refine ⟨109068355980851640121578941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72712237320567760081052627 109068355980851640121578941)
    ·
      refine ⟨40900633492819365045592103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109068355980851640121578941 40900633492819365045592103)
      ·
        refine ⟨61350950239229047568388155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40900633492819365045592103 61350950239229047568388155)
        ·
          refine ⟨92026425358843571352582233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61350950239229047568388155 92026425358843571352582233)
          ·
            refine ⟨69019819019132678514436675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92026425358843571352582233 69019819019132678514436675)
            ·
              refine ⟨103529728528699017771655013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69019819019132678514436675 103529728528699017771655013)
              ·
                refine ⟨19411824099131065832185315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103529728528699017771655013 19411824099131065832185315)
                ·
                  refine ⟨29117736148696598748277973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19411824099131065832185315 29117736148696598748277973)
                  ·
                    refine ⟨682446940985076533162765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29117736148696598748277973 682446940985076533162765)
                    ·
                      rfl

theorem cell22_1993591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1993591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993591 prefixEnd_1993591 := by exact prefixLift 1993591
  have htrace : WordTrace (prefixWord ++ tailWord_1993591) baseStart_1993591 baseEnd_1993591 := by
    simpa [prefixWord, tailWord_1993591, baseEnd_1993591] using wordTrace_append hprefix tailTrace_1993591
  have hstable : (prefixWord ++ tailWord_1993591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993591).length < 2 ^ (prefixWord ++ tailWord_1993591).sum := by decide
  have hdescent : baseEnd_1993591 < baseStart_1993591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993597 : List Nat := [1, 4, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_1993597 : Nat := 118140960795 + 1993597 * 2 ^ 59
def prefixEnd_1993597 : Nat := 4983230072969 + 3 ^ 40 * 1993597 * 2
def baseEnd_1993597 : Nat := 682448994907694517512747

theorem tailTrace_1993597 : CollatzResearch.WordTrace tailWord_1993597 prefixEnd_1993597 682448994907694517512747 := by
  unfold tailWord_1993597
  simp only [CollatzResearch.WordTrace]
  refine ⟨72712456158546023105771045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48474970772364015403847363 72712456158546023105771045)
  ·
    refine ⟨13633585529727379332332071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72712456158546023105771045 13633585529727379332332071)
    ·
      refine ⟨20450378294591068998498107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13633585529727379332332071 20450378294591068998498107)
      ·
        refine ⟨30675567441886603497747161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20450378294591068998498107 30675567441886603497747161)
        ·
          refine ⟨23006675581414952623310371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30675567441886603497747161 23006675581414952623310371)
          ·
            refine ⟨34510013372122428934965557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23006675581414952623310371 34510013372122428934965557)
            ·
              refine ⟨3235313753636477712653021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34510013372122428934965557 3235313753636477712653021)
              ·
                refine ⟨1213242657613679142244883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3235313753636477712653021 1213242657613679142244883)
                ·
                  refine ⟨1819863986420518713367325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213242657613679142244883 1819863986420518713367325)
                  ·
                    refine ⟨682448994907694517512747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819863986420518713367325 682448994907694517512747)
                    ·
                      rfl

theorem cell22_1993597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_1993597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993597 prefixEnd_1993597 := by exact prefixLift 1993597
  have htrace : WordTrace (prefixWord ++ tailWord_1993597) baseStart_1993597 baseEnd_1993597 := by
    simpa [prefixWord, tailWord_1993597, baseEnd_1993597] using wordTrace_append hprefix tailTrace_1993597
  have hstable : (prefixWord ++ tailWord_1993597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993597).length < 2 ^ (prefixWord ++ tailWord_1993597).sum := by decide
  have hdescent : baseEnd_1993597 < baseStart_1993597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993623 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1993623 : Nat := 118140960795 + 1993623 * 2 ^ 59
def prefixEnd_1993623 : Nat := 4983230072969 + 3 ^ 40 * 1993623 * 2
def baseEnd_1993623 : Nat := 682457895239039116362667

theorem tailTrace_1993623 : CollatzResearch.WordTrace tailWord_1993623 prefixEnd_1993623 682457895239039116362667 := by
  unfold tailWord_1993623
  simp only [CollatzResearch.WordTrace]
  refine ⟨72713404456451829546217523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48475602970967886364145015 72713404456451829546217523)
  ·
    refine ⟨109070106684677744319326285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72713404456451829546217523 109070106684677744319326285)
    ·
      refine ⟨40901290006754154119747357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109070106684677744319326285 40901290006754154119747357)
      ·
        refine ⟨15337983752532807794905259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40901290006754154119747357 15337983752532807794905259)
        ·
          refine ⟨23006975628799211692357889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337983752532807794905259 23006975628799211692357889)
          ·
            refine ⟨17255231721599408769268417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23006975628799211692357889 17255231721599408769268417)
            ·
              refine ⟨12941423791199556576951313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17255231721599408769268417 12941423791199556576951313)
              ·
                refine ⟨9706067843399667432713485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12941423791199556576951313 9706067843399667432713485)
                ·
                  refine ⟨3639775441274875287267557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9706067843399667432713485 3639775441274875287267557)
                  ·
                    refine ⟨682457895239039116362667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3639775441274875287267557 682457895239039116362667)
                    ·
                      rfl

theorem cell22_1993623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1993623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993623 prefixEnd_1993623 := by exact prefixLift 1993623
  have htrace : WordTrace (prefixWord ++ tailWord_1993623) baseStart_1993623 baseEnd_1993623 := by
    simpa [prefixWord, tailWord_1993623, baseEnd_1993623] using wordTrace_append hprefix tailTrace_1993623
  have hstable : (prefixWord ++ tailWord_1993623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993623).length < 2 ^ (prefixWord ++ tailWord_1993623).sum := by decide
  have hdescent : baseEnd_1993623 < baseStart_1993623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993657 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 1, 4]
def baseStart_1993657 : Nat := 118140960795 + 1993657 * 2 ^ 59
def prefixEnd_1993657 : Nat := 4983230072969 + 3 ^ 40 * 1993657 * 2
def baseEnd_1993657 : Nat := 682469534133874361012563

theorem tailTrace_1993657 : CollatzResearch.WordTrace tailWord_1993657 prefixEnd_1993657 682469534133874361012563 := by
  unfold tailWord_1993657
  simp only [CollatzResearch.WordTrace]
  refine ⟨72714644538328653352955225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48476429692219102235303483 72714644538328653352955225)
  ·
    refine ⟨54535983403746490014716419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72714644538328653352955225 54535983403746490014716419)
    ·
      refine ⟨81803975105619735022074629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54535983403746490014716419 81803975105619735022074629)
      ·
        refine ⟨15338245332303700316638993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81803975105619735022074629 15338245332303700316638993)
        ·
          refine ⟨11503683999227775237479245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15338245332303700316638993 11503683999227775237479245)
          ·
            refine ⟨4313881499710415714054717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11503683999227775237479245 4313881499710415714054717)
            ·
              refine ⟨1617705562391405892770519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4313881499710415714054717 1617705562391405892770519)
              ·
                refine ⟨2426558343587108839155779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617705562391405892770519 2426558343587108839155779)
                ·
                  refine ⟨3639837515380663258733669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426558343587108839155779 3639837515380663258733669)
                  ·
                    refine ⟨682469534133874361012563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3639837515380663258733669 682469534133874361012563)
                    ·
                      rfl

theorem cell22_1993657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_1993657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993657 prefixEnd_1993657 := by exact prefixLift 1993657
  have htrace : WordTrace (prefixWord ++ tailWord_1993657) baseStart_1993657 baseEnd_1993657 := by
    simpa [prefixWord, tailWord_1993657, baseEnd_1993657] using wordTrace_append hprefix tailTrace_1993657
  have hstable : (prefixWord ++ tailWord_1993657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993657).length < 2 ^ (prefixWord ++ tailWord_1993657).sum := by decide
  have hdescent : baseEnd_1993657 < baseStart_1993657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993672 : List Nat := [2, 1, 3, 1, 5, 1, 1, 4, 4]
def baseStart_1993672 : Nat := 118140960795 + 1993672 * 2 ^ 59
def prefixEnd_1993672 : Nat := 4983230072969 + 3 ^ 40 * 1993672 * 2
def baseEnd_1993672 : Nat := 227491556313473107295839

theorem tailTrace_1993672 : CollatzResearch.WordTrace tailWord_1993672 prefixEnd_1993672 227491556313473107295839 := by
  unfold tailWord_1993672
  simp only [CollatzResearch.WordTrace]
  refine ⟨36357595816637155457375635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48476794422182873943167513 36357595816637155457375635)
  ·
    refine ⟨54536393724955733186063453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36357595816637155457375635 54536393724955733186063453)
    ·
      refine ⟨20451147646858399944773795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54536393724955733186063453 20451147646858399944773795)
      ·
        refine ⟨30676721470287599917160693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20451147646858399944773795 30676721470287599917160693)
        ·
          refine ⟨2875942637839462492233815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30676721470287599917160693 2875942637839462492233815)
          ·
            refine ⟨4313913956759193738350723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875942637839462492233815 4313913956759193738350723)
            ·
              refine ⟨6470870935138790607526085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313913956759193738350723 6470870935138790607526085)
              ·
                refine ⟨1213288300338523238911141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6470870935138790607526085 1213288300338523238911141)
                ·
                  refine ⟨227491556313473107295839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213288300338523238911141 227491556313473107295839)
                  ·
                    rfl

theorem cell22_1993672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_1993672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993672 prefixEnd_1993672 := by exact prefixLift 1993672
  have htrace : WordTrace (prefixWord ++ tailWord_1993672) baseStart_1993672 baseEnd_1993672 := by
    simpa [prefixWord, tailWord_1993672, baseEnd_1993672] using wordTrace_append hprefix tailTrace_1993672
  have hstable : (prefixWord ++ tailWord_1993672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993672).length < 2 ^ (prefixWord ++ tailWord_1993672).sum := by decide
  have hdescent : baseEnd_1993672 < baseStart_1993672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993717 : List Nat := [1, 3, 5, 2, 1, 1, 9]
def baseStart_1993717 : Nat := 118140960795 + 1993717 * 2 ^ 59
def prefixEnd_1993717 : Nat := 4983230072969 + 3 ^ 40 * 1993717 * 2
def baseEnd_1993717 : Nat := 25277410124446452018977

theorem tailTrace_1993717 : CollatzResearch.WordTrace tailWord_1993717 prefixEnd_1993717 25277410124446452018977 := by
  unfold tailWord_1993717
  simp only [CollatzResearch.WordTrace]
  refine ⟨72716832918111283600139405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48477888612074189066759603 72716832918111283600139405)
  ·
    refine ⟨27268812344291731350052277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72716832918111283600139405 27268812344291731350052277)
    ·
      refine ⟨2556451157277349814067401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27268812344291731350052277 2556451157277349814067401)
      ·
        refine ⟨1917338367958012360550551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2556451157277349814067401 1917338367958012360550551)
        ·
          refine ⟨2876007551937018540825827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917338367958012360550551 2876007551937018540825827)
          ·
            refine ⟨4314011327905527811238741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876007551937018540825827 4314011327905527811238741)
            ·
              refine ⟨25277410124446452018977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4314011327905527811238741 25277410124446452018977)
              ·
                rfl

theorem cell22_1993717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 9].length) (baseStart_1993717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993717 prefixEnd_1993717 := by exact prefixLift 1993717
  have htrace : WordTrace (prefixWord ++ tailWord_1993717) baseStart_1993717 baseEnd_1993717 := by
    simpa [prefixWord, tailWord_1993717, baseEnd_1993717] using wordTrace_append hprefix tailTrace_1993717
  have hstable : (prefixWord ++ tailWord_1993717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993717).length < 2 ^ (prefixWord ++ tailWord_1993717).sum := by decide
  have hdescent : baseEnd_1993717 < baseStart_1993717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993826 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1993826 : Nat := 118140960795 + 1993826 * 2 ^ 59
def prefixEnd_1993826 : Nat := 4983230072969 + 3 ^ 40 * 1993826 * 2
def baseEnd_1993826 : Nat := 682527386287614253537045

theorem tailTrace_1993826 : CollatzResearch.WordTrace tailWord_1993826 prefixEnd_1993826 682527386287614253537045 := by
  unfold tailWord_1993826
  simp only [CollatzResearch.WordTrace]
  refine ⟨18180202118679098803964333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48480538983144263477238221 18180202118679098803964333)
  ·
    refine ⟨6817575794504662051486625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18180202118679098803964333 6817575794504662051486625)
    ·
      refine ⟨5113181845878496538614969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6817575794504662051486625 5113181845878496538614969)
      ·
        refine ⟨3834886384408872403961227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5113181845878496538614969 3834886384408872403961227)
        ·
          refine ⟨5752329576613308605941841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834886384408872403961227 5752329576613308605941841)
          ·
            refine ⟨4314247182459981454456381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5752329576613308605941841 4314247182459981454456381)
            ·
              refine ⟨1617842693422493045421143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4314247182459981454456381 1617842693422493045421143)
              ·
                refine ⟨2426764040133739568131715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617842693422493045421143 2426764040133739568131715)
                ·
                  refine ⟨3640146060200609352197573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426764040133739568131715 3640146060200609352197573)
                  ·
                    refine ⟨682527386287614253537045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640146060200609352197573 682527386287614253537045)
                    ·
                      rfl

theorem cell22_1993826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1993826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993826 prefixEnd_1993826 := by exact prefixLift 1993826
  have htrace : WordTrace (prefixWord ++ tailWord_1993826) baseStart_1993826 baseEnd_1993826 := by
    simpa [prefixWord, tailWord_1993826, baseEnd_1993826] using wordTrace_append hprefix tailTrace_1993826
  have hstable : (prefixWord ++ tailWord_1993826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993826).length < 2 ^ (prefixWord ++ tailWord_1993826).sum := by decide
  have hdescent : baseEnd_1993826 < baseStart_1993826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993837 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1993837 : Nat := 118140960795 + 1993837 * 2 ^ 59
def prefixEnd_1993837 : Nat := 4983230072969 + 3 ^ 40 * 1993837 * 2
def baseEnd_1993837 : Nat := 682531151812413891512011

theorem tailTrace_1993837 : CollatzResearch.WordTrace tailWord_1993837 prefixEnd_1993837 682531151812413891512011 := by
  unfold tailWord_1993837
  simp only [CollatzResearch.WordTrace]
  refine ⟨72721209677676544094507765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48480806451784362729671843 72721209677676544094507765)
  ·
    refine ⟨6817613407282176008860103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72721209677676544094507765 6817613407282176008860103)
    ·
      refine ⟨10226420110923264013290155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6817613407282176008860103 10226420110923264013290155)
      ·
        refine ⟨15339630166384896019935233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10226420110923264013290155 15339630166384896019935233)
        ·
          refine ⟨11504722624788672014951425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15339630166384896019935233 11504722624788672014951425)
          ·
            refine ⟨8628541968591504011213569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11504722624788672014951425 8628541968591504011213569)
            ·
              refine ⟨6471406476443628008410177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628541968591504011213569 6471406476443628008410177)
              ·
                refine ⟨4853554857332721006307633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471406476443628008410177 4853554857332721006307633)
                ·
                  refine ⟨3640166142999540754730725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853554857332721006307633 3640166142999540754730725)
                  ·
                    refine ⟨682531151812413891512011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640166142999540754730725 682531151812413891512011)
                    ·
                      rfl

theorem cell22_1993837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1993837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993837 prefixEnd_1993837 := by exact prefixLift 1993837
  have htrace : WordTrace (prefixWord ++ tailWord_1993837) baseStart_1993837 baseEnd_1993837 := by
    simpa [prefixWord, tailWord_1993837, baseEnd_1993837] using wordTrace_append hprefix tailTrace_1993837
  have hstable : (prefixWord ++ tailWord_1993837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993837).length < 2 ^ (prefixWord ++ tailWord_1993837).sum := by decide
  have hdescent : baseEnd_1993837 < baseStart_1993837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993901 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1993901 : Nat := 118140960795 + 1993901 * 2 ^ 59
def prefixEnd_1993901 : Nat := 4983230072969 + 3 ^ 40 * 1993901 * 2
def baseEnd_1993901 : Nat := 682553060320339057911815

theorem tailTrace_1993901 : CollatzResearch.WordTrace tailWord_1993901 prefixEnd_1993901 682553060320339057911815 := by
  unfold tailWord_1993901
  simp only [CollatzResearch.WordTrace]
  refine ⟨72723543949444683024837557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48482362632963122016558371 72723543949444683024837557)
  ·
    refine ⟨6817832245260439033578521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72723543949444683024837557 6817832245260439033578521)
    ·
      refine ⟨5113374183945329275183891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6817832245260439033578521 5113374183945329275183891)
      ·
        refine ⟨7670061275917993912775837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5113374183945329275183891 7670061275917993912775837)
        ·
          refine ⟨2876272978469247717290939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7670061275917993912775837 2876272978469247717290939)
          ·
            refine ⟨4314409467703871575936409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876272978469247717290939 4314409467703871575936409)
            ·
              refine ⟨3235807100777903681952307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314409467703871575936409 3235807100777903681952307)
              ·
                refine ⟨4853710651166855522928461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235807100777903681952307 4853710651166855522928461)
                ·
                  refine ⟨1820141494187570821098173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4853710651166855522928461 1820141494187570821098173)
                  ·
                    refine ⟨682553060320339057911815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820141494187570821098173 682553060320339057911815)
                    ·
                      rfl

theorem cell22_1993901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1993901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1993901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1993901 prefixEnd_1993901 := by exact prefixLift 1993901
  have htrace : WordTrace (prefixWord ++ tailWord_1993901) baseStart_1993901 baseEnd_1993901 := by
    simpa [prefixWord, tailWord_1993901, baseEnd_1993901] using wordTrace_append hprefix tailTrace_1993901
  have hstable : (prefixWord ++ tailWord_1993901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993901).length < 2 ^ (prefixWord ++ tailWord_1993901).sum := by decide
  have hdescent : baseEnd_1993901 < baseStart_1993901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994032 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 5]
def baseStart_1994032 : Nat := 118140960795 + 1994032 * 2 ^ 59
def prefixEnd_1994032 : Nat := 4983230072969 + 3 ^ 40 * 1994032 * 2
def baseEnd_1994032 : Nat := 227532634765832794295471

theorem tailTrace_1994032 : CollatzResearch.WordTrace tailWord_1994032 prefixEnd_1994032 227532634765832794295471 := by
  unfold tailWord_1994032
  simp only [CollatzResearch.WordTrace]
  refine ⟨36364160955985046198928175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48485547941313394931904233 36364160955985046198928175)
  ·
    refine ⟨54546241433977569298392263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36364160955985046198928175 54546241433977569298392263)
    ·
      refine ⟨81819362150966353947588395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54546241433977569298392263 81819362150966353947588395)
      ·
        refine ⟨122729043226449530921382593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81819362150966353947588395 122729043226449530921382593)
        ·
          refine ⟨92046782419837148191036945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122729043226449530921382593 92046782419837148191036945)
          ·
            refine ⟨69035086814877861143277709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92046782419837148191036945 69035086814877861143277709)
            ·
              refine ⟨25888157555579197928729141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69035086814877861143277709 25888157555579197928729141)
              ·
                refine ⟨2427014770835549805818357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25888157555579197928729141 2427014770835549805818357)
                ·
                  refine ⟨227532634765832794295471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2427014770835549805818357 227532634765832794295471)
                  ·
                    rfl

theorem cell22_1994032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_1994032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994032 prefixEnd_1994032 := by exact prefixLift 1994032
  have htrace : WordTrace (prefixWord ++ tailWord_1994032) baseStart_1994032 baseEnd_1994032 := by
    simpa [prefixWord, tailWord_1994032, baseEnd_1994032] using wordTrace_append hprefix tailTrace_1994032
  have hstable : (prefixWord ++ tailWord_1994032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994032).length < 2 ^ (prefixWord ++ tailWord_1994032).sum := by decide
  have hdescent : baseEnd_1994032 < baseStart_1994032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994036 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1994036 : Nat := 118140960795 + 1994036 * 2 ^ 59
def prefixEnd_1994036 : Nat := 4983230072969 + 3 ^ 40 * 1994036 * 2
def baseEnd_1994036 : Nat := 682599273579243705786401

theorem tailTrace_1994036 : CollatzResearch.WordTrace tailWord_1994036 prefixEnd_1994036 682599273579243705786401 := by
  unfold tailWord_1994036
  simp only [CollatzResearch.WordTrace]
  refine ⟨36364233901977800540500981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48485645202637067387334641 36364233901977800540500981)
  ·
    refine ⟨3409146928310418800671967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36364233901977800540500981 3409146928310418800671967)
    ·
      refine ⟨5113720392465628201007951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3409146928310418800671967 5113720392465628201007951)
      ·
        refine ⟨7670580588698442301511927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5113720392465628201007951 7670580588698442301511927)
        ·
          refine ⟨11505870883047663452267891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670580588698442301511927 11505870883047663452267891)
          ·
            refine ⟨17258806324571495178401837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11505870883047663452267891 17258806324571495178401837)
            ·
              refine ⟨6472052371714310691900689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17258806324571495178401837 6472052371714310691900689)
              ·
                refine ⟨4854039278785733018925517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6472052371714310691900689 4854039278785733018925517)
                ·
                  refine ⟨1820264729544649882097069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4854039278785733018925517 1820264729544649882097069)
                  ·
                    refine ⟨682599273579243705786401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820264729544649882097069 682599273579243705786401)
                    ·
                      rfl

theorem cell22_1994036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1994036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994036 prefixEnd_1994036 := by exact prefixLift 1994036
  have htrace : WordTrace (prefixWord ++ tailWord_1994036) baseStart_1994036 baseEnd_1994036 := by
    simpa [prefixWord, tailWord_1994036, baseEnd_1994036] using wordTrace_append hprefix tailTrace_1994036
  have hstable : (prefixWord ++ tailWord_1994036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994036).length < 2 ^ (prefixWord ++ tailWord_1994036).sum := by decide
  have hdescent : baseEnd_1994036 < baseStart_1994036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994038 : List Nat := [5, 1, 2, 3, 1, 1, 3, 6]
def baseStart_1994038 : Nat := 118140960795 + 1994038 * 2 ^ 59
def prefixEnd_1994038 : Nat := 4983230072969 + 3 ^ 40 * 1994038 * 2
def baseEnd_1994038 : Nat := 75844439802235151915155

theorem tailTrace_1994038 : CollatzResearch.WordTrace tailWord_1994038 prefixEnd_1994038 75844439802235151915155 := by
  unfold tailWord_1994038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545533796871772213910923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48485693833298903615049845 4545533796871772213910923)
  ·
    refine ⟨6818300695307658320866385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4545533796871772213910923 6818300695307658320866385)
    ·
      refine ⟨5113725521480743740649789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6818300695307658320866385 5113725521480743740649789)
      ·
        refine ⟨1917647070555278902743671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5113725521480743740649789 1917647070555278902743671)
        ·
          refine ⟨2876470605832918354115507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917647070555278902743671 2876470605832918354115507)
          ·
            refine ⟨4314705908749377531173261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876470605832918354115507 4314705908749377531173261)
            ·
              refine ⟨1618014715781016574189973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4314705908749377531173261 1618014715781016574189973)
              ·
                refine ⟨75844439802235151915155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1618014715781016574189973 75844439802235151915155)
                ·
                  rfl

theorem cell22_1994038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_1994038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994038 prefixEnd_1994038 := by exact prefixLift 1994038
  have htrace : WordTrace (prefixWord ++ tailWord_1994038) baseStart_1994038 baseEnd_1994038 := by
    simpa [prefixWord, tailWord_1994038, baseEnd_1994038] using wordTrace_append hprefix tailTrace_1994038
  have hstable : (prefixWord ++ tailWord_1994038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994038).length < 2 ^ (prefixWord ++ tailWord_1994038).sum := by decide
  have hdescent : baseEnd_1994038 < baseStart_1994038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994107 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 1, 6]
def baseStart_1994107 : Nat := 118140960795 + 1994107 * 2 ^ 59
def prefixEnd_1994107 : Nat := 4983230072969 + 3 ^ 40 * 1994107 * 2
def baseEnd_1994107 : Nat := 682623578330223187261183

theorem tailTrace_1994107 : CollatzResearch.WordTrace tailWord_1994107 prefixEnd_1994107 682623578330223187261183 := by
  unfold tailWord_1994107
  simp only [CollatzResearch.WordTrace]
  refine ⟨72731057386698380206836575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48487371591132253471224383 72731057386698380206836575)
  ·
    refine ⟨109096586080047570310254863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72731057386698380206836575 109096586080047570310254863)
    ·
      refine ⟨163644879120071355465382295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109096586080047570310254863 163644879120071355465382295)
      ·
        refine ⟨245467318680107033198073443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163644879120071355465382295 245467318680107033198073443)
        ·
          refine ⟨368200978020160549797110165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245467318680107033198073443 368200978020160549797110165)
          ·
            refine ⟨17259420844695025771739539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 368200978020160549797110165 17259420844695025771739539)
            ·
              refine ⟨25889131267042538657609309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17259420844695025771739539 25889131267042538657609309)
              ·
                refine ⟨9708424225140951996603491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25889131267042538657609309 9708424225140951996603491)
                ·
                  refine ⟨14562636337711427994905237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9708424225140951996603491 14562636337711427994905237)
                  ·
                    refine ⟨682623578330223187261183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14562636337711427994905237 682623578330223187261183)
                    ·
                      rfl

theorem cell22_1994107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_1994107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994107 prefixEnd_1994107 := by exact prefixLift 1994107
  have htrace : WordTrace (prefixWord ++ tailWord_1994107) baseStart_1994107 baseEnd_1994107 := by
    simpa [prefixWord, tailWord_1994107, baseEnd_1994107] using wordTrace_append hprefix tailTrace_1994107
  have hstable : (prefixWord ++ tailWord_1994107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994107).length < 2 ^ (prefixWord ++ tailWord_1994107).sum := by decide
  have hdescent : baseEnd_1994107 < baseStart_1994107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994109 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1994109 : Nat := 118140960795 + 1994109 * 2 ^ 59
def prefixEnd_1994109 : Nat := 4983230072969 + 3 ^ 40 * 1994109 * 2
def baseEnd_1994109 : Nat := 682624262971095848711177

theorem tailTrace_1994109 : CollatzResearch.WordTrace tailWord_1994109 prefixEnd_1994109 682624262971095848711177 := by
  unfold tailWord_1994109
  simp only [CollatzResearch.WordTrace]
  refine ⟨72731130332691134548409381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48487420221794089698939587 72731130332691134548409381)
  ·
    refine ⟨13637086937379587727826759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72731130332691134548409381 13637086937379587727826759)
    ·
      refine ⟨20455630406069381591740139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13637086937379587727826759 20455630406069381591740139)
      ·
        refine ⟨30683445609104072387610209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20455630406069381591740139 30683445609104072387610209)
        ·
          refine ⟨23012584206828054290707657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30683445609104072387610209 23012584206828054290707657)
          ·
            refine ⟨17259438155121040718030743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23012584206828054290707657 17259438155121040718030743)
            ·
              refine ⟨25889157232681561077046115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17259438155121040718030743 25889157232681561077046115)
              ·
                refine ⟨38833735849022341615569173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25889157232681561077046115 38833735849022341615569173)
                ·
                  refine ⟨1820331367922922263229805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38833735849022341615569173 1820331367922922263229805)
                  ·
                    refine ⟨682624262971095848711177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820331367922922263229805 682624262971095848711177)
                    ·
                      rfl

theorem cell22_1994109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1994109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994109 prefixEnd_1994109 := by exact prefixLift 1994109
  have htrace : WordTrace (prefixWord ++ tailWord_1994109) baseStart_1994109 baseEnd_1994109 := by
    simpa [prefixWord, tailWord_1994109, baseEnd_1994109] using wordTrace_append hprefix tailTrace_1994109
  have hstable : (prefixWord ++ tailWord_1994109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994109).length < 2 ^ (prefixWord ++ tailWord_1994109).sum := by decide
  have hdescent : baseEnd_1994109 < baseStart_1994109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994124 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_1994124 : Nat := 118140960795 + 1994124 * 2 ^ 59
def prefixEnd_1994124 : Nat := 4983230072969 + 3 ^ 40 * 1994124 * 2
def baseEnd_1994124 : Nat := 682629397777640809586131

theorem tailTrace_1994124 : CollatzResearch.WordTrace tailWord_1994124 prefixEnd_1994124 682629397777640809586131 := by
  unfold tailWord_1994124
  simp only [CollatzResearch.WordTrace]
  refine ⟨36365838713818396055102713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48487784951757861406803617 36365838713818396055102713)
  ·
    refine ⟨27274379035363797041327035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36365838713818396055102713 27274379035363797041327035)
    ·
      refine ⟨40911568553045695561990553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27274379035363797041327035 40911568553045695561990553)
      ·
        refine ⟨30683676414784271671492915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40911568553045695561990553 30683676414784271671492915)
        ·
          refine ⟨46025514622176407507239373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30683676414784271671492915 46025514622176407507239373)
          ·
            refine ⟨17259567983316152815214765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46025514622176407507239373 17259567983316152815214765)
            ·
              refine ⟨6472337993743557305705537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17259567983316152815214765 6472337993743557305705537)
              ·
                refine ⟨4854253495307667979279153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6472337993743557305705537 4854253495307667979279153)
                ·
                  refine ⟨3640690121480750984459365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4854253495307667979279153 3640690121480750984459365)
                  ·
                    refine ⟨682629397777640809586131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640690121480750984459365 682629397777640809586131)
                    ·
                      rfl

theorem cell22_1994124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_1994124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994124 prefixEnd_1994124 := by exact prefixLift 1994124
  have htrace : WordTrace (prefixWord ++ tailWord_1994124) baseStart_1994124 baseEnd_1994124 := by
    simpa [prefixWord, tailWord_1994124, baseEnd_1994124] using wordTrace_append hprefix tailTrace_1994124
  have hstable : (prefixWord ++ tailWord_1994124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994124).length < 2 ^ (prefixWord ++ tailWord_1994124).sum := by decide
  have hdescent : baseEnd_1994124 < baseStart_1994124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994143 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 2, 3]
def baseStart_1994143 : Nat := 118140960795 + 1994143 * 2 ^ 59
def prefixEnd_1994143 : Nat := 4983230072969 + 3 ^ 40 * 1994143 * 2
def baseEnd_1994143 : Nat := 682635901865931093361073

theorem tailTrace_1994143 : CollatzResearch.WordTrace tailWord_1994143 prefixEnd_1994143 682635901865931093361073 := by
  unfold tailWord_1994143
  simp only [CollatzResearch.WordTrace]
  refine ⟨72732370414567958355147083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48488246943045305570098055 72732370414567958355147083)
  ·
    refine ⟨109098555621851937532720625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72732370414567958355147083 109098555621851937532720625)
    ·
      refine ⟨81823916716388953149540469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109098555621851937532720625 81823916716388953149540469)
      ·
        refine ⟨7670992192161464357769419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81823916716388953149540469 7670992192161464357769419)
        ·
          refine ⟨11506488288242196536654129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670992192161464357769419 11506488288242196536654129)
          ·
            refine ⟨8629866216181647402490597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11506488288242196536654129 8629866216181647402490597)
            ·
              refine ⟨1618099915534058887966987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8629866216181647402490597 1618099915534058887966987)
              ·
                refine ⟨2427149873301088331950481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618099915534058887966987 2427149873301088331950481)
                ·
                  refine ⟨1820362404975816248962861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2427149873301088331950481 1820362404975816248962861)
                  ·
                    refine ⟨682635901865931093361073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820362404975816248962861 682635901865931093361073)
                    ·
                      rfl

theorem cell22_1994143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_1994143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994143 prefixEnd_1994143 := by exact prefixLift 1994143
  have htrace : WordTrace (prefixWord ++ tailWord_1994143) baseStart_1994143 baseEnd_1994143 := by
    simpa [prefixWord, tailWord_1994143, baseEnd_1994143] using wordTrace_append hprefix tailTrace_1994143
  have hstable : (prefixWord ++ tailWord_1994143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994143).length < 2 ^ (prefixWord ++ tailWord_1994143).sum := by decide
  have hdescent : baseEnd_1994143 < baseStart_1994143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994259 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 1, 6]
def baseStart_1994259 : Nat := 118140960795 + 1994259 * 2 ^ 59
def prefixEnd_1994259 : Nat := 4983230072969 + 3 ^ 40 * 1994259 * 2
def baseEnd_1994259 : Nat := 682675611036545457460717

theorem tailTrace_1994259 : CollatzResearch.WordTrace tailWord_1994259 prefixEnd_1994259 682675611036545457460717 := by
  unfold tailWord_1994259
  simp only [CollatzResearch.WordTrace]
  refine ⟨72736601282147710166369831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48491067521431806777579887 72736601282147710166369831)
  ·
    refine ⟨109104901923221565249554747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72736601282147710166369831 109104901923221565249554747)
    ·
      refine ⟨163657352884832347874332121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109104901923221565249554747 163657352884832347874332121)
      ·
        refine ⟨122743014663624260905749091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163657352884832347874332121 122743014663624260905749091)
        ·
          refine ⟨184114521995436391358623637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122743014663624260905749091 184114521995436391358623637)
          ·
            refine ⟨8630368218536080844935483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184114521995436391358623637 8630368218536080844935483)
            ·
              refine ⟨12945552327804121267403225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8630368218536080844935483 12945552327804121267403225)
              ·
                refine ⟨9709164245853090950552419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12945552327804121267403225 9709164245853090950552419)
                ·
                  refine ⟨14563746368779636425828629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9709164245853090950552419 14563746368779636425828629)
                  ·
                    refine ⟨682675611036545457460717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14563746368779636425828629 682675611036545457460717)
                    ·
                      rfl

theorem cell22_1994259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_1994259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994259 prefixEnd_1994259 := by exact prefixLift 1994259
  have htrace : WordTrace (prefixWord ++ tailWord_1994259) baseStart_1994259 baseEnd_1994259 := by
    simpa [prefixWord, tailWord_1994259, baseEnd_1994259] using wordTrace_append hprefix tailTrace_1994259
  have hstable : (prefixWord ++ tailWord_1994259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994259).length < 2 ^ (prefixWord ++ tailWord_1994259).sum := by decide
  have hdescent : baseEnd_1994259 < baseStart_1994259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994261 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1994261 : Nat := 118140960795 + 1994261 * 2 ^ 59
def prefixEnd_1994261 : Nat := 4983230072969 + 3 ^ 40 * 1994261 * 2
def baseEnd_1994261 : Nat := 682676295677418118910711

theorem tailTrace_1994261 : CollatzResearch.WordTrace tailWord_1994261 prefixEnd_1994261 682676295677418118910711 := by
  unfold tailWord_1994261
  simp only [CollatzResearch.WordTrace]
  refine ⟨72736674228140464507942637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48491116152093643005295091 72736674228140464507942637)
  ·
    refine ⟨27276252835552674190478489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72736674228140464507942637 27276252835552674190478489)
    ·
      refine ⟨20457189626664505642858867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27276252835552674190478489 20457189626664505642858867)
      ·
        refine ⟨30685784439996758464288301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20457189626664505642858867 30685784439996758464288301)
        ·
          refine ⟨11507169164998784424108113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30685784439996758464288301 11507169164998784424108113)
          ·
            refine ⟨8630376873749088318081085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11507169164998784424108113 8630376873749088318081085)
            ·
              refine ⟨3236391327655908119280407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8630376873749088318081085 3236391327655908119280407)
              ·
                refine ⟨4854586991483862178920611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236391327655908119280407 4854586991483862178920611)
                ·
                  refine ⟨7281880487225793268380917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854586991483862178920611 7281880487225793268380917)
                  ·
                    refine ⟨682676295677418118910711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7281880487225793268380917 682676295677418118910711)
                    ·
                      rfl

theorem cell22_1994261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1994261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994261 prefixEnd_1994261 := by exact prefixLift 1994261
  have htrace : WordTrace (prefixWord ++ tailWord_1994261) baseStart_1994261 baseEnd_1994261 := by
    simpa [prefixWord, tailWord_1994261, baseEnd_1994261] using wordTrace_append hprefix tailTrace_1994261
  have hstable : (prefixWord ++ tailWord_1994261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994261).length < 2 ^ (prefixWord ++ tailWord_1994261).sum := by decide
  have hdescent : baseEnd_1994261 < baseStart_1994261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994304 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_1994304 : Nat := 118140960795 + 1994304 * 2 ^ 59
def prefixEnd_1994304 : Nat := 4983230072969 + 3 ^ 40 * 1994304 * 2
def baseEnd_1994304 : Nat := 682691015456180340085579

theorem tailTrace_1994304 : CollatzResearch.WordTrace tailWord_1994304 prefixEnd_1994304 682691015456180340085579 := by
  unfold tailWord_1994304
  simp only [CollatzResearch.WordTrace]
  refine ⟨36369121283492341425878983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48492161711323121901171977 36369121283492341425878983)
  ·
    refine ⟨54553681925238512138818475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36369121283492341425878983 54553681925238512138818475)
    ·
      refine ⟨81830522887857768208227713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54553681925238512138818475 81830522887857768208227713)
      ·
        refine ⟨61372892165893326156170785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81830522887857768208227713 61372892165893326156170785)
        ·
          refine ⟨46029669124419994617128089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61372892165893326156170785 46029669124419994617128089)
          ·
            refine ⟨34522251843314995962846067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46029669124419994617128089 34522251843314995962846067)
            ·
              refine ⟨51783377764972493944269101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34522251843314995962846067 51783377764972493944269101)
              ·
                refine ⟨19418766661864685229100913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51783377764972493944269101 19418766661864685229100913)
                ·
                  refine ⟨14564074996398513921825685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19418766661864685229100913 14564074996398513921825685)
                  ·
                    refine ⟨682691015456180340085579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14564074996398513921825685 682691015456180340085579)
                    ·
                      rfl

theorem cell22_1994304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_1994304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994304 prefixEnd_1994304 := by exact prefixLift 1994304
  have htrace : WordTrace (prefixWord ++ tailWord_1994304) baseStart_1994304 baseEnd_1994304 := by
    simpa [prefixWord, tailWord_1994304, baseEnd_1994304] using wordTrace_append hprefix tailTrace_1994304
  have hstable : (prefixWord ++ tailWord_1994304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994304).length < 2 ^ (prefixWord ++ tailWord_1994304).sum := by decide
  have hdescent : baseEnd_1994304 < baseStart_1994304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994357 : List Nat := [1, 3, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1994357 : Nat := 118140960795 + 1994357 * 2 ^ 59
def prefixEnd_1994357 : Nat := 4983230072969 + 3 ^ 40 * 1994357 * 2
def baseEnd_1994357 : Nat := 682709158439305868510417

theorem tailTrace_1994357 : CollatzResearch.WordTrace tailWord_1994357 prefixEnd_1994357 682709158439305868510417 := by
  unfold tailWord_1994357
  simp only [CollatzResearch.WordTrace]
  refine ⟨72740175635792672903437325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48493450423861781935624883 72740175635792672903437325)
  ·
    refine ⟨27277565863422252338788997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72740175635792672903437325 27277565863422252338788997)
    ·
      refine ⟨5114543599391672313522937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27277565863422252338788997 5114543599391672313522937)
      ·
        refine ⟨3835907699543754235142203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5114543599391672313522937 3835907699543754235142203)
        ·
          refine ⟨5753861549315631352713305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835907699543754235142203 5753861549315631352713305)
          ·
            refine ⟨4315396161986723514534979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5753861549315631352713305 4315396161986723514534979)
            ·
              refine ⟨6473094242980085271802469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4315396161986723514534979 6473094242980085271802469)
              ·
                refine ⟨1213705170558765988462963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6473094242980085271802469 1213705170558765988462963)
                ·
                  refine ⟨1820557755838148982694445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213705170558765988462963 1820557755838148982694445)
                  ·
                    refine ⟨682709158439305868510417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820557755838148982694445 682709158439305868510417)
                    ·
                      rfl

theorem cell22_1994357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1994357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994357 prefixEnd_1994357 := by exact prefixLift 1994357
  have htrace : WordTrace (prefixWord ++ tailWord_1994357) baseStart_1994357 baseEnd_1994357 := by
    simpa [prefixWord, tailWord_1994357, baseEnd_1994357] using wordTrace_append hprefix tailTrace_1994357
  have hstable : (prefixWord ++ tailWord_1994357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994357).length < 2 ^ (prefixWord ++ tailWord_1994357).sum := by decide
  have hdescent : baseEnd_1994357 < baseStart_1994357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994400 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 1, 4]
def baseStart_1994400 : Nat := 118140960795 + 1994400 * 2 ^ 59
def prefixEnd_1994400 : Nat := 4983230072969 + 3 ^ 40 * 1994400 * 2
def baseEnd_1994400 : Nat := 682723878218068089685285

theorem tailTrace_1994400 : CollatzResearch.WordTrace tailWord_1994400 prefixEnd_1994400 682723878218068089685285 := by
  unfold tailWord_1994400
  simp only [CollatzResearch.WordTrace]
  refine ⟨36370871987318445623626327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48494495983091260831501769 36370871987318445623626327)
  ·
    refine ⟨54556307980977668435439491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36370871987318445623626327 54556307980977668435439491)
    ·
      refine ⟨81834461971466502653159237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54556307980977668435439491 81834461971466502653159237)
      ·
        refine ⟨15343961619649969247467357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81834461971466502653159237 15343961619649969247467357)
        ·
          refine ⟨5753985607368738467800259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15343961619649969247467357 5753985607368738467800259)
          ·
            refine ⟨8630978411053107701700389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753985607368738467800259 8630978411053107701700389)
            ·
              refine ⟨1618308452072457694068823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8630978411053107701700389 1618308452072457694068823)
              ·
                refine ⟨2427462678108686541103235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618308452072457694068823 2427462678108686541103235)
                ·
                  refine ⟨3641194017163029811654853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427462678108686541103235 3641194017163029811654853)
                  ·
                    refine ⟨682723878218068089685285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3641194017163029811654853 682723878218068089685285)
                    ·
                      rfl

theorem cell22_1994400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_1994400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994400 prefixEnd_1994400 := by exact prefixLift 1994400
  have htrace : WordTrace (prefixWord ++ tailWord_1994400) baseStart_1994400 baseEnd_1994400 := by
    simpa [prefixWord, tailWord_1994400, baseEnd_1994400] using wordTrace_append hprefix tailTrace_1994400
  have hstable : (prefixWord ++ tailWord_1994400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994400).length < 2 ^ (prefixWord ++ tailWord_1994400).sum := by decide
  have hdescent : baseEnd_1994400 < baseStart_1994400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994430 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1994430 : Nat := 118140960795 + 1994430 * 2 ^ 59
def prefixEnd_1994430 : Nat := 4983230072969 + 3 ^ 40 * 1994430 * 2
def baseEnd_1994430 : Nat := 682734147831158011435193

theorem tailTrace_1994430 : CollatzResearch.WordTrace tailWord_1994430 prefixEnd_1994430 682734147831158011435193 := by
  unfold tailWord_1994430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092854770566025796355593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48495225443018804247229829 9092854770566025796355593)
  ·
    refine ⟨6819641077924519347266695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9092854770566025796355593 6819641077924519347266695)
    ·
      refine ⟨10229461616886779020900043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6819641077924519347266695 10229461616886779020900043)
      ·
        refine ⟨15344192425330168531350065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229461616886779020900043 15344192425330168531350065)
        ·
          refine ⟨11508144318997626398512549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15344192425330168531350065 11508144318997626398512549)
          ·
            refine ⟨2157777059812054949721103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11508144318997626398512549 2157777059812054949721103)
            ·
              refine ⟨3236665589718082424581655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157777059812054949721103 3236665589718082424581655)
              ·
                refine ⟨4854998384577123636872483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236665589718082424581655 4854998384577123636872483)
                ·
                  refine ⟨7282497576865685455308725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854998384577123636872483 7282497576865685455308725)
                  ·
                    refine ⟨682734147831158011435193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7282497576865685455308725 682734147831158011435193)
                    ·
                      rfl

theorem cell22_1994430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1994430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994430 prefixEnd_1994430 := by exact prefixLift 1994430
  have htrace : WordTrace (prefixWord ++ tailWord_1994430) baseStart_1994430 baseEnd_1994430 := by
    simpa [prefixWord, tailWord_1994430, baseEnd_1994430] using wordTrace_append hprefix tailTrace_1994430
  have hstable : (prefixWord ++ tailWord_1994430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994430).length < 2 ^ (prefixWord ++ tailWord_1994430).sum := by decide
  have hdescent : baseEnd_1994430 < baseStart_1994430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994445 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1994445 : Nat := 118140960795 + 1994445 * 2 ^ 59
def prefixEnd_1994445 : Nat := 4983230072969 + 3 ^ 40 * 1994445 * 2
def baseEnd_1994445 : Nat := 682739282637702972310147

theorem tailTrace_1994445 : CollatzResearch.WordTrace tailWord_1994445 prefixEnd_1994445 682739282637702972310147 := by
  unfold tailWord_1994445
  simp only [CollatzResearch.WordTrace]
  refine ⟨72743385259473863932640789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48495590172982575955093859 72743385259473863932640789)
  ·
    refine ⟨3409846184037837371842537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72743385259473863932640789 3409846184037837371842537)
    ·
      refine ⟨2557384638028378028881903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3409846184037837371842537 2557384638028378028881903)
      ·
        refine ⟨3836076957042567043322855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557384638028378028881903 3836076957042567043322855)
        ·
          refine ⟨5754115435563850564984283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3836076957042567043322855 5754115435563850564984283)
          ·
            refine ⟨8631173153345775847476425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5754115435563850564984283 8631173153345775847476425)
            ·
              refine ⟨6473379865009331885607319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8631173153345775847476425 6473379865009331885607319)
              ·
                refine ⟨9710069797513997828410979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473379865009331885607319 9710069797513997828410979)
                ·
                  refine ⟨14565104696270996742616469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710069797513997828410979 14565104696270996742616469)
                  ·
                    refine ⟨682739282637702972310147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14565104696270996742616469 682739282637702972310147)
                    ·
                      rfl

theorem cell22_1994445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1994445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994445 prefixEnd_1994445 := by exact prefixLift 1994445
  have htrace : WordTrace (prefixWord ++ tailWord_1994445) baseStart_1994445 baseEnd_1994445 := by
    simpa [prefixWord, tailWord_1994445, baseEnd_1994445] using wordTrace_append hprefix tailTrace_1994445
  have hstable : (prefixWord ++ tailWord_1994445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994445).length < 2 ^ (prefixWord ++ tailWord_1994445).sum := by decide
  have hdescent : baseEnd_1994445 < baseStart_1994445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994460 : List Nat := [2, 2, 5, 1, 2, 2, 8]
def baseStart_1994460 : Nat := 118140960795 + 1994460 * 2 ^ 59
def prefixEnd_1994460 : Nat := 4983230072969 + 3 ^ 40 * 1994460 * 2
def baseEnd_1994460 : Nat := 25286830275712886414263

theorem tailTrace_1994460 : CollatzResearch.WordTrace tailWord_1994460 prefixEnd_1994460 25286830275712886414263 := by
  unfold tailWord_1994460
  simp only [CollatzResearch.WordTrace]
  refine ⟨36371966177209760747218417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48495954902946347662957889 36371966177209760747218417)
  ·
    refine ⟨27278974632907320560413813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36371966177209760747218417 27278974632907320560413813)
    ·
      refine ⟨2557403871835061302538795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27278974632907320560413813 2557403871835061302538795)
      ·
        refine ⟨3836105807752591953808193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557403871835061302538795 3836105807752591953808193)
        ·
          refine ⟨2877079355814443965356145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3836105807752591953808193 2877079355814443965356145)
          ·
            refine ⟨2157809516860832974017109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2877079355814443965356145 2157809516860832974017109)
            ·
              refine ⟨25286830275712886414263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2157809516860832974017109 25286830275712886414263)
              ·
                rfl

theorem cell22_1994460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 8].length) (baseStart_1994460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994460 prefixEnd_1994460 := by exact prefixLift 1994460
  have htrace : WordTrace (prefixWord ++ tailWord_1994460) baseStart_1994460 baseEnd_1994460 := by
    simpa [prefixWord, tailWord_1994460, baseEnd_1994460] using wordTrace_append hprefix tailTrace_1994460
  have hstable : (prefixWord ++ tailWord_1994460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994460).length < 2 ^ (prefixWord ++ tailWord_1994460).sum := by decide
  have hdescent : baseEnd_1994460 < baseStart_1994460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994475 : List Nat := [1, 1, 1, 1, 2, 4, 2, 6, 1, 3]
def baseStart_1994475 : Nat := 118140960795 + 1994475 * 2 ^ 59
def prefixEnd_1994475 : Nat := 4983230072969 + 3 ^ 40 * 1994475 * 2
def baseEnd_1994475 : Nat := 682749552250792894060055

theorem tailTrace_1994475 : CollatzResearch.WordTrace tailWord_1994475 prefixEnd_1994475 682749552250792894060055 := by
  unfold tailWord_1994475
  simp only [CollatzResearch.WordTrace]
  refine ⟨72744479449365179056232879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48496319632910119370821919 72744479449365179056232879)
  ·
    refine ⟨109116719174047768584349319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72744479449365179056232879 109116719174047768584349319)
    ·
      refine ⟨163675078761071652876523979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109116719174047768584349319 163675078761071652876523979)
      ·
        refine ⟨245512618141607479314785969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163675078761071652876523979 245512618141607479314785969)
        ·
          refine ⟨184134463606205609486089477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245512618141607479314785969 184134463606205609486089477)
          ·
            refine ⟨34525211926163551778641777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184134463606205609486089477 34525211926163551778641777)
            ·
              refine ⟨25893908944622663833981333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34525211926163551778641777 25893908944622663833981333)
              ·
                refine ⟨1213776981779187367217875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25893908944622663833981333 1213776981779187367217875)
                ·
                  refine ⟨1820665472668781050826813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213776981779187367217875 1820665472668781050826813)
                  ·
                    refine ⟨682749552250792894060055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820665472668781050826813 682749552250792894060055)
                    ·
                      rfl

theorem cell22_1994475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 3].length) (baseStart_1994475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994475 prefixEnd_1994475 := by exact prefixLift 1994475
  have htrace : WordTrace (prefixWord ++ tailWord_1994475) baseStart_1994475 baseEnd_1994475 := by
    simpa [prefixWord, tailWord_1994475, baseEnd_1994475] using wordTrace_append hprefix tailTrace_1994475
  have hstable : (prefixWord ++ tailWord_1994475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994475).length < 2 ^ (prefixWord ++ tailWord_1994475).sum := by decide
  have hdescent : baseEnd_1994475 < baseStart_1994475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994550 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1994550 : Nat := 118140960795 + 1994550 * 2 ^ 59
def prefixEnd_1994550 : Nat := 4983230072969 + 3 ^ 40 * 1994550 * 2
def baseEnd_1994550 : Nat := 227591742094505899478275

theorem tailTrace_1994550 : CollatzResearch.WordTrace tailWord_1994550 prefixEnd_1994550 227591742094505899478275 := by
  unfold tailWord_1994550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546700932755841679075819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48498143282728977910142069 4546700932755841679075819)
  ·
    refine ⟨6820051399133762518613729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4546700932755841679075819 6820051399133762518613729)
    ·
      refine ⟨5115038549350321888960297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6820051399133762518613729 5115038549350321888960297)
      ·
        refine ⟨3836278912012741416720223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5115038549350321888960297 3836278912012741416720223)
        ·
          refine ⟨5754418368019112125080335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3836278912012741416720223 5754418368019112125080335)
          ·
            refine ⟨8631627552028668187620503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5754418368019112125080335 8631627552028668187620503)
            ·
              refine ⟨12947441328043002281430755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631627552028668187620503 12947441328043002281430755)
              ·
                refine ⟨19421161992064503422146133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12947441328043002281430755 19421161992064503422146133)
                ·
                  refine ⟨227591742094505899478275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19421161992064503422146133 227591742094505899478275)
                  ·
                    rfl

theorem cell22_1994550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1994550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994550 prefixEnd_1994550 := by exact prefixLift 1994550
  have htrace : WordTrace (prefixWord ++ tailWord_1994550) baseStart_1994550 baseEnd_1994550 := by
    simpa [prefixWord, tailWord_1994550, baseEnd_1994550] using wordTrace_append hprefix tailTrace_1994550
  have hstable : (prefixWord ++ tailWord_1994550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994550).length < 2 ^ (prefixWord ++ tailWord_1994550).sum := by decide
  have hdescent : baseEnd_1994550 < baseStart_1994550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994563 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 1, 6]
def baseStart_1994563 : Nat := 118140960795 + 1994563 * 2 ^ 59
def prefixEnd_1994563 : Nat := 4983230072969 + 3 ^ 40 * 1994563 * 2
def baseEnd_1994563 : Nat := 682779676449189997859785

theorem tailTrace_1994563 : CollatzResearch.WordTrace tailWord_1994563 prefixEnd_1994563 682779676449189997859785 := by
  unfold tailWord_1994563
  simp only [CollatzResearch.WordTrace]
  refine ⟨72747689073046370085436343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48498459382030913390290895 72747689073046370085436343)
  ·
    refine ⟨109121533609569555128154515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72747689073046370085436343 109121533609569555128154515)
    ·
      refine ⟨163682300414354332692231773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109121533609569555128154515 163682300414354332692231773)
      ·
        refine ⟨61380862655382874759586915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163682300414354332692231773 61380862655382874759586915)
        ·
          refine ⟨92071293983074312139380373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61380862655382874759586915 92071293983074312139380373)
          ·
            refine ⟨4315841905456608381533455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92071293983074312139380373 4315841905456608381533455)
            ·
              refine ⟨6473762858184912572300183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4315841905456608381533455 6473762858184912572300183)
              ·
                refine ⟨9710644287277368858450275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473762858184912572300183 9710644287277368858450275)
                ·
                  refine ⟨14565966430916053287675413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710644287277368858450275 14565966430916053287675413)
                  ·
                    refine ⟨682779676449189997859785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14565966430916053287675413 682779676449189997859785)
                    ·
                      rfl

theorem cell22_1994563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_1994563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994563 prefixEnd_1994563 := by exact prefixLift 1994563
  have htrace : WordTrace (prefixWord ++ tailWord_1994563) baseStart_1994563 baseEnd_1994563 := by
    simpa [prefixWord, tailWord_1994563, baseEnd_1994563] using wordTrace_append hprefix tailTrace_1994563
  have hstable : (prefixWord ++ tailWord_1994563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994563).length < 2 ^ (prefixWord ++ tailWord_1994563).sum := by decide
  have hdescent : baseEnd_1994563 < baseStart_1994563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994578 : List Nat := [3, 2, 2, 1, 1, 4, 9]
def baseStart_1994578 : Nat := 118140960795 + 1994578 * 2 ^ 59
def prefixEnd_1994578 : Nat := 4983230072969 + 3 ^ 40 * 1994578 * 2
def baseEnd_1994578 : Nat := 25288326342804998471657

theorem tailTrace_1994578 : CollatzResearch.WordTrace tailWord_1994578 prefixEnd_1994578 25288326342804998471657 := by
  unfold tailWord_1994578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18187059041998006911808097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48498824111994685098154925 18187059041998006911808097)
  ·
    refine ⟨13640294281498505183856073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18187059041998006911808097 13640294281498505183856073)
    ·
      refine ⟨10230220711123878887892055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13640294281498505183856073 10230220711123878887892055)
      ·
        refine ⟨15345331066685818331838083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10230220711123878887892055 15345331066685818331838083)
        ·
          refine ⟨23017996600028727497757125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15345331066685818331838083 23017996600028727497757125)
          ·
            refine ⟨4315874362505386405829461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23017996600028727497757125 4315874362505386405829461)
            ·
              refine ⟨25288326342804998471657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4315874362505386405829461 25288326342804998471657)
              ·
                rfl

theorem cell22_1994578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 9].length) (baseStart_1994578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994578 prefixEnd_1994578 := by exact prefixLift 1994578
  have htrace : WordTrace (prefixWord ++ tailWord_1994578) baseStart_1994578 baseEnd_1994578 := by
    simpa [prefixWord, tailWord_1994578, baseEnd_1994578] using wordTrace_append hprefix tailTrace_1994578
  have hstable : (prefixWord ++ tailWord_1994578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994578).length < 2 ^ (prefixWord ++ tailWord_1994578).sum := by decide
  have hdescent : baseEnd_1994578 < baseStart_1994578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994644 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1994644 : Nat := 118140960795 + 1994644 * 2 ^ 59
def prefixEnd_1994644 : Nat := 4983230072969 + 3 ^ 40 * 1994644 * 2
def baseEnd_1994644 : Nat := 682807404404532786584537

theorem tailTrace_1994644 : CollatzResearch.WordTrace tailWord_1994644 prefixEnd_1994644 682807404404532786584537 := by
  unfold tailWord_1994644
  simp only [CollatzResearch.WordTrace]
  refine ⟨36375321692876460459567493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48500428923835280612756657 36375321692876460459567493)
  ·
    refine ⟨6820372817414336336168905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36375321692876460459567493 6820372817414336336168905)
    ·
      refine ⟨5115279613060752252126679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6820372817414336336168905 5115279613060752252126679)
      ·
        refine ⟨7672919419591128378190019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115279613060752252126679 7672919419591128378190019)
        ·
          refine ⟨11509379129386692567285029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672919419591128378190019 11509379129386692567285029)
          ·
            refine ⟨2158008586760004856365943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11509379129386692567285029 2158008586760004856365943)
            ·
              refine ⟨3237012880140007284548915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158008586760004856365943 3237012880140007284548915)
              ·
                refine ⟨4855519320210010926823373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237012880140007284548915 4855519320210010926823373)
                ·
                  refine ⟨1820819745078754097558765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4855519320210010926823373 1820819745078754097558765)
                  ·
                    refine ⟨682807404404532786584537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1820819745078754097558765 682807404404532786584537)
                    ·
                      rfl

theorem cell22_1994644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1994644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994644 prefixEnd_1994644 := by exact prefixLift 1994644
  have htrace : WordTrace (prefixWord ++ tailWord_1994644) baseStart_1994644 baseEnd_1994644 := by
    simpa [prefixWord, tailWord_1994644, baseEnd_1994644] using wordTrace_append hprefix tailTrace_1994644
  have hstable : (prefixWord ++ tailWord_1994644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994644).length < 2 ^ (prefixWord ++ tailWord_1994644).sum := by decide
  have hdescent : baseEnd_1994644 < baseStart_1994644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994657 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 5]
def baseStart_1994657 : Nat := 118140960795 + 1994657 * 2 ^ 59
def prefixEnd_1994657 : Nat := 4983230072969 + 3 ^ 40 * 1994657 * 2
def baseEnd_1994657 : Nat := 227603951523401695336499

theorem tailTrace_1994657 : CollatzResearch.WordTrace tailWord_1994657 prefixEnd_1994657 227603951523401695336499 := by
  unfold tailWord_1994657
  simp only [CollatzResearch.WordTrace]
  refine ⟨72751117534705824139358225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48500745023137216092905483 72751117534705824139358225)
  ·
    refine ⟨54563338151029368104518669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72751117534705824139358225 54563338151029368104518669)
    ·
      refine ⟨20461251806636013039194501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54563338151029368104518669 20461251806636013039194501)
      ·
        refine ⟨3836484713744252444848969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20461251806636013039194501 3836484713744252444848969)
        ·
          refine ⟨2877363535308189333636727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3836484713744252444848969 2877363535308189333636727)
          ·
            refine ⟨4316045302962284000455091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877363535308189333636727 4316045302962284000455091)
            ·
              refine ⟨6474067954443426000682637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316045302962284000455091 6474067954443426000682637)
              ·
                refine ⟨2427775482916284750255989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6474067954443426000682637 2427775482916284750255989)
                ·
                  refine ⟨227603951523401695336499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2427775482916284750255989 227603951523401695336499)
                  ·
                    rfl

theorem cell22_1994657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_1994657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994657 prefixEnd_1994657 := by exact prefixLift 1994657
  have htrace : WordTrace (prefixWord ++ tailWord_1994657) baseStart_1994657 baseEnd_1994657 := by
    simpa [prefixWord, tailWord_1994657, baseEnd_1994657] using wordTrace_append hprefix tailTrace_1994657
  have hstable : (prefixWord ++ tailWord_1994657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994657).length < 2 ^ (prefixWord ++ tailWord_1994657).sum := by decide
  have hdescent : baseEnd_1994657 < baseStart_1994657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994683 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 3, 5]
def baseStart_1994683 : Nat := 118140960795 + 1994683 * 2 ^ 59
def prefixEnd_1994683 : Nat := 4983230072969 + 3 ^ 40 * 1994683 * 2
def baseEnd_1994683 : Nat := 682820754901549684859417

theorem tailTrace_1994683 : CollatzResearch.WordTrace tailWord_1994683 prefixEnd_1994683 682820754901549684859417 := by
  unfold tailWord_1994683
  simp only [CollatzResearch.WordTrace]
  refine ⟨72752065832611630579804703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48501377221741087053203135 72752065832611630579804703)
  ·
    refine ⟨109128098748917445869707055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72752065832611630579804703 109128098748917445869707055)
    ·
      refine ⟨163692148123376168804560583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109128098748917445869707055 163692148123376168804560583)
      ·
        refine ⟨245538222185064253206840875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163692148123376168804560583 245538222185064253206840875)
        ·
          refine ⟨368307333277596379810261313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245538222185064253206840875 368307333277596379810261313)
          ·
            refine ⟨276230499958197284857695985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368307333277596379810261313 276230499958197284857695985)
            ·
              refine ⟨207172874968647963643271989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276230499958197284857695985 207172874968647963643271989)
              ·
                refine ⟨19422457028310746591556749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207172874968647963643271989 19422457028310746591556749)
                ·
                  refine ⟨7283421385616529971833781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19422457028310746591556749 7283421385616529971833781)
                  ·
                    refine ⟨682820754901549684859417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7283421385616529971833781 682820754901549684859417)
                    ·
                      rfl

theorem cell22_1994683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_1994683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994683 prefixEnd_1994683 := by exact prefixLift 1994683
  have htrace : WordTrace (prefixWord ++ tailWord_1994683) baseStart_1994683 baseEnd_1994683 := by
    simpa [prefixWord, tailWord_1994683, baseEnd_1994683] using wordTrace_append hprefix tailTrace_1994683
  have hstable : (prefixWord ++ tailWord_1994683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994683).length < 2 ^ (prefixWord ++ tailWord_1994683).sum := by decide
  have hdescent : baseEnd_1994683 < baseStart_1994683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994687 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 1, 4]
def baseStart_1994687 : Nat := 118140960795 + 1994687 * 2 ^ 59
def prefixEnd_1994687 : Nat := 4983230072969 + 3 ^ 40 * 1994687 * 2
def baseEnd_1994687 : Nat := 682822124183295007759405

theorem tailTrace_1994687 : CollatzResearch.WordTrace tailWord_1994687 prefixEnd_1994687 682822124183295007759405 := by
  unfold tailWord_1994687
  simp only [CollatzResearch.WordTrace]
  refine ⟨72752211724597139262950315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48501474483064759508633543 72752211724597139262950315)
  ·
    refine ⟨109128317586895708894425473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72752211724597139262950315 109128317586895708894425473)
    ·
      refine ⟨81846238190171781670819105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109128317586895708894425473 81846238190171781670819105)
      ·
        refine ⟨61384678642628836253114329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81846238190171781670819105 61384678642628836253114329)
        ·
          refine ⟨46038508981971627189835747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61384678642628836253114329 46038508981971627189835747)
          ·
            refine ⟨69057763472957440784753621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46038508981971627189835747 69057763472957440784753621)
            ·
              refine ⟨1618541331397440018392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69057763472957440784753621 1618541331397440018392663)
              ·
                refine ⟨2427811997096160027588995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618541331397440018392663 2427811997096160027588995)
                ·
                  refine ⟨3641717995644240041383493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427811997096160027588995 3641717995644240041383493)
                  ·
                    refine ⟨682822124183295007759405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3641717995644240041383493 682822124183295007759405)
                    ·
                      rfl

theorem cell22_1994687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_1994687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994687 prefixEnd_1994687 := by exact prefixLift 1994687
  have htrace : WordTrace (prefixWord ++ tailWord_1994687) baseStart_1994687 baseEnd_1994687 := by
    simpa [prefixWord, tailWord_1994687, baseEnd_1994687] using wordTrace_append hprefix tailTrace_1994687
  have hstable : (prefixWord ++ tailWord_1994687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994687).length < 2 ^ (prefixWord ++ tailWord_1994687).sum := by decide
  have hdescent : baseEnd_1994687 < baseStart_1994687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994702 : List Nat := [4, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_1994702 : Nat := 118140960795 + 1994702 * 2 ^ 59
def prefixEnd_1994702 : Nat := 4983230072969 + 3 ^ 40 * 1994702 * 2
def baseEnd_1994702 : Nat := 227609086329946656211453

theorem tailTrace_1994702 : CollatzResearch.WordTrace tailWord_1994702 prefixEnd_1994702 227609086329946656211453 := by
  unfold tailWord_1994702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9094094852442849603093295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48501839213028531216497573 9094094852442849603093295)
  ·
    refine ⟨13641142278664274404639943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9094094852442849603093295 13641142278664274404639943)
    ·
      refine ⟨20461713417996411606959915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13641142278664274404639943 20461713417996411606959915)
      ·
        refine ⟨30692570126994617410439873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20461713417996411606959915 30692570126994617410439873)
        ·
          refine ⟨23019427595245963057829905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30692570126994617410439873 23019427595245963057829905)
          ·
            refine ⟨17264570696434472293372429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23019427595245963057829905 17264570696434472293372429)
            ·
              refine ⟨6474214011162927110014661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17264570696434472293372429 6474214011162927110014661)
              ·
                refine ⟨1213915127093048833127749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6474214011162927110014661 1213915127093048833127749)
                ·
                  refine ⟨227609086329946656211453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213915127093048833127749 227609086329946656211453)
                  ·
                    rfl

theorem cell22_1994702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_1994702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994702 prefixEnd_1994702 := by exact prefixLift 1994702
  have htrace : WordTrace (prefixWord ++ tailWord_1994702) baseStart_1994702 baseEnd_1994702 := by
    simpa [prefixWord, tailWord_1994702, baseEnd_1994702] using wordTrace_append hprefix tailTrace_1994702
  have hstable : (prefixWord ++ tailWord_1994702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994702).length < 2 ^ (prefixWord ++ tailWord_1994702).sum := by decide
  have hdescent : baseEnd_1994702 < baseStart_1994702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994852 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1994852 : Nat := 118140960795 + 1994852 * 2 ^ 59
def prefixEnd_1994852 : Nat := 4983230072969 + 3 ^ 40 * 1994852 * 2
def baseEnd_1994852 : Nat := 682878607055289577383899

theorem tailTrace_1994852 : CollatzResearch.WordTrace tailWord_1994852 prefixEnd_1994852 682878607055289577383899 := by
  unfold tailWord_1994852
  simp only [CollatzResearch.WordTrace]
  refine ⟨36379114884499686221353405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48505486512666248295137873 36379114884499686221353405)
  ·
    refine ⟨13642168081687382333007527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36379114884499686221353405 13642168081687382333007527)
    ·
      refine ⟨20463252122531073499511291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13642168081687382333007527 20463252122531073499511291)
      ·
        refine ⟨30694878183796610249266937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463252122531073499511291 30694878183796610249266937)
        ·
          refine ⟨23021158637847457686950203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30694878183796610249266937 23021158637847457686950203)
          ·
            refine ⟨34531737956771186530425305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23021158637847457686950203 34531737956771186530425305)
            ·
              refine ⟨25898803467578389897818979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34531737956771186530425305 25898803467578389897818979)
              ·
                refine ⟨38848205201367584846728469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25898803467578389897818979 38848205201367584846728469)
                ·
                  refine ⟨1821009618814105539690397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38848205201367584846728469 1821009618814105539690397)
                  ·
                    refine ⟨682878607055289577383899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1821009618814105539690397 682878607055289577383899)
                    ·
                      rfl

theorem cell22_1994852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1994852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994852 prefixEnd_1994852 := by exact prefixLift 1994852
  have htrace : WordTrace (prefixWord ++ tailWord_1994852) baseStart_1994852 baseEnd_1994852 := by
    simpa [prefixWord, tailWord_1994852, baseEnd_1994852] using wordTrace_append hprefix tailTrace_1994852
  have hstable : (prefixWord ++ tailWord_1994852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994852).length < 2 ^ (prefixWord ++ tailWord_1994852).sum := by decide
  have hdescent : baseEnd_1994852 < baseStart_1994852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994871 : List Nat := [1, 1, 3, 1, 1, 7, 2, 2, 4]
def baseStart_1994871 : Nat := 118140960795 + 1994871 * 2 ^ 59
def prefixEnd_1994871 : Nat := 4983230072969 + 3 ^ 40 * 1994871 * 2
def baseEnd_1994871 : Nat := 227628370381193287052947

theorem tailTrace_1994871 : CollatzResearch.WordTrace tailWord_1994871 prefixEnd_1994871 227628370381193287052947 := by
  unfold tailWord_1994871
  simp only [CollatzResearch.WordTrace]
  refine ⟨72758922755930538687648467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48505948503953692458432311 72758922755930538687648467)
  ·
    refine ⟨109138384133895808031472701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72758922755930538687648467 109138384133895808031472701)
    ·
      refine ⟨40926894050210928011802263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109138384133895808031472701 40926894050210928011802263)
      ·
        refine ⟨61390341075316392017703395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40926894050210928011802263 61390341075316392017703395)
        ·
          refine ⟨92085511612974588026555093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61390341075316392017703395 92085511612974588026555093)
          ·
            refine ⟨2158254178429091906872385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92085511612974588026555093 2158254178429091906872385)
            ·
              refine ⟨1618690633821818930154289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158254178429091906872385 1618690633821818930154289)
              ·
                refine ⟨1214017975366364197615717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618690633821818930154289 1214017975366364197615717)
                ·
                  refine ⟨227628370381193287052947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1214017975366364197615717 227628370381193287052947)
                  ·
                    rfl

theorem cell22_1994871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 4].length) (baseStart_1994871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994871 prefixEnd_1994871 := by exact prefixLift 1994871
  have htrace : WordTrace (prefixWord ++ tailWord_1994871) baseStart_1994871 baseEnd_1994871 := by
    simpa [prefixWord, tailWord_1994871, baseEnd_1994871] using wordTrace_append hprefix tailTrace_1994871
  have hstable : (prefixWord ++ tailWord_1994871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994871).length < 2 ^ (prefixWord ++ tailWord_1994871).sum := by decide
  have hdescent : baseEnd_1994871 < baseStart_1994871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994880 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_1994880 : Nat := 118140960795 + 1994880 * 2 ^ 59
def prefixEnd_1994880 : Nat := 4983230072969 + 3 ^ 40 * 1994880 * 2
def baseEnd_1994880 : Nat := 682888192027506837683813

theorem tailTrace_1994880 : CollatzResearch.WordTrace tailWord_1994880 prefixEnd_1994880 682888192027506837683813 := by
  unfold tailWord_1994880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36379625506448966612363047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48506167341931955483150729 36379625506448966612363047)
  ·
    refine ⟨54569438259673449918544571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36379625506448966612363047 54569438259673449918544571)
    ·
      refine ⟨81854157389510174877816857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54569438259673449918544571 81854157389510174877816857)
      ·
        refine ⟨61390618042132631158362643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81854157389510174877816857 61390618042132631158362643)
        ·
          refine ⟨92085927063198946737543965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61390618042132631158362643 92085927063198946737543965)
          ·
            refine ⟨34532222648699605026578987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92085927063198946737543965 34532222648699605026578987)
            ·
              refine ⟨51798333973049407539868481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34532222648699605026578987 51798333973049407539868481)
              ·
                refine ⟨38848750479787055654901361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51798333973049407539868481 38848750479787055654901361)
                ·
                  refine ⟨29136562859840291741176021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38848750479787055654901361 29136562859840291741176021)
                  ·
                    refine ⟨682888192027506837683813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29136562859840291741176021 682888192027506837683813)
                    ·
                      rfl

theorem cell22_1994880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_1994880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994880 prefixEnd_1994880 := by exact prefixLift 1994880
  have htrace : WordTrace (prefixWord ++ tailWord_1994880) baseStart_1994880 baseEnd_1994880 := by
    simpa [prefixWord, tailWord_1994880, baseEnd_1994880] using wordTrace_append hprefix tailTrace_1994880
  have hstable : (prefixWord ++ tailWord_1994880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994880).length < 2 ^ (prefixWord ++ tailWord_1994880).sum := by decide
  have hdescent : baseEnd_1994880 < baseStart_1994880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994965 : List Nat := [1, 3, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_1994965 : Nat := 118140960795 + 1994965 * 2 ^ 59
def prefixEnd_1994965 : Nat := 4983230072969 + 3 ^ 40 * 1994965 * 2
def baseEnd_1994965 : Nat := 682917289264594949308553

theorem tailTrace_1994965 : CollatzResearch.WordTrace tailWord_1994965 prefixEnd_1994965 682917289264594949308553 := by
  unfold tailWord_1994965
  simp only [CollatzResearch.WordTrace]
  refine ⟨72762351217589992741570349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48508234145059995161046899 72762351217589992741570349)
  ·
    refine ⟨27285881706596247278088881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72762351217589992741570349 27285881706596247278088881)
    ·
      refine ⟨20464411279947185458566661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27285881706596247278088881 20464411279947185458566661)
      ·
        refine ⟨3837077114990097273481249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20464411279947185458566661 3837077114990097273481249)
        ·
          refine ⟨2877807836242572955110937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3837077114990097273481249 2877807836242572955110937)
          ·
            refine ⟨2158355877181929716333203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2877807836242572955110937 2158355877181929716333203)
            ·
              refine ⟨3237533815772894574499805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158355877181929716333203 3237533815772894574499805)
              ·
                refine ⟨1214075180914835465437427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237533815772894574499805 1214075180914835465437427)
                ·
                  refine ⟨1821112771372253198156141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214075180914835465437427 1821112771372253198156141)
                  ·
                    refine ⟨682917289264594949308553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1821112771372253198156141 682917289264594949308553)
                    ·
                      rfl

theorem cell22_1994965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_1994965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1994965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1994965 prefixEnd_1994965 := by exact prefixLift 1994965
  have htrace : WordTrace (prefixWord ++ tailWord_1994965) baseStart_1994965 baseEnd_1994965 := by
    simpa [prefixWord, tailWord_1994965, baseEnd_1994965] using wordTrace_append hprefix tailTrace_1994965
  have hstable : (prefixWord ++ tailWord_1994965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994965).length < 2 ^ (prefixWord ++ tailWord_1994965).sum := by decide
  have hdescent : baseEnd_1994965 < baseStart_1994965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995017 : List Nat := [1, 2, 1, 1, 3, 4, 2, 8]
def baseStart_1995017 : Nat := 118140960795 + 1995017 * 2 ^ 59
def prefixEnd_1995017 : Nat := 4983230072969 + 3 ^ 40 * 1995017 * 2
def baseEnd_1995017 : Nat := 75881676658587127445377

theorem tailTrace_1995017 : CollatzResearch.WordTrace tailWord_1995017 prefixEnd_1995017 75881676658587127445377 := by
  unfold tailWord_1995017
  simp only [CollatzResearch.WordTrace]
  refine ⟨72764247813401605622463305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48509498542267737081642203 72764247813401605622463305)
  ·
    refine ⟨54573185860051204216847479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72764247813401605622463305 54573185860051204216847479)
    ·
      refine ⟨81859778790076806325271219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54573185860051204216847479 81859778790076806325271219)
      ·
        refine ⟨122789668185115209487906829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81859778790076806325271219 122789668185115209487906829)
        ·
          refine ⟨46046125569418203557965061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122789668185115209487906829 46046125569418203557965061)
          ·
            refine ⟨8633648544265913167118449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46046125569418203557965061 8633648544265913167118449)
            ·
              refine ⟨6475236408199434875338837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8633648544265913167118449 6475236408199434875338837)
              ·
                refine ⟨75881676658587127445377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6475236408199434875338837 75881676658587127445377)
                ·
                  rfl

theorem cell22_1995017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 8].length) (baseStart_1995017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995017 prefixEnd_1995017 := by exact prefixLift 1995017
  have htrace : WordTrace (prefixWord ++ tailWord_1995017) baseStart_1995017 baseEnd_1995017 := by
    simpa [prefixWord, tailWord_1995017, baseEnd_1995017] using wordTrace_append hprefix tailTrace_1995017
  have hstable : (prefixWord ++ tailWord_1995017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995017).length < 2 ^ (prefixWord ++ tailWord_1995017).sum := by decide
  have hdescent : baseEnd_1995017 < baseStart_1995017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995019 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 2, 4]
def baseStart_1995019 : Nat := 118140960795 + 1995019 * 2 ^ 59
def prefixEnd_1995019 : Nat := 4983230072969 + 3 ^ 40 * 1995019 * 2
def baseEnd_1995019 : Nat := 682935774568156808458387

theorem tailTrace_1995019 : CollatzResearch.WordTrace tailWord_1995019 prefixEnd_1995019 682935774568156808458387 := by
  unfold tailWord_1995019
  simp only [CollatzResearch.WordTrace]
  refine ⟨72764320759394359964036111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48509547172929573309357407 72764320759394359964036111)
  ·
    refine ⟨109146481139091539946054167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72764320759394359964036111 109146481139091539946054167)
    ·
      refine ⟨163719721708637309919081251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109146481139091539946054167 163719721708637309919081251)
      ·
        refine ⟨245579582562955964878621877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163719721708637309919081251 245579582562955964878621877)
        ·
          refine ⟨23023085865277121707370801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245579582562955964878621877 23023085865277121707370801)
          ·
            refine ⟨17267314398957841280528101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23023085865277121707370801 17267314398957841280528101)
            ·
              refine ⟨3237621449804595240099019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17267314398957841280528101 3237621449804595240099019)
              ·
                refine ⟨4856432174706892860148529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237621449804595240099019 4856432174706892860148529)
                ·
                  refine ⟨3642324131030169645111397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4856432174706892860148529 3642324131030169645111397)
                  ·
                    refine ⟨682935774568156808458387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3642324131030169645111397 682935774568156808458387)
                    ·
                      rfl

theorem cell22_1995019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4].length) (baseStart_1995019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995019 prefixEnd_1995019 := by exact prefixLift 1995019
  have htrace : WordTrace (prefixWord ++ tailWord_1995019) baseStart_1995019 baseEnd_1995019 := by
    simpa [prefixWord, tailWord_1995019, baseEnd_1995019] using wordTrace_append hprefix tailTrace_1995019
  have hstable : (prefixWord ++ tailWord_1995019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995019).length < 2 ^ (prefixWord ++ tailWord_1995019).sum := by decide
  have hdescent : baseEnd_1995019 < baseStart_1995019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995034 : List Nat := [3, 1, 1, 3, 5, 9]
def baseStart_1995034 : Nat := 118140960795 + 1995034 * 2 ^ 59
def prefixEnd_1995034 : Nat := 4983230072969 + 3 ^ 40 * 1995034 * 2
def baseEnd_1995034 : Nat := 8431369251539528016461

theorem tailTrace_1995034 : CollatzResearch.WordTrace tailWord_1995034 prefixEnd_1995034 8431369251539528016461 := by
  unfold tailWord_1995034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18191216963585004381458039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48509911902893345017221437 18191216963585004381458039)
  ·
    refine ⟨27286825445377506572187059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18191216963585004381458039 27286825445377506572187059)
    ·
      refine ⟨40930238168066259858280589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27286825445377506572187059 40930238168066259858280589)
      ·
        refine ⟨15348839313024847446855221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40930238168066259858280589 15348839313024847446855221)
        ·
          refine ⟨1438953685596079448142677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15348839313024847446855221 1438953685596079448142677)
          ·
            refine ⟨8431369251539528016461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1438953685596079448142677 8431369251539528016461)
            ·
              rfl

theorem cell22_1995034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 9].length) (baseStart_1995034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995034 prefixEnd_1995034 := by exact prefixLift 1995034
  have htrace : WordTrace (prefixWord ++ tailWord_1995034) baseStart_1995034 baseEnd_1995034 := by
    simpa [prefixWord, tailWord_1995034, baseEnd_1995034] using wordTrace_append hprefix tailTrace_1995034
  have hstable : (prefixWord ++ tailWord_1995034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995034).length < 2 ^ (prefixWord ++ tailWord_1995034).sum := by decide
  have hdescent : baseEnd_1995034 < baseStart_1995034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995066 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_1995066 : Nat := 118140960795 + 1995066 * 2 ^ 59
def prefixEnd_1995066 : Nat := 4983230072969 + 3 ^ 40 * 1995066 * 2
def baseEnd_1995066 : Nat := 682951863628664352533243

theorem tailTrace_1995066 : CollatzResearch.WordTrace tailWord_1995066 prefixEnd_1995066 682951863628664352533243 := by
  unfold tailWord_1995066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18191508747556021747749263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48510689993482724660664701 18191508747556021747749263)
  ·
    refine ⟨27287263121334032621623895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18191508747556021747749263 27287263121334032621623895)
    ·
      refine ⟨40930894682001048932435843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27287263121334032621623895 40930894682001048932435843)
      ·
        refine ⟨61396342023001573398653765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40930894682001048932435843 61396342023001573398653765)
        ·
          refine ⟨11511814129312795012247581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61396342023001573398653765 11511814129312795012247581)
          ·
            refine ⟨4316930298492298129592843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11511814129312795012247581 4316930298492298129592843)
            ·
              refine ⟨6475395447738447194389265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316930298492298129592843 6475395447738447194389265)
              ·
                refine ⟨4856546585803835395791949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6475395447738447194389265 4856546585803835395791949)
                ·
                  refine ⟨1821204969676438273421981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4856546585803835395791949 1821204969676438273421981)
                  ·
                    refine ⟨682951863628664352533243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1821204969676438273421981 682951863628664352533243)
                    ·
                      rfl

theorem cell22_1995066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_1995066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995066 prefixEnd_1995066 := by exact prefixLift 1995066
  have htrace : WordTrace (prefixWord ++ tailWord_1995066) baseStart_1995066 baseEnd_1995066 := by
    simpa [prefixWord, tailWord_1995066, baseEnd_1995066] using wordTrace_append hprefix tailTrace_1995066
  have hstable : (prefixWord ++ tailWord_1995066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995066).length < 2 ^ (prefixWord ++ tailWord_1995066).sum := by decide
  have hdescent : baseEnd_1995066 < baseStart_1995066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995100 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1995100 : Nat := 118140960795 + 1995100 * 2 ^ 59
def prefixEnd_1995100 : Nat := 4983230072969 + 3 ^ 40 * 1995100 * 2
def baseEnd_1995100 : Nat := 682963502523499597183139

theorem tailTrace_1995100 : CollatzResearch.WordTrace tailWord_1995100 prefixEnd_1995100 682963502523499597183139 := by
  unfold tailWord_1995100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36383637536050455398867377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48511516714733940531823169 36383637536050455398867377)
  ·
    refine ⟨27287728152037841549150533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36383637536050455398867377 27287728152037841549150533)
    ·
      refine ⟨5116449028507095290465725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27287728152037841549150533 5116449028507095290465725)
      ·
        refine ⟨1918668385690160733924647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5116449028507095290465725 1918668385690160733924647)
        ·
          refine ⟨2878002578535241100886971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918668385690160733924647 2878002578535241100886971)
          ·
            refine ⟨4317003867802861651330457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878002578535241100886971 4317003867802861651330457)
            ·
              refine ⟨3237752900852146238497843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4317003867802861651330457 3237752900852146238497843)
              ·
                refine ⟨4856629351278219357746765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237752900852146238497843 4856629351278219357746765)
                ·
                  refine ⟨1821236006729332259155037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4856629351278219357746765 1821236006729332259155037)
                  ·
                    refine ⟨682963502523499597183139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1821236006729332259155037 682963502523499597183139)
                    ·
                      rfl

theorem cell22_1995100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1995100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995100 prefixEnd_1995100 := by exact prefixLift 1995100
  have htrace : WordTrace (prefixWord ++ tailWord_1995100) baseStart_1995100 baseEnd_1995100 := by
    simpa [prefixWord, tailWord_1995100, baseEnd_1995100] using wordTrace_append hprefix tailTrace_1995100
  have hstable : (prefixWord ++ tailWord_1995100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995100).length < 2 ^ (prefixWord ++ tailWord_1995100).sum := by decide
  have hdescent : baseEnd_1995100 < baseStart_1995100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995231 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 5]
def baseStart_1995231 : Nat := 118140960795 + 1995231 * 2 ^ 59
def prefixEnd_1995231 : Nat := 4983230072969 + 3 ^ 40 * 1995231 * 2
def baseEnd_1995231 : Nat := 227669448833552974052579

theorem tailTrace_1995231 : CollatzResearch.WordTrace tailWord_1995231 prefixEnd_1995231 227669448833552974052579 := by
  unfold tailWord_1995231
  simp only [CollatzResearch.WordTrace]
  refine ⟨72772053034626320170753547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48514702023084213447169031 72772053034626320170753547)
  ·
    refine ⟨109158079551939480256130321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72772053034626320170753547 109158079551939480256130321)
    ·
      refine ⟨81868559663954610192097741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109158079551939480256130321 81868559663954610192097741)
      ·
        refine ⟨30700709873982978822036653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81868559663954610192097741 30700709873982978822036653)
        ·
          refine ⟨11512766202743617058263745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30700709873982978822036653 11512766202743617058263745)
          ·
            refine ⟨8634574652057712793697809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11512766202743617058263745 8634574652057712793697809)
            ·
              refine ⟨6475930989043284595273357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8634574652057712793697809 6475930989043284595273357)
              ·
                refine ⟨2428474120891231723227509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6475930989043284595273357 2428474120891231723227509)
                ·
                  refine ⟨227669448833552974052579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2428474120891231723227509 227669448833552974052579)
                  ·
                    rfl

theorem cell22_1995231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 5].length) (baseStart_1995231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995231 prefixEnd_1995231 := by exact prefixLift 1995231
  have htrace : WordTrace (prefixWord ++ tailWord_1995231) baseStart_1995231 baseEnd_1995231 := by
    simpa [prefixWord, tailWord_1995231, baseEnd_1995231] using wordTrace_append hprefix tailTrace_1995231
  have hstable : (prefixWord ++ tailWord_1995231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995231).length < 2 ^ (prefixWord ++ tailWord_1995231).sum := by decide
  have hdescent : baseEnd_1995231 < baseStart_1995231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995276 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 6]
def baseStart_1995276 : Nat := 118140960795 + 1995276 * 2 ^ 59
def prefixEnd_1995276 : Nat := 4983230072969 + 3 ^ 40 * 1995276 * 2
def baseEnd_1995276 : Nat := 227674583640097934927533

theorem tailTrace_1995276 : CollatzResearch.WordTrace tailWord_1995276 prefixEnd_1995276 227674583640097934927533 := by
  unfold tailWord_1995276
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386847159731646428070841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48515796212975528570761121 36386847159731646428070841)
  ·
    refine ⟨27290135369798734821053131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36386847159731646428070841 27290135369798734821053131)
    ·
      refine ⟨40935203054698102231579697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27290135369798734821053131 40935203054698102231579697)
      ·
        refine ⟨30701402291023576673684773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40935203054698102231579697 30701402291023576673684773)
        ·
          refine ⟨5756512929566920626315895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30701402291023576673684773 5756512929566920626315895)
          ·
            refine ⟨8634769394350380939473843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756512929566920626315895 8634769394350380939473843)
            ·
              refine ⟨12952154091525571409210765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634769394350380939473843 12952154091525571409210765)
              ·
                refine ⟨4857057784322089278454037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12952154091525571409210765 4857057784322089278454037)
                ·
                  refine ⟨227674583640097934927533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4857057784322089278454037 227674583640097934927533)
                  ·
                    rfl

theorem cell22_1995276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_1995276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995276 prefixEnd_1995276 := by exact prefixLift 1995276
  have htrace : WordTrace (prefixWord ++ tailWord_1995276) baseStart_1995276 baseEnd_1995276 := by
    simpa [prefixWord, tailWord_1995276, baseEnd_1995276] using wordTrace_append hprefix tailTrace_1995276
  have hstable : (prefixWord ++ tailWord_1995276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995276).length < 2 ^ (prefixWord ++ tailWord_1995276).sum := by decide
  have hdescent : baseEnd_1995276 < baseStart_1995276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995411 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 6]
def baseStart_1995411 : Nat := 118140960795 + 1995411 * 2 ^ 59
def prefixEnd_1995411 : Nat := 4983230072969 + 3 ^ 40 * 1995411 * 2
def baseEnd_1995411 : Nat := 227689988059732817552395

theorem tailTrace_1995411 : CollatzResearch.WordTrace tailWord_1995411 prefixEnd_1995411 227689988059732817552395 := by
  unfold tailWord_1995411
  simp only [CollatzResearch.WordTrace]
  refine ⟨72778618173974210912306087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48519078782649473941537391 72778618173974210912306087)
  ·
    refine ⟨109167927260961316368459131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72778618173974210912306087 109167927260961316368459131)
    ·
      refine ⟨163751890891441974552688697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109167927260961316368459131 163751890891441974552688697)
      ·
        refine ⟨122813918168581480914516523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163751890891441974552688697 122813918168581480914516523)
        ·
          refine ⟨184220877252872221371774785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122813918168581480914516523 184220877252872221371774785)
          ·
            refine ⟨138165657939654166028831089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184220877252872221371774785 138165657939654166028831089)
            ·
              refine ⟨103624243454740624521623317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138165657939654166028831089 103624243454740624521623317)
              ·
                refine ⟨4857386411940966774451093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103624243454740624521623317 4857386411940966774451093)
                ·
                  refine ⟨227689988059732817552395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4857386411940966774451093 227689988059732817552395)
                  ·
                    rfl

theorem cell22_1995411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 6].length) (baseStart_1995411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995411 prefixEnd_1995411 := by exact prefixLift 1995411
  have htrace : WordTrace (prefixWord ++ tailWord_1995411) baseStart_1995411 baseEnd_1995411 := by
    simpa [prefixWord, tailWord_1995411, baseEnd_1995411] using wordTrace_append hprefix tailTrace_1995411
  have hstable : (prefixWord ++ tailWord_1995411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995411).length < 2 ^ (prefixWord ++ tailWord_1995411).sum := by decide
  have hdescent : baseEnd_1995411 < baseStart_1995411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995434 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_1995434 : Nat := 118140960795 + 1995434 * 2 ^ 59
def prefixEnd_1995434 : Nat := 4983230072969 + 3 ^ 40 * 1995434 * 2
def baseEnd_1995434 : Nat := 227692612516411353110705

theorem tailTrace_1995434 : CollatzResearch.WordTrace tailWord_1995434 prefixEnd_1995434 227692612516411353110705 := by
  unfold tailWord_1995434
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194864263222721460098339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48519638035260590560262237 18194864263222721460098339)
  ·
    refine ⟨27292296394834082190147509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18194864263222721460098339 27292296394834082190147509)
    ·
      refine ⟨2558652787015695205326329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27292296394834082190147509 2558652787015695205326329)
      ·
        refine ⟨1918989590261771403994747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2558652787015695205326329 1918989590261771403994747)
        ·
          refine ⟨2878484385392657105992121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918989590261771403994747 2878484385392657105992121)
          ·
            refine ⟨2158863289044492829494091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2878484385392657105992121 2158863289044492829494091)
            ·
              refine ⟨3238294933566739244241137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158863289044492829494091 3238294933566739244241137)
              ·
                refine ⟨2428721200175054433180853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3238294933566739244241137 2428721200175054433180853)
                ·
                  refine ⟨227692612516411353110705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2428721200175054433180853 227692612516411353110705)
                  ·
                    rfl

theorem cell22_1995434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_1995434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995434 prefixEnd_1995434 := by exact prefixLift 1995434
  have htrace : WordTrace (prefixWord ++ tailWord_1995434) baseStart_1995434 baseEnd_1995434 := by
    simpa [prefixWord, tailWord_1995434, baseEnd_1995434] using wordTrace_append hprefix tailTrace_1995434
  have hstable : (prefixWord ++ tailWord_1995434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995434).length < 2 ^ (prefixWord ++ tailWord_1995434).sum := by decide
  have hdescent : baseEnd_1995434 < baseStart_1995434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995445 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 6]
def baseStart_1995445 : Nat := 118140960795 + 1995445 * 2 ^ 59
def prefixEnd_1995445 : Nat := 4983230072969 + 3 ^ 40 * 1995445 * 2
def baseEnd_1995445 : Nat := 227693867691344565769027

theorem tailTrace_1995445 : CollatzResearch.WordTrace tailWord_1995445 prefixEnd_1995445 227693867691344565769027 := by
  unfold tailWord_1995445
  simp only [CollatzResearch.WordTrace]
  refine ⟨72779858255851034719043789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48519905503900689812695859 72779858255851034719043789)
  ·
    refine ⟨27292446845944138019641421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72779858255851034719043789 27292446845944138019641421)
    ·
      refine ⟨10234667567229051757365533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27292446845944138019641421 10234667567229051757365533)
      ·
        refine ⟨3838000337710894409012075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10234667567229051757365533 3838000337710894409012075)
        ·
          refine ⟨5757000506566341613518113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838000337710894409012075 5757000506566341613518113)
          ·
            refine ⟨4317750379924756210138585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5757000506566341613518113 4317750379924756210138585)
            ·
              refine ⟨3238312784943567157603939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4317750379924756210138585 3238312784943567157603939)
              ·
                refine ⟨4857469177415350736405909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238312784943567157603939 4857469177415350736405909)
                ·
                  refine ⟨227693867691344565769027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4857469177415350736405909 227693867691344565769027)
                  ·
                    rfl

theorem cell22_1995445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_1995445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995445 prefixEnd_1995445 := by exact prefixLift 1995445
  have htrace : WordTrace (prefixWord ++ tailWord_1995445) baseStart_1995445 baseEnd_1995445 := by
    simpa [prefixWord, tailWord_1995445, baseEnd_1995445] using wordTrace_append hprefix tailTrace_1995445
  have hstable : (prefixWord ++ tailWord_1995445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995445).length < 2 ^ (prefixWord ++ tailWord_1995445).sum := by decide
  have hdescent : baseEnd_1995445 < baseStart_1995445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995460 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1995460 : Nat := 118140960795 + 1995460 * 2 ^ 59
def prefixEnd_1995460 : Nat := 4983230072969 + 3 ^ 40 * 1995460 * 2
def baseEnd_1995460 : Nat := 683086737880578658182035

theorem tailTrace_1995460 : CollatzResearch.WordTrace tailWord_1995460 prefixEnd_1995460 683086737880578658182035 := by
  unfold tailWord_1995460
  simp only [CollatzResearch.WordTrace]
  refine ⟨36390202675398346140419917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48520270233864461520559889 36390202675398346140419917)
  ·
    refine ⟨13646326003274379802657469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36390202675398346140419917 13646326003274379802657469)
    ·
      refine ⟨5117372251227892425996551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13646326003274379802657469 5117372251227892425996551)
      ·
        refine ⟨7676058376841838638994827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5117372251227892425996551 7676058376841838638994827)
        ·
          refine ⟨11514087565262757958492241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7676058376841838638994827 11514087565262757958492241)
          ·
            refine ⟨8635565673947068468869181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11514087565262757958492241 8635565673947068468869181)
            ·
              refine ⟨3238337127730150675825943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8635565673947068468869181 3238337127730150675825943)
              ·
                refine ⟨4857505691595226013738915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238337127730150675825943 4857505691595226013738915)
                ·
                  refine ⟨7286258537392839020608373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857505691595226013738915 7286258537392839020608373)
                  ·
                    refine ⟨683086737880578658182035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7286258537392839020608373 683086737880578658182035)
                    ·
                      rfl

theorem cell22_1995460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1995460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995460 prefixEnd_1995460 := by exact prefixLift 1995460
  have htrace : WordTrace (prefixWord ++ tailWord_1995460) baseStart_1995460 baseEnd_1995460 := by
    simpa [prefixWord, tailWord_1995460, baseEnd_1995460] using wordTrace_append hprefix tailTrace_1995460
  have hstable : (prefixWord ++ tailWord_1995460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995460).length < 2 ^ (prefixWord ++ tailWord_1995460).sum := by decide
  have hdescent : baseEnd_1995460 < baseStart_1995460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995640 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 5, 3]
def baseStart_1995640 : Nat := 118140960795 + 1995640 * 2 ^ 59
def prefixEnd_1995640 : Nat := 4983230072969 + 3 ^ 40 * 1995640 * 2
def baseEnd_1995640 : Nat := 683148355559118188681483

theorem tailTrace_1995640 : CollatzResearch.WordTrace tailWord_1995640 prefixEnd_1995640 683148355559118188681483 := by
  unfold tailWord_1995640
  simp only [CollatzResearch.WordTrace]
  refine ⟨36393485245072291511196187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48524646993429722014928249 36393485245072291511196187)
  ·
    refine ⟨54590227867608437266794281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36393485245072291511196187 54590227867608437266794281)
    ·
      refine ⟨40942670900706327950095711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54590227867608437266794281 40942670900706327950095711)
      ·
        refine ⟨61414006351059491925143567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40942670900706327950095711 61414006351059491925143567)
        ·
          refine ⟨92121009526589237887715351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61414006351059491925143567 92121009526589237887715351)
          ·
            refine ⟨138181514289883856831573027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92121009526589237887715351 138181514289883856831573027)
            ·
              refine ⟨207272271434825785247359541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138181514289883856831573027 207272271434825785247359541)
              ·
                refine ⟨19431775447014917366939957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207272271434825785247359541 19431775447014917366939957)
                ·
                  refine ⟨1821728948157648503150621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19431775447014917366939957 1821728948157648503150621)
                  ·
                    refine ⟨683148355559118188681483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1821728948157648503150621 683148355559118188681483)
                    ·
                      rfl

theorem cell22_1995640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_1995640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995640 prefixEnd_1995640 := by exact prefixLift 1995640
  have htrace : WordTrace (prefixWord ++ tailWord_1995640) baseStart_1995640 baseEnd_1995640 := by
    simpa [prefixWord, tailWord_1995640, baseEnd_1995640] using wordTrace_append hprefix tailTrace_1995640
  have hstable : (prefixWord ++ tailWord_1995640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995640).length < 2 ^ (prefixWord ++ tailWord_1995640).sum := by decide
  have hdescent : baseEnd_1995640 < baseStart_1995640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995734 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1995734 : Nat := 118140960795 + 1995734 * 2 ^ 59
def prefixEnd_1995734 : Nat := 4983230072969 + 3 ^ 40 * 1995734 * 2
def baseEnd_1995734 : Nat := 683180533680133276831195

theorem tailTrace_1995734 : CollatzResearch.WordTrace tailWord_1995734 prefixEnd_1995734 683180533680133276831195 := by
  unfold tailWord_1995734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549399934487752317269641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48526932634536024717542837 4549399934487752317269641)
  ·
    refine ⟨3412049950865814237952231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4549399934487752317269641 3412049950865814237952231)
    ·
      refine ⟨5118074926298721356928347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3412049950865814237952231 5118074926298721356928347)
      ·
        refine ⟨7677112389448082035392521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118074926298721356928347 7677112389448082035392521)
        ·
          refine ⟨5757834292086061526544391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7677112389448082035392521 5757834292086061526544391)
          ·
            refine ⟨8636751438129092289816587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757834292086061526544391 8636751438129092289816587)
            ·
              refine ⟨12955127157193638434724881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8636751438129092289816587 12955127157193638434724881)
              ·
                refine ⟨9716345367895228826043661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12955127157193638434724881 9716345367895228826043661)
                ·
                  refine ⟨3643629512960710809766373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9716345367895228826043661 3643629512960710809766373)
                  ·
                    refine ⟨683180533680133276831195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3643629512960710809766373 683180533680133276831195)
                    ·
                      rfl

theorem cell22_1995734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1995734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995734 prefixEnd_1995734 := by exact prefixLift 1995734
  have htrace : WordTrace (prefixWord ++ tailWord_1995734) baseStart_1995734 baseEnd_1995734 := by
    simpa [prefixWord, tailWord_1995734, baseEnd_1995734] using wordTrace_append hprefix tailTrace_1995734
  have hstable : (prefixWord ++ tailWord_1995734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995734).length < 2 ^ (prefixWord ++ tailWord_1995734).sum := by decide
  have hdescent : baseEnd_1995734 < baseStart_1995734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995745 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1995745 : Nat := 118140960795 + 1995745 * 2 ^ 59
def prefixEnd_1995745 : Nat := 4983230072969 + 3 ^ 40 * 1995745 * 2
def baseEnd_1995745 : Nat := 683184299204932914806161

theorem tailTrace_1995745 : CollatzResearch.WordTrace tailWord_1995745 prefixEnd_1995745 683184299204932914806161 := by
  unfold tailWord_1995745
  simp only [CollatzResearch.WordTrace]
  refine ⟨72790800154764185954964689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48527200103176123969976459 72790800154764185954964689)
  ·
    refine ⟨54593100116073139466223517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72790800154764185954964689 54593100116073139466223517)
    ·
      refine ⟨20472412543527427299833819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54593100116073139466223517 20472412543527427299833819)
      ·
        refine ⟨30708618815291140949750729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20472412543527427299833819 30708618815291140949750729)
        ·
          refine ⟨23031464111468355712313047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30708618815291140949750729 23031464111468355712313047)
          ·
            refine ⟨34547196167202533568469571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23031464111468355712313047 34547196167202533568469571)
            ·
              refine ⟨51820794250803800352704357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34547196167202533568469571 51820794250803800352704357)
              ·
                refine ⟨9716398922025712566132067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51820794250803800352704357 9716398922025712566132067)
                ·
                  refine ⟨14574598383038568849198101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9716398922025712566132067 14574598383038568849198101)
                  ·
                    refine ⟨683184299204932914806161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14574598383038568849198101 683184299204932914806161)
                    ·
                      rfl

theorem cell22_1995745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1995745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995745 prefixEnd_1995745 := by exact prefixLift 1995745
  have htrace : WordTrace (prefixWord ++ tailWord_1995745) baseStart_1995745 baseEnd_1995745 := by
    simpa [prefixWord, tailWord_1995745, baseEnd_1995745] using wordTrace_append hprefix tailTrace_1995745
  have hstable : (prefixWord ++ tailWord_1995745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995745).length < 2 ^ (prefixWord ++ tailWord_1995745).sum := by decide
  have hdescent : baseEnd_1995745 < baseStart_1995745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995747 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 1, 5]
def baseStart_1995747 : Nat := 118140960795 + 1995747 * 2 ^ 59
def prefixEnd_1995747 : Nat := 4983230072969 + 3 ^ 40 * 1995747 * 2
def baseEnd_1995747 : Nat := 683184983845805576256155

theorem tailTrace_1995747 : CollatzResearch.WordTrace tailWord_1995747 prefixEnd_1995747 683184983845805576256155 := by
  unfold tailWord_1995747
  simp only [CollatzResearch.WordTrace]
  refine ⟨72790873100756940296537495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48527248733837960197691663 72790873100756940296537495)
  ·
    refine ⟨109186309651135410444806243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72790873100756940296537495 109186309651135410444806243)
    ·
      refine ⟨163779464476703115667209365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109186309651135410444806243 163779464476703115667209365)
      ·
        refine ⟨7677162397345458546900439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163779464476703115667209365 7677162397345458546900439)
        ·
          refine ⟨11515743596018187820350659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677162397345458546900439 11515743596018187820350659)
          ·
            refine ⟨17273615394027281730525989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11515743596018187820350659 17273615394027281730525989)
            ·
              refine ⟨3238802886380115324473623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17273615394027281730525989 3238802886380115324473623)
              ·
                refine ⟨4858204329570172986710435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238802886380115324473623 4858204329570172986710435)
                ·
                  refine ⟨7287306494355259480065653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858204329570172986710435 7287306494355259480065653)
                  ·
                    refine ⟨683184983845805576256155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7287306494355259480065653 683184983845805576256155)
                    ·
                      rfl

theorem cell22_1995747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5].length) (baseStart_1995747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995747 prefixEnd_1995747 := by exact prefixLift 1995747
  have htrace : WordTrace (prefixWord ++ tailWord_1995747) baseStart_1995747 baseEnd_1995747 := by
    simpa [prefixWord, tailWord_1995747, baseEnd_1995747] using wordTrace_append hprefix tailTrace_1995747
  have hstable : (prefixWord ++ tailWord_1995747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995747).length < 2 ^ (prefixWord ++ tailWord_1995747).sum := by decide
  have hdescent : baseEnd_1995747 < baseStart_1995747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995749 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 6]
def baseStart_1995749 : Nat := 118140960795 + 1995749 * 2 ^ 59
def prefixEnd_1995749 : Nat := 4983230072969 + 3 ^ 40 * 1995749 * 2
def baseEnd_1995749 : Nat := 227728556162226079235383

theorem tailTrace_1995749 : CollatzResearch.WordTrace tailWord_1995749 prefixEnd_1995749 227728556162226079235383 := by
  unfold tailWord_1995749
  simp only [CollatzResearch.WordTrace]
  refine ⟨72790946046749694638110301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48527297364499796425406867 72790946046749694638110301)
  ·
    refine ⟨27296604767531135489291363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72790946046749694638110301 27296604767531135489291363)
    ·
      refine ⟨40944907151296703233937045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27296604767531135489291363 40944907151296703233937045)
      ·
        refine ⟨1919292522717032964090799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40944907151296703233937045 1919292522717032964090799)
        ·
          refine ⟨2878938784075549446136199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919292522717032964090799 2878938784075549446136199)
          ·
            refine ⟨4318408176113324169204299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878938784075549446136199 4318408176113324169204299)
            ·
              refine ⟨6477612264169986253806449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318408176113324169204299 6477612264169986253806449)
              ·
                refine ⟨4858209198127489690354837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6477612264169986253806449 4858209198127489690354837)
                ·
                  refine ⟨227728556162226079235383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4858209198127489690354837 227728556162226079235383)
                  ·
                    rfl

theorem cell22_1995749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_1995749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995749 prefixEnd_1995749 := by exact prefixLift 1995749
  have htrace : WordTrace (prefixWord ++ tailWord_1995749) baseStart_1995749 baseEnd_1995749 := by
    simpa [prefixWord, tailWord_1995749, baseEnd_1995749] using wordTrace_append hprefix tailTrace_1995749
  have hstable : (prefixWord ++ tailWord_1995749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995749).length < 2 ^ (prefixWord ++ tailWord_1995749).sum := by decide
  have hdescent : baseEnd_1995749 < baseStart_1995749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995766 : List Nat := [5, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1995766 : Nat := 118140960795 + 1995766 * 2 ^ 59
def prefixEnd_1995766 : Nat := 4983230072969 + 3 ^ 40 * 1995766 * 2
def baseEnd_1995766 : Nat := 227730495978031953343699

theorem tailTrace_1995766 : CollatzResearch.WordTrace tailWord_1995766 prefixEnd_1995766 227730495978031953343699 := by
  unfold tailWord_1995766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549472880480506658842447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48527710725125404360986101 4549472880480506658842447)
  ·
    refine ⟨6824209320720759988263671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4549472880480506658842447 6824209320720759988263671)
    ·
      refine ⟨10236313981081139982395507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6824209320720759988263671 10236313981081139982395507)
      ·
        refine ⟨15354470971621709973593261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10236313981081139982395507 15354470971621709973593261)
        ·
          refine ⟨5757926614358141240097473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15354470971621709973593261 5757926614358141240097473)
          ·
            refine ⟨4318444960768605930073105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5757926614358141240097473 4318444960768605930073105)
            ·
              refine ⟨3238833720576454447554829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4318444960768605930073105 3238833720576454447554829)
              ·
                refine ⟨1214562645216170417833061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3238833720576454447554829 1214562645216170417833061)
                ·
                  refine ⟨227730495978031953343699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1214562645216170417833061 227730495978031953343699)
                  ·
                    rfl

theorem cell22_1995766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1995766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995766 prefixEnd_1995766 := by exact prefixLift 1995766
  have htrace : WordTrace (prefixWord ++ tailWord_1995766) baseStart_1995766 baseEnd_1995766 := by
    simpa [prefixWord, tailWord_1995766, baseEnd_1995766] using wordTrace_append hprefix tailTrace_1995766
  have hstable : (prefixWord ++ tailWord_1995766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995766).length < 2 ^ (prefixWord ++ tailWord_1995766).sum := by decide
  have hdescent : baseEnd_1995766 < baseStart_1995766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995809 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1995809 : Nat := 118140960795 + 1995809 * 2 ^ 59
def prefixEnd_1995809 : Nat := 4983230072969 + 3 ^ 40 * 1995809 * 2
def baseEnd_1995809 : Nat := 683206207712858081205965

theorem tailTrace_1995809 : CollatzResearch.WordTrace tailWord_1995809 prefixEnd_1995809 683206207712858081205965 := by
  unfold tailWord_1995809
  simp only [CollatzResearch.WordTrace]
  refine ⟨72793134426532324885294481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48528756284354883256862987 72793134426532324885294481)
  ·
    refine ⟨54594850819899243663970861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72793134426532324885294481 54594850819899243663970861)
    ·
      refine ⟨20473069057462216373989073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54594850819899243663970861 20473069057462216373989073)
      ·
        refine ⟨15354801793096662280491805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20473069057462216373989073 15354801793096662280491805)
        ·
          refine ⟨5758050672411248355184427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15354801793096662280491805 5758050672411248355184427)
          ·
            refine ⟨8637076008616872532776641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758050672411248355184427 8637076008616872532776641)
            ·
              refine ⟨6477807006462654399582481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8637076008616872532776641 6477807006462654399582481)
              ·
                refine ⟨4858355254846990799686861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6477807006462654399582481 4858355254846990799686861)
                ·
                  refine ⟨1821883220567621549882573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4858355254846990799686861 1821883220567621549882573)
                  ·
                    refine ⟨683206207712858081205965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1821883220567621549882573 683206207712858081205965)
                    ·
                      rfl

theorem cell22_1995809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1995809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995809 prefixEnd_1995809 := by exact prefixLift 1995809
  have htrace : WordTrace (prefixWord ++ tailWord_1995809) baseStart_1995809 baseEnd_1995809 := by
    simpa [prefixWord, tailWord_1995809, baseEnd_1995809] using wordTrace_append hprefix tailTrace_1995809
  have hstable : (prefixWord ++ tailWord_1995809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995809).length < 2 ^ (prefixWord ++ tailWord_1995809).sum := by decide
  have hdescent : baseEnd_1995809 < baseStart_1995809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995822 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1995822 : Nat := 118140960795 + 1995822 * 2 ^ 59
def prefixEnd_1995822 : Nat := 4983230072969 + 3 ^ 40 * 1995822 * 2
def baseEnd_1995822 : Nat := 227736885959510126876975

theorem tailTrace_1995822 : CollatzResearch.WordTrace tailWord_1995822 prefixEnd_1995822 227736885959510126876975 := by
  unfold tailWord_1995822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099201071935653513189715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48529072383656818737011813 9099201071935653513189715)
  ·
    refine ⟨13648801607903480269784573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9099201071935653513189715 13648801607903480269784573)
    ·
      refine ⟨5118300602963805101169215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13648801607903480269784573 5118300602963805101169215)
      ·
        refine ⟨7677450904445707651753823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118300602963805101169215 7677450904445707651753823)
        ·
          refine ⟨11516176356668561477630735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677450904445707651753823 11516176356668561477630735)
          ·
            refine ⟨17274264535002842216446103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11516176356668561477630735 17274264535002842216446103)
            ·
              refine ⟨25911396802504263324669155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17274264535002842216446103 25911396802504263324669155)
              ·
                refine ⟨38867095203756394987003733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25911396802504263324669155 38867095203756394987003733)
                ·
                  refine ⟨227736885959510126876975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38867095203756394987003733 227736885959510126876975)
                  ·
                    rfl

theorem cell22_1995822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1995822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995822 prefixEnd_1995822 := by exact prefixLift 1995822
  have htrace : WordTrace (prefixWord ++ tailWord_1995822) baseStart_1995822 baseEnd_1995822 := by
    simpa [prefixWord, tailWord_1995822, baseEnd_1995822] using wordTrace_append hprefix tailTrace_1995822
  have hstable : (prefixWord ++ tailWord_1995822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995822).length < 2 ^ (prefixWord ++ tailWord_1995822).sum := by decide
  have hdescent : baseEnd_1995822 < baseStart_1995822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995852 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_1995852 : Nat := 118140960795 + 1995852 * 2 ^ 59
def prefixEnd_1995852 : Nat := 4983230072969 + 3 ^ 40 * 1995852 * 2
def baseEnd_1995852 : Nat := 683220927491620302380833

theorem tailTrace_1995852 : CollatzResearch.WordTrace tailWord_1995852 prefixEnd_1995852 683220927491620302380833 := by
  unfold tailWord_1995852
  simp only [CollatzResearch.WordTrace]
  refine ⟨36397351382688271614554905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48529801843584362152739873 36397351382688271614554905)
  ·
    refine ⟨27298013537016203710916179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36397351382688271614554905 27298013537016203710916179)
    ·
      refine ⟨40947020305524305566374269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27298013537016203710916179 40947020305524305566374269)
      ·
        refine ⟨15355132614571614587390351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40947020305524305566374269 15355132614571614587390351)
        ·
          refine ⟨23032698921857421881085527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15355132614571614587390351 23032698921857421881085527)
          ·
            refine ⟨34549048382786132821628291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23032698921857421881085527 34549048382786132821628291)
            ·
              refine ⟨51823572574179199232442437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34549048382786132821628291 51823572574179199232442437)
              ·
                refine ⟨9716919857658599856082957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51823572574179199232442437 9716919857658599856082957)
                ·
                  refine ⟨3643844946621974946031109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9716919857658599856082957 3643844946621974946031109)
                  ·
                    refine ⟨683220927491620302380833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3643844946621974946031109 683220927491620302380833)
                    ·
                      rfl

theorem cell22_1995852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_1995852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995852 prefixEnd_1995852 := by exact prefixLift 1995852
  have htrace : WordTrace (prefixWord ++ tailWord_1995852) baseStart_1995852 baseEnd_1995852 := by
    simpa [prefixWord, tailWord_1995852, baseEnd_1995852] using wordTrace_append hprefix tailTrace_1995852
  have hstable : (prefixWord ++ tailWord_1995852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995852).length < 2 ^ (prefixWord ++ tailWord_1995852).sum := by decide
  have hdescent : baseEnd_1995852 < baseStart_1995852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995884 : List Nat := [2, 2, 1, 1, 3, 2, 2, 5, 4]
def baseStart_1995884 : Nat := 118140960795 + 1995884 * 2 ^ 59
def prefixEnd_1995884 : Nat := 4983230072969 + 3 ^ 40 * 1995884 * 2
def baseEnd_1995884 : Nat := 227743960581860961860245

theorem tailTrace_1995884 : CollatzResearch.WordTrace tailWord_1995884 prefixEnd_1995884 227743960581860961860245 := by
  unfold tailWord_1995884
  simp only [CollatzResearch.WordTrace]
  refine ⟨36397934950630306347137353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48530579934173741796183137 36397934950630306347137353)
  ·
    refine ⟨27298451212972729760353015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36397934950630306347137353 27298451212972729760353015)
    ·
      refine ⟨40947676819459094640529523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27298451212972729760353015 40947676819459094640529523)
      ·
        refine ⟨61421515229188641960794285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40947676819459094640529523 61421515229188641960794285)
        ·
          refine ⟨23033068210945740735297857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61421515229188641960794285 23033068210945740735297857)
          ·
            refine ⟨17274801158209305551473393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23033068210945740735297857 17274801158209305551473393)
            ·
              refine ⟨12956100868656979163605045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17274801158209305551473393 12956100868656979163605045)
              ·
                refine ⟨1214634456436591796587973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12956100868656979163605045 1214634456436591796587973)
                ·
                  refine ⟨227743960581860961860245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1214634456436591796587973 227743960581860961860245)
                  ·
                    rfl

theorem cell22_1995884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_1995884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995884 prefixEnd_1995884 := by exact prefixLift 1995884
  have htrace : WordTrace (prefixWord ++ tailWord_1995884) baseStart_1995884 baseEnd_1995884 := by
    simpa [prefixWord, tailWord_1995884, baseEnd_1995884] using wordTrace_append hprefix tailTrace_1995884
  have hstable : (prefixWord ++ tailWord_1995884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995884).length < 2 ^ (prefixWord ++ tailWord_1995884).sum := by decide
  have hdescent : baseEnd_1995884 < baseStart_1995884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995961 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 3, 3]
def baseStart_1995961 : Nat := 118140960795 + 1995961 * 2 ^ 59
def prefixEnd_1995961 : Nat := 4983230072969 + 3 ^ 40 * 1995961 * 2
def baseEnd_1995961 : Nat := 683258240419180351405499

theorem tailTrace_1995961 : CollatzResearch.WordTrace tailWord_1995961 prefixEnd_1995961 683258240419180351405499 := by
  unfold tailWord_1995961
  simp only [CollatzResearch.WordTrace]
  refine ⟨72798678321981654844827737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48532452214654436563218491 72798678321981654844827737)
  ·
    refine ⟨54599008741486241133620803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72798678321981654844827737 54599008741486241133620803)
    ·
      refine ⟨81898513112229361700431205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54599008741486241133620803 81898513112229361700431205)
      ·
        refine ⟨15355971208543005318830851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81898513112229361700431205 15355971208543005318830851)
        ·
          refine ⟨23033956812814507978246277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15355971208543005318830851 23033956812814507978246277)
          ·
            refine ⟨4318866902402720245921177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23033956812814507978246277 4318866902402720245921177)
            ·
              refine ⟨3239150176802040184440883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4318866902402720245921177 3239150176802040184440883)
              ·
                refine ⟨4858725265203060276661325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239150176802040184440883 4858725265203060276661325)
                ·
                  refine ⟨1822021974451147603747997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4858725265203060276661325 1822021974451147603747997)
                  ·
                    refine ⟨683258240419180351405499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1822021974451147603747997 683258240419180351405499)
                    ·
                      rfl

theorem cell22_1995961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_1995961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1995961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1995961 prefixEnd_1995961 := by exact prefixLift 1995961
  have htrace : WordTrace (prefixWord ++ tailWord_1995961) baseStart_1995961 baseEnd_1995961 := by
    simpa [prefixWord, tailWord_1995961, baseEnd_1995961] using wordTrace_append hprefix tailTrace_1995961
  have hstable : (prefixWord ++ tailWord_1995961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995961).length < 2 ^ (prefixWord ++ tailWord_1995961).sum := by decide
  have hdescent : baseEnd_1995961 < baseStart_1995961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996019 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 6]
def baseStart_1996019 : Nat := 118140960795 + 1996019 * 2 ^ 59
def prefixEnd_1996019 : Nat := 4983230072969 + 3 ^ 40 * 1996019 * 2
def baseEnd_1996019 : Nat := 227759365001495844485107

theorem tailTrace_1996019 : CollatzResearch.WordTrace tailWord_1996019 prefixEnd_1996019 227759365001495844485107 := by
  unfold tailWord_1996019
  simp only [CollatzResearch.WordTrace]
  refine ⟨72800793755771530750439111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48533862503847687166959407 72800793755771530750439111)
  ·
    refine ⟨109201190633657296125658667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72800793755771530750439111 109201190633657296125658667)
    ·
      refine ⟨163801785950485944188488001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109201190633657296125658667 163801785950485944188488001)
      ·
        refine ⟨122851339462864458141366001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163801785950485944188488001 122851339462864458141366001)
        ·
          refine ⟨92138504597148343606024501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122851339462864458141366001 92138504597148343606024501)
          ·
            refine ⟨8637984805982657213064797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92138504597148343606024501 8637984805982657213064797)
            ·
              refine ⟨3239244302243496454899299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8637984805982657213064797 3239244302243496454899299)
              ·
                refine ⟨4858866453365244682348949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239244302243496454899299 4858866453365244682348949)
                ·
                  refine ⟨227759365001495844485107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4858866453365244682348949 227759365001495844485107)
                  ·
                    rfl

theorem cell22_1996019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 6].length) (baseStart_1996019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996019 prefixEnd_1996019 := by exact prefixLift 1996019
  have htrace : WordTrace (prefixWord ++ tailWord_1996019) baseStart_1996019 baseEnd_1996019 := by
    simpa [prefixWord, tailWord_1996019, baseEnd_1996019] using wordTrace_append hprefix tailTrace_1996019
  have hstable : (prefixWord ++ tailWord_1996019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996019).length < 2 ^ (prefixWord ++ tailWord_1996019).sum := by decide
  have hdescent : baseEnd_1996019 < baseStart_1996019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996064 : List Nat := [2, 1, 1, 5, 3, 10]
def baseStart_1996064 : Nat := 118140960795 + 1996064 * 2 ^ 59
def prefixEnd_1996064 : Nat := 4983230072969 + 3 ^ 40 * 1996064 * 2
def baseEnd_1996064 : Nat := 8435722215112622420743

theorem tailTrace_1996064 : CollatzResearch.WordTrace tailWord_1996064 prefixEnd_1996064 8435722215112622420743 := by
  unfold tailWord_1996064
  simp only [CollatzResearch.WordTrace]
  refine ⟨36401217520304251717913623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48534956693739002290551497 36401217520304251717913623)
  ·
    refine ⟨54601826280456377576870435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36401217520304251717913623 54601826280456377576870435)
    ·
      refine ⟨81902739420684566365305653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54601826280456377576870435 81902739420684566365305653)
      ·
        refine ⟨7678381820689178096747405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81902739420684566365305653 7678381820689178096747405)
        ·
          refine ⟨2879393182758441786280277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7678381820689178096747405 2879393182758441786280277)
          ·
            refine ⟨8435722215112622420743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2879393182758441786280277 8435722215112622420743)
            ·
              rfl

theorem cell22_1996064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 10].length) (baseStart_1996064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996064 prefixEnd_1996064 := by exact prefixLift 1996064
  have htrace : WordTrace (prefixWord ++ tailWord_1996064) baseStart_1996064 baseEnd_1996064 := by
    simpa [prefixWord, tailWord_1996064, baseEnd_1996064] using wordTrace_append hprefix tailTrace_1996064
  have hstable : (prefixWord ++ tailWord_1996064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996064).length < 2 ^ (prefixWord ++ tailWord_1996064).sum := by decide
  have hdescent : baseEnd_1996064 < baseStart_1996064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996068 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1996068 : Nat := 118140960795 + 1996068 * 2 ^ 59
def prefixEnd_1996068 : Nat := 4983230072969 + 3 ^ 40 * 1996068 * 2
def baseEnd_1996068 : Nat := 683294868705867738980171

theorem tailTrace_1996068 : CollatzResearch.WordTrace tailWord_1996068 prefixEnd_1996068 683294868705867738980171 := by
  unfold tailWord_1996068
  simp only [CollatzResearch.WordTrace]
  refine ⟨36401290466297006059486429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48535053955062674745981905 36401290466297006059486429)
  ·
    refine ⟨13650483924861377272307411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36401290466297006059486429 13650483924861377272307411)
    ·
      refine ⟨20475725887292065908461117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13650483924861377272307411 20475725887292065908461117)
      ·
        refine ⟨7678397207734524715672919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20475725887292065908461117 7678397207734524715672919)
        ·
          refine ⟨11517595811601787073509379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678397207734524715672919 11517595811601787073509379)
          ·
            refine ⟨17276393717402680610264069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517595811601787073509379 17276393717402680610264069)
            ·
              refine ⟨3239323822013002614424513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17276393717402680610264069 3239323822013002614424513)
              ·
                refine ⟨2429492866509751960818385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239323822013002614424513 2429492866509751960818385)
                ·
                  refine ⟨1822119649882313970613789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2429492866509751960818385 1822119649882313970613789)
                  ·
                    refine ⟨683294868705867738980171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1822119649882313970613789 683294868705867738980171)
                    ·
                      rfl

theorem cell22_1996068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1996068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996068 prefixEnd_1996068 := by exact prefixLift 1996068
  have htrace : WordTrace (prefixWord ++ tailWord_1996068) baseStart_1996068 baseEnd_1996068 := by
    simpa [prefixWord, tailWord_1996068, baseEnd_1996068] using wordTrace_append hprefix tailTrace_1996068
  have hstable : (prefixWord ++ tailWord_1996068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996068).length < 2 ^ (prefixWord ++ tailWord_1996068).sum := by decide
  have hdescent : baseEnd_1996068 < baseStart_1996068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996081 : List Nat := [1, 2, 2, 3, 3, 3, 1, 7]
def baseStart_1996081 : Nat := 118140960795 + 1996081 * 2 ^ 59
def prefixEnd_1996081 : Nat := 4983230072969 + 3 ^ 40 * 1996081 * 2
def baseEnd_1996081 : Nat := 75922146541282226489459

theorem tailTrace_1996081 : CollatzResearch.WordTrace tailWord_1996081 prefixEnd_1996081 75922146541282226489459 := by
  unfold tailWord_1996081
  simp only [CollatzResearch.WordTrace]
  refine ⟨72803055081546915339196097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48535370054364610226130731 72803055081546915339196097)
  ·
    refine ⟨54602291311160186504397073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72803055081546915339196097 54602291311160186504397073)
    ·
      refine ⟨40951718483370139878297805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54602291311160186504397073 40951718483370139878297805)
      ·
        refine ⟨15356894431263802454361677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40951718483370139878297805 15356894431263802454361677)
        ·
          refine ⟨5758835411723925920385629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15356894431263802454361677 5758835411723925920385629)
          ·
            refine ⟨2159563279396472220144611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5758835411723925920385629 2159563279396472220144611)
            ·
              refine ⟨3239344919094708330216917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159563279396472220144611 3239344919094708330216917)
              ·
                refine ⟨75922146541282226489459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3239344919094708330216917 75922146541282226489459)
                ·
                  rfl

theorem cell22_1996081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 7].length) (baseStart_1996081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996081 prefixEnd_1996081 := by exact prefixLift 1996081
  have htrace : WordTrace (prefixWord ++ tailWord_1996081) baseStart_1996081 baseEnd_1996081 := by
    simpa [prefixWord, tailWord_1996081, baseEnd_1996081] using wordTrace_append hprefix tailTrace_1996081
  have hstable : (prefixWord ++ tailWord_1996081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996081).length < 2 ^ (prefixWord ++ tailWord_1996081).sum := by decide
  have hdescent : baseEnd_1996081 < baseStart_1996081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996096 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 3, 3]
def baseStart_1996096 : Nat := 118140960795 + 1996096 * 2 ^ 59
def prefixEnd_1996096 : Nat := 4983230072969 + 3 ^ 40 * 1996096 * 2
def baseEnd_1996096 : Nat := 683304453678084999280085

theorem tailTrace_1996096 : CollatzResearch.WordTrace tailWord_1996096 prefixEnd_1996096 683304453678084999280085 := by
  unfold tailWord_1996096
  simp only [CollatzResearch.WordTrace]
  refine ⟨36401801088246286450496071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48535734784328381933994761 36401801088246286450496071)
  ·
    refine ⟨54602701632369429675744107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36401801088246286450496071 54602701632369429675744107)
    ·
      refine ⟨81904052448554144513616161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54602701632369429675744107 81904052448554144513616161)
      ·
        refine ⟨61428039336415608385212121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81904052448554144513616161 61428039336415608385212121)
        ·
          refine ⟨46071029502311706288909091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61428039336415608385212121 46071029502311706288909091)
          ·
            refine ⟨69106544253467559433363637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46071029502311706288909091 69106544253467559433363637)
            ·
              refine ⟨6478738523762583696877841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69106544253467559433363637 6478738523762583696877841)
              ·
                refine ⟨4859053892821937772658381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478738523762583696877841 4859053892821937772658381)
                ·
                  refine ⟨1822145209808226664746893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4859053892821937772658381 1822145209808226664746893)
                  ·
                    refine ⟨683304453678084999280085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1822145209808226664746893 683304453678084999280085)
                    ·
                      rfl

theorem cell22_1996096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_1996096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996096 prefixEnd_1996096 := by exact prefixLift 1996096
  have htrace : WordTrace (prefixWord ++ tailWord_1996096) baseStart_1996096 baseEnd_1996096 := by
    simpa [prefixWord, tailWord_1996096, baseEnd_1996096] using wordTrace_append hprefix tailTrace_1996096
  have hstable : (prefixWord ++ tailWord_1996096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996096).length < 2 ^ (prefixWord ++ tailWord_1996096).sum := by decide
  have hdescent : baseEnd_1996096 < baseStart_1996096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996100 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1996100 : Nat := 118140960795 + 1996100 * 2 ^ 59
def prefixEnd_1996100 : Nat := 4983230072969 + 3 ^ 40 * 1996100 * 2
def baseEnd_1996100 : Nat := 683305822959830322180073

theorem tailTrace_1996100 : CollatzResearch.WordTrace tailWord_1996100 prefixEnd_1996100 683305822959830322180073 := by
  unfold tailWord_1996100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36401874034239040792068877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48535832045652054389425169 36401874034239040792068877)
  ·
    refine ⟨13650702762839640297025829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36401874034239040792068877 13650702762839640297025829)
    ·
      refine ⟨2559506768032432555692343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13650702762839640297025829 2559506768032432555692343)
      ·
        refine ⟨3839260152048648833538515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559506768032432555692343 3839260152048648833538515)
        ·
          refine ⟨5758890228072973250307773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839260152048648833538515 5758890228072973250307773)
          ·
            refine ⟨2159583835527364968865415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5758890228072973250307773 2159583835527364968865415)
            ·
              refine ⟨3239375753291047453298123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159583835527364968865415 3239375753291047453298123)
              ·
                refine ⟨4859063629936571179947185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239375753291047453298123 4859063629936571179947185)
                ·
                  refine ⟨3644297722452428384960389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859063629936571179947185 3644297722452428384960389)
                  ·
                    refine ⟨683305822959830322180073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3644297722452428384960389 683305822959830322180073)
                    ·
                      rfl

theorem cell22_1996100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1996100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996100 prefixEnd_1996100 := by exact prefixLift 1996100
  have htrace : WordTrace (prefixWord ++ tailWord_1996100) baseStart_1996100 baseEnd_1996100 := by
    simpa [prefixWord, tailWord_1996100, baseEnd_1996100] using wordTrace_append hprefix tailTrace_1996100
  have hstable : (prefixWord ++ tailWord_1996100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996100).length < 2 ^ (prefixWord ++ tailWord_1996100).sum := by decide
  have hdescent : baseEnd_1996100 < baseStart_1996100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996130 : List Nat := [3, 3, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1996130 : Nat := 118140960795 + 1996130 * 2 ^ 59
def prefixEnd_1996130 : Nat := 4983230072969 + 3 ^ 40 * 1996130 * 2
def baseEnd_1996130 : Nat := 683316092572920243929981

theorem tailTrace_1996130 : CollatzResearch.WordTrace tailWord_1996130 prefixEnd_1996130 683316092572920243929981 := by
  unfold tailWord_1996130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18201210564592349176932461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48536561505579597805153229 18201210564592349176932461)
  ·
    refine ⟨6825453961722130941349673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18201210564592349176932461 6825453961722130941349673)
    ·
      refine ⟨5119090471291598206012255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6825453961722130941349673 5119090471291598206012255)
      ·
        refine ⟨7678635706937397309018383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5119090471291598206012255 7678635706937397309018383)
        ·
          refine ⟨11517953560406095963527575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678635706937397309018383 11517953560406095963527575)
          ·
            refine ⟨17276930340609143945291363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517953560406095963527575 17276930340609143945291363)
            ·
              refine ⟨25915395510913715917937045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17276930340609143945291363 25915395510913715917937045)
              ·
                refine ⟨1214784164574080433653299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25915395510913715917937045 1214784164574080433653299)
                ·
                  refine ⟨1822176246861120650479949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214784164574080433653299 1822176246861120650479949)
                  ·
                    refine ⟨683316092572920243929981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1822176246861120650479949 683316092572920243929981)
                    ·
                      rfl

theorem cell22_1996130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1996130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996130 prefixEnd_1996130 := by exact prefixLift 1996130
  have htrace : WordTrace (prefixWord ++ tailWord_1996130) baseStart_1996130 baseEnd_1996130 := by
    simpa [prefixWord, tailWord_1996130, baseEnd_1996130] using wordTrace_append hprefix tailTrace_1996130
  have hstable : (prefixWord ++ tailWord_1996130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996130).length < 2 ^ (prefixWord ++ tailWord_1996130).sum := by decide
  have hdescent : baseEnd_1996130 < baseStart_1996130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996141 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1996141 : Nat := 118140960795 + 1996141 * 2 ^ 59
def prefixEnd_1996141 : Nat := 4983230072969 + 3 ^ 40 * 1996141 * 2
def baseEnd_1996141 : Nat := 683319858097719881904947

theorem tailTrace_1996141 : CollatzResearch.WordTrace tailWord_1996141 prefixEnd_1996141 683319858097719881904947 := by
  unfold tailWord_1996141
  simp only [CollatzResearch.WordTrace]
  refine ⟨72805243461329545586380277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48536828974219697057586851 72805243461329545586380277)
  ·
    refine ⟨6825491574499644898723151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72805243461329545586380277 6825491574499644898723151)
    ·
      refine ⟨10238237361749467348084727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6825491574499644898723151 10238237361749467348084727)
      ·
        refine ⟨15357356042624201022127091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10238237361749467348084727 15357356042624201022127091)
        ·
          refine ⟨23036034063936301533190637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15357356042624201022127091 23036034063936301533190637)
          ·
            refine ⟨8638512773976113074946489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23036034063936301533190637 8638512773976113074946489)
            ·
              refine ⟨6478884580482084806209867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8638512773976113074946489 6478884580482084806209867)
              ·
                refine ⟨9718326870723127209314801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478884580482084806209867 9718326870723127209314801)
                ·
                  refine ⟨7288745153042345406986101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9718326870723127209314801 7288745153042345406986101)
                  ·
                    refine ⟨683319858097719881904947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7288745153042345406986101 683319858097719881904947)
                    ·
                      rfl

theorem cell22_1996141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1996141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996141 prefixEnd_1996141 := by exact prefixLift 1996141
  have htrace : WordTrace (prefixWord ++ tailWord_1996141) baseStart_1996141 baseEnd_1996141 := by
    simpa [prefixWord, tailWord_1996141, baseEnd_1996141] using wordTrace_append hprefix tailTrace_1996141
  have hstable : (prefixWord ++ tailWord_1996141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996141).length < 2 ^ (prefixWord ++ tailWord_1996141).sum := by decide
  have hdescent : baseEnd_1996141 < baseStart_1996141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996291 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 5, 4]
def baseStart_1996291 : Nat := 118140960795 + 1996291 * 2 ^ 59
def prefixEnd_1996291 : Nat := 4983230072969 + 3 ^ 40 * 1996291 * 2
def baseEnd_1996291 : Nat := 683371206163169490654487

theorem tailTrace_1996291 : CollatzResearch.WordTrace tailWord_1996291 prefixEnd_1996291 683371206163169490654487 := by
  unfold tailWord_1996291
  simp only [CollatzResearch.WordTrace]
  refine ⟨72810714410786121204340727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48540476273857414136227151 72810714410786121204340727)
  ·
    refine ⟨109216071616179181806511091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72810714410786121204340727 109216071616179181806511091)
    ·
      refine ⟨163824107424268772709766637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109216071616179181806511091 163824107424268772709766637)
      ·
        refine ⟨61434040284100789766162489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163824107424268772709766637 61434040284100789766162489)
        ·
          refine ⟨46075530213075592324621867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61434040284100789766162489 46075530213075592324621867)
          ·
            refine ⟨69113295319613388486932801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46075530213075592324621867 69113295319613388486932801)
            ·
              refine ⟨51834971489710041365199601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69113295319613388486932801 51834971489710041365199601)
              ·
                refine ⟨38876228617282531023899701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51834971489710041365199601 38876228617282531023899701)
                ·
                  refine ⟨3644646432870237283490597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38876228617282531023899701 3644646432870237283490597)
                  ·
                    refine ⟨683371206163169490654487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3644646432870237283490597 683371206163169490654487)
                    ·
                      rfl

theorem cell22_1996291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_1996291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996291 prefixEnd_1996291 := by exact prefixLift 1996291
  have htrace : WordTrace (prefixWord ++ tailWord_1996291) baseStart_1996291 baseEnd_1996291 := by
    simpa [prefixWord, tailWord_1996291, baseEnd_1996291] using wordTrace_append hprefix tailTrace_1996291
  have hstable : (prefixWord ++ tailWord_1996291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996291).length < 2 ^ (prefixWord ++ tailWord_1996291).sum := by decide
  have hdescent : baseEnd_1996291 < baseStart_1996291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996295 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 5]
def baseStart_1996295 : Nat := 118140960795 + 1996295 * 2 ^ 59
def prefixEnd_1996295 : Nat := 4983230072969 + 3 ^ 40 * 1996295 * 2
def baseEnd_1996295 : Nat := 227790858481638271184825

theorem tailTrace_1996295 : CollatzResearch.WordTrace tailWord_1996295 prefixEnd_1996295 227790858481638271184825 := by
  unfold tailWord_1996295
  simp only [CollatzResearch.WordTrace]
  refine ⟨72810860302771629887486339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48540573535181086591657559 72810860302771629887486339)
  ·
    refine ⟨109216290454157444831229509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72810860302771629887486339 109216290454157444831229509)
    ·
      refine ⟨20478054460154520905855533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109216290454157444831229509 20478054460154520905855533)
      ·
        refine ⟨7679270422557945339695825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20478054460154520905855533 7679270422557945339695825)
        ·
          refine ⟨5759452816918459004771869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7679270422557945339695825 5759452816918459004771869)
          ·
            refine ⟨2159794806344422126789451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5759452816918459004771869 2159794806344422126789451)
            ·
              refine ⟨3239692209516633190184177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159794806344422126789451 3239692209516633190184177)
              ·
                refine ⟨2429769157137474892638133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239692209516633190184177 2429769157137474892638133)
                ·
                  refine ⟨227790858481638271184825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2429769157137474892638133 227790858481638271184825)
                  ·
                    rfl

theorem cell22_1996295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 5].length) (baseStart_1996295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996295 prefixEnd_1996295 := by exact prefixLift 1996295
  have htrace : WordTrace (prefixWord ++ tailWord_1996295) baseStart_1996295 baseEnd_1996295 := by
    simpa [prefixWord, tailWord_1996295, baseEnd_1996295] using wordTrace_append hprefix tailTrace_1996295
  have hstable : (prefixWord ++ tailWord_1996295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996295).length < 2 ^ (prefixWord ++ tailWord_1996295).sum := by decide
  have hdescent : baseEnd_1996295 < baseStart_1996295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996351 : List Nat := [1, 1, 2, 2, 3, 3, 10]
def baseStart_1996351 : Nat := 118140960795 + 1996351 * 2 ^ 59
def prefixEnd_1996351 : Nat := 4983230072969 + 3 ^ 40 * 1996351 * 2
def baseEnd_1996351 : Nat := 25310805384790716079789

theorem tailTrace_1996351 : CollatzResearch.WordTrace tailWord_1996351 prefixEnd_1996351 25310805384790716079789 := by
  unfold tailWord_1996351
  simp only [CollatzResearch.WordTrace]
  refine ⟨72812902790568751451524907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48541935193712500967683271 72812902790568751451524907)
  ·
    refine ⟨109219354185853127177287361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72812902790568751451524907 109219354185853127177287361)
    ·
      refine ⟨81914515639389845382965521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109219354185853127177287361 81914515639389845382965521)
      ·
        refine ⟨61435886729542384037224141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81914515639389845382965521 61435886729542384037224141)
        ·
          refine ⟨23038457523578394013959053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61435886729542384037224141 23038457523578394013959053)
          ·
            refine ⟨8639421571341897755234645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23038457523578394013959053 8639421571341897755234645)
            ·
              refine ⟨25310805384790716079789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8639421571341897755234645 25310805384790716079789)
              ·
                rfl

theorem cell22_1996351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 10].length) (baseStart_1996351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996351 prefixEnd_1996351 := by exact prefixLift 1996351
  have htrace : WordTrace (prefixWord ++ tailWord_1996351) baseStart_1996351 baseEnd_1996351 := by
    simpa [prefixWord, tailWord_1996351, baseEnd_1996351] using wordTrace_append hprefix tailTrace_1996351
  have hstable : (prefixWord ++ tailWord_1996351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996351).length < 2 ^ (prefixWord ++ tailWord_1996351).sum := by decide
  have hdescent : baseEnd_1996351 < baseStart_1996351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996428 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_1996428 : Nat := 118140960795 + 1996428 * 2 ^ 59
def prefixEnd_1996428 : Nat := 4983230072969 + 3 ^ 40 * 1996428 * 2
def baseEnd_1996428 : Nat := 683418104062946799979067

theorem tailTrace_1996428 : CollatzResearch.WordTrace tailWord_1996428 prefixEnd_1996428 683418104062946799979067 := by
  unfold tailWord_1996428
  simp only [CollatzResearch.WordTrace]
  refine ⟨36407855605644896801038969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48543807474193195734718625 36407855605644896801038969)
  ·
    refine ⟨27305891704233672600779227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36407855605644896801038969 27305891704233672600779227)
    ·
      refine ⟨40958837556350508901168841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27305891704233672600779227 40958837556350508901168841)
      ·
        refine ⟨30719128167262881675876631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40958837556350508901168841 30719128167262881675876631)
        ·
          refine ⟨46078692250894322513814947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30719128167262881675876631 46078692250894322513814947)
          ·
            refine ⟨69118038376341483770722421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46078692250894322513814947 69118038376341483770722421)
            ·
              refine ⟨6479816097782014103505227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69118038376341483770722421 6479816097782014103505227)
              ·
                refine ⟨9719724146673021155257841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6479816097782014103505227 9719724146673021155257841)
                ·
                  refine ⟨7289793110004765866443381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9719724146673021155257841 7289793110004765866443381)
                  ·
                    refine ⟨683418104062946799979067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7289793110004765866443381 683418104062946799979067)
                    ·
                      rfl

theorem cell22_1996428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_1996428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996428 prefixEnd_1996428 := by exact prefixLift 1996428
  have htrace : WordTrace (prefixWord ++ tailWord_1996428) baseStart_1996428 baseEnd_1996428 := by
    simpa [prefixWord, tailWord_1996428, baseEnd_1996428] using wordTrace_append hprefix tailTrace_1996428
  have hstable : (prefixWord ++ tailWord_1996428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996428).length < 2 ^ (prefixWord ++ tailWord_1996428).sum := by decide
  have hdescent : baseEnd_1996428 < baseStart_1996428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996430 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1996430 : Nat := 118140960795 + 1996430 * 2 ^ 59
def prefixEnd_1996430 : Nat := 4983230072969 + 3 ^ 40 * 1996430 * 2
def baseEnd_1996430 : Nat := 227806262901273153809687

theorem tailTrace_1996430 : CollatzResearch.WordTrace tailWord_1996430 prefixEnd_1996430 227806262901273153809687 := by
  unfold tailWord_1996430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101973019660318492956343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48543856104855031962433829 9101973019660318492956343)
  ·
    refine ⟨13652959529490477739434515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9101973019660318492956343 13652959529490477739434515)
    ·
      refine ⟨20479439294235716609151773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13652959529490477739434515 20479439294235716609151773)
      ·
        refine ⟨7679789735338393728431915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20479439294235716609151773 7679789735338393728431915)
        ·
          refine ⟨11519684603007590592647873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7679789735338393728431915 11519684603007590592647873)
          ·
            refine ⟨8639763452255692944485905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11519684603007590592647873 8639763452255692944485905)
            ·
              refine ⟨6479822589191769708364429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8639763452255692944485905 6479822589191769708364429)
              ·
                refine ⟨2429933470946913640636661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6479822589191769708364429 2429933470946913640636661)
                ·
                  refine ⟨227806262901273153809687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2429933470946913640636661 227806262901273153809687)
                  ·
                    rfl

theorem cell22_1996430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1996430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996430 prefixEnd_1996430 := by exact prefixLift 1996430
  have htrace : WordTrace (prefixWord ++ tailWord_1996430) baseStart_1996430 baseEnd_1996430 := by
    simpa [prefixWord, tailWord_1996430, baseEnd_1996430] using wordTrace_append hprefix tailTrace_1996430
  have hstable : (prefixWord ++ tailWord_1996430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996430).length < 2 ^ (prefixWord ++ tailWord_1996430).sum := by decide
  have hdescent : baseEnd_1996430 < baseStart_1996430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996473 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_1996473 : Nat := 118140960795 + 1996473 * 2 ^ 59
def prefixEnd_1996473 : Nat := 4983230072969 + 3 ^ 40 * 1996473 * 2
def baseEnd_1996473 : Nat := 683433508482581682603929

theorem tailTrace_1996473 : CollatzResearch.WordTrace tailWord_1996473 prefixEnd_1996473 683433508482581682603929 := by
  unfold tailWord_1996473
  simp only [CollatzResearch.WordTrace]
  refine ⟨72817352496126766287466073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48544901664084510858310715 72817352496126766287466073)
  ·
    refine ⟨54613014372095074715599555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72817352496126766287466073 54613014372095074715599555)
    ·
      refine ⟨81919521558142612073399333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54613014372095074715599555 81919521558142612073399333)
      ·
        refine ⟨15359910292151739763762375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81919521558142612073399333 15359910292151739763762375)
        ·
          refine ⟨23039865438227609645643563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15359910292151739763762375 23039865438227609645643563)
          ·
            refine ⟨34559798157341414468465345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23039865438227609645643563 34559798157341414468465345)
            ·
              refine ⟨25919848618006060851349009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34559798157341414468465345 25919848618006060851349009)
              ·
                refine ⟨19439886463504545638511757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25919848618006060851349009 19439886463504545638511757)
                ·
                  refine ⟨7289957423814204614441909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19439886463504545638511757 7289957423814204614441909)
                  ·
                    refine ⟨683433508482581682603929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7289957423814204614441909 683433508482581682603929)
                    ·
                      rfl

theorem cell22_1996473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_1996473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996473 prefixEnd_1996473 := by exact prefixLift 1996473
  have htrace : WordTrace (prefixWord ++ tailWord_1996473) baseStart_1996473 baseEnd_1996473 := by
    simpa [prefixWord, tailWord_1996473, baseEnd_1996473] using wordTrace_append hprefix tailTrace_1996473
  have hstable : (prefixWord ++ tailWord_1996473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996473).length < 2 ^ (prefixWord ++ tailWord_1996473).sum := by decide
  have hdescent : baseEnd_1996473 < baseStart_1996473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996488 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_1996488 : Nat := 118140960795 + 1996488 * 2 ^ 59
def prefixEnd_1996488 : Nat := 4983230072969 + 3 ^ 40 * 1996488 * 2
def baseEnd_1996488 : Nat := 683438643289126643478883

theorem tailTrace_1996488 : CollatzResearch.WordTrace tailWord_1996488 prefixEnd_1996488 683438643289126643478883 := by
  unfold tailWord_1996488
  simp only [CollatzResearch.WordTrace]
  refine ⟨36408949795536211924631059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48545266394048282566174745 36408949795536211924631059)
  ·
    refine ⟨54613424693304317886946589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36408949795536211924631059 54613424693304317886946589)
    ·
      refine ⟨20480034259989119207604971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54613424693304317886946589 20480034259989119207604971)
      ·
        refine ⟨30720051389983678811407457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20480034259989119207604971 30720051389983678811407457)
        ·
          refine ⟨23040038542487759108555593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30720051389983678811407457 23040038542487759108555593)
          ·
            refine ⟨17280028906865819331416695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23040038542487759108555593 17280028906865819331416695)
            ·
              refine ⟨25920043360298728997125043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17280028906865819331416695 25920043360298728997125043)
              ·
                refine ⟨38880065040448093495687565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25920043360298728997125043 38880065040448093495687565)
                ·
                  refine ⟨14580024390168035060882837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38880065040448093495687565 14580024390168035060882837)
                  ·
                    refine ⟨683438643289126643478883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14580024390168035060882837 683438643289126643478883)
                    ·
                      rfl

theorem cell22_1996488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1996488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996488 prefixEnd_1996488 := by exact prefixLift 1996488
  have htrace : WordTrace (prefixWord ++ tailWord_1996488) baseStart_1996488 baseEnd_1996488 := by
    simpa [prefixWord, tailWord_1996488, baseEnd_1996488] using wordTrace_append hprefix tailTrace_1996488
  have hstable : (prefixWord ++ tailWord_1996488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996488).length < 2 ^ (prefixWord ++ tailWord_1996488).sum := by decide
  have hdescent : baseEnd_1996488 < baseStart_1996488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996503 : List Nat := [1, 1, 3, 2, 1, 3, 3, 8]
def baseStart_1996503 : Nat := 118140960795 + 1996503 * 2 ^ 59
def prefixEnd_1996503 : Nat := 4983230072969 + 3 ^ 40 * 1996503 * 2
def baseEnd_1996503 : Nat := 75938197566185733817093

theorem tailTrace_1996503 : CollatzResearch.WordTrace tailWord_1996503 prefixEnd_1996503 75938197566185733817093 := by
  unfold tailWord_1996503
  simp only [CollatzResearch.WordTrace]
  refine ⟨72818446686018081411058163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48545631124012054274038775 72818446686018081411058163)
  ·
    refine ⟨109227670029027122116587245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72818446686018081411058163 109227670029027122116587245)
    ·
      refine ⟨40960376260885170793720217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109227670029027122116587245 40960376260885170793720217)
      ·
        refine ⟨30720282195663878095290163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40960376260885170793720217 30720282195663878095290163)
        ·
          refine ⟨46080423293495817142935245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30720282195663878095290163 46080423293495817142935245)
          ·
            refine ⟨17280158735060931428600717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46080423293495817142935245 17280158735060931428600717)
            ·
              refine ⟨6480059525647849285725269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17280158735060931428600717 6480059525647849285725269)
              ·
                refine ⟨75938197566185733817093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6480059525647849285725269 75938197566185733817093)
                ·
                  rfl

theorem cell22_1996503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 8].length) (baseStart_1996503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996503 prefixEnd_1996503 := by exact prefixLift 1996503
  have htrace : WordTrace (prefixWord ++ tailWord_1996503) baseStart_1996503 baseEnd_1996503 := by
    simpa [prefixWord, tailWord_1996503, baseEnd_1996503] using wordTrace_append hprefix tailTrace_1996503
  have hstable : (prefixWord ++ tailWord_1996503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996503).length < 2 ^ (prefixWord ++ tailWord_1996503).sum := by decide
  have hdescent : baseEnd_1996503 < baseStart_1996503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996520 : List Nat := [2, 1, 4, 1, 3, 3, 8]
def baseStart_1996520 : Nat := 118140960795 + 1996520 * 2 ^ 59
def prefixEnd_1996520 : Nat := 4983230072969 + 3 ^ 40 * 1996520 * 2
def baseEnd_1996520 : Nat := 25312948057151452839955

theorem tailTrace_1996520 : CollatzResearch.WordTrace tailWord_1996520 prefixEnd_1996520 25312948057151452839955 := by
  unfold tailWord_1996520
  simp only [CollatzResearch.WordTrace]
  refine ⟨36409533363478246657213507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48546044484637662209618009 36409533363478246657213507)
  ·
    refine ⟨54614300045217369985820261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36409533363478246657213507 54614300045217369985820261)
    ·
      refine ⟨10240181258478256872341299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54614300045217369985820261 10240181258478256872341299)
      ·
        refine ⟨15360271887717385308511949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240181258478256872341299 15360271887717385308511949)
        ·
          refine ⟨5760101957894019490691981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15360271887717385308511949 5760101957894019490691981)
          ·
            refine ⟨2160038234210257309009493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5760101957894019490691981 2160038234210257309009493)
            ·
              refine ⟨25312948057151452839955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2160038234210257309009493 25312948057151452839955)
              ·
                rfl

theorem cell22_1996520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 8].length) (baseStart_1996520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996520 prefixEnd_1996520 := by exact prefixLift 1996520
  have htrace : WordTrace (prefixWord ++ tailWord_1996520) baseStart_1996520 baseEnd_1996520 := by
    simpa [prefixWord, tailWord_1996520, baseEnd_1996520] using wordTrace_append hprefix tailTrace_1996520
  have hstable : (prefixWord ++ tailWord_1996520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996520).length < 2 ^ (prefixWord ++ tailWord_1996520).sum := by decide
  have hdescent : baseEnd_1996520 < baseStart_1996520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996563 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 3, 7]
def baseStart_1996563 : Nat := 118140960795 + 1996563 * 2 ^ 59
def prefixEnd_1996563 : Nat := 4983230072969 + 3 ^ 40 * 1996563 * 2
def baseEnd_1996563 : Nat := 683464317321851447853653

theorem tailTrace_1996563 : CollatzResearch.WordTrace tailWord_1996563 prefixEnd_1996563 683464317321851447853653 := by
  unfold tailWord_1996563
  simp only [CollatzResearch.WordTrace]
  refine ⟨72820635065800711658242343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48547090043867141105494895 72820635065800711658242343)
  ·
    refine ⟨109230952598701067487363515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72820635065800711658242343 109230952598701067487363515)
    ·
      refine ⟨163846428898051601231045273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109230952598701067487363515 163846428898051601231045273)
      ·
        refine ⟨122884821673538700923283955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163846428898051601231045273 122884821673538700923283955)
        ·
          refine ⟨184327232510308051384925933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122884821673538700923283955 184327232510308051384925933)
          ·
            refine ⟨69122712191365519269347225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184327232510308051384925933 69122712191365519269347225)
            ·
              refine ⟨51842034143524139452010419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69122712191365519269347225 51842034143524139452010419)
              ·
                refine ⟨77763051215286209178015629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51842034143524139452010419 77763051215286209178015629)
                ·
                  refine ⟨29161144205732328441755861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77763051215286209178015629 29161144205732328441755861)
                  ·
                    refine ⟨683464317321851447853653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29161144205732328441755861 683464317321851447853653)
                    ·
                      rfl

theorem cell22_1996563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_1996563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996563 prefixEnd_1996563 := by exact prefixLift 1996563
  have htrace : WordTrace (prefixWord ++ tailWord_1996563) baseStart_1996563 baseEnd_1996563 := by
    simpa [prefixWord, tailWord_1996563, baseEnd_1996563] using wordTrace_append hprefix tailTrace_1996563
  have hstable : (prefixWord ++ tailWord_1996563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996563).length < 2 ^ (prefixWord ++ tailWord_1996563).sum := by decide
  have hdescent : baseEnd_1996563 < baseStart_1996563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996597 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1996597 : Nat := 118140960795 + 1996597 * 2 ^ 59
def prefixEnd_1996597 : Nat := 4983230072969 + 3 ^ 40 * 1996597 * 2
def baseEnd_1996597 : Nat := 683475956216686692503549

theorem tailTrace_1996597 : CollatzResearch.WordTrace tailWord_1996597 prefixEnd_1996597 683475956216686692503549 := by
  unfold tailWord_1996597
  simp only [CollatzResearch.WordTrace]
  refine ⟨72821875147677535464980045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48547916765118356976653363 72821875147677535464980045)
  ·
    refine ⟨27308203180379075799367517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72821875147677535464980045 27308203180379075799367517)
    ·
      refine ⟨10240576192642153424762819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27308203180379075799367517 10240576192642153424762819)
      ·
        refine ⟨15360864288963230137144229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240576192642153424762819 15360864288963230137144229)
        ·
          refine ⟨2880162054180605650714543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15360864288963230137144229 2880162054180605650714543)
          ·
            refine ⟨4320243081270908476071815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880162054180605650714543 4320243081270908476071815)
            ·
              refine ⟨6480364621906362714107723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320243081270908476071815 6480364621906362714107723)
              ·
                refine ⟨9720546932859544071161585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480364621906362714107723 9720546932859544071161585)
                ·
                  refine ⟨7290410199644658053371189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9720546932859544071161585 7290410199644658053371189)
                  ·
                    refine ⟨683475956216686692503549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7290410199644658053371189 683475956216686692503549)
                    ·
                      rfl

theorem cell22_1996597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1996597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996597 prefixEnd_1996597 := by exact prefixLift 1996597
  have htrace : WordTrace (prefixWord ++ tailWord_1996597) baseStart_1996597 baseEnd_1996597 := by
    simpa [prefixWord, tailWord_1996597, baseEnd_1996597] using wordTrace_append hprefix tailTrace_1996597
  have hstable : (prefixWord ++ tailWord_1996597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996597).length < 2 ^ (prefixWord ++ tailWord_1996597).sum := by decide
  have hdescent : baseEnd_1996597 < baseStart_1996597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996629 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_1996629 : Nat := 118140960795 + 1996629 * 2 ^ 59
def prefixEnd_1996629 : Nat := 4983230072969 + 3 ^ 40 * 1996629 * 2
def baseEnd_1996629 : Nat := 683486910470649275703451

theorem tailTrace_1996629 : CollatzResearch.WordTrace tailWord_1996629 prefixEnd_1996629 683486910470649275703451 := by
  unfold tailWord_1996629
  simp only [CollatzResearch.WordTrace]
  refine ⟨72823042283561604930144941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48548694855707736620096627 72823042283561604930144941)
  ·
    refine ⟨27308640856335601848804353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72823042283561604930144941 27308640856335601848804353)
    ·
      refine ⟨20481480642251701386603265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27308640856335601848804353 20481480642251701386603265)
      ·
        refine ⟨15361110481688776039952449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20481480642251701386603265 15361110481688776039952449)
        ·
          refine ⟨11520832861266582029964337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15361110481688776039952449 11520832861266582029964337)
          ·
            refine ⟨8640624645949936522473253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11520832861266582029964337 8640624645949936522473253)
            ·
              refine ⟨1620117121115613097963735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8640624645949936522473253 1620117121115613097963735)
              ·
                refine ⟨2430175681673419646945603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620117121115613097963735 2430175681673419646945603)
                ·
                  refine ⟨3645263522510129470418405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430175681673419646945603 3645263522510129470418405)
                  ·
                    refine ⟨683486910470649275703451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3645263522510129470418405 683486910470649275703451)
                    ·
                      rfl

theorem cell22_1996629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_1996629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996629 prefixEnd_1996629 := by exact prefixLift 1996629
  have htrace : WordTrace (prefixWord ++ tailWord_1996629) baseStart_1996629 baseEnd_1996629 := by
    simpa [prefixWord, tailWord_1996629, baseEnd_1996629] using wordTrace_append hprefix tailTrace_1996629
  have hstable : (prefixWord ++ tailWord_1996629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996629).length < 2 ^ (prefixWord ++ tailWord_1996629).sum := by decide
  have hdescent : baseEnd_1996629 < baseStart_1996629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996745 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 8]
def baseStart_1996745 : Nat := 118140960795 + 1996745 * 2 ^ 59
def prefixEnd_1996745 : Nat := 4983230072969 + 3 ^ 40 * 1996745 * 2
def baseEnd_1996745 : Nat := 227842206547087879934365

theorem tailTrace_1996745 : CollatzResearch.WordTrace tailWord_1996745 prefixEnd_1996745 227842206547087879934365 := by
  unfold tailWord_1996745
  simp only [CollatzResearch.WordTrace]
  refine ⟨72827273151141356741367689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48551515434094237827578459 72827273151141356741367689)
  ·
    refine ⟨54620454863356017556025767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72827273151141356741367689 54620454863356017556025767)
    ·
      refine ⟨81930682295034026334038651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54620454863356017556025767 81930682295034026334038651)
      ·
        refine ⟨122896023442551039501057977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81930682295034026334038651 122896023442551039501057977)
        ·
          refine ⟨92172017581913279625793483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122896023442551039501057977 92172017581913279625793483)
          ·
            refine ⟨138258026372869919438690225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92172017581913279625793483 138258026372869919438690225)
            ·
              refine ⟨103693519779652439579017669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138258026372869919438690225 103693519779652439579017669)
              ·
                refine ⟨19442534958684832421065813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103693519779652439579017669 19442534958684832421065813)
                ·
                  refine ⟨227842206547087879934365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19442534958684832421065813 227842206547087879934365)
                  ·
                    rfl

theorem cell22_1996745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_1996745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996745 prefixEnd_1996745 := by exact prefixLift 1996745
  have htrace : WordTrace (prefixWord ++ tailWord_1996745) baseStart_1996745 baseEnd_1996745 := by
    simpa [prefixWord, tailWord_1996745, baseEnd_1996745] using wordTrace_append hprefix tailTrace_1996745
  have hstable : (prefixWord ++ tailWord_1996745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996745).length < 2 ^ (prefixWord ++ tailWord_1996745).sum := by decide
  have hdescent : baseEnd_1996745 < baseStart_1996745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996798 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1996798 : Nat := 118140960795 + 1996798 * 2 ^ 59
def prefixEnd_1996798 : Nat := 4983230072969 + 3 ^ 40 * 1996798 * 2
def baseEnd_1996798 : Nat := 683544762624389168227933

theorem tailTrace_1996798 : CollatzResearch.WordTrace tailWord_1996798 prefixEnd_1996798 683544762624389168227933 := by
  unfold tailWord_1996798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103650777493668349130881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48552804146632897862031365 9103650777493668349130881)
  ·
    refine ⟨6827738083120251261848161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9103650777493668349130881 6827738083120251261848161)
    ·
      refine ⟨5120803562340188446386121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6827738083120251261848161 5120803562340188446386121)
      ·
        refine ⟨3840602671755141334789591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5120803562340188446386121 3840602671755141334789591)
        ·
          refine ⟨5760904007632712002184387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3840602671755141334789591 5760904007632712002184387)
          ·
            refine ⟨8641356011449068003276581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760904007632712002184387 8641356011449068003276581)
            ·
              refine ⟨1620254252146700250614359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8641356011449068003276581 1620254252146700250614359)
              ·
                refine ⟨2430381378220050375921539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620254252146700250614359 2430381378220050375921539)
                ·
                  refine ⟨3645572067330075563882309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430381378220050375921539 3645572067330075563882309)
                  ·
                    refine ⟨683544762624389168227933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3645572067330075563882309 683544762624389168227933)
                    ·
                      rfl

theorem cell22_1996798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1996798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996798 prefixEnd_1996798 := by exact prefixLift 1996798
  have htrace : WordTrace (prefixWord ++ tailWord_1996798) baseStart_1996798 baseEnd_1996798 := by
    simpa [prefixWord, tailWord_1996798, baseEnd_1996798] using wordTrace_append hprefix tailTrace_1996798
  have hstable : (prefixWord ++ tailWord_1996798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996798).length < 2 ^ (prefixWord ++ tailWord_1996798).sum := by decide
  have hdescent : baseEnd_1996798 < baseStart_1996798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996807 : List Nat := [1, 1, 4, 3, 1, 3, 9]
def baseStart_1996807 : Nat := 118140960795 + 1996807 * 2 ^ 59
def prefixEnd_1996807 : Nat := 4983230072969 + 3 ^ 40 * 1996807 * 2
def baseEnd_1996807 : Nat := 25316586796604301657515

theorem tailTrace_1996807 : CollatzResearch.WordTrace tailWord_1996807 prefixEnd_1996807 25316586796604301657515 := by
  unfold tailWord_1996807
  simp only [CollatzResearch.WordTrace]
  refine ⟨72829534476916741330124675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48553022984611160886749783 72829534476916741330124675)
  ·
    refine ⟨109244301715375111995187013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72829534476916741330124675 109244301715375111995187013)
    ·
      refine ⟨20483306571632833499097565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109244301715375111995187013 20483306571632833499097565)
      ·
        refine ⟨7681239964362312562161587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20483306571632833499097565 7681239964362312562161587)
        ·
          refine ⟨11521859946543468843242381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7681239964362312562161587 11521859946543468843242381)
          ·
            refine ⟨4320697479953800816215893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11521859946543468843242381 4320697479953800816215893)
            ·
              refine ⟨25316586796604301657515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4320697479953800816215893 25316586796604301657515)
              ·
                rfl

theorem cell22_1996807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 9].length) (baseStart_1996807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996807 prefixEnd_1996807 := by exact prefixLift 1996807
  have htrace : WordTrace (prefixWord ++ tailWord_1996807) baseStart_1996807 baseEnd_1996807 := by
    simpa [prefixWord, tailWord_1996807, baseEnd_1996807] using wordTrace_append hprefix tailTrace_1996807
  have hstable : (prefixWord ++ tailWord_1996807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996807).length < 2 ^ (prefixWord ++ tailWord_1996807).sum := by decide
  have hdescent : baseEnd_1996807 < baseStart_1996807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996828 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_1996828 : Nat := 118140960795 + 1996828 * 2 ^ 59
def prefixEnd_1996828 : Nat := 4983230072969 + 3 ^ 40 * 1996828 * 2
def baseEnd_1996828 : Nat := 683555032237479089977841

theorem tailTrace_1996828 : CollatzResearch.WordTrace tailWord_1996828 prefixEnd_1996828 683555032237479089977841 := by
  unfold tailWord_1996828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36415150204920330958319569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48553533606560441277759425 36415150204920330958319569)
  ·
    refine ⟨27311362653690248218739677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36415150204920330958319569 27311362653690248218739677)
    ·
      refine ⟨10241760995133843082027379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27311362653690248218739677 10241760995133843082027379)
      ·
        refine ⟨15362641492700764623041069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241760995133843082027379 15362641492700764623041069)
        ·
          refine ⟨5760990559762786733640401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15362641492700764623041069 5760990559762786733640401)
          ·
            refine ⟨4320742919822090050230301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5760990559762786733640401 4320742919822090050230301)
            ·
              refine ⟨1620278594933283768836363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4320742919822090050230301 1620278594933283768836363)
              ·
                refine ⟨2430417892399925653254545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620278594933283768836363 2430417892399925653254545)
                ·
                  refine ⟨1822813419299944239940909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2430417892399925653254545 1822813419299944239940909)
                  ·
                    refine ⟨683555032237479089977841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1822813419299944239940909 683555032237479089977841)
                    ·
                      rfl

theorem cell22_1996828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_1996828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996828 prefixEnd_1996828 := by exact prefixLift 1996828
  have htrace : WordTrace (prefixWord ++ tailWord_1996828) baseStart_1996828 baseEnd_1996828 := by
    simpa [prefixWord, tailWord_1996828, baseEnd_1996828] using wordTrace_append hprefix tailTrace_1996828
  have hstable : (prefixWord ++ tailWord_1996828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996828).length < 2 ^ (prefixWord ++ tailWord_1996828).sum := by decide
  have hdescent : baseEnd_1996828 < baseStart_1996828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996867 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 2, 5]
def baseStart_1996867 : Nat := 118140960795 + 1996867 * 2 ^ 59
def prefixEnd_1996867 : Nat := 4983230072969 + 3 ^ 40 * 1996867 * 2
def baseEnd_1996867 : Nat := 683568382734495988252721

theorem tailTrace_1996867 : CollatzResearch.WordTrace tailWord_1996867 prefixEnd_1996867 683568382734495988252721 := by
  unfold tailWord_1996867
  simp only [CollatzResearch.WordTrace]
  refine ⟨72831722856699371577308855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48554481904466247718205903 72831722856699371577308855)
  ·
    refine ⟨109247584285049057365963283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72831722856699371577308855 109247584285049057365963283)
    ·
      refine ⟨163871376427573586048944925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109247584285049057365963283 163871376427573586048944925)
      ·
        refine ⟨61451766160340094768354347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163871376427573586048944925 61451766160340094768354347)
        ·
          refine ⟨92177649240510142152531521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61451766160340094768354347 92177649240510142152531521)
          ·
            refine ⟨69133236930382606614398641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92177649240510142152531521 69133236930382606614398641)
            ·
              refine ⟨51849927697786954960798981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69133236930382606614398641 51849927697786954960798981)
              ·
                refine ⟨9721861443335054055149809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51849927697786954960798981 9721861443335054055149809)
                ·
                  refine ⟨7291396082501290541362357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721861443335054055149809 7291396082501290541362357)
                  ·
                    refine ⟨683568382734495988252721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7291396082501290541362357 683568382734495988252721)
                    ·
                      rfl

theorem cell22_1996867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_1996867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996867 prefixEnd_1996867 := by exact prefixLift 1996867
  have htrace : WordTrace (prefixWord ++ tailWord_1996867) baseStart_1996867 baseEnd_1996867 := by
    simpa [prefixWord, tailWord_1996867, baseEnd_1996867] using wordTrace_append hprefix tailTrace_1996867
  have hstable : (prefixWord ++ tailWord_1996867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996867).length < 2 ^ (prefixWord ++ tailWord_1996867).sum := by decide
  have hdescent : baseEnd_1996867 < baseStart_1996867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996873 : List Nat := [1, 2, 1, 1, 2, 2, 7, 2, 1, 3]
def baseStart_1996873 : Nat := 118140960795 + 1996873 * 2 ^ 59
def prefixEnd_1996873 : Nat := 4983230072969 + 3 ^ 40 * 1996873 * 2
def baseEnd_1996873 : Nat := 683570436657113972602703

theorem tailTrace_1996873 : CollatzResearch.WordTrace tailWord_1996873 prefixEnd_1996873 683570436657113972602703 := by
  unfold tailWord_1996873
  simp only [CollatzResearch.WordTrace]
  refine ⟨72831941694677634602027273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48554627796451756401351515 72831941694677634602027273)
  ·
    refine ⟨54623956271008225951520455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72831941694677634602027273 54623956271008225951520455)
    ·
      refine ⟨81935934406512338927280683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54623956271008225951520455 81935934406512338927280683)
      ·
        refine ⟨122903901609768508390921025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81935934406512338927280683 122903901609768508390921025)
        ·
          refine ⟨92177926207326381293190769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122903901609768508390921025 92177926207326381293190769)
          ·
            refine ⟨69133444655494785969893077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92177926207326381293190769 69133444655494785969893077)
            ·
              refine ⟨1620315109113159046169369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69133444655494785969893077 1620315109113159046169369)
              ·
                refine ⟨1215236331834869284627027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620315109113159046169369 1215236331834869284627027)
                ·
                  refine ⟨1822854497752303926940541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215236331834869284627027 1822854497752303926940541)
                  ·
                    refine ⟨683570436657113972602703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1822854497752303926940541 683570436657113972602703)
                    ·
                      rfl

theorem cell22_1996873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 3].length) (baseStart_1996873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996873 prefixEnd_1996873 := by exact prefixLift 1996873
  have htrace : WordTrace (prefixWord ++ tailWord_1996873) baseStart_1996873 baseEnd_1996873 := by
    simpa [prefixWord, tailWord_1996873, baseEnd_1996873] using wordTrace_append hprefix tailTrace_1996873
  have hstable : (prefixWord ++ tailWord_1996873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996873).length < 2 ^ (prefixWord ++ tailWord_1996873).sum := by decide
  have hdescent : baseEnd_1996873 < baseStart_1996873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996897 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 8]
def baseStart_1996897 : Nat := 118140960795 + 1996897 * 2 ^ 59
def prefixEnd_1996897 : Nat := 4983230072969 + 3 ^ 40 * 1996897 * 2
def baseEnd_1996897 : Nat := 227859550782528636667543

theorem tailTrace_1996897 : CollatzResearch.WordTrace tailWord_1996897 prefixEnd_1996897 227859550782528636667543 := by
  unfold tailWord_1996897
  simp only [CollatzResearch.WordTrace]
  refine ⟨72832817046590686700900945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48555211364393791133933963 72832817046590686700900945)
  ·
    refine ⟨54624612784943015025675709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72832817046590686700900945 54624612784943015025675709)
    ·
      refine ⟨20484229794353630634628391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54624612784943015025675709 20484229794353630634628391)
      ·
        refine ⟨30726344691530445951942587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20484229794353630634628391 30726344691530445951942587)
        ·
          refine ⟨46089517037295668927913881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30726344691530445951942587 46089517037295668927913881)
          ·
            refine ⟨34567137777971751695935411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46089517037295668927913881 34567137777971751695935411)
            ·
              refine ⟨51850706666957627543903117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34567137777971751695935411 51850706666957627543903117)
              ·
                refine ⟨19444015000109110328963669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51850706666957627543903117 19444015000109110328963669)
                ·
                  refine ⟨227859550782528636667543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19444015000109110328963669 227859550782528636667543)
                  ·
                    rfl

theorem cell22_1996897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_1996897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996897 prefixEnd_1996897 := by exact prefixLift 1996897
  have htrace : WordTrace (prefixWord ++ tailWord_1996897) baseStart_1996897 baseEnd_1996897 := by
    simpa [prefixWord, tailWord_1996897, baseEnd_1996897] using wordTrace_append hprefix tailTrace_1996897
  have hstable : (prefixWord ++ tailWord_1996897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996897).length < 2 ^ (prefixWord ++ tailWord_1996897).sum := by decide
  have hdescent : baseEnd_1996897 < baseStart_1996897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996931 : List Nat := [1, 1, 1, 3, 3, 4, 1, 4, 4]
def baseStart_1996931 : Nat := 118140960795 + 1996931 * 2 ^ 59
def prefixEnd_1996931 : Nat := 4983230072969 + 3 ^ 40 * 1996931 * 2
def baseEnd_1996931 : Nat := 227863430414140384884175

theorem tailTrace_1996931 : CollatzResearch.WordTrace tailWord_1996931 prefixEnd_1996931 227863430414140384884175 := by
  unfold tailWord_1996931
  simp only [CollatzResearch.WordTrace]
  refine ⟨72834057128467510507638647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48556038085645007005092431 72834057128467510507638647)
  ·
    refine ⟨109251085692701265761457971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72834057128467510507638647 109251085692701265761457971)
    ·
      refine ⟨163876628539051898642186957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109251085692701265761457971 163876628539051898642186957)
      ·
        refine ⟨61453735702144461990820109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163876628539051898642186957 61453735702144461990820109)
        ·
          refine ⟨23045150888304173246557541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61453735702144461990820109 23045150888304173246557541)
          ·
            refine ⟨4320965791557032483729539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23045150888304173246557541 4320965791557032483729539)
            ·
              refine ⟨6481448687335548725594309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320965791557032483729539 6481448687335548725594309)
              ·
                refine ⟨1215271628875415386048933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6481448687335548725594309 1215271628875415386048933)
                ·
                  refine ⟨227863430414140384884175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1215271628875415386048933 227863430414140384884175)
                  ·
                    rfl

theorem cell22_1996931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 4].length) (baseStart_1996931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996931 prefixEnd_1996931 := by exact prefixLift 1996931
  have htrace : WordTrace (prefixWord ++ tailWord_1996931) baseStart_1996931 baseEnd_1996931 := by
    simpa [prefixWord, tailWord_1996931, baseEnd_1996931] using wordTrace_append hprefix tailTrace_1996931
  have hstable : (prefixWord ++ tailWord_1996931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996931).length < 2 ^ (prefixWord ++ tailWord_1996931).sum := by decide
  have hdescent : baseEnd_1996931 < baseStart_1996931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996946 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1996946 : Nat := 118140960795 + 1996946 * 2 ^ 59
def prefixEnd_1996946 : Nat := 4983230072969 + 3 ^ 40 * 1996946 * 2
def baseEnd_1996946 : Nat := 683595426048966115527479

theorem tailTrace_1996946 : CollatzResearch.WordTrace tailWord_1996946 prefixEnd_1996946 683595426048966115527479 := by
  unfold tailWord_1996946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18208651055853292017358673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48556402815608778712956461 18208651055853292017358673)
  ·
    refine ⟨13656488291889969013019005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18208651055853292017358673 13656488291889969013019005)
    ·
      refine ⟨5121183109458738379882127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13656488291889969013019005 5121183109458738379882127)
      ·
        refine ⟨7681774664188107569823191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121183109458738379882127 7681774664188107569823191)
        ·
          refine ⟨11522661996282161354734787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7681774664188107569823191 11522661996282161354734787)
          ·
            refine ⟨17283992994423242032102181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11522661996282161354734787 17283992994423242032102181)
            ·
              refine ⟨3240748686454357881019159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17283992994423242032102181 3240748686454357881019159)
              ·
                refine ⟨4861123029681536821528739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240748686454357881019159 4861123029681536821528739)
                ·
                  refine ⟨7291684544522305232293109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861123029681536821528739 7291684544522305232293109)
                  ·
                    refine ⟨683595426048966115527479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7291684544522305232293109 683595426048966115527479)
                    ·
                      rfl

theorem cell22_1996946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1996946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996946 prefixEnd_1996946 := by exact prefixLift 1996946
  have htrace : WordTrace (prefixWord ++ tailWord_1996946) baseStart_1996946 baseEnd_1996946 := by
    simpa [prefixWord, tailWord_1996946, baseEnd_1996946] using wordTrace_append hprefix tailTrace_1996946
  have hstable : (prefixWord ++ tailWord_1996946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996946).length < 2 ^ (prefixWord ++ tailWord_1996946).sum := by decide
  have hdescent : baseEnd_1996946 < baseStart_1996946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996948 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1996948 : Nat := 118140960795 + 1996948 * 2 ^ 59
def prefixEnd_1996948 : Nat := 4983230072969 + 3 ^ 40 * 1996948 * 2
def baseEnd_1996948 : Nat := 227865370229946258992491

theorem tailTrace_1996948 : CollatzResearch.WordTrace tailWord_1996948 prefixEnd_1996948 227865370229946258992491 := by
  unfold tailWord_1996948
  simp only [CollatzResearch.WordTrace]
  refine ⟨36417338584702961205503749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48556451446270614940671665 36417338584702961205503749)
  ·
    refine ⟨6828250984631805226031953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36417338584702961205503749 6828250984631805226031953)
    ·
      refine ⟨5121188238473853919523965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6828250984631805226031953 5121188238473853919523965)
      ·
        refine ⟨1920445589427695219821487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5121188238473853919523965 1920445589427695219821487)
        ·
          refine ⟨2880668384141542829732231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920445589427695219821487 2880668384141542829732231)
          ·
            refine ⟨4321002576212314244598347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880668384141542829732231 4321002576212314244598347)
            ·
              refine ⟨6481503864318471366897521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321002576212314244598347 6481503864318471366897521)
              ·
                refine ⟨4861127898238853525173141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6481503864318471366897521 4861127898238853525173141)
                ·
                  refine ⟨227865370229946258992491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4861127898238853525173141 227865370229946258992491)
                  ·
                    rfl

theorem cell22_1996948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1996948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996948 prefixEnd_1996948 := by exact prefixLift 1996948
  have htrace : WordTrace (prefixWord ++ tailWord_1996948) baseStart_1996948 baseEnd_1996948 := by
    simpa [prefixWord, tailWord_1996948, baseEnd_1996948] using wordTrace_append hprefix tailTrace_1996948
  have hstable : (prefixWord ++ tailWord_1996948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996948).length < 2 ^ (prefixWord ++ tailWord_1996948).sum := by decide
  have hdescent : baseEnd_1996948 < baseStart_1996948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996961 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1996961 : Nat := 118140960795 + 1996961 * 2 ^ 59
def prefixEnd_1996961 : Nat := 4983230072969 + 3 ^ 40 * 1996961 * 2
def baseEnd_1996961 : Nat := 683600560855511076402433

theorem tailTrace_1996961 : CollatzResearch.WordTrace tailWord_1996961 prefixEnd_1996961 683600560855511076402433 := by
  unfold tailWord_1996961
  simp only [CollatzResearch.WordTrace]
  refine ⟨72835151318358825631230737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48556767545572550420820491 72835151318358825631230737)
  ·
    refine ⟨54626363488769119223423053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72835151318358825631230737 54626363488769119223423053)
    ·
      refine ⟨20484886308288419708783645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54626363488769119223423053 20484886308288419708783645)
      ·
        refine ⟨7681832365608157390793867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20484886308288419708783645 7681832365608157390793867)
        ·
          refine ⟨11522748548412236086190801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7681832365608157390793867 11522748548412236086190801)
          ·
            refine ⟨8642061411309177064643101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11522748548412236086190801 8642061411309177064643101)
            ·
              refine ⟨3240773029240941399241163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8642061411309177064643101 3240773029240941399241163)
              ·
                refine ⟨4861159543861412098861745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240773029240941399241163 4861159543861412098861745)
                ·
                  refine ⟨3645869657896059074146309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4861159543861412098861745 3645869657896059074146309)
                  ·
                    refine ⟨683600560855511076402433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3645869657896059074146309 683600560855511076402433)
                    ·
                      rfl

theorem cell22_1996961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1996961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996961 prefixEnd_1996961 := by exact prefixLift 1996961
  have htrace : WordTrace (prefixWord ++ tailWord_1996961) baseStart_1996961 baseEnd_1996961 := by
    simpa [prefixWord, tailWord_1996961, baseEnd_1996961] using wordTrace_append hprefix tailTrace_1996961
  have hstable : (prefixWord ++ tailWord_1996961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996961).length < 2 ^ (prefixWord ++ tailWord_1996961).sum := by decide
  have hdescent : baseEnd_1996961 < baseStart_1996961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996967 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1996967 : Nat := 118140960795 + 1996967 * 2 ^ 59
def prefixEnd_1996967 : Nat := 4983230072969 + 3 ^ 40 * 1996967 * 2
def baseEnd_1996967 : Nat := 683602614778129060752415

theorem tailTrace_1996967 : CollatzResearch.WordTrace tailWord_1996967 prefixEnd_1996967 683602614778129060752415 := by
  unfold tailWord_1996967
  simp only [CollatzResearch.WordTrace]
  refine ⟨72835370156337088655949155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48556913437558059103966103 72835370156337088655949155)
  ·
    refine ⟨109253055234505632983923733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72835370156337088655949155 109253055234505632983923733)
    ·
      refine ⟨5121236964117451546121425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109253055234505632983923733 5121236964117451546121425)
      ·
        refine ⟨3840927723088088659591069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121236964117451546121425 3840927723088088659591069)
        ·
          refine ⟨1440347896158033247346651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3840927723088088659591069 1440347896158033247346651)
          ·
            refine ⟨2160521844237049871019977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440347896158033247346651 2160521844237049871019977)
            ·
              refine ⟨1620391383177787403264983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2160521844237049871019977 1620391383177787403264983)
              ·
                refine ⟨2430587074766681104897475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620391383177787403264983 2430587074766681104897475)
                ·
                  refine ⟨3645880612150021657346213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430587074766681104897475 3645880612150021657346213)
                  ·
                    refine ⟨683602614778129060752415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3645880612150021657346213 683602614778129060752415)
                    ·
                      rfl

theorem cell22_1996967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1996967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1996967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1996967 prefixEnd_1996967 := by exact prefixLift 1996967
  have htrace : WordTrace (prefixWord ++ tailWord_1996967) baseStart_1996967 baseEnd_1996967 := by
    simpa [prefixWord, tailWord_1996967, baseEnd_1996967] using wordTrace_append hprefix tailTrace_1996967
  have hstable : (prefixWord ++ tailWord_1996967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996967).length < 2 ^ (prefixWord ++ tailWord_1996967).sum := by decide
  have hdescent : baseEnd_1996967 < baseStart_1996967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997021 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 7]
def baseStart_1997021 : Nat := 118140960795 + 1997021 * 2 ^ 59
def prefixEnd_1997021 : Nat := 4983230072969 + 3 ^ 40 * 1997021 * 2
def baseEnd_1997021 : Nat := 227873700027230306634083

theorem tailTrace_1997021 : CollatzResearch.WordTrace tailWord_1997021 prefixEnd_1997021 227873700027230306634083 := by
  unfold tailWord_1997021
  simp only [CollatzResearch.WordTrace]
  refine ⟨72837339698141455878414917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48558226465427637252276611 72837339698141455878414917)
  ·
    refine ⟨13657001193401522977202797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72837339698141455878414917 13657001193401522977202797)
    ·
      refine ⟨5121375447525571116451049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13657001193401522977202797 5121375447525571116451049)
      ·
        refine ⟨3841031585644178337338287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121375447525571116451049 3841031585644178337338287)
        ·
          refine ⟨5761547378466267506007431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841031585644178337338287 5761547378466267506007431)
          ·
            refine ⟨8642321067699401259011147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761547378466267506007431 8642321067699401259011147)
            ·
              refine ⟨12963481601549101888516721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642321067699401259011147 12963481601549101888516721)
              ·
                refine ⟨9722611201161826416387541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12963481601549101888516721 9722611201161826416387541)
                ·
                  refine ⟨227873700027230306634083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9722611201161826416387541 227873700027230306634083)
                  ·
                    rfl

theorem cell22_1997021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_1997021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997021 prefixEnd_1997021 := by exact prefixLift 1997021
  have htrace : WordTrace (prefixWord ++ tailWord_1997021) baseStart_1997021 baseEnd_1997021 := by
    simpa [prefixWord, tailWord_1997021, baseEnd_1997021] using wordTrace_append hprefix tailTrace_1997021
  have hstable : (prefixWord ++ tailWord_1997021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997021).length < 2 ^ (prefixWord ++ tailWord_1997021).sum := by decide
  have hdescent : baseEnd_1997021 < baseStart_1997021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997042 : List Nat := [3, 2, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_1997042 : Nat := 118140960795 + 1997042 * 2 ^ 59
def prefixEnd_1997042 : Nat := 4983230072969 + 3 ^ 40 * 1997042 * 2
def baseEnd_1997042 : Nat := 683628288810853865127185

theorem tailTrace_1997042 : CollatzResearch.WordTrace tailWord_1997042 prefixEnd_1997042 683628288810853865127185 := by
  unfold tailWord_1997042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18209526407766344116232345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48558737087376917643286253 18209526407766344116232345)
  ·
    refine ⟨13657144805824758087174259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18209526407766344116232345 13657144805824758087174259)
    ·
      refine ⟨20485717208737137130761389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13657144805824758087174259 20485717208737137130761389)
      ·
        refine ⟨7682143953276426424035521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20485717208737137130761389 7682143953276426424035521)
        ·
          refine ⟨5761607964957319818026641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7682143953276426424035521 5761607964957319818026641)
          ·
            refine ⟨4321205973717989863519981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5761607964957319818026641 4321205973717989863519981)
            ·
              refine ⟨1620452240144246198819993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4321205973717989863519981 1620452240144246198819993)
              ·
                refine ⟨1215339180108184649114995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620452240144246198819993 1215339180108184649114995)
                ·
                  refine ⟨1823008770162276973672493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215339180108184649114995 1823008770162276973672493)
                  ·
                    refine ⟨683628288810853865127185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1823008770162276973672493 683628288810853865127185)
                    ·
                      rfl

theorem cell22_1997042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_1997042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997042 prefixEnd_1997042 := by exact prefixLift 1997042
  have htrace : WordTrace (prefixWord ++ tailWord_1997042) baseStart_1997042 baseEnd_1997042 := by
    simpa [prefixWord, tailWord_1997042, baseEnd_1997042] using wordTrace_append hprefix tailTrace_1997042
  have hstable : (prefixWord ++ tailWord_1997042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997042).length < 2 ^ (prefixWord ++ tailWord_1997042).sum := by decide
  have hdescent : baseEnd_1997042 < baseStart_1997042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997049 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 6]
def baseStart_1997049 : Nat := 118140960795 + 1997049 * 2 ^ 59
def prefixEnd_1997049 : Nat := 4983230072969 + 3 ^ 40 * 1997049 * 2
def baseEnd_1997049 : Nat := 227876895017969393400721

theorem tailTrace_1997049 : CollatzResearch.WordTrace tailWord_1997049 prefixEnd_1997049 227876895017969393400721 := by
  unfold tailWord_1997049
  simp only [CollatzResearch.WordTrace]
  refine ⟨72838360942040016660434201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48558907294693344440289467 72838360942040016660434201)
  ·
    refine ⟨54628770706530012495325651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72838360942040016660434201 54628770706530012495325651)
    ·
      refine ⟨81943156059795018742988477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54628770706530012495325651 81943156059795018742988477)
      ·
        refine ⟨30728683522423132028620679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81943156059795018742988477 30728683522423132028620679)
        ·
          refine ⟨46093025283634698042931019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30728683522423132028620679 46093025283634698042931019)
          ·
            refine ⟨69139537925452047064396529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46093025283634698042931019 69139537925452047064396529)
            ·
              refine ⟨51854653444089035298297397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69139537925452047064396529 51854653444089035298297397)
              ·
                refine ⟨4861373760383347059215381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51854653444089035298297397 4861373760383347059215381)
                ·
                  refine ⟨227876895017969393400721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4861373760383347059215381 227876895017969393400721)
                  ·
                    rfl

theorem cell22_1997049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_1997049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997049 prefixEnd_1997049 := by exact prefixLift 1997049
  have htrace : WordTrace (prefixWord ++ tailWord_1997049) baseStart_1997049 baseEnd_1997049 := by
    simpa [prefixWord, tailWord_1997049, baseEnd_1997049] using wordTrace_append hprefix tailTrace_1997049
  have hstable : (prefixWord ++ tailWord_1997049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997049).length < 2 ^ (prefixWord ++ tailWord_1997049).sum := by decide
  have hdescent : baseEnd_1997049 < baseStart_1997049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997156 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1997156 : Nat := 118140960795 + 1997156 * 2 ^ 59
def prefixEnd_1997156 : Nat := 4983230072969 + 3 ^ 40 * 1997156 * 2
def baseEnd_1997156 : Nat := 227889104446865189258945

theorem tailTrace_1997156 : CollatzResearch.WordTrace tailWord_1997156 prefixEnd_1997156 227889104446865189258945 := by
  unfold tailWord_1997156
  simp only [CollatzResearch.WordTrace]
  refine ⟨36421131776326186967289661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48561509035101582623052881 36421131776326186967289661)
  ·
    refine ⟨13657924416122320112733623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36421131776326186967289661 13657924416122320112733623)
    ·
      refine ⟨20486886624183480169100435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13657924416122320112733623 20486886624183480169100435)
      ·
        refine ⟨30730329936275220253650653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20486886624183480169100435 30730329936275220253650653)
        ·
          refine ⟨11523873726103207595118995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30730329936275220253650653 11523873726103207595118995)
          ·
            refine ⟨17285810589154811392678493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11523873726103207595118995 17285810589154811392678493)
            ·
              refine ⟨6482178970933054272254435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17285810589154811392678493 6482178970933054272254435)
              ·
                refine ⟨9723268456399581408381653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482178970933054272254435 9723268456399581408381653)
                ·
                  refine ⟨227889104446865189258945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9723268456399581408381653 227889104446865189258945)
                  ·
                    rfl

theorem cell22_1997156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1997156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997156 prefixEnd_1997156 := by exact prefixLift 1997156
  have htrace : WordTrace (prefixWord ++ tailWord_1997156) baseStart_1997156 baseEnd_1997156 := by
    simpa [prefixWord, tailWord_1997156, baseEnd_1997156] using wordTrace_append hprefix tailTrace_1997156
  have hstable : (prefixWord ++ tailWord_1997156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997156).length < 2 ^ (prefixWord ++ tailWord_1997156).sum := by decide
  have hdescent : baseEnd_1997156 < baseStart_1997156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997160 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 3, 3]
def baseStart_1997160 : Nat := 118140960795 + 1997160 * 2 ^ 59
def prefixEnd_1997160 : Nat := 4983230072969 + 3 ^ 40 * 1997160 * 2
def baseEnd_1997160 : Nat := 683668682622340890676823

theorem tailTrace_1997160 : CollatzResearch.WordTrace tailWord_1997160 prefixEnd_1997160 683668682622340890676823 := by
  unfold tailWord_1997160
  simp only [CollatzResearch.WordTrace]
  refine ⟨36421204722318941308862467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48561606296425255078483289 36421204722318941308862467)
  ·
    refine ⟨54631807083478411963293701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36421204722318941308862467 54631807083478411963293701)
    ·
      refine ⟨10243463828152202243117569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54631807083478411963293701 10243463828152202243117569)
      ·
        refine ⟨7682597871114151682338177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10243463828152202243117569 7682597871114151682338177)
        ·
          refine ⟨5761948403335613761753633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7682597871114151682338177 5761948403335613761753633)
          ·
            refine ⟨4321461302501710321315225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5761948403335613761753633 4321461302501710321315225)
            ·
              refine ⟨3241095976876282740986419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4321461302501710321315225 3241095976876282740986419)
              ·
                refine ⟨4861643965314424111479629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241095976876282740986419 4861643965314424111479629)
                ·
                  refine ⟨1823116486992909041804861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4861643965314424111479629 1823116486992909041804861)
                  ·
                    refine ⟨683668682622340890676823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1823116486992909041804861 683668682622340890676823)
                    ·
                      rfl

theorem cell22_1997160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_1997160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997160 prefixEnd_1997160 := by exact prefixLift 1997160
  have htrace : WordTrace (prefixWord ++ tailWord_1997160) baseStart_1997160 baseEnd_1997160 := by
    simpa [prefixWord, tailWord_1997160, baseEnd_1997160] using wordTrace_append hprefix tailTrace_1997160
  have hstable : (prefixWord ++ tailWord_1997160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997160).length < 2 ^ (prefixWord ++ tailWord_1997160).sum := by decide
  have hdescent : baseEnd_1997160 < baseStart_1997160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997237 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1997237 : Nat := 118140960795 + 1997237 * 2 ^ 59
def prefixEnd_1997237 : Nat := 4983230072969 + 3 ^ 40 * 1997237 * 2
def baseEnd_1997237 : Nat := 683695041295938356501587

theorem tailTrace_1997237 : CollatzResearch.WordTrace tailWord_1997237 prefixEnd_1997237 683695041295938356501587 := by
  unfold tailWord_1997237
  simp only [CollatzResearch.WordTrace]
  refine ⟨72845217865358924768277965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48563478576905949845518643 72845217865358924768277965)
  ·
    refine ⟨27316956699509596788104237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72845217865358924768277965 27316956699509596788104237)
    ·
      refine ⟨10243858762316098795539089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27316956699509596788104237 10243858762316098795539089)
      ·
        refine ⟨7682894071737074096654317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10243858762316098795539089 7682894071737074096654317)
        ·
          refine ⟨2881085276901402786245369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7682894071737074096654317 2881085276901402786245369)
          ·
            refine ⟨2160813957676052089684027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2881085276901402786245369 2160813957676052089684027)
            ·
              refine ⟨3241220936514078134526041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160813957676052089684027 3241220936514078134526041)
              ·
                refine ⟨2430915702385558600894531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241220936514078134526041 2430915702385558600894531)
                ·
                  refine ⟨3646373553578337901341797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430915702385558600894531 3646373553578337901341797)
                  ·
                    refine ⟨683695041295938356501587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3646373553578337901341797 683695041295938356501587)
                    ·
                      rfl

theorem cell22_1997237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1997237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997237 prefixEnd_1997237 := by exact prefixLift 1997237
  have htrace : WordTrace (prefixWord ++ tailWord_1997237) baseStart_1997237 baseEnd_1997237 := by
    simpa [prefixWord, tailWord_1997237, baseEnd_1997237] using wordTrace_append hprefix tailTrace_1997237
  have hstable : (prefixWord ++ tailWord_1997237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997237).length < 2 ^ (prefixWord ++ tailWord_1997237).sum := by decide
  have hdescent : baseEnd_1997237 < baseStart_1997237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997318 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1997318 : Nat := 118140960795 + 1997318 * 2 ^ 59
def prefixEnd_1997318 : Nat := 4983230072969 + 3 ^ 40 * 1997318 * 2
def baseEnd_1997318 : Nat := 683722769251281145226339

theorem tailTrace_1997318 : CollatzResearch.WordTrace tailWord_1997318 prefixEnd_1997318 683722769251281145226339 := by
  unfold tailWord_1997318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2276505380564546112561769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48565448118710317067984405 2276505380564546112561769)
  ·
    refine ⟨1707379035423409584421327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2276505380564546112561769 1707379035423409584421327)
    ·
      refine ⟨2561068553135114376631991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707379035423409584421327 2561068553135114376631991)
      ·
        refine ⟨3841602829702671564947987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561068553135114376631991 3841602829702671564947987)
        ·
          refine ⟨5762404244554007347421981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841602829702671564947987 5762404244554007347421981)
          ·
            refine ⟨2160901591707752755283243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5762404244554007347421981 2160901591707752755283243)
            ·
              refine ⟨3241352387561629132924865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160901591707752755283243 3241352387561629132924865)
              ·
                refine ⟨2431014290671221849693649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241352387561629132924865 2431014290671221849693649)
                ·
                  refine ⟨1823260718003416387270237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2431014290671221849693649 1823260718003416387270237)
                  ·
                    refine ⟨683722769251281145226339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1823260718003416387270237 683722769251281145226339)
                    ·
                      rfl

theorem cell22_1997318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1997318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997318 prefixEnd_1997318 := by exact prefixLift 1997318
  have htrace : WordTrace (prefixWord ++ tailWord_1997318) baseStart_1997318 baseEnd_1997318 := by
    simpa [prefixWord, tailWord_1997318, baseEnd_1997318] using wordTrace_append hprefix tailTrace_1997318
  have hstable : (prefixWord ++ tailWord_1997318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997318).length < 2 ^ (prefixWord ++ tailWord_1997318).sum := by decide
  have hdescent : baseEnd_1997318 < baseStart_1997318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997323 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 2, 5]
def baseStart_1997323 : Nat := 118140960795 + 1997323 * 2 ^ 59
def prefixEnd_1997323 : Nat := 4983230072969 + 3 ^ 40 * 1997323 * 2
def baseEnd_1997323 : Nat := 683724480853462798851323

theorem tailTrace_1997323 : CollatzResearch.WordTrace tailWord_1997323 prefixEnd_1997323 683724480853462798851323 := by
  unfold tailWord_1997323
  simp only [CollatzResearch.WordTrace]
  refine ⟨72848354543047361455908623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48565569695364907637272415 72848354543047361455908623)
  ·
    refine ⟨109272531814571042183862935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72848354543047361455908623 109272531814571042183862935)
    ·
      refine ⟨163908797721856563275794403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109272531814571042183862935 163908797721856563275794403)
      ·
        refine ⟨245863196582784844913691605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163908797721856563275794403 245863196582784844913691605)
        ·
          refine ⟨5762418669909019802664647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 245863196582784844913691605 5762418669909019802664647)
          ·
            refine ⟨8643628004863529703996971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5762418669909019802664647 8643628004863529703996971)
            ·
              refine ⟨12965442007295294555995457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8643628004863529703996971 12965442007295294555995457)
              ·
                refine ⟨9724081505471470916996593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12965442007295294555995457 9724081505471470916996593)
                ·
                  refine ⟨7293061129103603187747445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9724081505471470916996593 7293061129103603187747445)
                  ·
                    refine ⟨683724480853462798851323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7293061129103603187747445 683724480853462798851323)
                    ·
                      rfl

theorem cell22_1997323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_1997323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997323 prefixEnd_1997323 := by exact prefixLift 1997323
  have htrace : WordTrace (prefixWord ++ tailWord_1997323) baseStart_1997323 baseEnd_1997323 := by
    simpa [prefixWord, tailWord_1997323, baseEnd_1997323] using wordTrace_append hprefix tailTrace_1997323
  have hstable : (prefixWord ++ tailWord_1997323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997323).length < 2 ^ (prefixWord ++ tailWord_1997323).sum := by decide
  have hdescent : baseEnd_1997323 < baseStart_1997323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997338 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_1997338 : Nat := 118140960795 + 1997338 * 2 ^ 59
def prefixEnd_1997338 : Nat := 4983230072969 + 3 ^ 40 * 1997338 * 2
def baseEnd_1997338 : Nat := 683729615660007759726277

theorem tailTrace_1997338 : CollatzResearch.WordTrace tailWord_1997338 prefixEnd_1997338 683729615660007759726277 := by
  unfold tailWord_1997338
  simp only [CollatzResearch.WordTrace]
  refine ⟨18212225409498254754426167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48565934425328679345136445 18212225409498254754426167)
  ·
    refine ⟨27318338114247382131639251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18212225409498254754426167 27318338114247382131639251)
    ·
      refine ⟨40977507171371073197458877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27318338114247382131639251 40977507171371073197458877)
      ·
        refine ⟨15366565189264152449047079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40977507171371073197458877 15366565189264152449047079)
        ·
          refine ⟨23049847783896228673570619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15366565189264152449047079 23049847783896228673570619)
          ·
            refine ⟨34574771675844343010355929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23049847783896228673570619 34574771675844343010355929)
            ·
              refine ⟨25931078756883257257766947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34574771675844343010355929 25931078756883257257766947)
              ·
                refine ⟨38896618135324885886650421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25931078756883257257766947 38896618135324885886650421)
                ·
                  refine ⟨3646557950186708051873477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38896618135324885886650421 3646557950186708051873477)
                  ·
                    refine ⟨683729615660007759726277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3646557950186708051873477 683729615660007759726277)
                    ·
                      rfl

theorem cell22_1997338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_1997338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997338 prefixEnd_1997338 := by exact prefixLift 1997338
  have htrace : WordTrace (prefixWord ++ tailWord_1997338) baseStart_1997338 baseEnd_1997338 := by
    simpa [prefixWord, tailWord_1997338, baseEnd_1997338] using wordTrace_append hprefix tailTrace_1997338
  have hstable : (prefixWord ++ tailWord_1997338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997338).length < 2 ^ (prefixWord ++ tailWord_1997338).sum := by decide
  have hdescent : baseEnd_1997338 < baseStart_1997338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997368 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_1997368 : Nat := 118140960795 + 1997368 * 2 ^ 59
def prefixEnd_1997368 : Nat := 4983230072969 + 3 ^ 40 * 1997368 * 2
def baseEnd_1997368 : Nat := 683739885273097681476185

theorem tailTrace_1997368 : CollatzResearch.WordTrace tailWord_1997368 prefixEnd_1997368 683739885273097681476185 := by
  unfold tailWord_1997368
  simp only [CollatzResearch.WordTrace]
  refine ⟨36424997913942167070648379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48566663885256222760864505 36424997913942167070648379)
  ·
    refine ⟨54637496870913250605972569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36424997913942167070648379 54637496870913250605972569)
    ·
      refine ⟨40978122653184937954479427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54637496870913250605972569 40978122653184937954479427)
      ·
        refine ⟨61467183979777406931719141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40978122653184937954479427 61467183979777406931719141)
        ·
          refine ⟨11525096996208263799697339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61467183979777406931719141 11525096996208263799697339)
          ·
            refine ⟨17287645494312395699546009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525096996208263799697339 17287645494312395699546009)
            ·
              refine ⟨12965734120734296774659507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17287645494312395699546009 12965734120734296774659507)
              ·
                refine ⟨19448601181101445161989261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12965734120734296774659507 19448601181101445161989261)
                ·
                  refine ⟨7293225442913041935745973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19448601181101445161989261 7293225442913041935745973)
                  ·
                    refine ⟨683739885273097681476185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7293225442913041935745973 683739885273097681476185)
                    ·
                      rfl

theorem cell22_1997368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_1997368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997368 prefixEnd_1997368 := by exact prefixLift 1997368
  have htrace : WordTrace (prefixWord ++ tailWord_1997368) baseStart_1997368 baseEnd_1997368 := by
    simpa [prefixWord, tailWord_1997368, baseEnd_1997368] using wordTrace_append hprefix tailTrace_1997368
  have hstable : (prefixWord ++ tailWord_1997368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997368).length < 2 ^ (prefixWord ++ tailWord_1997368).sum := by decide
  have hdescent : baseEnd_1997368 < baseStart_1997368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997380 : List Nat := [2, 3, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1997380 : Nat := 118140960795 + 1997380 * 2 ^ 59
def prefixEnd_1997380 : Nat := 4983230072969 + 3 ^ 40 * 1997380 * 2
def baseEnd_1997380 : Nat := 683743993118333650176149

theorem tailTrace_1997380 : CollatzResearch.WordTrace tailWord_1997380 prefixEnd_1997380 683743993118333650176149 := by
  unfold tailWord_1997380
  simp only [CollatzResearch.WordTrace]
  refine ⟨36425216751920430095366797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48566955669227240127155729 36425216751920430095366797)
  ·
    refine ⟨13659456281970161285762549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36425216751920430095366797 13659456281970161285762549)
    ·
      refine ⟨1280574026434702620540239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13659456281970161285762549 1280574026434702620540239)
      ·
        refine ⟨1920861039652053930810359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280574026434702620540239 1920861039652053930810359)
        ·
          refine ⟨2881291559478080896215539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920861039652053930810359 2881291559478080896215539)
          ·
            refine ⟨4321937339217121344323309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881291559478080896215539 4321937339217121344323309)
            ·
              refine ⟨1620726502206420504121241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4321937339217121344323309 1620726502206420504121241)
              ·
                refine ⟨1215544876654815378090931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620726502206420504121241 1215544876654815378090931)
                ·
                  refine ⟨1823317314982223067136397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215544876654815378090931 1823317314982223067136397)
                  ·
                    refine ⟨683743993118333650176149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1823317314982223067136397 683743993118333650176149)
                    ·
                      rfl

theorem cell22_1997380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1997380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1997380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1997380 prefixEnd_1997380 := by exact prefixLift 1997380
  have htrace : WordTrace (prefixWord ++ tailWord_1997380) baseStart_1997380 baseEnd_1997380 := by
    simpa [prefixWord, tailWord_1997380, baseEnd_1997380] using wordTrace_append hprefix tailTrace_1997380
  have hstable : (prefixWord ++ tailWord_1997380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997380).length < 2 ^ (prefixWord ++ tailWord_1997380).sum := by decide
  have hdescent : baseEnd_1997380 < baseStart_1997380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
