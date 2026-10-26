import V185TrunkScan22Chunk385

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3441727 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 3, 3]
def baseStart_3441727 : Nat := 118140960795 + 3441727 * 2 ^ 59
def prefixEnd_3441727 : Nat := 4983230072969 + 3 ^ 40 * 3441727 * 2
def baseEnd_3441727 : Nat := 1178173488371307307322861

theorem tailTrace_3441727 : CollatzResearch.WordTrace tailWord_3441727 prefixEnd_3441727 1178173488371307307322861 := by
  unfold tailWord_3441727
  simp only [CollatzResearch.WordTrace]
  refine ⟨125530096402218354019547435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83686730934812236013031623 125530096402218354019547435)
  ·
    refine ⟨188295144603327531029321153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125530096402218354019547435 188295144603327531029321153)
    ·
      refine ⟨141221358452495648271990865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188295144603327531029321153 141221358452495648271990865)
      ·
        refine ⟨105916018839371736203993149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141221358452495648271990865 105916018839371736203993149)
        ·
          refine ⟨39718507064764401076497431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105916018839371736203993149 39718507064764401076497431)
          ·
            refine ⟨59577760597146601614746147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39718507064764401076497431 59577760597146601614746147)
            ·
              refine ⟨89366640895719902422119221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59577760597146601614746147 89366640895719902422119221)
              ·
                refine ⟨8378122583973740852073677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89366640895719902422119221 8378122583973740852073677)
                ·
                  refine ⟨3141795968990152819527629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8378122583973740852073677 3141795968990152819527629)
                  ·
                    refine ⟨1178173488371307307322861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141795968990152819527629 1178173488371307307322861)
                    ·
                      rfl

theorem cell22_3441727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_3441727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441727 prefixEnd_3441727 := by exact prefixLift 3441727
  have htrace : WordTrace (prefixWord ++ tailWord_3441727) baseStart_3441727 baseEnd_3441727 := by
    simpa [prefixWord, tailWord_3441727, baseEnd_3441727] using wordTrace_append hprefix tailTrace_3441727
  have hstable : (prefixWord ++ tailWord_3441727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441727).length < 2 ^ (prefixWord ++ tailWord_3441727).sum := by decide
  have hdescent : baseEnd_3441727 < baseStart_3441727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441729 : List Nat := [1, 2, 5, 1, 3, 2, 1, 7]
def baseStart_3441729 : Nat := 118140960795 + 3441729 * 2 ^ 59
def prefixEnd_3441729 : Nat := 4983230072969 + 3 ^ 40 * 3441729 * 2
def baseEnd_3441729 : Nat := 130908241445797774308095

theorem tailTrace_3441729 : CollatzResearch.WordTrace tailWord_3441729 prefixEnd_3441729 130908241445797774308095 := by
  unfold tailWord_3441729
  simp only [CollatzResearch.WordTrace]
  refine ⟨125530169348211108361120241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83686779565474072240746827 125530169348211108361120241)
  ·
    refine ⟨94147627011158331270840181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125530169348211108361120241 94147627011158331270840181)
    ·
      refine ⟨8826340032296093556641267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94147627011158331270840181 8826340032296093556641267)
      ·
        refine ⟨13239510048444140334961901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8826340032296093556641267 13239510048444140334961901)
        ·
          refine ⟨4964816268166552625610713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13239510048444140334961901 4964816268166552625610713)
          ·
            refine ⟨3723612201124914469208035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4964816268166552625610713 3723612201124914469208035)
            ·
              refine ⟨5585418301687371703812053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723612201124914469208035 5585418301687371703812053)
              ·
                refine ⟨130908241445797774308095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5585418301687371703812053 130908241445797774308095)
                ·
                  rfl

theorem cell22_3441729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 7].length) (baseStart_3441729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441729 prefixEnd_3441729 := by exact prefixLift 3441729
  have htrace : WordTrace (prefixWord ++ tailWord_3441729) baseStart_3441729 baseEnd_3441729 := by
    simpa [prefixWord, tailWord_3441729, baseEnd_3441729] using wordTrace_append hprefix tailTrace_3441729
  have hstable : (prefixWord ++ tailWord_3441729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441729).length < 2 ^ (prefixWord ++ tailWord_3441729).sum := by decide
  have hdescent : baseEnd_3441729 < baseStart_3441729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441740 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 9]
def baseStart_3441740 : Nat := 118140960795 + 3441740 * 2 ^ 59
def prefixEnd_3441740 : Nat := 4983230072969 + 3 ^ 40 * 3441740 * 2
def baseEnd_3441740 : Nat := 392725979512326535582607

theorem tailTrace_3441740 : CollatzResearch.WordTrace tailWord_3441740 prefixEnd_3441740 392725979512326535582607 := by
  unfold tailWord_3441740
  simp only [CollatzResearch.WordTrace]
  refine ⟨62765285275585628619885337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83687047034114171493180449 62765285275585628619885337)
  ·
    refine ⟨47073963956689221464914003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62765285275585628619885337 47073963956689221464914003)
    ·
      refine ⟨70610945935033832197371005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47073963956689221464914003 70610945935033832197371005)
      ·
        refine ⟨26479104725637687074014127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70610945935033832197371005 26479104725637687074014127)
        ·
          refine ⟨39718657088456530611021191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26479104725637687074014127 39718657088456530611021191)
          ·
            refine ⟨59577985632684795916531787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39718657088456530611021191 59577985632684795916531787)
            ·
              refine ⟨89366978449027193874797681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59577985632684795916531787 89366978449027193874797681)
              ·
                refine ⟨67025233836770395406098261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89366978449027193874797681 67025233836770395406098261)
                ·
                  refine ⟨392725979512326535582607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67025233836770395406098261 392725979512326535582607)
                  ·
                    rfl

theorem cell22_3441740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_3441740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441740 prefixEnd_3441740 := by exact prefixLift 3441740
  have htrace : WordTrace (prefixWord ++ tailWord_3441740) baseStart_3441740 baseEnd_3441740 := by
    simpa [prefixWord, tailWord_3441740, baseEnd_3441740] using wordTrace_append hprefix tailTrace_3441740
  have hstable : (prefixWord ++ tailWord_3441740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441740).length < 2 ^ (prefixWord ++ tailWord_3441740).sum := by decide
  have hdescent : baseEnd_3441740 < baseStart_3441740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441774 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_3441774 : Nat := 118140960795 + 3441774 * 2 ^ 59
def prefixEnd_3441774 : Nat := 4983230072969 + 3 ^ 40 * 3441774 * 2
def baseEnd_3441774 : Nat := 392729859143938283799239

theorem tailTrace_3441774 : CollatzResearch.WordTrace tailWord_3441774 prefixEnd_3441774 392729859143938283799239 := by
  unfold tailWord_3441774
  simp only [CollatzResearch.WordTrace]
  refine ⟨15691476329131010130813547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83687873755365387364338917 15691476329131010130813547)
  ·
    refine ⟨23537214493696515196220321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15691476329131010130813547 23537214493696515196220321)
    ·
      refine ⟨17652910870272386397165241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23537214493696515196220321 17652910870272386397165241)
      ·
        refine ⟨13239683152704289797873931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17652910870272386397165241 13239683152704289797873931)
        ·
          refine ⟨19859524729056434696810897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13239683152704289797873931 19859524729056434696810897)
          ·
            refine ⟨14894643546792326022608173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19859524729056434696810897 14894643546792326022608173)
            ·
              refine ⟨5585491330047122258478065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14894643546792326022608173 5585491330047122258478065)
              ·
                refine ⟨4189118497535341693858549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5585491330047122258478065 4189118497535341693858549)
                ·
                  refine ⟨392729859143938283799239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4189118497535341693858549 392729859143938283799239)
                  ·
                    rfl

theorem cell22_3441774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_3441774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441774 prefixEnd_3441774 := by exact prefixLift 3441774
  have htrace : WordTrace (prefixWord ++ tailWord_3441774) baseStart_3441774 baseEnd_3441774 := by
    simpa [prefixWord, tailWord_3441774, baseEnd_3441774] using wordTrace_append hprefix tailTrace_3441774
  have hstable : (prefixWord ++ tailWord_3441774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441774).length < 2 ^ (prefixWord ++ tailWord_3441774).sum := by decide
  have hdescent : baseEnd_3441774 < baseStart_3441774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441802 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_3441802 : Nat := 118140960795 + 3441802 * 2 ^ 59
def prefixEnd_3441802 : Nat := 4983230072969 + 3 ^ 40 * 3441802 * 2
def baseEnd_3441802 : Nat := 392733054134677370565877

theorem tailTrace_3441802 : CollatzResearch.WordTrace tailWord_3441802 prefixEnd_3441802 392733054134677370565877 := by
  unfold tailWord_3441802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31383207969236660457131915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83688554584631094552351773 31383207969236660457131915)
  ·
    refine ⟨47074811953854990685697873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31383207969236660457131915 47074811953854990685697873)
    ·
      refine ⟨35306108965391243014273405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47074811953854990685697873 35306108965391243014273405)
      ·
        refine ⟨13239790862021716130352527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35306108965391243014273405 13239790862021716130352527)
        ·
          refine ⟨19859686293032574195528791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13239790862021716130352527 19859686293032574195528791)
          ·
            refine ⟨29789529439548861293293187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19859686293032574195528791 29789529439548861293293187)
            ·
              refine ⟨44684294159323291939939781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29789529439548861293293187 44684294159323291939939781)
              ·
                refine ⟨8378305154873117238738709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44684294159323291939939781 8378305154873117238738709)
                ·
                  refine ⟨392733054134677370565877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8378305154873117238738709 392733054134677370565877)
                  ·
                    rfl

theorem cell22_3441802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_3441802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441802 prefixEnd_3441802 := by exact prefixLift 3441802
  have htrace : WordTrace (prefixWord ++ tailWord_3441802) baseStart_3441802 baseEnd_3441802 := by
    simpa [prefixWord, tailWord_3441802, baseEnd_3441802] using wordTrace_append hprefix tailTrace_3441802
  have hstable : (prefixWord ++ tailWord_3441802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441802).length < 2 ^ (prefixWord ++ tailWord_3441802).sum := by decide
  have hdescent : baseEnd_3441802 < baseStart_3441802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441847 : List Nat := [1, 1, 3, 1, 4, 1, 4, 7]
def baseStart_3441847 : Nat := 118140960795 + 3441847 * 2 ^ 59
def prefixEnd_3441847 : Nat := 4983230072969 + 3 ^ 40 * 3441847 * 2
def baseEnd_3441847 : Nat := 130912729647074110480277

theorem tailTrace_3441847 : CollatzResearch.WordTrace tailWord_3441847 prefixEnd_3441847 130912729647074110480277 := by
  unfold tailWord_3441847
  simp only [CollatzResearch.WordTrace]
  refine ⟨125534473161783614513915795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83689648774522409675943863 125534473161783614513915795)
  ·
    refine ⟨188301709742675421770873693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125534473161783614513915795 188301709742675421770873693)
    ·
      refine ⟨70613141153503283164077635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188301709742675421770873693 70613141153503283164077635)
      ·
        refine ⟨105919711730254924746116453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70613141153503283164077635 105919711730254924746116453)
        ·
          refine ⟨19859945949422798389896835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105919711730254924746116453 19859945949422798389896835)
          ·
            refine ⟨29789918924134197584845253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19859945949422798389896835 29789918924134197584845253)
            ·
              refine ⟨5585609798275162047158485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29789918924134197584845253 5585609798275162047158485)
              ·
                refine ⟨130912729647074110480277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5585609798275162047158485 130912729647074110480277)
                ·
                  rfl

theorem cell22_3441847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 7].length) (baseStart_3441847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441847 prefixEnd_3441847 := by exact prefixLift 3441847
  have htrace : WordTrace (prefixWord ++ tailWord_3441847) baseStart_3441847 baseEnd_3441847 := by
    simpa [prefixWord, tailWord_3441847, baseEnd_3441847] using wordTrace_append hprefix tailTrace_3441847
  have hstable : (prefixWord ++ tailWord_3441847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441847).length < 2 ^ (prefixWord ++ tailWord_3441847).sum := by decide
  have hdescent : baseEnd_3441847 < baseStart_3441847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441892 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3441892 : Nat := 118140960795 + 3441892 * 2 ^ 59
def prefixEnd_3441892 : Nat := 4983230072969 + 3 ^ 40 * 3441892 * 2
def baseEnd_3441892 : Nat := 392743323747767292315785

theorem tailTrace_3441892 : CollatzResearch.WordTrace tailWord_3441892 prefixEnd_3441892 392743323747767292315785 := by
  unfold tailWord_3441892
  simp only [CollatzResearch.WordTrace]
  refine ⟨62768057223310293599651965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83690742964413724799535953 62768057223310293599651965)
  ·
    refine ⟨23538021458741360099869487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62768057223310293599651965 23538021458741360099869487)
    ·
      refine ⟨35307032188112040149804231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23538021458741360099869487 35307032188112040149804231)
      ·
        refine ⟨52960548282168060224706347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35307032188112040149804231 52960548282168060224706347)
        ·
          refine ⟨79440822423252090337059521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52960548282168060224706347 79440822423252090337059521)
          ·
            refine ⟨59580616817439067752794641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79440822423252090337059521 59580616817439067752794641)
            ·
              refine ⟨44685462613079300814595981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59580616817439067752794641 44685462613079300814595981)
              ·
                refine ⟨16757048479904737805473493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44685462613079300814595981 16757048479904737805473493)
                ·
                  refine ⟨392743323747767292315785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16757048479904737805473493 392743323747767292315785)
                  ·
                    rfl

theorem cell22_3441892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3441892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441892 prefixEnd_3441892 := by exact prefixLift 3441892
  have htrace : WordTrace (prefixWord ++ tailWord_3441892) baseStart_3441892 baseEnd_3441892 := by
    simpa [prefixWord, tailWord_3441892, baseEnd_3441892] using wordTrace_append hprefix tailTrace_3441892
  have hstable : (prefixWord ++ tailWord_3441892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441892).length < 2 ^ (prefixWord ++ tailWord_3441892).sum := by decide
  have hdescent : baseEnd_3441892 < baseStart_3441892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441907 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 1, 7]
def baseStart_3441907 : Nat := 118140960795 + 3441907 * 2 ^ 59
def prefixEnd_3441907 : Nat := 4983230072969 + 3 ^ 40 * 3441907 * 2
def baseEnd_3441907 : Nat := 1178235106049846837822309

theorem tailTrace_3441907 : CollatzResearch.WordTrace tailWord_3441907 prefixEnd_3441907 1178235106049846837822309 := by
  unfold tailWord_3441907
  simp only [CollatzResearch.WordTrace]
  refine ⟨125536661541566244761099975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83691107694377496507399983 125536661541566244761099975)
  ·
    refine ⟨188304992312349367141649963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125536661541566244761099975 188304992312349367141649963)
    ·
      refine ⟨282457488468524050712474945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188304992312349367141649963 282457488468524050712474945)
      ·
        refine ⟨211843116351393038034356209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282457488468524050712474945 211843116351393038034356209)
        ·
          refine ⟨158882337263544778525767157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211843116351393038034356209 158882337263544778525767157)
          ·
            refine ⟨14895219118457322986790671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158882337263544778525767157 14895219118457322986790671)
            ·
              refine ⟨22342828677685984480186007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895219118457322986790671 22342828677685984480186007)
              ·
                refine ⟨33514243016528976720279011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22342828677685984480186007 33514243016528976720279011)
                ·
                  refine ⟨50271364524793465080418517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33514243016528976720279011 50271364524793465080418517)
                  ·
                    refine ⟨1178235106049846837822309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50271364524793465080418517 1178235106049846837822309)
                    ·
                      rfl

theorem cell22_3441907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_3441907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441907 prefixEnd_3441907 := by exact prefixLift 3441907
  have htrace : WordTrace (prefixWord ++ tailWord_3441907) baseStart_3441907 baseEnd_3441907 := by
    simpa [prefixWord, tailWord_3441907, baseEnd_3441907] using wordTrace_append hprefix tailTrace_3441907
  have hstable : (prefixWord ++ tailWord_3441907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441907).length < 2 ^ (prefixWord ++ tailWord_3441907).sum := by decide
  have hdescent : baseEnd_3441907 < baseStart_3441907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441937 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 8]
def baseStart_3441937 : Nat := 118140960795 + 3441937 * 2 ^ 59
def prefixEnd_3441937 : Nat := 4983230072969 + 3 ^ 40 * 3441937 * 2
def baseEnd_3441937 : Nat := 392748458554312253190739

theorem tailTrace_3441937 : CollatzResearch.WordTrace tailWord_3441937 prefixEnd_3441937 392748458554312253190739 := by
  unfold tailWord_3441937
  simp only [CollatzResearch.WordTrace]
  refine ⟨125537755731457559884692065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83691837154305039923128043 125537755731457559884692065)
  ·
    refine ⟨94153316798593169913519049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125537755731457559884692065 94153316798593169913519049)
    ·
      refine ⟨70614987598944877435139287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94153316798593169913519049 70614987598944877435139287)
      ·
        refine ⟨105922481398417316152708931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70614987598944877435139287 105922481398417316152708931)
        ·
          refine ⟨158883722097625974229063397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105922481398417316152708931 158883722097625974229063397)
          ·
            refine ⟨29790697893304870167949387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158883722097625974229063397 29790697893304870167949387)
            ·
              refine ⟨44686046839957305251924081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29790697893304870167949387 44686046839957305251924081)
              ·
                refine ⟨33514535129967978938943061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44686046839957305251924081 33514535129967978938943061)
                ·
                  refine ⟨392748458554312253190739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33514535129967978938943061 392748458554312253190739)
                  ·
                    rfl

theorem cell22_3441937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_3441937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441937 prefixEnd_3441937 := by exact prefixLift 3441937
  have htrace : WordTrace (prefixWord ++ tailWord_3441937) baseStart_3441937 baseEnd_3441937 := by
    simpa [prefixWord, tailWord_3441937, baseEnd_3441937] using wordTrace_append hprefix tailTrace_3441937
  have hstable : (prefixWord ++ tailWord_3441937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441937).length < 2 ^ (prefixWord ++ tailWord_3441937).sum := by decide
  have hdescent : baseEnd_3441937 < baseStart_3441937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441984 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_3441984 : Nat := 118140960795 + 3441984 * 2 ^ 59
def prefixEnd_3441984 : Nat := 4983230072969 + 3 ^ 40 * 3441984 * 2
def baseEnd_3441984 : Nat := 1178261464723444303647073

theorem tailTrace_3441984 : CollatzResearch.WordTrace tailWord_3441984 prefixEnd_3441984 1178261464723444303647073 := by
  unfold tailWord_3441984
  simp only [CollatzResearch.WordTrace]
  refine ⟨62769734981143643455826503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83692979974858191274435337 62769734981143643455826503)
  ·
    refine ⟨94154602471715465183739755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62769734981143643455826503 94154602471715465183739755)
    ·
      refine ⟨141231903707573197775609633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94154602471715465183739755 141231903707573197775609633)
      ·
        refine ⟨105923927780679898331707225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141231903707573197775609633 105923927780679898331707225)
        ·
          refine ⟨79442945835509923748780419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105923927780679898331707225 79442945835509923748780419)
          ·
            refine ⟨119164418753264885623170629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79442945835509923748780419 119164418753264885623170629)
            ·
              refine ⟨22343328516237166054344493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119164418753264885623170629 22343328516237166054344493)
              ·
                refine ⟨8378748193588937270379185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22343328516237166054344493 8378748193588937270379185)
                ·
                  refine ⟨6284061145191702952784389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8378748193588937270379185 6284061145191702952784389)
                  ·
                    refine ⟨1178261464723444303647073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6284061145191702952784389 1178261464723444303647073)
                    ·
                      rfl

theorem cell22_3441984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_3441984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441984 prefixEnd_3441984 := by exact prefixLift 3441984
  have htrace : WordTrace (prefixWord ++ tailWord_3441984) baseStart_3441984 baseEnd_3441984 := by
    simpa [prefixWord, tailWord_3441984, baseEnd_3441984] using wordTrace_append hprefix tailTrace_3441984
  have hstable : (prefixWord ++ tailWord_3441984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441984).length < 2 ^ (prefixWord ++ tailWord_3441984).sum := by decide
  have hdescent : baseEnd_3441984 < baseStart_3441984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442020 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_3442020 : Nat := 118140960795 + 3442020 * 2 ^ 59
def prefixEnd_3442020 : Nat := 4983230072969 + 3 ^ 40 * 3442020 * 2
def baseEnd_3442020 : Nat := 1178273788259152209746963

theorem tailTrace_3442020 : CollatzResearch.WordTrace tailWord_3442020 prefixEnd_3442020 1178273788259152209746963 := by
  unfold tailWord_3442020
  simp only [CollatzResearch.WordTrace]
  refine ⟨62770391495078432529981757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83693855326771243373309009 62770391495078432529981757)
  ·
    refine ⟨23538896810654412198743159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62770391495078432529981757 23538896810654412198743159)
    ·
      refine ⟨35308345215981618298114739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23538896810654412198743159 35308345215981618298114739)
      ·
        refine ⟨52962517823972427447172109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35308345215981618298114739 52962517823972427447172109)
        ·
          refine ⟨19860944183989660292689541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52962517823972427447172109 19860944183989660292689541)
          ·
            refine ⟨3723927034498061304879289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19860944183989660292689541 3723927034498061304879289)
            ·
              refine ⟨2792945275873545978659467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3723927034498061304879289 2792945275873545978659467)
              ·
                refine ⟨4189417913810318967989201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792945275873545978659467 4189417913810318967989201)
                ·
                  refine ⟨3142063435357739225991901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4189417913810318967989201 3142063435357739225991901)
                  ·
                    refine ⟨1178273788259152209746963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142063435357739225991901 1178273788259152209746963)
                    ·
                      rfl

theorem cell22_3442020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_3442020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442020 prefixEnd_3442020 := by exact prefixLift 3442020
  have htrace : WordTrace (prefixWord ++ tailWord_3442020) baseStart_3442020 baseEnd_3442020 := by
    simpa [prefixWord, tailWord_3442020, baseEnd_3442020] using wordTrace_append hprefix tailTrace_3442020
  have hstable : (prefixWord ++ tailWord_3442020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442020).length < 2 ^ (prefixWord ++ tailWord_3442020).sum := by decide
  have hdescent : baseEnd_3442020 < baseStart_3442020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442059 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 2, 5]
def baseStart_3442059 : Nat := 118140960795 + 3442059 * 2 ^ 59
def prefixEnd_3442059 : Nat := 4983230072969 + 3 ^ 40 * 3442059 * 2
def baseEnd_3442059 : Nat := 1178287138756169108021843

theorem tailTrace_3442059 : CollatzResearch.WordTrace tailWord_3442059 prefixEnd_3442059 1178287138756169108021843 := by
  unfold tailWord_3442059
  simp only [CollatzResearch.WordTrace]
  refine ⟨125542205437015574720633231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83694803624677049813755487 125542205437015574720633231)
  ·
    refine ⟨188313308155523362080949847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125542205437015574720633231 188313308155523362080949847)
    ·
      refine ⟨282469962233285043121424771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188313308155523362080949847 282469962233285043121424771)
      ·
        refine ⟨423704943349927564682137157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282469962233285043121424771 423704943349927564682137157)
        ·
          refine ⟨79444676878111418377900717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423704943349927564682137157 79444676878111418377900717)
          ·
            refine ⟨29791753829291781891712769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79444676878111418377900717 29791753829291781891712769)
            ·
              refine ⟨22343815371968836418784577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29791753829291781891712769 22343815371968836418784577)
              ·
                refine ⟨16757861528976627314088433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22343815371968836418784577 16757861528976627314088433)
                ·
                  refine ⟨12568396146732470485566325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16757861528976627314088433 12568396146732470485566325)
                  ·
                    refine ⟨1178287138756169108021843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12568396146732470485566325 1178287138756169108021843)
                    ·
                      rfl

theorem cell22_3442059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_3442059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442059 prefixEnd_3442059 := by exact prefixLift 3442059
  have htrace : WordTrace (prefixWord ++ tailWord_3442059) baseStart_3442059 baseEnd_3442059 := by
    simpa [prefixWord, tailWord_3442059, baseEnd_3442059] using wordTrace_append hprefix tailTrace_3442059
  have hstable : (prefixWord ++ tailWord_3442059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442059).length < 2 ^ (prefixWord ++ tailWord_3442059).sum := by decide
  have hdescent : baseEnd_3442059 < baseStart_3442059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442138 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_3442138 : Nat := 118140960795 + 3442138 * 2 ^ 59
def prefixEnd_3442138 : Nat := 4983230072969 + 3 ^ 40 * 3442138 * 2
def baseEnd_3442138 : Nat := 1178314182070639235296601

theorem tailTrace_3442138 : CollatzResearch.WordTrace tailWord_3442138 prefixEnd_3442138 1178314182070639235296601 := by
  unfold tailWord_3442138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31386271700932342803189767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83696724535819580808506045 31386271700932342803189767)
  ·
    refine ⟨47079407551398514204784651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31386271700932342803189767 47079407551398514204784651)
    ·
      refine ⟨70619111327097771307176977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47079407551398514204784651 70619111327097771307176977)
      ·
        refine ⟨52964333495323328480382733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70619111327097771307176977 52964333495323328480382733)
        ·
          refine ⟨19861625060746248180143525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52964333495323328480382733 19861625060746248180143525)
          ·
            refine ⟨3724054698889921533776911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19861625060746248180143525 3724054698889921533776911)
            ·
              refine ⟨5586082048334882300665367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724054698889921533776911 5586082048334882300665367)
              ·
                refine ⟨8379123072502323450998051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586082048334882300665367 8379123072502323450998051)
                ·
                  refine ⟨12568684608753485176497077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8379123072502323450998051 12568684608753485176497077)
                  ·
                    refine ⟨1178314182070639235296601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12568684608753485176497077 1178314182070639235296601)
                    ·
                      rfl

theorem cell22_3442138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_3442138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442138 prefixEnd_3442138 := by exact prefixLift 3442138
  have htrace : WordTrace (prefixWord ++ tailWord_3442138) baseStart_3442138 baseEnd_3442138 := by
    simpa [prefixWord, tailWord_3442138, baseEnd_3442138] using wordTrace_append hprefix tailTrace_3442138
  have hstable : (prefixWord ++ tailWord_3442138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442138).length < 2 ^ (prefixWord ++ tailWord_3442138).sum := by decide
  have hdescent : baseEnd_3442138 < baseStart_3442138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442151 : List Nat := [1, 1, 5, 2, 1, 3, 1, 8]
def baseStart_3442151 : Nat := 118140960795 + 3442151 * 2 ^ 59
def prefixEnd_3442151 : Nat := 4983230072969 + 3 ^ 40 * 3442151 * 2
def baseEnd_3442151 : Nat := 130924292470701281635729

theorem tailTrace_3442151 : CollatzResearch.WordTrace tailWord_3442151 prefixEnd_3442151 130924292470701281635729 := by
  unfold tailWord_3442151
  simp only [CollatzResearch.WordTrace]
  refine ⟨125545560952682274432982307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83697040635121516288654871 125545560952682274432982307)
  ·
    refine ⟨188318341429023411649473461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125545560952682274432982307 188318341429023411649473461)
    ·
      refine ⟨17654844508970944842138137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188318341429023411649473461 17654844508970944842138137)
      ·
        refine ⟨13241133381728208631603603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17654844508970944842138137 13241133381728208631603603)
        ·
          refine ⟨19861700072592312947405405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13241133381728208631603603 19861700072592312947405405)
          ·
            refine ⟨7448137527222117355277027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19861700072592312947405405 7448137527222117355277027)
            ·
              refine ⟨11172206290833176032915541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448137527222117355277027 11172206290833176032915541)
              ·
                refine ⟨130924292470701281635729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11172206290833176032915541 130924292470701281635729)
                ·
                  rfl

theorem cell22_3442151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 8].length) (baseStart_3442151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442151 prefixEnd_3442151 := by exact prefixLift 3442151
  have htrace : WordTrace (prefixWord ++ tailWord_3442151) baseStart_3442151 baseEnd_3442151 := by
    simpa [prefixWord, tailWord_3442151, baseEnd_3442151] using wordTrace_append hprefix tailTrace_3442151
  have hstable : (prefixWord ++ tailWord_3442151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442151).length < 2 ^ (prefixWord ++ tailWord_3442151).sum := by decide
  have hdescent : baseEnd_3442151 < baseStart_3442151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442157 : List Nat := [1, 5, 1, 3, 2, 2, 1, 3, 4]
def baseStart_3442157 : Nat := 118140960795 + 3442157 * 2 ^ 59
def prefixEnd_3442157 : Nat := 4983230072969 + 3 ^ 40 * 3442157 * 2
def baseEnd_3442157 : Nat := 392773562052976506357181

theorem tailTrace_3442157 : CollatzResearch.WordTrace tailWord_3442157 prefixEnd_3442157 392773562052976506357181 := by
  unfold tailWord_3442157
  simp only [CollatzResearch.WordTrace]
  refine ⟨125545779790660537457700725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83697186527107024971800483 125545779790660537457700725)
  ·
    refine ⟨11769916855374425386659443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125545779790660537457700725 11769916855374425386659443)
    ·
      refine ⟨17654875283061638079989165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11769916855374425386659443 17654875283061638079989165)
      ·
        refine ⟨6620578231148114279995937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17654875283061638079989165 6620578231148114279995937)
        ·
          refine ⟨4965433673361085709996953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6620578231148114279995937 4965433673361085709996953)
          ·
            refine ⟨3724075255020814282497715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4965433673361085709996953 3724075255020814282497715)
            ·
              refine ⟨5586112882531221423746573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724075255020814282497715 5586112882531221423746573)
              ·
                refine ⟨2094792330949208033904965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5586112882531221423746573 2094792330949208033904965)
                ·
                  refine ⟨392773562052976506357181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094792330949208033904965 392773562052976506357181)
                  ·
                    rfl

theorem cell22_3442157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_3442157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442157 prefixEnd_3442157 := by exact prefixLift 3442157
  have htrace : WordTrace (prefixWord ++ tailWord_3442157) baseStart_3442157 baseEnd_3442157 := by
    simpa [prefixWord, tailWord_3442157, baseEnd_3442157] using wordTrace_append hprefix tailTrace_3442157
  have hstable : (prefixWord ++ tailWord_3442157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442157).length < 2 ^ (prefixWord ++ tailWord_3442157).sum := by decide
  have hdescent : baseEnd_3442157 < baseStart_3442157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442174 : List Nat := [4, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3442174 : Nat := 118140960795 + 3442174 * 2 ^ 59
def prefixEnd_3442174 : Nat := 4983230072969 + 3 ^ 40 * 3442174 * 2
def baseEnd_3442174 : Nat := 392775501868782380465497

theorem tailTrace_3442174 : CollatzResearch.WordTrace tailWord_3442174 prefixEnd_3442174 392775501868782380465497 := by
  unfold tailWord_3442174
  simp only [CollatzResearch.WordTrace]
  refine ⟨15693299978949868670133697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83697599887732632907379717 15693299978949868670133697)
  ·
    refine ⟨11769974984212401502600273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15693299978949868670133697 11769974984212401502600273)
    ·
      refine ⟨8827481238159301126950205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11769974984212401502600273 8827481238159301126950205)
      ·
        refine ⟨3310305464309737922606327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8827481238159301126950205 3310305464309737922606327)
        ·
          refine ⟨4965458196464606883909491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310305464309737922606327 4965458196464606883909491)
          ·
            refine ⟨7448187294696910325864237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965458196464606883909491 7448187294696910325864237)
            ·
              refine ⟨2793070235511341372199089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7448187294696910325864237 2793070235511341372199089)
              ·
                refine ⟨2094802676633506029149317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793070235511341372199089 2094802676633506029149317)
                ·
                  refine ⟨392775501868782380465497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094802676633506029149317 392775501868782380465497)
                  ·
                    rfl

theorem cell22_3442174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3442174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442174 prefixEnd_3442174 := by exact prefixLift 3442174
  have htrace : WordTrace (prefixWord ++ tailWord_3442174) baseStart_3442174 baseEnd_3442174 := by
    simpa [prefixWord, tailWord_3442174, baseEnd_3442174] using wordTrace_append hprefix tailTrace_3442174
  have hstable : (prefixWord ++ tailWord_3442174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442174).length < 2 ^ (prefixWord ++ tailWord_3442174).sum := by decide
  have hdescent : baseEnd_3442174 < baseStart_3442174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442189 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3442189 : Nat := 118140960795 + 3442189 * 2 ^ 59
def prefixEnd_3442189 : Nat := 4983230072969 + 3 ^ 40 * 3442189 * 2
def baseEnd_3442189 : Nat := 1178331640412892102271445

theorem tailTrace_3442189 : CollatzResearch.WordTrace tailWord_3442189 prefixEnd_3442189 1178331640412892102271445 := by
  unfold tailWord_3442189
  simp only [CollatzResearch.WordTrace]
  refine ⟨125546946926544606922865621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83697964617696404615243747 125546946926544606922865621)
  ·
    refine ⟨2942506568590889224754663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 125546946926544606922865621 2942506568590889224754663)
    ·
      refine ⟨4413759852886333837131995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942506568590889224754663 4413759852886333837131995)
      ·
        refine ⟨6620639779329500755697993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4413759852886333837131995 6620639779329500755697993)
        ·
          refine ⟨4965479834497125566773495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6620639779329500755697993 4965479834497125566773495)
          ·
            refine ⟨7448219751745688350160243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965479834497125566773495 7448219751745688350160243)
            ·
              refine ⟨11172329627618532525240365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448219751745688350160243 11172329627618532525240365)
              ·
                refine ⟨4189623610356949696965137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11172329627618532525240365 4189623610356949696965137)
                ·
                  refine ⟨3142217707767712272723853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4189623610356949696965137 3142217707767712272723853)
                  ·
                    refine ⟨1178331640412892102271445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142217707767712272723853 1178331640412892102271445)
                    ·
                      rfl

theorem cell22_3442189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3442189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442189 prefixEnd_3442189 := by exact prefixLift 3442189
  have htrace : WordTrace (prefixWord ++ tailWord_3442189) baseStart_3442189 baseEnd_3442189 := by
    simpa [prefixWord, tailWord_3442189, baseEnd_3442189] using wordTrace_append hprefix tailTrace_3442189
  have hstable : (prefixWord ++ tailWord_3442189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442189).length < 2 ^ (prefixWord ++ tailWord_3442189).sum := by decide
  have hdescent : baseEnd_3442189 < baseStart_3442189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442258 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3442258 : Nat := 118140960795 + 3442258 * 2 ^ 59
def prefixEnd_3442258 : Nat := 4983230072969 + 3 ^ 40 * 3442258 * 2
def baseEnd_3442258 : Nat := 392785086840999640765411

theorem tailTrace_3442258 : CollatzResearch.WordTrace tailWord_3442258 prefixEnd_3442258 392785086840999640765411 := by
  unfold tailWord_3442258
  simp only [CollatzResearch.WordTrace]
  refine ⟨31387365890823657926781857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83699642375529754471418285 31387365890823657926781857)
  ·
    refine ⟨23540524418117743445086393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31387365890823657926781857 23540524418117743445086393)
    ·
      refine ⟨17655393313588307583814795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23540524418117743445086393 17655393313588307583814795)
      ·
        refine ⟨26483089970382461375722193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17655393313588307583814795 26483089970382461375722193)
        ·
          refine ⟨19862317477786846031791645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26483089970382461375722193 19862317477786846031791645)
          ·
            refine ⟨7448369054170067261921867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19862317477786846031791645 7448369054170067261921867)
            ·
              refine ⟨11172553581255100892882801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448369054170067261921867 11172553581255100892882801)
              ·
                refine ⟨8379415185941325669662101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11172553581255100892882801 8379415185941325669662101)
                ·
                  refine ⟨392785086840999640765411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8379415185941325669662101 392785086840999640765411)
                  ·
                    rfl

theorem cell22_3442258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3442258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442258 prefixEnd_3442258 := by exact prefixLift 3442258
  have htrace : WordTrace (prefixWord ++ tailWord_3442258) baseStart_3442258 baseEnd_3442258 := by
    simpa [prefixWord, tailWord_3442258, baseEnd_3442258] using wordTrace_append hprefix tailTrace_3442258
  have hstable : (prefixWord ++ tailWord_3442258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442258).length < 2 ^ (prefixWord ++ tailWord_3442258).sum := by decide
  have hdescent : baseEnd_3442258 < baseStart_3442258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442273 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 4, 3]
def baseStart_3442273 : Nat := 118140960795 + 3442273 * 2 ^ 59
def prefixEnd_3442273 : Nat := 4983230072969 + 3 ^ 40 * 3442273 * 2
def baseEnd_3442273 : Nat := 1178360395329543883171187

theorem tailTrace_3442273 : CollatzResearch.WordTrace tailWord_3442273 prefixEnd_3442273 1178360395329543883171187 := by
  unfold tailWord_3442273
  simp only [CollatzResearch.WordTrace]
  refine ⟨125550010658240289268923473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83700007105493526179282315 125550010658240289268923473)
  ·
    refine ⟨94162507993680216951692605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125550010658240289268923473 94162507993680216951692605)
    ·
      refine ⟨35310940497630081356884727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94162507993680216951692605 35310940497630081356884727)
      ·
        refine ⟨52966410746445122035327091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35310940497630081356884727 52966410746445122035327091)
        ·
          refine ⟨79449616119667683052990637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52966410746445122035327091 79449616119667683052990637)
          ·
            refine ⟨29793606044875381144871489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79449616119667683052990637 29793606044875381144871489)
            ·
              refine ⟨22345204533656535858653617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29793606044875381144871489 22345204533656535858653617)
              ·
                refine ⟨16758903400242401893990213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22345204533656535858653617 16758903400242401893990213)
                ·
                  refine ⟨3142294387545450355123165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16758903400242401893990213 3142294387545450355123165)
                  ·
                    refine ⟨1178360395329543883171187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142294387545450355123165 1178360395329543883171187)
                    ·
                      rfl

theorem cell22_3442273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_3442273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442273 prefixEnd_3442273 := by exact prefixLift 3442273
  have htrace : WordTrace (prefixWord ++ tailWord_3442273) baseStart_3442273 baseEnd_3442273 := by
    simpa [prefixWord, tailWord_3442273, baseEnd_3442273] using wordTrace_append hprefix tailTrace_3442273
  have hstable : (prefixWord ++ tailWord_3442273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442273).length < 2 ^ (prefixWord ++ tailWord_3442273).sum := by decide
  have hdescent : baseEnd_3442273 < baseStart_3442273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442275 : List Nat := [1, 1, 1, 5, 1, 4, 2, 3, 4]
def baseStart_3442275 : Nat := 118140960795 + 3442275 * 2 ^ 59
def prefixEnd_3442275 : Nat := 4983230072969 + 3 ^ 40 * 3442275 * 2
def baseEnd_3442275 : Nat := 392787026656805514873727

theorem tailTrace_3442275 : CollatzResearch.WordTrace tailWord_3442275 prefixEnd_3442275 392787026656805514873727 := by
  unfold tailWord_3442275
  simp only [CollatzResearch.WordTrace]
  refine ⟨125550083604233043610496279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83700055736155362406997519 125550083604233043610496279)
  ·
    refine ⟨188325125406349565415744419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125550083604233043610496279 188325125406349565415744419)
    ·
      refine ⟨282487688109524348123616629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188325125406349565415744419 282487688109524348123616629)
      ·
        refine ⟨26483220760267907636589059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282487688109524348123616629 26483220760267907636589059)
        ·
          refine ⟨39724831140401861454883589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26483220760267907636589059 39724831140401861454883589)
          ·
            refine ⟨7448405838825349022790673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39724831140401861454883589 7448405838825349022790673)
            ·
              refine ⟨5586304379119011767093005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7448405838825349022790673 5586304379119011767093005)
              ·
                refine ⟨2094864142169629412659877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5586304379119011767093005 2094864142169629412659877)
                ·
                  refine ⟨392787026656805514873727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094864142169629412659877 392787026656805514873727)
                  ·
                    rfl

theorem cell22_3442275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 4].length) (baseStart_3442275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442275 prefixEnd_3442275 := by exact prefixLift 3442275
  have htrace : WordTrace (prefixWord ++ tailWord_3442275) baseStart_3442275 baseEnd_3442275 := by
    simpa [prefixWord, tailWord_3442275, baseEnd_3442275] using wordTrace_append hprefix tailTrace_3442275
  have hstable : (prefixWord ++ tailWord_3442275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442275).length < 2 ^ (prefixWord ++ tailWord_3442275).sum := by decide
  have hdescent : baseEnd_3442275 < baseStart_3442275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442277 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_3442277 : Nat := 118140960795 + 3442277 * 2 ^ 59
def prefixEnd_3442277 : Nat := 4983230072969 + 3 ^ 40 * 3442277 * 2
def baseEnd_3442277 : Nat := 1178361764611289206071175

theorem tailTrace_3442277 : CollatzResearch.WordTrace tailWord_3442277 prefixEnd_3442277 1178361764611289206071175 := by
  unfold tailWord_3442277
  simp only [CollatzResearch.WordTrace]
  refine ⟨125550156550225797952069085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83700104366817198634712723 125550156550225797952069085)
  ·
    refine ⟨47081308706334674232025907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125550156550225797952069085 47081308706334674232025907)
    ·
      refine ⟨70621963059502011348038861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47081308706334674232025907 70621963059502011348038861)
      ·
        refine ⟨26483236147313254255514573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70621963059502011348038861 26483236147313254255514573)
        ·
          refine ⟨9931213555242470345817965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26483236147313254255514573 9931213555242470345817965)
          ·
            refine ⟨3724205083215926379681737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9931213555242470345817965 3724205083215926379681737)
            ·
              refine ⟨2793153812411944784761303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724205083215926379681737 2793153812411944784761303)
              ·
                refine ⟨4189730718617917177141955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793153812411944784761303 4189730718617917177141955)
                ·
                  refine ⟨6284596077926875765712933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189730718617917177141955 6284596077926875765712933)
                  ·
                    refine ⟨1178361764611289206071175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6284596077926875765712933 1178361764611289206071175)
                    ·
                      rfl

theorem cell22_3442277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_3442277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442277 prefixEnd_3442277 := by exact prefixLift 3442277
  have htrace : WordTrace (prefixWord ++ tailWord_3442277) baseStart_3442277 baseEnd_3442277 := by
    simpa [prefixWord, tailWord_3442277, baseEnd_3442277] using wordTrace_append hprefix tailTrace_3442277
  have hstable : (prefixWord ++ tailWord_3442277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442277).length < 2 ^ (prefixWord ++ tailWord_3442277).sum := by decide
  have hdescent : baseEnd_3442277 < baseStart_3442277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442290 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_3442290 : Nat := 118140960795 + 3442290 * 2 ^ 59
def prefixEnd_3442290 : Nat := 4983230072969 + 3 ^ 40 * 3442290 * 2
def baseEnd_3442290 : Nat := 1178366214776961505496135

theorem tailTrace_3442290 : CollatzResearch.WordTrace tailWord_3442290 prefixEnd_3442290 1178366214776961505496135 := by
  unfold tailWord_3442290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31387657674794675293073081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83700420466119134114861549 31387657674794675293073081)
  ·
    refine ⟨23540743256096006469804811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31387657674794675293073081 23540743256096006469804811)
    ·
      refine ⟨35311114884144009704707217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23540743256096006469804811 35311114884144009704707217)
      ·
        refine ⟨26483336163108007278530413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35311114884144009704707217 26483336163108007278530413)
        ·
          refine ⟨9931251061165502729448905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26483336163108007278530413 9931251061165502729448905)
          ·
            refine ⟨7448438295874127047086679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9931251061165502729448905 7448438295874127047086679)
            ·
              refine ⟨11172657443811190570630019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448438295874127047086679 11172657443811190570630019)
              ·
                refine ⟨16758986165716785855945029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11172657443811190570630019 16758986165716785855945029)
                ·
                  refine ⟨3142309906071897347989693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16758986165716785855945029 3142309906071897347989693)
                  ·
                    refine ⟨1178366214776961505496135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142309906071897347989693 1178366214776961505496135)
                    ·
                      rfl

theorem cell22_3442290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_3442290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442290 prefixEnd_3442290 := by exact prefixLift 3442290
  have htrace : WordTrace (prefixWord ++ tailWord_3442290) baseStart_3442290 baseEnd_3442290 := by
    simpa [prefixWord, tailWord_3442290, baseEnd_3442290] using wordTrace_append hprefix tailTrace_3442290
  have hstable : (prefixWord ++ tailWord_3442290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442290).length < 2 ^ (prefixWord ++ tailWord_3442290).sum := by decide
  have hdescent : baseEnd_3442290 < baseStart_3442290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442403 : List Nat := [1, 1, 1, 7, 3, 1, 2, 2, 1, 3]
def baseStart_3442403 : Nat := 118140960795 + 3442403 * 2 ^ 59
def prefixEnd_3442403 : Nat := 4983230072969 + 3 ^ 40 * 3442403 * 2
def baseEnd_3442403 : Nat := 1178404896986266877420789

theorem tailTrace_3442403 : CollatzResearch.WordTrace tailWord_3442403 prefixEnd_3442403 1178404896986266877420789 := by
  unfold tailWord_3442403
  simp only [CollatzResearch.WordTrace]
  refine ⟨125554752147769321471155863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83703168098512880980770575 125554752147769321471155863)
  ·
    refine ⟨188332128221653982206733795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125554752147769321471155863 188332128221653982206733795)
    ·
      refine ⟨282498192332480973310100693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188332128221653982206733795 282498192332480973310100693)
      ·
        refine ⟨6621051382792522811955485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 282498192332480973310100693 6621051382792522811955485)
        ·
          refine ⟨2482894268547196054483307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6621051382792522811955485 2482894268547196054483307)
          ·
            refine ⟨3724341402820794081724961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482894268547196054483307 3724341402820794081724961)
            ·
              refine ⟨2793256052115595561293721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724341402820794081724961 2793256052115595561293721)
              ·
                refine ⟨2094942039086696670970291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793256052115595561293721 2094942039086696670970291)
                ·
                  refine ⟨3142413058630045006455437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094942039086696670970291 3142413058630045006455437)
                  ·
                    refine ⟨1178404896986266877420789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142413058630045006455437 1178404896986266877420789)
                    ·
                      rfl

theorem cell22_3442403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 3].length) (baseStart_3442403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442403 prefixEnd_3442403 := by exact prefixLift 3442403
  have htrace : WordTrace (prefixWord ++ tailWord_3442403) baseStart_3442403 baseEnd_3442403 := by
    simpa [prefixWord, tailWord_3442403, baseEnd_3442403] using wordTrace_append hprefix tailTrace_3442403
  have hstable : (prefixWord ++ tailWord_3442403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442403).length < 2 ^ (prefixWord ++ tailWord_3442403).sum := by decide
  have hdescent : baseEnd_3442403 < baseStart_3442403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442423 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3442423 : Nat := 118140960795 + 3442423 * 2 ^ 59
def prefixEnd_3442423 : Nat := 4983230072969 + 3 ^ 40 * 3442423 * 2
def baseEnd_3442423 : Nat := 1178411743394993491920727

theorem tailTrace_3442423 : CollatzResearch.WordTrace tailWord_3442423 prefixEnd_3442423 1178411743394993491920727 := by
  unfold tailWord_3442423
  simp only [CollatzResearch.WordTrace]
  refine ⟨125555481607696864886883923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83703654405131243257922615 125555481607696864886883923)
  ·
    refine ⟨188333222411545297330325885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125555481607696864886883923 188333222411545297330325885)
    ·
      refine ⟨70624958404329486498872207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188333222411545297330325885 70624958404329486498872207)
      ·
        refine ⟨105937437606494229748308311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70624958404329486498872207 105937437606494229748308311)
        ·
          refine ⟨158906156409741344622462467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105937437606494229748308311 158906156409741344622462467)
          ·
            refine ⟨238359234614612016933693701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158906156409741344622462467 238359234614612016933693701)
            ·
              refine ⟨44692356490239753175067569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238359234614612016933693701 44692356490239753175067569)
              ·
                refine ⟨33519267367679814881300677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44692356490239753175067569 33519267367679814881300677)
                ·
                  refine ⟨6284862631439965290243877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33519267367679814881300677 6284862631439965290243877)
                  ·
                    refine ⟨1178411743394993491920727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6284862631439965290243877 1178411743394993491920727)
                    ·
                      rfl

theorem cell22_3442423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3442423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442423 prefixEnd_3442423 := by exact prefixLift 3442423
  have htrace : WordTrace (prefixWord ++ tailWord_3442423) baseStart_3442423 baseEnd_3442423 := by
    simpa [prefixWord, tailWord_3442423, baseEnd_3442423] using wordTrace_append hprefix tailTrace_3442423
  have hstable : (prefixWord ++ tailWord_3442423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442423).length < 2 ^ (prefixWord ++ tailWord_3442423).sum := by decide
  have hdescent : baseEnd_3442423 < baseStart_3442423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442489 : List Nat := [1, 2, 1, 7, 1, 2, 2, 6]
def baseStart_3442489 : Nat := 118140960795 + 3442489 * 2 ^ 59
def prefixEnd_3442489 : Nat := 4983230072969 + 3 ^ 40 * 3442489 * 2
def baseEnd_3442489 : Nat := 130937148504865702196725

theorem tailTrace_3442489 : CollatzResearch.WordTrace tailWord_3442489 prefixEnd_3442489 130937148504865702196725 := by
  unfold tailWord_3442489
  simp only [CollatzResearch.WordTrace]
  refine ⟨125557888825457758158786521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83705259216971838772524347 125557888825457758158786521)
  ·
    refine ⟨94168416619093318619089891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125557888825457758158786521 94168416619093318619089891)
    ·
      refine ⟨141252624928639977928634837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94168416619093318619089891 141252624928639977928634837)
      ·
        refine ⟨3310608396764999482702379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 141252624928639977928634837 3310608396764999482702379)
        ·
          refine ⟨4965912595147499224053569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310608396764999482702379 4965912595147499224053569)
          ·
            refine ⟨3724434446360624418040177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4965912595147499224053569 3724434446360624418040177)
            ·
              refine ⟨2793325834770468313530133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724434446360624418040177 2793325834770468313530133)
              ·
                refine ⟨130937148504865702196725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2793325834770468313530133 130937148504865702196725)
                ·
                  rfl

theorem cell22_3442489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 6].length) (baseStart_3442489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442489 prefixEnd_3442489 := by exact prefixLift 3442489
  have htrace : WordTrace (prefixWord ++ tailWord_3442489) baseStart_3442489 baseEnd_3442489 := by
    simpa [prefixWord, tailWord_3442489, baseEnd_3442489] using wordTrace_append hprefix tailTrace_3442489
  have hstable : (prefixWord ++ tailWord_3442489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442489).length < 2 ^ (prefixWord ++ tailWord_3442489).sum := by decide
  have hdescent : baseEnd_3442489 < baseStart_3442489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442504 : List Nat := [2, 1, 3, 1, 1, 4, 3, 3, 1, 3]
def baseStart_3442504 : Nat := 118140960795 + 3442504 * 2 ^ 59
def prefixEnd_3442504 : Nat := 4983230072969 + 3 ^ 40 * 3442504 * 2
def baseEnd_3442504 : Nat := 1178439471350336280645479

theorem tailTrace_3442504 : CollatzResearch.WordTrace tailWord_3442504 prefixEnd_3442504 1178439471350336280645479 := by
  unfold tailWord_3442504
  simp only [CollatzResearch.WordTrace]
  refine ⟨62779217960201707860291283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83705623946935610480388377 62779217960201707860291283)
  ·
    refine ⟨94168826940302561790436925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62779217960201707860291283 94168826940302561790436925)
    ·
      refine ⟨35313310102613460671413847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94168826940302561790436925 35313310102613460671413847)
      ·
        refine ⟨52969965153920191007120771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35313310102613460671413847 52969965153920191007120771)
        ·
          refine ⟨79454947730880286510681157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52969965153920191007120771 79454947730880286510681157)
          ·
            refine ⟨14897802699540053720752717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79454947730880286510681157 14897802699540053720752717)
            ·
              refine ⟨5586676012327520145282269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14897802699540053720752717 5586676012327520145282269)
              ·
                refine ⟨2095003504622820054480851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5586676012327520145282269 2095003504622820054480851)
                ·
                  refine ⟨3142505256934230081721277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095003504622820054480851 3142505256934230081721277)
                  ·
                    refine ⟨1178439471350336280645479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142505256934230081721277 1178439471350336280645479)
                    ·
                      rfl

theorem cell22_3442504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_3442504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442504 prefixEnd_3442504 := by exact prefixLift 3442504
  have htrace : WordTrace (prefixWord ++ tailWord_3442504) baseStart_3442504 baseEnd_3442504 := by
    simpa [prefixWord, tailWord_3442504, baseEnd_3442504] using wordTrace_append hprefix tailTrace_3442504
  have hstable : (prefixWord ++ tailWord_3442504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442504).length < 2 ^ (prefixWord ++ tailWord_3442504).sum := by decide
  have hdescent : baseEnd_3442504 < baseStart_3442504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442560 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_3442560 : Nat := 118140960795 + 3442560 * 2 ^ 59
def prefixEnd_3442560 : Nat := 4983230072969 + 3 ^ 40 * 3442560 * 2
def baseEnd_3442560 : Nat := 1178458641294770801245307

theorem tailTrace_3442560 : CollatzResearch.WordTrace tailWord_3442560 prefixEnd_3442560 1178458641294770801245307 := by
  unfold tailWord_3442560
  simp only [CollatzResearch.WordTrace]
  refine ⟨62780239204100268642310567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83706985605467024856414089 62780239204100268642310567)
  ·
    refine ⟨94170358806150402963465851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62780239204100268642310567 94170358806150402963465851)
    ·
      refine ⟨141255538209225604445198777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94170358806150402963465851 141255538209225604445198777)
      ·
        refine ⟨105941653656919203333899083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141255538209225604445198777 105941653656919203333899083)
        ·
          refine ⟨158912480485378805000848625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105941653656919203333899083 158912480485378805000848625)
          ·
            refine ⟨119184360364034103750636469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158912480485378805000848625 119184360364034103750636469)
            ·
              refine ⟨11173533784128197226622169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119184360364034103750636469 11173533784128197226622169)
              ·
                refine ⟨8380150338096147919966627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11173533784128197226622169 8380150338096147919966627)
                ·
                  refine ⟨12570225507144221879949941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8380150338096147919966627 12570225507144221879949941)
                  ·
                    refine ⟨1178458641294770801245307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12570225507144221879949941 1178458641294770801245307)
                    ·
                      rfl

theorem cell22_3442560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_3442560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442560 prefixEnd_3442560 := by exact prefixLift 3442560
  have htrace : WordTrace (prefixWord ++ tailWord_3442560) baseStart_3442560 baseEnd_3442560 := by
    simpa [prefixWord, tailWord_3442560, baseEnd_3442560] using wordTrace_append hprefix tailTrace_3442560
  have hstable : (prefixWord ++ tailWord_3442560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442560).length < 2 ^ (prefixWord ++ tailWord_3442560).sum := by decide
  have hdescent : baseEnd_3442560 < baseStart_3442560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442577 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 2, 3]
def baseStart_3442577 : Nat := 118140960795 + 3442577 * 2 ^ 59
def prefixEnd_3442577 : Nat := 4983230072969 + 3 ^ 40 * 3442577 * 2
def baseEnd_3442577 : Nat := 1178464460742188423570255

theorem tailTrace_3442577 : CollatzResearch.WordTrace tailWord_3442577 prefixEnd_3442577 1178464460742188423570255 := by
  unfold tailWord_3442577
  simp only [CollatzResearch.WordTrace]
  refine ⟨125561098449138949187989985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83707398966092632791993323 125561098449138949187989985)
  ·
    refine ⟨94170823836854211890992489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125561098449138949187989985 94170823836854211890992489)
    ·
      refine ⟨70628117877640658918244367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94170823836854211890992489 70628117877640658918244367)
      ·
        refine ⟨105942176816460988377366551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70628117877640658918244367 105942176816460988377366551)
        ·
          refine ⟨158913265224691482566049827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105942176816460988377366551 158913265224691482566049827)
          ·
            refine ⟨238369897837037223849074741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158913265224691482566049827 238369897837037223849074741)
            ·
              refine ⟨22347177922222239735850757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238369897837037223849074741 22347177922222239735850757)
              ·
                refine ⟨4190095860416669950472017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22347177922222239735850757 4190095860416669950472017)
                ·
                  refine ⟨3142571895312502462854013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190095860416669950472017 3142571895312502462854013)
                  ·
                    refine ⟨1178464460742188423570255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142571895312502462854013 1178464460742188423570255)
                    ·
                      rfl

theorem cell22_3442577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_3442577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442577 prefixEnd_3442577 := by exact prefixLift 3442577
  have htrace : WordTrace (prefixWord ++ tailWord_3442577) baseStart_3442577 baseEnd_3442577 := by
    simpa [prefixWord, tailWord_3442577, baseEnd_3442577] using wordTrace_append hprefix tailTrace_3442577
  have hstable : (prefixWord ++ tailWord_3442577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442577).length < 2 ^ (prefixWord ++ tailWord_3442577).sum := by decide
  have hdescent : baseEnd_3442577 < baseStart_3442577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442594 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3442594 : Nat := 118140960795 + 3442594 * 2 ^ 59
def prefixEnd_3442594 : Nat := 4983230072969 + 3 ^ 40 * 3442594 * 2
def baseEnd_3442594 : Nat := 1178470280189606045895203

theorem tailTrace_3442594 : CollatzResearch.WordTrace tailWord_3442594 prefixEnd_3442594 1178470280189606045895203 := by
  unfold tailWord_3442594
  simp only [CollatzResearch.WordTrace]
  refine ⟨31390429622519340272839709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83707812326718240727572557 31390429622519340272839709)
  ·
    refine ⟨11771411108444752602314891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31390429622519340272839709 11771411108444752602314891)
    ·
      refine ⟨17657116662667128903472337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11771411108444752602314891 17657116662667128903472337)
      ·
        refine ⟨13242837497000346677604253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17657116662667128903472337 13242837497000346677604253)
        ·
          refine ⟨4966064061375130004101595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13242837497000346677604253 4966064061375130004101595)
          ·
            refine ⟨7449096092062695006152393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966064061375130004101595 7449096092062695006152393)
            ·
              refine ⟨5586822069047021254614295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449096092062695006152393 5586822069047021254614295)
              ·
                refine ⟨8380233103570531881921443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586822069047021254614295 8380233103570531881921443)
                ·
                  refine ⟨12570349655355797822882165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8380233103570531881921443 12570349655355797822882165)
                  ·
                    refine ⟨1178470280189606045895203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12570349655355797822882165 1178470280189606045895203)
                    ·
                      rfl

theorem cell22_3442594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3442594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442594 prefixEnd_3442594 := by exact prefixLift 3442594
  have htrace : WordTrace (prefixWord ++ tailWord_3442594) baseStart_3442594 baseEnd_3442594 := by
    simpa [prefixWord, tailWord_3442594, baseEnd_3442594] using wordTrace_append hprefix tailTrace_3442594
  have hstable : (prefixWord ++ tailWord_3442594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442594).length < 2 ^ (prefixWord ++ tailWord_3442594).sum := by decide
  have hdescent : baseEnd_3442594 < baseStart_3442594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442609 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 2, 4]
def baseStart_3442609 : Nat := 118140960795 + 3442609 * 2 ^ 59
def prefixEnd_3442609 : Nat := 4983230072969 + 3 ^ 40 * 3442609 * 2
def baseEnd_3442609 : Nat := 1178475414996151006770157

theorem tailTrace_3442609 : CollatzResearch.WordTrace tailWord_3442609 prefixEnd_3442609 1178475414996151006770157 := by
  unfold tailWord_3442609
  simp only [CollatzResearch.WordTrace]
  refine ⟨125562265585023018653154881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83708177056682012435436587 125562265585023018653154881)
  ·
    refine ⟨94171699188767263989866161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125562265585023018653154881 94171699188767263989866161)
    ·
      refine ⟨70628774391575447992399621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94171699188767263989866161 70628774391575447992399621)
      ·
        refine ⟨13242895198420396498574929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70628774391575447992399621 13242895198420396498574929)
        ·
          refine ⟨9932171398815297373931197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13242895198420396498574929 9932171398815297373931197)
          ·
            refine ⟨3724564274555736515224199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9932171398815297373931197 3724564274555736515224199)
            ·
              refine ⟨5586846411833604772836299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724564274555736515224199 5586846411833604772836299)
              ·
                refine ⟨8380269617750407159254449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586846411833604772836299 8380269617750407159254449)
                ·
                  refine ⟨6285202213312805369440837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8380269617750407159254449 6285202213312805369440837)
                  ·
                    refine ⟨1178475414996151006770157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285202213312805369440837 1178475414996151006770157)
                    ·
                      rfl

theorem cell22_3442609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_3442609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442609 prefixEnd_3442609 := by exact prefixLift 3442609
  have htrace : WordTrace (prefixWord ++ tailWord_3442609) baseStart_3442609 baseEnd_3442609 := by
    simpa [prefixWord, tailWord_3442609, baseEnd_3442609] using wordTrace_append hprefix tailTrace_3442609
  have hstable : (prefixWord ++ tailWord_3442609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442609).length < 2 ^ (prefixWord ++ tailWord_3442609).sum := by decide
  have hdescent : baseEnd_3442609 < baseStart_3442609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442635 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 7]
def baseStart_3442635 : Nat := 118140960795 + 3442635 * 2 ^ 59
def prefixEnd_3442635 : Nat := 4983230072969 + 3 ^ 40 * 3442635 * 2
def baseEnd_3442635 : Nat := 392828105109165201873359

theorem tailTrace_3442635 : CollatzResearch.WordTrace tailWord_3442635 prefixEnd_3442635 392828105109165201873359 := by
  unfold tailWord_3442635
  simp only [CollatzResearch.WordTrace]
  refine ⟨125563213882928825093601359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83708809255285883395734239 125563213882928825093601359)
  ·
    refine ⟨188344820824393237640402039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125563213882928825093601359 188344820824393237640402039)
    ·
      refine ⟨282517231236589856460603059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188344820824393237640402039 282517231236589856460603059)
      ·
        refine ⟨423775846854884784690904589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282517231236589856460603059 423775846854884784690904589)
        ·
          refine ⟨158915942570581794259089221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423775846854884784690904589 158915942570581794259089221)
          ·
            refine ⟨29796739231984086423579229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158915942570581794259089221 29796739231984086423579229)
            ·
              refine ⟨11173777211994032408842211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29796739231984086423579229 11173777211994032408842211)
              ·
                refine ⟨16760665817991048613263317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11173777211994032408842211 16760665817991048613263317)
                ·
                  refine ⟨392828105109165201873359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16760665817991048613263317 392828105109165201873359)
                  ·
                    rfl

theorem cell22_3442635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 7].length) (baseStart_3442635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442635 prefixEnd_3442635 := by exact prefixLift 3442635
  have htrace : WordTrace (prefixWord ++ tailWord_3442635) baseStart_3442635 baseEnd_3442635 := by
    simpa [prefixWord, tailWord_3442635, baseEnd_3442635] using wordTrace_append hprefix tailTrace_3442635
  have hstable : (prefixWord ++ tailWord_3442635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442635).length < 2 ^ (prefixWord ++ tailWord_3442635).sum := by decide
  have hdescent : baseEnd_3442635 < baseStart_3442635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442639 : List Nat := [1, 1, 2, 1, 1, 5, 1, 6, 1, 3]
def baseStart_3442639 : Nat := 118140960795 + 3442639 * 2 ^ 59
def prefixEnd_3442639 : Nat := 4983230072969 + 3 ^ 40 * 3442639 * 2
def baseEnd_3442639 : Nat := 1178485684609240928520065

theorem tailTrace_3442639 : CollatzResearch.WordTrace tailWord_3442639 prefixEnd_3442639 1178485684609240928520065 := by
  unfold tailWord_3442639
  simp only [CollatzResearch.WordTrace]
  refine ⟨125563359774914333776746971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83708906516609555851164647 125563359774914333776746971)
  ·
    refine ⟨188345039662371500665120457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125563359774914333776746971 188345039662371500665120457)
    ·
      refine ⟨141258779746778625498840343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188345039662371500665120457 141258779746778625498840343)
      ·
        refine ⟨211888169620167938248260515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141258779746778625498840343 211888169620167938248260515)
        ·
          refine ⟨317832254430251907372390773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211888169620167938248260515 317832254430251907372390773)
          ·
            refine ⟨29796773852836116316161635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 317832254430251907372390773 29796773852836116316161635)
            ·
              refine ⟨44695160779254174474242453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29796773852836116316161635 44695160779254174474242453)
              ·
                refine ⟨2095085661527539428480115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44695160779254174474242453 2095085661527539428480115)
                ·
                  refine ⟨3142628492291309142720173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095085661527539428480115 3142628492291309142720173)
                  ·
                    refine ⟨1178485684609240928520065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142628492291309142720173 1178485684609240928520065)
                    ·
                      rfl

theorem cell22_3442639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 3].length) (baseStart_3442639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442639 prefixEnd_3442639 := by exact prefixLift 3442639
  have htrace : WordTrace (prefixWord ++ tailWord_3442639) baseStart_3442639 baseEnd_3442639 := by
    simpa [prefixWord, tailWord_3442639, baseEnd_3442639] using wordTrace_append hprefix tailTrace_3442639
  have hstable : (prefixWord ++ tailWord_3442639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442639).length < 2 ^ (prefixWord ++ tailWord_3442639).sum := by decide
  have hdescent : baseEnd_3442639 < baseStart_3442639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442658 : List Nat := [3, 3, 3, 1, 3, 1, 2, 6]
def baseStart_3442658 : Nat := 118140960795 + 3442658 * 2 ^ 59
def prefixEnd_3442658 : Nat := 4983230072969 + 3 ^ 40 * 3442658 * 2
def baseEnd_3442658 : Nat := 130943576521947912477223

theorem tailTrace_3442658 : CollatzResearch.WordTrace tailWord_3442658 prefixEnd_3442658 130943576521947912477223 := by
  unfold tailWord_3442658
  simp only [CollatzResearch.WordTrace]
  refine ⟨31391013190461375005422157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83709368507897000014459085 31391013190461375005422157)
  ·
    refine ⟨11771629946423015627033309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31391013190461375005422157 11771629946423015627033309)
    ·
      refine ⟨4414361229908630860137491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11771629946423015627033309 4414361229908630860137491)
      ·
        refine ⟨6621541844862946290206237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414361229908630860137491 6621541844862946290206237)
        ·
          refine ⟨2483078191823604858827339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6621541844862946290206237 2483078191823604858827339)
          ·
            refine ⟨3724617287735407288241009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483078191823604858827339 3724617287735407288241009)
            ·
              refine ⟨2793462965801555466180757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724617287735407288241009 2793462965801555466180757)
              ·
                refine ⟨130943576521947912477223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2793462965801555466180757 130943576521947912477223)
                ·
                  rfl

theorem cell22_3442658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_3442658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442658 prefixEnd_3442658 := by exact prefixLift 3442658
  have htrace : WordTrace (prefixWord ++ tailWord_3442658) baseStart_3442658 baseEnd_3442658 := by
    simpa [prefixWord, tailWord_3442658, baseEnd_3442658] using wordTrace_append hprefix tailTrace_3442658
  have hstable : (prefixWord ++ tailWord_3442658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442658).length < 2 ^ (prefixWord ++ tailWord_3442658).sum := by decide
  have hdescent : baseEnd_3442658 < baseStart_3442658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442673 : List Nat := [1, 2, 2, 2, 5, 2, 1, 3, 1, 3]
def baseStart_3442673 : Nat := 118140960795 + 3442673 * 2 ^ 59
def prefixEnd_3442673 : Nat := 4983230072969 + 3 ^ 40 * 3442673 * 2
def baseEnd_3442673 : Nat := 1178497323504076173169961

theorem tailTrace_3442673 : CollatzResearch.WordTrace tailWord_3442673 prefixEnd_3442673 1178497323504076173169961 := by
  unfold tailWord_3442673
  simp only [CollatzResearch.WordTrace]
  refine ⟨125564599856791157583484673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83709733237860771722323115 125564599856791157583484673)
  ·
    refine ⟨94173449892593368187613505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125564599856791157583484673 94173449892593368187613505)
    ·
      refine ⟨70630087419445026140710129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94173449892593368187613505 70630087419445026140710129)
      ·
        refine ⟨52972565564583769605532597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70630087419445026140710129 52972565564583769605532597)
        ·
          refine ⟨4966178021679728400518681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52972565564583769605532597 4966178021679728400518681)
          ·
            refine ⟨3724633516259796300389011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4966178021679728400518681 3724633516259796300389011)
            ·
              refine ⟨5586950274389694450583517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724633516259796300389011 5586950274389694450583517)
              ·
                refine ⟨2095106352896135418968819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5586950274389694450583517 2095106352896135418968819)
                ·
                  refine ⟨3142659529344203128453229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095106352896135418968819 3142659529344203128453229)
                  ·
                    refine ⟨1178497323504076173169961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142659529344203128453229 1178497323504076173169961)
                    ·
                      rfl

theorem cell22_3442673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_3442673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442673 prefixEnd_3442673 := by exact prefixLift 3442673
  have htrace : WordTrace (prefixWord ++ tailWord_3442673) baseStart_3442673 baseEnd_3442673 := by
    simpa [prefixWord, tailWord_3442673, baseEnd_3442673] using wordTrace_append hprefix tailTrace_3442673
  have hstable : (prefixWord ++ tailWord_3442673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442673).length < 2 ^ (prefixWord ++ tailWord_3442673).sum := by decide
  have hdescent : baseEnd_3442673 < baseStart_3442673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442680 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 8]
def baseStart_3442680 : Nat := 118140960795 + 3442680 * 2 ^ 59
def prefixEnd_3442680 : Nat := 4983230072969 + 3 ^ 40 * 3442680 * 2
def baseEnd_3442680 : Nat := 392833239915710162748313

theorem tailTrace_3442680 : CollatzResearch.WordTrace tailWord_3442680 prefixEnd_3442680 392833239915710162748313 := by
  unfold tailWord_3442680
  simp only [CollatzResearch.WordTrace]
  refine ⟨62782427583882898889494747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83709903445177198519326329 62782427583882898889494747)
  ·
    refine ⟨94173641375824348334242121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62782427583882898889494747 94173641375824348334242121)
    ·
      refine ⟨70630231031868261250681591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94173641375824348334242121 70630231031868261250681591)
      ·
        refine ⟨105945346547802391876022387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70630231031868261250681591 105945346547802391876022387)
        ·
          refine ⟨158918019821703587814033581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105945346547802391876022387 158918019821703587814033581)
          ·
            refine ⟨59594257433138845430262593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158918019821703587814033581 59594257433138845430262593)
            ·
              refine ⟨44695693074854134072696945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59594257433138845430262593 44695693074854134072696945)
              ·
                refine ⟨33521769806140600554522709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44695693074854134072696945 33521769806140600554522709)
                ·
                  refine ⟨392833239915710162748313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33521769806140600554522709 392833239915710162748313)
                  ·
                    rfl

theorem cell22_3442680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_3442680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442680 prefixEnd_3442680 := by exact prefixLift 3442680
  have htrace : WordTrace (prefixWord ++ tailWord_3442680) baseStart_3442680 baseEnd_3442680 := by
    simpa [prefixWord, tailWord_3442680, baseEnd_3442680] using wordTrace_append hprefix tailTrace_3442680
  have hstable : (prefixWord ++ tailWord_3442680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442680).length < 2 ^ (prefixWord ++ tailWord_3442680).sum := by decide
  have hdescent : baseEnd_3442680 < baseStart_3442680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442712 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_3442712 : Nat := 118140960795 + 3442712 * 2 ^ 59
def prefixEnd_3442712 : Nat := 4983230072969 + 3 ^ 40 * 3442712 * 2
def baseEnd_3442712 : Nat := 1178510674001093071444841

theorem tailTrace_3442712 : CollatzResearch.WordTrace tailWord_3442712 prefixEnd_3442712 1178510674001093071444841 := by
  unfold tailWord_3442712
  simp only [CollatzResearch.WordTrace]
  refine ⟨62783011151824933622077195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83710681535766578162769593 62783011151824933622077195)
  ·
    refine ⟨94174516727737400433115793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62783011151824933622077195 94174516727737400433115793)
    ·
      refine ⟨70630887545803050324836845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94174516727737400433115793 70630887545803050324836845)
      ·
        refine ⟨26486582829676143871813817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70630887545803050324836845 26486582829676143871813817)
        ·
          refine ⟨19864937122257107903860363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26486582829676143871813817 19864937122257107903860363)
          ·
            refine ⟨29797405683385661855790545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19864937122257107903860363 29797405683385661855790545)
            ·
              refine ⟨22348054262539246391842909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29797405683385661855790545 22348054262539246391842909)
              ·
                refine ⟨8380520348452217396941091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22348054262539246391842909 8380520348452217396941091)
                ·
                  refine ⟨12570780522678326095411637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8380520348452217396941091 12570780522678326095411637)
                  ·
                    refine ⟨1178510674001093071444841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12570780522678326095411637 1178510674001093071444841)
                    ·
                      rfl

theorem cell22_3442712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_3442712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442712 prefixEnd_3442712 := by exact prefixLift 3442712
  have htrace : WordTrace (prefixWord ++ tailWord_3442712) baseStart_3442712 baseEnd_3442712 := by
    simpa [prefixWord, tailWord_3442712, baseEnd_3442712] using wordTrace_append hprefix tailTrace_3442712
  have hstable : (prefixWord ++ tailWord_3442712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442712).length < 2 ^ (prefixWord ++ tailWord_3442712).sum := by decide
  have hdescent : baseEnd_3442712 < baseStart_3442712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442716 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_3442716 : Nat := 118140960795 + 3442716 * 2 ^ 59
def prefixEnd_3442716 : Nat := 4983230072969 + 3 ^ 40 * 3442716 * 2
def baseEnd_3442716 : Nat := 1178512043282838394344829

theorem tailTrace_3442716 : CollatzResearch.WordTrace tailWord_3442716 prefixEnd_3442716 1178512043282838394344829 := by
  unfold tailWord_3442716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62783084097817687963650001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83710778797090250618200001 62783084097817687963650001)
  ·
    refine ⟨47087313073363265972737501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62783084097817687963650001 47087313073363265972737501)
    ·
      refine ⟨17657742402511224739776563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47087313073363265972737501 17657742402511224739776563)
      ·
        refine ⟨26486613603766837109664845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17657742402511224739776563 26486613603766837109664845)
        ·
          refine ⟨9932480101412563916124317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26486613603766837109664845 9932480101412563916124317)
          ·
            refine ⟨3724680038029711468546619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9932480101412563916124317 3724680038029711468546619)
            ·
              refine ⟨5587020057044567202819929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724680038029711468546619 5587020057044567202819929)
              ·
                refine ⟨4190265042783425402114947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5587020057044567202819929 4190265042783425402114947)
                ·
                  refine ⟨6285397564175138103172421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4190265042783425402114947 6285397564175138103172421)
                  ·
                    refine ⟨1178512043282838394344829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285397564175138103172421 1178512043282838394344829)
                    ·
                      rfl

theorem cell22_3442716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_3442716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442716 prefixEnd_3442716 := by exact prefixLift 3442716
  have htrace : WordTrace (prefixWord ++ tailWord_3442716) baseStart_3442716 baseEnd_3442716 := by
    simpa [prefixWord, tailWord_3442716, baseEnd_3442716] using wordTrace_append hprefix tailTrace_3442716
  have hstable : (prefixWord ++ tailWord_3442716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442716).length < 2 ^ (prefixWord ++ tailWord_3442716).sum := by decide
  have hdescent : baseEnd_3442716 < baseStart_3442716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442772 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3442772 : Nat := 118140960795 + 3442772 * 2 ^ 59
def prefixEnd_3442772 : Nat := 4983230072969 + 3 ^ 40 * 3442772 * 2
def baseEnd_3442772 : Nat := 1178531213227272914944657

theorem tailTrace_3442772 : CollatzResearch.WordTrace tailWord_3442772 prefixEnd_3442772 1178531213227272914944657 := by
  unfold tailWord_3442772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62784105341716248745669285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83712140455621664994225713 62784105341716248745669285)
  ·
    refine ⟨11772019751571796639812991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62784105341716248745669285 11772019751571796639812991)
    ·
      refine ⟨17658029627357694959719487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11772019751571796639812991 17658029627357694959719487)
      ·
        refine ⟨26487044441036542439579231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17658029627357694959719487 26487044441036542439579231)
        ·
          refine ⟨39730566661554813659368847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26487044441036542439579231 39730566661554813659368847)
          ·
            refine ⟨59595849992332220489053271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39730566661554813659368847 59595849992332220489053271)
            ·
              refine ⟨89393774988498330733579907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59595849992332220489053271 89393774988498330733579907)
              ·
                refine ⟨134090662482747496100369861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89393774988498330733579907 134090662482747496100369861)
                ·
                  refine ⟨25141999215515155518819349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134090662482747496100369861 25141999215515155518819349)
                  ·
                    refine ⟨1178531213227272914944657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25141999215515155518819349 1178531213227272914944657)
                    ·
                      rfl

theorem cell22_3442772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3442772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442772 prefixEnd_3442772 := by exact prefixLift 3442772
  have htrace : WordTrace (prefixWord ++ tailWord_3442772) baseStart_3442772 baseEnd_3442772 := by
    simpa [prefixWord, tailWord_3442772, baseEnd_3442772] using wordTrace_append hprefix tailTrace_3442772
  have hstable : (prefixWord ++ tailWord_3442772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442772).length < 2 ^ (prefixWord ++ tailWord_3442772).sum := by decide
  have hdescent : baseEnd_3442772 < baseStart_3442772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442821 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 5]
def baseStart_3442821 : Nat := 118140960795 + 3442821 * 2 ^ 59
def prefixEnd_3442821 : Nat := 4983230072969 + 3 ^ 40 * 3442821 * 2
def baseEnd_3442821 : Nat := 392849328976217706823169

theorem tailTrace_3442821 : CollatzResearch.WordTrace tailWord_3442821 prefixEnd_3442821 392849328976217706823169 := by
  unfold tailWord_3442821
  simp only [CollatzResearch.WordTrace]
  refine ⟨125569997860254978859872317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83713331906836652573248211 125569997860254978859872317)
  ·
    refine ⟨47088749197595617072452119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125569997860254978859872317 47088749197595617072452119)
    ·
      refine ⟨70633123796393425608678179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47088749197595617072452119 70633123796393425608678179)
      ·
        refine ⟨105949685694590138413017269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70633123796393425608678179 105949685694590138413017269)
        ·
          refine ⟨9932783033867825476220369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105949685694590138413017269 9932783033867825476220369)
          ·
            refine ⟨7449587275400869107165277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9932783033867825476220369 7449587275400869107165277)
            ·
              refine ⟨2793595228275325915186979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7449587275400869107165277 2793595228275325915186979)
              ·
                refine ⟨4190392842412988872780469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793595228275325915186979 4190392842412988872780469)
                ·
                  refine ⟨392849328976217706823169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4190392842412988872780469 392849328976217706823169)
                  ·
                    rfl

theorem cell22_3442821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_3442821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442821 prefixEnd_3442821 := by exact prefixLift 3442821
  have htrace : WordTrace (prefixWord ++ tailWord_3442821) baseStart_3442821 baseEnd_3442821 := by
    simpa [prefixWord, tailWord_3442821, baseEnd_3442821] using wordTrace_append hprefix tailTrace_3442821
  have hstable : (prefixWord ++ tailWord_3442821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442821).length < 2 ^ (prefixWord ++ tailWord_3442821).sum := by decide
  have hdescent : baseEnd_3442821 < baseStart_3442821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442832 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 6]
def baseStart_3442832 : Nat := 118140960795 + 3442832 * 2 ^ 59
def prefixEnd_3442832 : Nat := 4983230072969 + 3 ^ 40 * 3442832 * 2
def baseEnd_3442832 : Nat := 392850584151150919481491

theorem tailTrace_3442832 : CollatzResearch.WordTrace tailWord_3442832 prefixEnd_3442832 392850584151150919481491 := by
  unfold tailWord_3442832
  simp only [CollatzResearch.WordTrace]
  refine ⟨62785199531607563869261375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83713599375476751825681833 62785199531607563869261375)
  ·
    refine ⟨94177799297411345803892063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62785199531607563869261375 94177799297411345803892063)
    ·
      refine ⟨141266698946117018705838095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94177799297411345803892063 141266698946117018705838095)
      ·
        refine ⟨211900048419175528058757143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141266698946117018705838095 211900048419175528058757143)
        ·
          refine ⟨317850072628763292088135715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211900048419175528058757143 317850072628763292088135715)
          ·
            refine ⟨476775108943144938132203573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317850072628763292088135715 476775108943144938132203573)
            ·
              refine ⟨44697666463419837949894085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476775108943144938132203573 44697666463419837949894085)
              ·
                refine ⟨8380812461891219615605141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44697666463419837949894085 8380812461891219615605141)
                ·
                  refine ⟨392850584151150919481491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8380812461891219615605141 392850584151150919481491)
                  ·
                    rfl

theorem cell22_3442832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_3442832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442832 prefixEnd_3442832 := by exact prefixLift 3442832
  have htrace : WordTrace (prefixWord ++ tailWord_3442832) baseStart_3442832 baseEnd_3442832 := by
    simpa [prefixWord, tailWord_3442832, baseEnd_3442832] using wordTrace_append hprefix tailTrace_3442832
  have hstable : (prefixWord ++ tailWord_3442832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442832).length < 2 ^ (prefixWord ++ tailWord_3442832).sum := by decide
  have hdescent : baseEnd_3442832 < baseStart_3442832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442842 : List Nat := [3, 1, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_3442842 : Nat := 118140960795 + 3442842 * 2 ^ 59
def prefixEnd_3442842 : Nat := 4983230072969 + 3 ^ 40 * 3442842 * 2
def baseEnd_3442842 : Nat := 1178555175657816065694443

theorem tailTrace_3442842 : CollatzResearch.WordTrace tailWord_3442842 prefixEnd_3442842 1178555175657816065694443 := by
  unfold tailWord_3442842
  simp only [CollatzResearch.WordTrace]
  refine ⟨31392690948294724861596695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83713842528785932964257853 31392690948294724861596695)
  ·
    refine ⟨47089036422442087292395043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31392690948294724861596695 47089036422442087292395043)
    ·
      refine ⟨70633554633663130938592565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47089036422442087292395043 70633554633663130938592565)
      ·
        refine ⟨6621895746905918525493053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70633554633663130938592565 6621895746905918525493053)
        ·
          refine ⟨2483210905089719447059895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6621895746905918525493053 2483210905089719447059895)
          ·
            refine ⟨3724816357634579170589843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483210905089719447059895 3724816357634579170589843)
            ·
              refine ⟨5587224536451868755884765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724816357634579170589843 5587224536451868755884765)
              ·
                refine ⟨2095209201169450783456787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5587224536451868755884765 2095209201169450783456787)
                ·
                  refine ⟨3142813801754176175185181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095209201169450783456787 3142813801754176175185181)
                  ·
                    refine ⟨1178555175657816065694443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142813801754176175185181 1178555175657816065694443)
                    ·
                      rfl

theorem cell22_3442842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_3442842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442842 prefixEnd_3442842 := by exact prefixLift 3442842
  have htrace : WordTrace (prefixWord ++ tailWord_3442842) baseStart_3442842 baseEnd_3442842 := by
    simpa [prefixWord, tailWord_3442842, baseEnd_3442842] using wordTrace_append hprefix tailTrace_3442842
  have hstable : (prefixWord ++ tailWord_3442842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442842).length < 2 ^ (prefixWord ++ tailWord_3442842).sum := by decide
  have hdescent : baseEnd_3442842 < baseStart_3442842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442894 : List Nat := [4, 1, 1, 1, 4, 1, 2, 8]
def baseStart_3442894 : Nat := 118140960795 + 3442894 * 2 ^ 59
def prefixEnd_3442894 : Nat := 4983230072969 + 3 ^ 40 * 3442894 * 2
def baseEnd_3442894 : Nat := 130952552924500584821587

theorem tailTrace_3442894 : CollatzResearch.WordTrace tailWord_3442894 prefixEnd_3442894 130952552924500584821587 := by
  unfold tailWord_3442894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696582548623814040909967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83715106925993674884853157 15696582548623814040909967)
  ·
    refine ⟨23544873822935721061364951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15696582548623814040909967 23544873822935721061364951)
    ·
      refine ⟨35317310734403581592047427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23544873822935721061364951 35317310734403581592047427)
      ·
        refine ⟨52975966101605372388071141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35317310734403581592047427 52975966101605372388071141)
        ·
          refine ⟨9932993644051007322763339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52975966101605372388071141 9932993644051007322763339)
          ·
            refine ⟨14899490466076510984145009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9932993644051007322763339 14899490466076510984145009)
            ·
              refine ⟨11174617849557383238108757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14899490466076510984145009 11174617849557383238108757)
              ·
                refine ⟨130952552924500584821587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11174617849557383238108757 130952552924500584821587)
                ·
                  rfl

theorem cell22_3442894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_3442894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442894 prefixEnd_3442894 := by exact prefixLift 3442894
  have htrace : WordTrace (prefixWord ++ tailWord_3442894) baseStart_3442894 baseEnd_3442894 := by
    simpa [prefixWord, tailWord_3442894, baseEnd_3442894] using wordTrace_append hprefix tailTrace_3442894
  have hstable : (prefixWord ++ tailWord_3442894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442894).length < 2 ^ (prefixWord ++ tailWord_3442894).sum := by decide
  have hdescent : baseEnd_3442894 < baseStart_3442894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442907 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 1, 8]
def baseStart_3442907 : Nat := 118140960795 + 3442907 * 2 ^ 59
def prefixEnd_3442907 : Nat := 4983230072969 + 3 ^ 40 * 3442907 * 2
def baseEnd_3442907 : Nat := 1178577426486177562819243

theorem tailTrace_3442907 : CollatzResearch.WordTrace tailWord_3442907 prefixEnd_3442907 1178577426486177562819243 := by
  unfold tailWord_3442907
  simp only [CollatzResearch.WordTrace]
  refine ⟨125573134537943415547502975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83715423025295610365001983 125573134537943415547502975)
  ·
    refine ⟨188359701806915123321254463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125573134537943415547502975 188359701806915123321254463)
    ·
      refine ⟨282539552710372684981881695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188359701806915123321254463 282539552710372684981881695)
      ·
        refine ⟨423809329065559027472822543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282539552710372684981881695 423809329065559027472822543)
        ·
          refine ⟨635713993598338541209233815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423809329065559027472822543 635713993598338541209233815)
          ·
            refine ⟨953570990397507811813850723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635713993598338541209233815 953570990397507811813850723)
            ·
              refine ⟨1430356485596261717720776085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953570990397507811813850723 1430356485596261717720776085)
              ·
                refine ⟨67047960262324768018161379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1430356485596261717720776085 67047960262324768018161379)
                ·
                  refine ⟨100571940393487152027242069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67047960262324768018161379 100571940393487152027242069)
                  ·
                    refine ⟨1178577426486177562819243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100571940393487152027242069 1178577426486177562819243)
                    ·
                      rfl

theorem cell22_3442907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_3442907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442907 prefixEnd_3442907 := by exact prefixLift 3442907
  have htrace : WordTrace (prefixWord ++ tailWord_3442907) baseStart_3442907 baseEnd_3442907 := by
    simpa [prefixWord, tailWord_3442907, baseEnd_3442907] using wordTrace_append hprefix tailTrace_3442907
  have hstable : (prefixWord ++ tailWord_3442907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442907).length < 2 ^ (prefixWord ++ tailWord_3442907).sum := by decide
  have hdescent : baseEnd_3442907 < baseStart_3442907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442915 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 2, 3]
def baseStart_3442915 : Nat := 118140960795 + 3442915 * 2 ^ 59
def prefixEnd_3442915 : Nat := 4983230072969 + 3 ^ 40 * 3442915 * 2
def baseEnd_3442915 : Nat := 1178580165049668208619219

theorem tailTrace_3442915 : CollatzResearch.WordTrace tailWord_3442915 prefixEnd_3442915 1178580165049668208619219 := by
  unfold tailWord_3442915
  simp only [CollatzResearch.WordTrace]
  refine ⟨125573426321914432913794199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83715617547942955275862799 125573426321914432913794199)
  ·
    refine ⟨188360139482871649370691299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125573426321914432913794199 188360139482871649370691299)
    ·
      refine ⟨282540209224307474056036949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188360139482871649370691299 282540209224307474056036949)
      ·
        refine ⟨3311018076847353211594183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 282540209224307474056036949 3311018076847353211594183)
        ·
          refine ⟨4966527115271029817391275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311018076847353211594183 4966527115271029817391275)
          ·
            refine ⟨7449790672906544726086913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966527115271029817391275 7449790672906544726086913)
            ·
              refine ⟨5587343004679908544565185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449790672906544726086913 5587343004679908544565185)
              ·
                refine ⟨4190507253509931408423889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5587343004679908544565185 4190507253509931408423889)
                ·
                  refine ⟨3142880440132448556317917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190507253509931408423889 3142880440132448556317917)
                  ·
                    refine ⟨1178580165049668208619219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142880440132448556317917 1178580165049668208619219)
                    ·
                      rfl

theorem cell22_3442915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 3].length) (baseStart_3442915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442915 prefixEnd_3442915 := by exact prefixLift 3442915
  have htrace : WordTrace (prefixWord ++ tailWord_3442915) baseStart_3442915 baseEnd_3442915 := by
    simpa [prefixWord, tailWord_3442915, baseEnd_3442915] using wordTrace_append hprefix tailTrace_3442915
  have hstable : (prefixWord ++ tailWord_3442915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442915).length < 2 ^ (prefixWord ++ tailWord_3442915).sum := by decide
  have hdescent : baseEnd_3442915 < baseStart_3442915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3442926 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3442926 : Nat := 118140960795 + 3442926 * 2 ^ 59
def prefixEnd_3442926 : Nat := 4983230072969 + 3 ^ 40 * 3442926 * 2
def baseEnd_3442926 : Nat := 1178583930574467846594185

theorem tailTrace_3442926 : CollatzResearch.WordTrace tailWord_3442926 prefixEnd_3442926 1178583930574467846594185 := by
  unfold tailWord_3442926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696728440609322724055579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83715885016583054528296421 15696728440609322724055579)
  ·
    refine ⟨23545092660913984086083369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15696728440609322724055579 23545092660913984086083369)
    ·
      refine ⟨17658819495685488064562527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23545092660913984086083369 17658819495685488064562527)
      ·
        refine ⟨26488229243528232096843791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17658819495685488064562527 26488229243528232096843791)
        ·
          refine ⟨39732343865292348145265687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26488229243528232096843791 39732343865292348145265687)
          ·
            refine ⟨59598515797938522217898531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39732343865292348145265687 59598515797938522217898531)
            ·
              refine ⟨89397773696907783326847797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59598515797938522217898531 89397773696907783326847797)
              ·
                refine ⟨8381041284085104686891981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89397773696907783326847797 8381041284085104686891981)
                ·
                  refine ⟨3142890481531914257584493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8381041284085104686891981 3142890481531914257584493)
                  ·
                    refine ⟨1178583930574467846594185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142890481531914257584493 1178583930574467846594185)
                    ·
                      rfl

theorem cell22_3442926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3442926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3442926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3442926 prefixEnd_3442926 := by exact prefixLift 3442926
  have htrace : WordTrace (prefixWord ++ tailWord_3442926) baseStart_3442926 baseEnd_3442926 := by
    simpa [prefixWord, tailWord_3442926, baseEnd_3442926] using wordTrace_append hprefix tailTrace_3442926
  have hstable : (prefixWord ++ tailWord_3442926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3442926).length < 2 ^ (prefixWord ++ tailWord_3442926).sum := by decide
  have hdescent : baseEnd_3442926 < baseStart_3442926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3442926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443001 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 6]
def baseStart_3443001 : Nat := 118140960795 + 3443001 * 2 ^ 59
def prefixEnd_3443001 : Nat := 4983230072969 + 3 ^ 40 * 3443001 * 2
def baseEnd_3443001 : Nat := 392869868202397550322985

theorem tailTrace_3443001 : CollatzResearch.WordTrace tailWord_3443001 prefixEnd_3443001 392869868202397550322985 := by
  unfold tailWord_3443001
  simp only [CollatzResearch.WordTrace]
  refine ⟨125576562999602869601424857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83717708666401913067616571 125576562999602869601424857)
  ·
    refine ⟨94182422249702152201068643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125576562999602869601424857 94182422249702152201068643)
    ·
      refine ⟨141273633374553228301602965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94182422249702152201068643 141273633374553228301602965)
      ·
        refine ⟨6622201564432182576637639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141273633374553228301602965 6622201564432182576637639)
        ·
          refine ⟨9933302346648273864956459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622201564432182576637639 9933302346648273864956459)
          ·
            refine ⟨14899953519972410797434689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9933302346648273864956459 14899953519972410797434689)
            ·
              refine ⟨11174965139979308098076017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14899953519972410797434689 11174965139979308098076017)
              ·
                refine ⟨8381223854984481073557013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11174965139979308098076017 8381223854984481073557013)
                ·
                  refine ⟨392869868202397550322985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8381223854984481073557013 392869868202397550322985)
                  ·
                    rfl

theorem cell22_3443001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_3443001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443001 prefixEnd_3443001 := by exact prefixLift 3443001
  have htrace : WordTrace (prefixWord ++ tailWord_3443001) baseStart_3443001 baseEnd_3443001 := by
    simpa [prefixWord, tailWord_3443001, baseEnd_3443001] using wordTrace_append hprefix tailTrace_3443001
  have hstable : (prefixWord ++ tailWord_3443001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443001).length < 2 ^ (prefixWord ++ tailWord_3443001).sum := by decide
  have hdescent : baseEnd_3443001 < baseStart_3443001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443016 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 4, 3]
def baseStart_3443016 : Nat := 118140960795 + 3443016 * 2 ^ 59
def prefixEnd_3443016 : Nat := 4983230072969 + 3 ^ 40 * 3443016 * 2
def baseEnd_3443016 : Nat := 1178614739413737611843909

theorem tailTrace_3443016 : CollatzResearch.WordTrace tailWord_3443016 prefixEnd_3443016 1178614739413737611843909 := by
  unfold tailWord_3443016
  simp only [CollatzResearch.WordTrace]
  refine ⟨62788555047274263581610451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83718073396365684775480601 62788555047274263581610451)
  ·
    refine ⟨94182832570911395372415677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62788555047274263581610451 94182832570911395372415677)
    ·
      refine ⟨35318562214091773264655879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94182832570911395372415677 35318562214091773264655879)
      ·
        refine ⟨52977843321137659896983819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35318562214091773264655879 52977843321137659896983819)
        ·
          refine ⟨79466764981706489845475729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52977843321137659896983819 79466764981706489845475729)
          ·
            refine ⟨59600073736279867384106797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79466764981706489845475729 59600073736279867384106797)
            ·
              refine ⟨22350027651104950269040049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59600073736279867384106797 22350027651104950269040049)
              ·
                refine ⟨16762520738328712701780037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22350027651104950269040049 16762520738328712701780037)
                ·
                  refine ⟨3142972638436633631583757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16762520738328712701780037 3142972638436633631583757)
                  ·
                    refine ⟨1178614739413737611843909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142972638436633631583757 1178614739413737611843909)
                    ·
                      rfl

theorem cell22_3443016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_3443016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443016 prefixEnd_3443016 := by exact prefixLift 3443016
  have htrace : WordTrace (prefixWord ++ tailWord_3443016) baseStart_3443016 baseEnd_3443016 := by
    simpa [prefixWord, tailWord_3443016, baseEnd_3443016] using wordTrace_append hprefix tailTrace_3443016
  have hstable : (prefixWord ++ tailWord_3443016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443016).length < 2 ^ (prefixWord ++ tailWord_3443016).sum := by decide
  have hdescent : baseEnd_3443016 < baseStart_3443016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443031 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3443031 : Nat := 118140960795 + 3443031 * 2 ^ 59
def prefixEnd_3443031 : Nat := 4983230072969 + 3 ^ 40 * 3443031 * 2
def baseEnd_3443031 : Nat := 1178619874220282572718863

theorem tailTrace_3443031 : CollatzResearch.WordTrace tailWord_3443031 prefixEnd_3443031 1178619874220282572718863 := by
  unfold tailWord_3443031
  simp only [CollatzResearch.WordTrace]
  refine ⟨125577657189494184725016947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83718438126329456483344631 125577657189494184725016947)
  ·
    refine ⟨188366485784241277087525421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125577657189494184725016947 188366485784241277087525421)
    ·
      refine ⟨70637432169090478907822033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188366485784241277087525421 70637432169090478907822033)
      ·
        refine ⟨52978074126817859180866525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70637432169090478907822033 52978074126817859180866525)
        ·
          refine ⟨19866777797556697192824947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52978074126817859180866525 19866777797556697192824947)
          ·
            refine ⟨29800166696335045789237421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19866777797556697192824947 29800166696335045789237421)
            ·
              refine ⟨11175062511125642170964033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29800166696335045789237421 11175062511125642170964033)
              ·
                refine ⟨8381296883344231628223025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11175062511125642170964033 8381296883344231628223025)
                ·
                  refine ⟨6285972662508173721167269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8381296883344231628223025 6285972662508173721167269)
                  ·
                    refine ⟨1178619874220282572718863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6285972662508173721167269 1178619874220282572718863)
                    ·
                      rfl

theorem cell22_3443031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3443031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443031 prefixEnd_3443031 := by exact prefixLift 3443031
  have htrace : WordTrace (prefixWord ++ tailWord_3443031) baseStart_3443031 baseEnd_3443031 := by
    simpa [prefixWord, tailWord_3443031, baseEnd_3443031] using wordTrace_append hprefix tailTrace_3443031
  have hstable : (prefixWord ++ tailWord_3443031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443031).length < 2 ^ (prefixWord ++ tailWord_3443031).sum := by decide
  have hdescent : baseEnd_3443031 < baseStart_3443031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443050 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_3443050 : Nat := 118140960795 + 3443050 * 2 ^ 59
def prefixEnd_3443050 : Nat := 4983230072969 + 3 ^ 40 * 3443050 * 2
def baseEnd_3443050 : Nat := 1178626378308572856493805

theorem tailTrace_3443050 : CollatzResearch.WordTrace tailWord_3443050 prefixEnd_3443050 1178626378308572856493805 := by
  unfold tailWord_3443050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31394587544106337742489651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83718900117616900646639069 31394587544106337742489651)
  ·
    refine ⟨47091881316159506613734477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31394587544106337742489651 47091881316159506613734477)
    ·
      refine ⟨17659455493559814980150429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47091881316159506613734477 17659455493559814980150429)
      ·
        refine ⟨6622295810084930617556411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17659455493559814980150429 6622295810084930617556411)
        ·
          refine ⟨9933443715127395926334617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622295810084930617556411 9933443715127395926334617)
          ·
            refine ⟨7450082786345546944750963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9933443715127395926334617 7450082786345546944750963)
            ·
              refine ⟨11175124179518320417126445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450082786345546944750963 11175124179518320417126445)
              ·
                refine ⟨4190671567319370156422417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11175124179518320417126445 4190671567319370156422417)
                ·
                  refine ⟨3143003675489527617316813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190671567319370156422417 3143003675489527617316813)
                  ·
                    refine ⟨1178626378308572856493805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3143003675489527617316813 1178626378308572856493805)
                    ·
                      rfl

theorem cell22_3443050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_3443050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443050 prefixEnd_3443050 := by exact prefixLift 3443050
  have htrace : WordTrace (prefixWord ++ tailWord_3443050) baseStart_3443050 baseEnd_3443050 := by
    simpa [prefixWord, tailWord_3443050, baseEnd_3443050] using wordTrace_append hprefix tailTrace_3443050
  have hstable : (prefixWord ++ tailWord_3443050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443050).length < 2 ^ (prefixWord ++ tailWord_3443050).sum := by decide
  have hdescent : baseEnd_3443050 < baseStart_3443050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443059 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 2, 6]
def baseStart_3443059 : Nat := 118140960795 + 3443059 * 2 ^ 59
def prefixEnd_3443059 : Nat := 4983230072969 + 3 ^ 40 * 3443059 * 2
def baseEnd_3443059 : Nat := 1178629459192499833018777

theorem tailTrace_3443059 : CollatzResearch.WordTrace tailWord_3443059 prefixEnd_3443059 1178629459192499833018777 := by
  unfold tailWord_3443059
  simp only [CollatzResearch.WordTrace]
  refine ⟨125578678433392745507036231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83719118955595163671357487 125578678433392745507036231)
  ·
    refine ⟨188368017650089118260554347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125578678433392745507036231 188368017650089118260554347)
    ·
      refine ⟨282552026475133677390831521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188368017650089118260554347 282552026475133677390831521)
      ·
        refine ⟨211914019856350258043123641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282552026475133677390831521 211914019856350258043123641)
        ·
          refine ⟨158935514892262693532342731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211914019856350258043123641 158935514892262693532342731)
          ·
            refine ⟨238403272338394040298514097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158935514892262693532342731 238403272338394040298514097)
            ·
              refine ⟨178802454253795530223885573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238403272338394040298514097 178802454253795530223885573)
              ·
                refine ⟨33525460172586661916978545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178802454253795530223885573 33525460172586661916978545)
                ·
                  refine ⟨25144095129439996437733909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33525460172586661916978545 25144095129439996437733909)
                  ·
                    refine ⟨1178629459192499833018777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25144095129439996437733909 1178629459192499833018777)
                    ·
                      rfl

theorem cell22_3443059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_3443059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443059 prefixEnd_3443059 := by exact prefixLift 3443059
  have htrace : WordTrace (prefixWord ++ tailWord_3443059) baseStart_3443059 baseEnd_3443059 := by
    simpa [prefixWord, tailWord_3443059, baseEnd_3443059] using wordTrace_append hprefix tailTrace_3443059
  have hstable : (prefixWord ++ tailWord_3443059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443059).length < 2 ^ (prefixWord ++ tailWord_3443059).sum := by decide
  have hdescent : baseEnd_3443059 < baseStart_3443059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443260 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 5]
def baseStart_3443260 : Nat := 118140960795 + 3443260 * 2 ^ 59
def prefixEnd_3443260 : Nat := 4983230072969 + 3 ^ 40 * 3443260 * 2
def baseEnd_3443260 : Nat := 392899421866734102914387

theorem tailTrace_3443260 : CollatzResearch.WordTrace tailWord_3443260 prefixEnd_3443260 392899421866734102914387 := by
  unfold tailWord_3443260
  simp only [CollatzResearch.WordTrace]
  refine ⟨62793004752832278417551617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83724006337109704556735489 62793004752832278417551617)
  ·
    refine ⟨47094753564624208813163713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62793004752832278417551617 47094753564624208813163713)
    ·
      refine ⟨35321065173468156609872785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47094753564624208813163713 35321065173468156609872785)
      ·
        refine ⟨26490798880101117457404589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35321065173468156609872785 26490798880101117457404589)
        ·
          refine ⟨9934049580037919046526721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26490798880101117457404589 9934049580037919046526721)
          ·
            refine ⟨7450537185028439284895041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9934049580037919046526721 7450537185028439284895041)
            ·
              refine ⟨5587902888771329463671281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7450537185028439284895041 5587902888771329463671281)
              ·
                refine ⟨4190927166578497097753461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5587902888771329463671281 4190927166578497097753461)
                ·
                  refine ⟨392899421866734102914387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4190927166578497097753461 392899421866734102914387)
                  ·
                    rfl

theorem cell22_3443260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_3443260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443260 prefixEnd_3443260 := by exact prefixLift 3443260
  have htrace : WordTrace (prefixWord ++ tailWord_3443260) baseStart_3443260 baseEnd_3443260 := by
    simpa [prefixWord, tailWord_3443260, baseEnd_3443260] using wordTrace_append hprefix tailTrace_3443260
  have hstable : (prefixWord ++ tailWord_3443260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443260).length < 2 ^ (prefixWord ++ tailWord_3443260).sum := by decide
  have hdescent : baseEnd_3443260 < baseStart_3443260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443367 : List Nat := [1, 1, 6, 3, 1, 2, 8]
def baseStart_3443367 : Nat := 118140960795 + 3443367 * 2 ^ 59
def prefixEnd_3443367 : Nat := 4983230072969 + 3 ^ 40 * 3443367 * 2
def baseEnd_3443367 : Nat := 43656847921736655419179

theorem tailTrace_3443367 : CollatzResearch.WordTrace tailWord_3443367 prefixEnd_3443367 43656847921736655419179 := by
  unfold tailWord_3443367
  simp only [CollatzResearch.WordTrace]
  refine ⟨125589912116276914109248355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83726608077517942739498903 125589912116276914109248355)
  ·
    refine ⟨188384868174415371163872533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125589912116276914109248355 188384868174415371163872533)
    ·
      refine ⟨8830540695675720523306525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188384868174415371163872533 8830540695675720523306525)
      ·
        refine ⟨3311452760878395196239947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8830540695675720523306525 3311452760878395196239947)
        ·
          refine ⟨4967179141317592794359921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311452760878395196239947 4967179141317592794359921)
          ·
            refine ⟨3725384355988194595769941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4967179141317592794359921 3725384355988194595769941)
            ·
              refine ⟨43656847921736655419179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3725384355988194595769941 43656847921736655419179)
              ·
                rfl

theorem cell22_3443367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 8].length) (baseStart_3443367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443367 prefixEnd_3443367 := by exact prefixLift 3443367
  have htrace : WordTrace (prefixWord ++ tailWord_3443367) baseStart_3443367 baseEnd_3443367 := by
    simpa [prefixWord, tailWord_3443367, baseEnd_3443367] using wordTrace_append hprefix tailTrace_3443367
  have hstable : (prefixWord ++ tailWord_3443367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443367).length < 2 ^ (prefixWord ++ tailWord_3443367).sum := by decide
  have hdescent : baseEnd_3443367 < baseStart_3443367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443455 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 6, 3]
def baseStart_3443455 : Nat := 118140960795 + 3443455 * 2 ^ 59
def prefixEnd_3443455 : Nat := 4983230072969 + 3 ^ 40 * 3443455 * 2
def baseEnd_3443455 : Nat := 1178765018085286800117563

theorem tailTrace_3443455 : CollatzResearch.WordTrace tailWord_3443455 prefixEnd_3443455 1178765018085286800117563 := by
  unfold tailWord_3443455
  simp only [CollatzResearch.WordTrace]
  refine ⟨125593121739958105138451819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83728747826638736758967879 125593121739958105138451819)
  ·
    refine ⟨188389682609937157707677729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125593121739958105138451819 188389682609937157707677729)
    ·
      refine ⟨141292261957452868280758297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188389682609937157707677729 141292261957452868280758297)
      ·
        refine ⟨105969196468089651210568723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141292261957452868280758297 105969196468089651210568723)
        ·
          refine ⟨158953794702134476815853085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105969196468089651210568723 158953794702134476815853085)
          ·
            refine ⟨59607673013300428805944907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158953794702134476815853085 59607673013300428805944907)
            ·
              refine ⟨89411509519950643208917361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59607673013300428805944907 89411509519950643208917361)
              ·
                refine ⟨67058632139962982406688021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89411509519950643208917361 67058632139962982406688021)
                ·
                  refine ⟨3143373381560764800313501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67058632139962982406688021 3143373381560764800313501)
                  ·
                    refine ⟨1178765018085286800117563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3143373381560764800313501 1178765018085286800117563)
                    ·
                      rfl

theorem cell22_3443455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_3443455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443455 prefixEnd_3443455 := by exact prefixLift 3443455
  have htrace : WordTrace (prefixWord ++ tailWord_3443455) baseStart_3443455 baseEnd_3443455 := by
    simpa [prefixWord, tailWord_3443455, baseEnd_3443455] using wordTrace_append hprefix tailTrace_3443455
  have hstable : (prefixWord ++ tailWord_3443455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443455).length < 2 ^ (prefixWord ++ tailWord_3443455).sum := by decide
  have hdescent : baseEnd_3443455 < baseStart_3443455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443551 : List Nat := [1, 1, 2, 3, 1, 3, 5, 2, 1, 3]
def baseStart_3443551 : Nat := 118140960795 + 3443551 * 2 ^ 59
def prefixEnd_3443551 : Nat := 4983230072969 + 3 ^ 40 * 3443551 * 2
def baseEnd_3443551 : Nat := 1178797880847174549717269

theorem tailTrace_3443551 : CollatzResearch.WordTrace tailWord_3443551 prefixEnd_3443551 1178797880847174549717269 := by
  unfold tailWord_3443551
  simp only [CollatzResearch.WordTrace]
  refine ⟨125596623147610313533946507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83731082098406875689297671 125596623147610313533946507)
  ·
    refine ⟨188394934721415470300919761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125596623147610313533946507 188394934721415470300919761)
    ·
      refine ⟨141296201041061602725689821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188394934721415470300919761 141296201041061602725689821)
      ·
        refine ⟨52986075390398101022133683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141296201041061602725689821 52986075390398101022133683)
        ·
          refine ⟨79479113085597151533200525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52986075390398101022133683 79479113085597151533200525)
          ·
            refine ⟨29804667407098931824950197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79479113085597151533200525 29804667407098931824950197)
            ·
              refine ⟨2794187569415524858589081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29804667407098931824950197 2794187569415524858589081)
              ·
                refine ⟨2095640677061643643941811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2794187569415524858589081 2095640677061643643941811)
                ·
                  refine ⟨3143461015592465465912717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095640677061643643941811 3143461015592465465912717)
                  ·
                    refine ⟨1178797880847174549717269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3143461015592465465912717 1178797880847174549717269)
                    ·
                      rfl

theorem cell22_3443551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 3].length) (baseStart_3443551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443551 prefixEnd_3443551 := by exact prefixLift 3443551
  have htrace : WordTrace (prefixWord ++ tailWord_3443551) baseStart_3443551 baseEnd_3443551 := by
    simpa [prefixWord, tailWord_3443551, baseEnd_3443551] using wordTrace_append hprefix tailTrace_3443551
  have hstable : (prefixWord ++ tailWord_3443551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443551).length < 2 ^ (prefixWord ++ tailWord_3443551).sum := by decide
  have hdescent : baseEnd_3443551 < baseStart_3443551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443575 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 6]
def baseStart_3443575 : Nat := 118140960795 + 3443575 * 2 ^ 59
def prefixEnd_3443575 : Nat := 4983230072969 + 3 ^ 40 * 3443575 * 2
def baseEnd_3443575 : Nat := 392935365512548829039065

theorem tailTrace_3443575 : CollatzResearch.WordTrace tailWord_3443575 prefixEnd_3443575 392935365512548829039065 := by
  unfold tailWord_3443575
  simp only [CollatzResearch.WordTrace]
  refine ⟨125597498499523365632820179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83731665666348910421880119 125597498499523365632820179)
  ·
    refine ⟨188396247749285048449230269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125597498499523365632820179 188396247749285048449230269)
    ·
      refine ⟨70648592905981893168461351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188396247749285048449230269 70648592905981893168461351)
      ·
        refine ⟨105972889358972839752692027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70648592905981893168461351 105972889358972839752692027)
        ·
          refine ⟨158959334038459259629038041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105972889358972839752692027 158959334038459259629038041)
          ·
            refine ⟨119219500528844444721778531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158959334038459259629038041 119219500528844444721778531)
            ·
              refine ⟨178829250793266667082667797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119219500528844444721778531 178829250793266667082667797)
              ·
                refine ⟨8382621130934375019500053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178829250793266667082667797 8382621130934375019500053)
                ·
                  refine ⟨392935365512548829039065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8382621130934375019500053 392935365512548829039065)
                  ·
                    rfl

theorem cell22_3443575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 6].length) (baseStart_3443575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443575 prefixEnd_3443575 := by exact prefixLift 3443575
  have htrace : WordTrace (prefixWord ++ tailWord_3443575) baseStart_3443575 baseEnd_3443575 := by
    simpa [prefixWord, tailWord_3443575, baseEnd_3443575] using wordTrace_append hprefix tailTrace_3443575
  have hstable : (prefixWord ++ tailWord_3443575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443575).length < 2 ^ (prefixWord ++ tailWord_3443575).sum := by decide
  have hdescent : baseEnd_3443575 < baseStart_3443575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443577 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_3443577 : Nat := 118140960795 + 3443577 * 2 ^ 59
def prefixEnd_3443577 : Nat := 4983230072969 + 3 ^ 40 * 3443577 * 2
def baseEnd_3443577 : Nat := 1178806781178519148567189

theorem tailTrace_3443577 : CollatzResearch.WordTrace tailWord_3443577 prefixEnd_3443577 1178806781178519148567189 := by
  unfold tailWord_3443577
  simp only [CollatzResearch.WordTrace]
  refine ⟨125597571445516119974392985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83731714297010746649595323 125597571445516119974392985)
  ·
    refine ⟨94198178584137089980794739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125597571445516119974392985 94198178584137089980794739)
    ·
      refine ⟨141297267876205634971192109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94198178584137089980794739 141297267876205634971192109)
      ·
        refine ⟨52986475453577113114197041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141297267876205634971192109 52986475453577113114197041)
        ·
          refine ⟨39739856590182834835647781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52986475453577113114197041 39739856590182834835647781)
          ·
            refine ⟨7451223110659281531683959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39739856590182834835647781 7451223110659281531683959)
            ·
              refine ⟨11176834665988922297525939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7451223110659281531683959 11176834665988922297525939)
              ·
                refine ⟨16765251998983383446288909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176834665988922297525939 16765251998983383446288909)
                ·
                  refine ⟨6286969499618768792358341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16765251998983383446288909 6286969499618768792358341)
                  ·
                    refine ⟨1178806781178519148567189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6286969499618768792358341 1178806781178519148567189)
                    ·
                      rfl

theorem cell22_3443577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_3443577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443577 prefixEnd_3443577 := by exact prefixLift 3443577
  have htrace : WordTrace (prefixWord ++ tailWord_3443577) baseStart_3443577 baseEnd_3443577 := by
    simpa [prefixWord, tailWord_3443577, baseEnd_3443577] using wordTrace_append hprefix tailTrace_3443577
  have hstable : (prefixWord ++ tailWord_3443577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443577).length < 2 ^ (prefixWord ++ tailWord_3443577).sum := by decide
  have hdescent : baseEnd_3443577 < baseStart_3443577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443602 : List Nat := [3, 2, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3443602 : Nat := 118140960795 + 3443602 * 2 ^ 59
def prefixEnd_3443602 : Nat := 4983230072969 + 3 ^ 40 * 3443602 * 2
def baseEnd_3443602 : Nat := 1178815339189427416692113

theorem tailTrace_3443602 : CollatzResearch.WordTrace tailWord_3443602 prefixEnd_3443602 1178815339189427416692113 := by
  unfold tailWord_3443602
  simp only [CollatzResearch.WordTrace]
  refine ⟨31399620817606387311013265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83732322180283699496035373 31399620817606387311013265)
  ·
    refine ⟨23549715613204790483259949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31399620817606387311013265 23549715613204790483259949)
    ·
      refine ⟨8831143354951796431222481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23549715613204790483259949 8831143354951796431222481)
      ·
        refine ⟨6623357516213847323416861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8831143354951796431222481 6623357516213847323416861)
        ·
          refine ⟨2483759068580192746281323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6623357516213847323416861 2483759068580192746281323)
          ·
            refine ⟨3725638602870289119421985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483759068580192746281323 3725638602870289119421985)
            ·
              refine ⟨2794228952152716839566489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3725638602870289119421985 2794228952152716839566489)
              ·
                refine ⟨2095671714114537629674867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2794228952152716839566489 2095671714114537629674867)
                ·
                  refine ⟨3143507571171806444512301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095671714114537629674867 3143507571171806444512301)
                  ·
                    refine ⟨1178815339189427416692113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3143507571171806444512301 1178815339189427416692113)
                    ·
                      rfl

theorem cell22_3443602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3443602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443602 prefixEnd_3443602 := by exact prefixLift 3443602
  have htrace : WordTrace (prefixWord ++ tailWord_3443602) baseStart_3443602 baseEnd_3443602 := by
    simpa [prefixWord, tailWord_3443602, baseEnd_3443602] using wordTrace_append hprefix tailTrace_3443602
  have hstable : (prefixWord ++ tailWord_3443602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443602).length < 2 ^ (prefixWord ++ tailWord_3443602).sum := by decide
  have hdescent : baseEnd_3443602 < baseStart_3443602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443635 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 9]
def baseStart_3443635 : Nat := 118140960795 + 3443635 * 2 ^ 59
def prefixEnd_3443635 : Nat := 4983230072969 + 3 ^ 40 * 3443635 * 2
def baseEnd_3443635 : Nat := 1178826635763826330617011

theorem tailTrace_3443635 : CollatzResearch.WordTrace tailWord_3443635 prefixEnd_3443635 1178826635763826330617011 := by
  unfold tailWord_3443635
  simp only [CollatzResearch.WordTrace]
  refine ⟨125599686879305995880004359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83733124586203997253336239 125599686879305995880004359)
  ·
    refine ⟨188399530318958993820006539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125599686879305995880004359 188399530318958993820006539)
    ·
      refine ⟨282599295478438490730009809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188399530318958993820006539 282599295478438490730009809)
      ·
        refine ⟨211949471608828868047507357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282599295478438490730009809 211949471608828868047507357)
        ·
          refine ⟨79481051853310825517815259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211949471608828868047507357 79481051853310825517815259)
          ·
            refine ⟨119221577779966238276722889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79481051853310825517815259 119221577779966238276722889)
            ·
              refine ⟨89416183334974678707542167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119221577779966238276722889 89416183334974678707542167)
              ·
                refine ⟨134124275002462018061313251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89416183334974678707542167 134124275002462018061313251)
                ·
                  refine ⟨201186412503693027091969877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134124275002462018061313251 201186412503693027091969877)
                  ·
                    refine ⟨1178826635763826330617011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 201186412503693027091969877 1178826635763826330617011)
                    ·
                      rfl

theorem cell22_3443635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_3443635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443635 prefixEnd_3443635 := by exact prefixLift 3443635
  have htrace : WordTrace (prefixWord ++ tailWord_3443635) baseStart_3443635 baseEnd_3443635 := by
    simpa [prefixWord, tailWord_3443635, baseEnd_3443635] using wordTrace_append hprefix tailTrace_3443635
  have hstable : (prefixWord ++ tailWord_3443635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443635).length < 2 ^ (prefixWord ++ tailWord_3443635).sum := by decide
  have hdescent : baseEnd_3443635 < baseStart_3443635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443746 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3443746 : Nat := 118140960795 + 3443746 * 2 ^ 59
def prefixEnd_3443746 : Nat := 4983230072969 + 3 ^ 40 * 3443746 * 2
def baseEnd_3443746 : Nat := 1178864633332259041091671

theorem tailTrace_3443746 : CollatzResearch.WordTrace tailWord_3443746 prefixEnd_3443746 1178864633332259041091671 := by
  unfold tailWord_3443746
  simp only [CollatzResearch.WordTrace]
  refine ⟨31400933845475965459323773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83735823587935907891530061 31400933845475965459323773)
  ·
    refine ⟨11775350192053487047246415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31400933845475965459323773 11775350192053487047246415)
    ·
      refine ⟨17663025288080230570869623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11775350192053487047246415 17663025288080230570869623)
      ·
        refine ⟨26494537932120345856304435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17663025288080230570869623 26494537932120345856304435)
        ·
          refine ⟨39741806898180518784456653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26494537932120345856304435 39741806898180518784456653)
          ·
            refine ⟨14903177586817694544171245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39741806898180518784456653 14903177586817694544171245)
            ·
              refine ⟨5588691595056635454064217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14903177586817694544171245 5588691595056635454064217)
              ·
                refine ⟨4191518696292476590548163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5588691595056635454064217 4191518696292476590548163)
                ·
                  refine ⟨6287278044438714885822245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191518696292476590548163 6287278044438714885822245)
                  ·
                    refine ⟨1178864633332259041091671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6287278044438714885822245 1178864633332259041091671)
                    ·
                      rfl

theorem cell22_3443746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3443746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443746 prefixEnd_3443746 := by exact prefixLift 3443746
  have htrace : WordTrace (prefixWord ++ tailWord_3443746) baseStart_3443746 baseEnd_3443746 := by
    simpa [prefixWord, tailWord_3443746, baseEnd_3443746] using wordTrace_append hprefix tailTrace_3443746
  have hstable : (prefixWord ++ tailWord_3443746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443746).length < 2 ^ (prefixWord ++ tailWord_3443746).sum := by decide
  have hdescent : baseEnd_3443746 < baseStart_3443746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443772 : List Nat := [2, 2, 2, 2, 2, 12]
def baseStart_3443772 : Nat := 118140960795 + 3443772 * 2 ^ 59
def prefixEnd_3443772 : Nat := 4983230072969 + 3 ^ 40 * 3443772 * 2
def baseEnd_3443772 : Nat := 14553994242760538764711

theorem tailTrace_3443772 : CollatzResearch.WordTrace tailWord_3443772 prefixEnd_3443772 14553994242760538764711 := by
  unfold tailWord_3443772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62802341839904834138870785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83736455786539778851827713 62802341839904834138870785)
  ·
    refine ⟨47101756379928625604153089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62802341839904834138870785 47101756379928625604153089)
    ·
      refine ⟨35326317284946469203114817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47101756379928625604153089 35326317284946469203114817)
      ·
        refine ⟨26494737963709851902336113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35326317284946469203114817 26494737963709851902336113)
        ·
          refine ⟨19871053472782388926752085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26494737963709851902336113 19871053472782388926752085)
          ·
            refine ⟨14553994242760538764711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19871053472782388926752085 14553994242760538764711)
            ·
              rfl

theorem cell22_3443772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 12].length) (baseStart_3443772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443772 prefixEnd_3443772 := by exact prefixLift 3443772
  have htrace : WordTrace (prefixWord ++ tailWord_3443772) baseStart_3443772 baseEnd_3443772 := by
    simpa [prefixWord, tailWord_3443772, baseEnd_3443772] using wordTrace_append hprefix tailTrace_3443772
  have hstable : (prefixWord ++ tailWord_3443772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443772).length < 2 ^ (prefixWord ++ tailWord_3443772).sum := by decide
  have hdescent : baseEnd_3443772 < baseStart_3443772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443776 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 2, 3]
def baseStart_3443776 : Nat := 118140960795 + 3443776 * 2 ^ 59
def prefixEnd_3443776 : Nat := 4983230072969 + 3 ^ 40 * 3443776 * 2
def baseEnd_3443776 : Nat := 1178874902945348962841579

theorem tailTrace_3443776 : CollatzResearch.WordTrace tailWord_3443776 prefixEnd_3443776 1178874902945348962841579 := by
  unfold tailWord_3443776
  simp only [CollatzResearch.WordTrace]
  refine ⟨62802414785897588480443591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83736553047863451307258121 62802414785897588480443591)
  ·
    refine ⟨94203622178846382720665387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62802414785897588480443591 94203622178846382720665387)
    ·
      refine ⟨141305433268269574080998081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94203622178846382720665387 141305433268269574080998081)
      ·
        refine ⟨105979074951202180560748561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141305433268269574080998081 105979074951202180560748561)
        ·
          refine ⟨79484306213401635420561421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105979074951202180560748561 79484306213401635420561421)
          ·
            refine ⟨29806614830025613282710533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79484306213401635420561421 29806614830025613282710533)
            ·
              refine ⟨5588740280629802490508225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29806614830025613282710533 5588740280629802490508225)
              ·
                refine ⟨4191555210472351867881169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5588740280629802490508225 4191555210472351867881169)
                ·
                  refine ⟨3143666407854263900910877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4191555210472351867881169 3143666407854263900910877)
                  ·
                    refine ⟨1178874902945348962841579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3143666407854263900910877 1178874902945348962841579)
                    ·
                      rfl

theorem cell22_3443776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_3443776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443776 prefixEnd_3443776 := by exact prefixLift 3443776
  have htrace : WordTrace (prefixWord ++ tailWord_3443776) baseStart_3443776 baseEnd_3443776 := by
    simpa [prefixWord, tailWord_3443776, baseEnd_3443776] using wordTrace_append hprefix tailTrace_3443776
  have hstable : (prefixWord ++ tailWord_3443776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443776).length < 2 ^ (prefixWord ++ tailWord_3443776).sum := by decide
  have hdescent : baseEnd_3443776 < baseStart_3443776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443849 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_3443849 : Nat := 118140960795 + 3443849 * 2 ^ 59
def prefixEnd_3443849 : Nat := 4983230072969 + 3 ^ 40 * 3443849 * 2
def baseEnd_3443849 : Nat := 1178899892337201105766355

theorem tailTrace_3443849 : CollatzResearch.WordTrace tailWord_3443849 prefixEnd_3443849 1178899892337201105766355 := by
  unfold tailWord_3443849
  simp only [CollatzResearch.WordTrace]
  refine ⟨125607492100530710428294601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83738328067020473618863067 125607492100530710428294601)
  ·
    refine ⟨94205619075398032821220951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125607492100530710428294601 94205619075398032821220951)
    ·
      refine ⟨141308428613097049231831427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94205619075398032821220951 141308428613097049231831427)
      ·
        refine ⟨211962642919645573847747141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141308428613097049231831427 211962642919645573847747141)
        ·
          refine ⟨39742995547433545096452589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211962642919645573847747141 39742995547433545096452589)
          ·
            refine ⟨14903623330287579411169721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39742995547433545096452589 14903623330287579411169721)
            ·
              refine ⟨11177717497715684558377291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14903623330287579411169721 11177717497715684558377291)
              ·
                refine ⟨16766576246573526837565937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11177717497715684558377291 16766576246573526837565937)
                ·
                  refine ⟨12574932184930145128174453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16766576246573526837565937 12574932184930145128174453)
                  ·
                    refine ⟨1178899892337201105766355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12574932184930145128174453 1178899892337201105766355)
                    ·
                      rfl

theorem cell22_3443849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_3443849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443849 prefixEnd_3443849 := by exact prefixLift 3443849
  have htrace : WordTrace (prefixWord ++ tailWord_3443849) baseStart_3443849 baseEnd_3443849 := by
    simpa [prefixWord, tailWord_3443849, baseEnd_3443849] using wordTrace_append hprefix tailTrace_3443849
  have hstable : (prefixWord ++ tailWord_3443849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443849).length < 2 ^ (prefixWord ++ tailWord_3443849).sum := by decide
  have hdescent : baseEnd_3443849 < baseStart_3443849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443909 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_3443909 : Nat := 118140960795 + 3443909 * 2 ^ 59
def prefixEnd_3443909 : Nat := 4983230072969 + 3 ^ 40 * 3443909 * 2
def baseEnd_3443909 : Nat := 1178920431563380949266171

theorem tailTrace_3443909 : CollatzResearch.WordTrace tailWord_3443909 prefixEnd_3443909 1178920431563380949266171 := by
  unfold tailWord_3443909
  simp only [CollatzResearch.WordTrace]
  refine ⟨125609680480313340675478781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83739786986875560450319187 125609680480313340675478781)
  ·
    refine ⟨47103630180117502753304543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125609680480313340675478781 47103630180117502753304543)
    ·
      refine ⟨70655445270176254129956815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47103630180117502753304543 70655445270176254129956815)
      ·
        refine ⟨105983167905264381194935223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70655445270176254129956815 105983167905264381194935223)
        ·
          refine ⟨158974751857896571792402835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105983167905264381194935223 158974751857896571792402835)
          ·
            refine ⟨238462127786844857688604253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158974751857896571792402835 238462127786844857688604253)
            ·
              refine ⟨89423297920066821633226595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238462127786844857688604253 89423297920066821633226595)
              ·
                refine ⟨134134946880100232449839893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89423297920066821633226595 134134946880100232449839893)
                ·
                  refine ⟨6287575635004698396086245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134134946880100232449839893 6287575635004698396086245)
                  ·
                    refine ⟨1178920431563380949266171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6287575635004698396086245 1178920431563380949266171)
                    ·
                      rfl

theorem cell22_3443909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_3443909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443909 prefixEnd_3443909 := by exact prefixLift 3443909
  have htrace : WordTrace (prefixWord ++ tailWord_3443909) baseStart_3443909 baseEnd_3443909 := by
    simpa [prefixWord, tailWord_3443909, baseEnd_3443909] using wordTrace_append hprefix tailTrace_3443909
  have hstable : (prefixWord ++ tailWord_3443909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443909).length < 2 ^ (prefixWord ++ tailWord_3443909).sum := by decide
  have hdescent : baseEnd_3443909 < baseStart_3443909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3443941 : List Nat := [1, 3, 1, 4, 4, 9]
def baseStart_3443941 : Nat := 118140960795 + 3443941 * 2 ^ 59
def prefixEnd_3443941 : Nat := 4983230072969 + 3 ^ 40 * 3443941 * 2
def baseEnd_3443941 : Nat := 14554708466880784351433

theorem tailTrace_3443941 : CollatzResearch.WordTrace tailWord_3443941 prefixEnd_3443941 14554708466880784351433 := by
  unfold tailWord_3443941
  simp only [CollatzResearch.WordTrace]
  refine ⟨125610847616197410140643677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83740565077464940093762451 125610847616197410140643677)
  ·
    refine ⟨47104067856074028802741379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125610847616197410140643677 47104067856074028802741379)
    ·
      refine ⟨70656101784111043204112069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47104067856074028802741379 70656101784111043204112069)
      ·
        refine ⟨13248019084520820600771013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70656101784111043204112069 13248019084520820600771013)
        ·
          refine ⟨2484003578347653862644565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13248019084520820600771013 2484003578347653862644565)
          ·
            refine ⟨14554708466880784351433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2484003578347653862644565 14554708466880784351433)
            ·
              rfl

theorem cell22_3443941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 9].length) (baseStart_3443941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3443941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3443941 prefixEnd_3443941 := by exact prefixLift 3443941
  have htrace : WordTrace (prefixWord ++ tailWord_3443941) baseStart_3443941 baseEnd_3443941 := by
    simpa [prefixWord, tailWord_3443941, baseEnd_3443941] using wordTrace_append hprefix tailTrace_3443941
  have hstable : (prefixWord ++ tailWord_3443941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3443941).length < 2 ^ (prefixWord ++ tailWord_3443941).sum := by decide
  have hdescent : baseEnd_3443941 < baseStart_3443941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3443941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444003 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 5]
def baseStart_3444003 : Nat := 118140960795 + 3444003 * 2 ^ 59
def prefixEnd_3444003 : Nat := 4983230072969 + 3 ^ 40 * 3444003 * 2
def baseEnd_3444003 : Nat := 392984203228132012471961

theorem tailTrace_3444003 : CollatzResearch.WordTrace tailWord_3444003 prefixEnd_3444003 392984203228132012471961 := by
  unfold tailWord_3444003
  simp only [CollatzResearch.WordTrace]
  refine ⟨125613108941972794729400663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83742072627981863152933775 125613108941972794729400663)
  ·
    refine ⟨188419663412959192094100995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125613108941972794729400663 188419663412959192094100995)
    ·
      refine ⟨282629495119438788141151493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188419663412959192094100995 282629495119438788141151493)
      ·
        refine ⟨52993030334894772776465905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282629495119438788141151493 52993030334894772776465905)
        ·
          refine ⟨39744772751171079582349429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52993030334894772776465905 39744772751171079582349429)
          ·
            refine ⟨3726072445422288710845259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39744772751171079582349429 3726072445422288710845259)
            ·
              refine ⟨5589108668133433066267889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726072445422288710845259 5589108668133433066267889)
              ·
                refine ⟨4191831501100074799700917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589108668133433066267889 4191831501100074799700917)
                ·
                  refine ⟨392984203228132012471961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4191831501100074799700917 392984203228132012471961)
                  ·
                    rfl

theorem cell22_3444003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 5].length) (baseStart_3444003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444003 prefixEnd_3444003 := by exact prefixLift 3444003
  have htrace : WordTrace (prefixWord ++ tailWord_3444003) baseStart_3444003 baseEnd_3444003 := by
    simpa [prefixWord, tailWord_3444003, baseEnd_3444003] using wordTrace_append hprefix tailTrace_3444003
  have hstable : (prefixWord ++ tailWord_3444003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444003).length < 2 ^ (prefixWord ++ tailWord_3444003).sum := by decide
  have hdescent : baseEnd_3444003 < baseStart_3444003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444020 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3444020 : Nat := 118140960795 + 3444020 * 2 ^ 59
def prefixEnd_3444020 : Nat := 4983230072969 + 3 ^ 40 * 3444020 * 2
def baseEnd_3444020 : Nat := 392986143043937886580277

theorem tailTrace_3444020 : CollatzResearch.WordTrace tailWord_3444020 prefixEnd_3444020 392986143043937886580277 := by
  unfold tailWord_3444020
  simp only [CollatzResearch.WordTrace]
  refine ⟨62806864491455603316384757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83742485988607471088513009 62806864491455603316384757)
  ·
    refine ⟨5888143546073962810911071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62806864491455603316384757 5888143546073962810911071)
    ·
      refine ⟨8832215319110944216366607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5888143546073962810911071 8832215319110944216366607)
      ·
        refine ⟨13248322978666416324549911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8832215319110944216366607 13248322978666416324549911)
        ·
          refine ⟨19872484467999624486824867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248322978666416324549911 19872484467999624486824867)
          ·
            refine ⟨29808726701999436730237301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19872484467999624486824867 29808726701999436730237301)
            ·
              refine ⟨2794568128312447193459747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29808726701999436730237301 2794568128312447193459747)
              ·
                refine ⟨4191852192468670790189621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794568128312447193459747 4191852192468670790189621)
                ·
                  refine ⟨392986143043937886580277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4191852192468670790189621 392986143043937886580277)
                  ·
                    rfl

theorem cell22_3444020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3444020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444020 prefixEnd_3444020 := by exact prefixLift 3444020
  have htrace : WordTrace (prefixWord ++ tailWord_3444020) baseStart_3444020 baseEnd_3444020 := by
    simpa [prefixWord, tailWord_3444020, baseEnd_3444020] using wordTrace_append hprefix tailTrace_3444020
  have hstable : (prefixWord ++ tailWord_3444020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444020).length < 2 ^ (prefixWord ++ tailWord_3444020).sum := by decide
  have hdescent : baseEnd_3444020 < baseStart_3444020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444031 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 6]
def baseStart_3444031 : Nat := 118140960795 + 3444031 * 2 ^ 59
def prefixEnd_3444031 : Nat := 4983230072969 + 3 ^ 40 * 3444031 * 2
def baseEnd_3444031 : Nat := 392987398218871099238599

theorem tailTrace_3444031 : CollatzResearch.WordTrace tailWord_3444031 prefixEnd_3444031 392987398218871099238599 := by
  unfold tailWord_3444031
  simp only [CollatzResearch.WordTrace]
  refine ⟨125614130185871355511419947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83742753457247570340946631 125614130185871355511419947)
  ·
    refine ⟨188421195278807033267129921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125614130185871355511419947 188421195278807033267129921)
    ·
      refine ⟨141315896459105274950347441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188421195278807033267129921 141315896459105274950347441)
      ·
        refine ⟨105986922344328956212760581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141315896459105274950347441 105986922344328956212760581)
        ·
          refine ⟨19872547939561679289892609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105986922344328956212760581 19872547939561679289892609)
          ·
            refine ⟨14904410954671259467419457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19872547939561679289892609 14904410954671259467419457)
            ·
              refine ⟨11178308216003444600564593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14904410954671259467419457 11178308216003444600564593)
              ·
                refine ⟨8383731162002583450423445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11178308216003444600564593 8383731162002583450423445)
                ·
                  refine ⟨392987398218871099238599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8383731162002583450423445 392987398218871099238599)
                  ·
                    rfl

theorem cell22_3444031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 6].length) (baseStart_3444031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444031 prefixEnd_3444031 := by exact prefixLift 3444031
  have htrace : WordTrace (prefixWord ++ tailWord_3444031) baseStart_3444031 baseEnd_3444031 := by
    simpa [prefixWord, tailWord_3444031, baseEnd_3444031] using wordTrace_append hprefix tailTrace_3444031
  have hstable : (prefixWord ++ tailWord_3444031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444031).length < 2 ^ (prefixWord ++ tailWord_3444031).sum := by decide
  have hdescent : baseEnd_3444031 < baseStart_3444031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444046 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3444046 : Nat := 118140960795 + 3444046 * 2 ^ 59
def prefixEnd_3444046 : Nat := 4983230072969 + 3 ^ 40 * 3444046 * 2
def baseEnd_3444046 : Nat := 1178967329463158258590751

theorem tailTrace_3444046 : CollatzResearch.WordTrace tailWord_3444046 prefixEnd_3444046 1178967329463158258590751 := by
  unfold tailWord_3444046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15701834660102126634151999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83743118187211342048810661 15701834660102126634151999)
  ·
    refine ⟨23552751990153189951227999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15701834660102126634151999 23552751990153189951227999)
    ·
      refine ⟨35329127985229784926841999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23552751990153189951227999 35329127985229784926841999)
      ·
        refine ⟨52993691977844677390262999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35329127985229784926841999 52993691977844677390262999)
        ·
          refine ⟨79490537966767016085394499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52993691977844677390262999 79490537966767016085394499)
          ·
            refine ⟨119235806950150524128091749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79490537966767016085394499 119235806950150524128091749)
            ·
              refine ⟨22356713803153223274017203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119235806950150524128091749 22356713803153223274017203)
              ·
                refine ⟨33535070704729834911025805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22356713803153223274017203 33535070704729834911025805)
                ·
                  refine ⟨12575651514273688091634677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33535070704729834911025805 12575651514273688091634677)
                  ·
                    refine ⟨1178967329463158258590751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12575651514273688091634677 1178967329463158258590751)
                    ·
                      rfl

theorem cell22_3444046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3444046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444046 prefixEnd_3444046 := by exact prefixLift 3444046
  have htrace : WordTrace (prefixWord ++ tailWord_3444046) baseStart_3444046 baseEnd_3444046 := by
    simpa [prefixWord, tailWord_3444046, baseEnd_3444046] using wordTrace_append hprefix tailTrace_3444046
  have hstable : (prefixWord ++ tailWord_3444046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444046).length < 2 ^ (prefixWord ++ tailWord_3444046).sum := by decide
  have hdescent : baseEnd_3444046 < baseStart_3444046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444063 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 2, 3]
def baseStart_3444063 : Nat := 118140960795 + 3444063 * 2 ^ 59
def prefixEnd_3444063 : Nat := 4983230072969 + 3 ^ 40 * 3444063 * 2
def baseEnd_3444063 : Nat := 1178973148910575880915699

theorem tailTrace_3444063 : CollatzResearch.WordTrace tailWord_3444063 prefixEnd_3444063 1178973148910575880915699 := by
  unfold tailWord_3444063
  simp only [CollatzResearch.WordTrace]
  refine ⟨125615297321755424976584843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83743531547836949984389895 125615297321755424976584843)
  ·
    refine ⟨188422945982633137464877265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125615297321755424976584843 188422945982633137464877265)
    ·
      refine ⟨141317209486974853098657949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188422945982633137464877265 141317209486974853098657949)
      ·
        refine ⟨52993953557615569911996731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141317209486974853098657949 52993953557615569911996731)
        ·
          refine ⟨79490930336423354867995097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52993953557615569911996731 79490930336423354867995097)
          ·
            refine ⟨59618197752317516150996323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79490930336423354867995097 59618197752317516150996323)
            ·
              refine ⟨89427296628476274226494485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59618197752317516150996323 89427296628476274226494485)
              ·
                refine ⟨4191904529459825354366929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89427296628476274226494485 4191904529459825354366929)
                ·
                  refine ⟨3143928397094869015775197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4191904529459825354366929 3143928397094869015775197)
                  ·
                    refine ⟨1178973148910575880915699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3143928397094869015775197 1178973148910575880915699)
                    ·
                      rfl

theorem cell22_3444063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_3444063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444063 prefixEnd_3444063 := by exact prefixLift 3444063
  have htrace : WordTrace (prefixWord ++ tailWord_3444063) baseStart_3444063 baseEnd_3444063 := by
    simpa [prefixWord, tailWord_3444063, baseEnd_3444063] using wordTrace_append hprefix tailTrace_3444063
  have hstable : (prefixWord ++ tailWord_3444063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444063).length < 2 ^ (prefixWord ++ tailWord_3444063).sum := by decide
  have hdescent : baseEnd_3444063 < baseStart_3444063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444076 : List Nat := [2, 2, 1, 1, 5, 1, 1, 9]
def baseStart_3444076 : Nat := 118140960795 + 3444076 * 2 ^ 59
def prefixEnd_3444076 : Nat := 4983230072969 + 3 ^ 40 * 3444076 * 2
def baseEnd_3444076 : Nat := 130997511008472020037851

theorem tailTrace_3444076 : CollatzResearch.WordTrace tailWord_3444076 prefixEnd_3444076 130997511008472020037851 := by
  unfold tailWord_3444076
  simp only [CollatzResearch.WordTrace]
  refine ⟨62807885735354164098404041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83743847647138885464538721 62807885735354164098404041)
  ·
    refine ⟨47105914301515623073803031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62807885735354164098404041 47105914301515623073803031)
    ·
      refine ⟨70658871452273434610704547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47105914301515623073803031 70658871452273434610704547)
      ·
        refine ⟨105988307178410151916056821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70658871452273434610704547 105988307178410151916056821)
        ·
          refine ⟨9936403797975951742130327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105988307178410151916056821 9936403797975951742130327)
          ·
            refine ⟨14904605696963927613195491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9936403797975951742130327 14904605696963927613195491)
            ·
              refine ⟨22356908545445891419793237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14904605696963927613195491 22356908545445891419793237)
              ·
                refine ⟨130997511008472020037851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22356908545445891419793237 130997511008472020037851)
                ·
                  rfl

theorem cell22_3444076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 9].length) (baseStart_3444076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444076 prefixEnd_3444076 := by exact prefixLift 3444076
  have htrace : WordTrace (prefixWord ++ tailWord_3444076) baseStart_3444076 baseEnd_3444076 := by
    simpa [prefixWord, tailWord_3444076, baseEnd_3444076] using wordTrace_append hprefix tailTrace_3444076
  have hstable : (prefixWord ++ tailWord_3444076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444076).length < 2 ^ (prefixWord ++ tailWord_3444076).sum := by decide
  have hdescent : baseEnd_3444076 < baseStart_3444076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444114 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3444114 : Nat := 118140960795 + 3444114 * 2 ^ 59
def prefixEnd_3444114 : Nat := 4983230072969 + 3 ^ 40 * 3444114 * 2
def baseEnd_3444114 : Nat := 1178990607252828747890543

theorem tailTrace_3444114 : CollatzResearch.WordTrace tailWord_3444114 prefixEnd_3444114 1178990607252828747890543 := by
  unfold tailWord_3444114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31404289361142665171672849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83744771629713773791127597 31404289361142665171672849)
  ·
    refine ⟨23553217020856998878754637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31404289361142665171672849 23553217020856998878754637)
    ·
      refine ⟨8832456382821374579532989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23553217020856998878754637 8832456382821374579532989)
      ·
        refine ⟨3312171143558015467324871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8832456382821374579532989 3312171143558015467324871)
        ·
          refine ⟨4968256715337023200987307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312171143558015467324871 4968256715337023200987307)
          ·
            refine ⟨7452385073005534801480961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968256715337023200987307 7452385073005534801480961)
            ·
              refine ⟨5589288804754151101110721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452385073005534801480961 5589288804754151101110721)
              ·
                refine ⟨4191966603565613325833041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589288804754151101110721 4191966603565613325833041)
                ·
                  refine ⟨3143974952674209994374781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4191966603565613325833041 3143974952674209994374781)
                  ·
                    refine ⟨1178990607252828747890543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3143974952674209994374781 1178990607252828747890543)
                    ·
                      rfl

theorem cell22_3444114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3444114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444114 prefixEnd_3444114 := by exact prefixLift 3444114
  have htrace : WordTrace (prefixWord ++ tailWord_3444114) baseStart_3444114 baseEnd_3444114 := by
    simpa [prefixWord, tailWord_3444114, baseEnd_3444114] using wordTrace_append hprefix tailTrace_3444114
  have hstable : (prefixWord ++ tailWord_3444114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444114).length < 2 ^ (prefixWord ++ tailWord_3444114).sum := by decide
  have hdescent : baseEnd_3444114 < baseStart_3444114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444202 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_3444202 : Nat := 118140960795 + 3444202 * 2 ^ 59
def prefixEnd_3444202 : Nat := 4983230072969 + 3 ^ 40 * 3444202 * 2
def baseEnd_3444202 : Nat := 1179020731451225851690273

theorem tailTrace_3444202 : CollatzResearch.WordTrace tailWord_3444202 prefixEnd_3444202 1179020731451225851690273 := by
  unfold tailWord_3444202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31405091767062962928973715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83746911378834567810596573 31405091767062962928973715)
  ·
    refine ⟨47107637650594444393460573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31405091767062962928973715 47107637650594444393460573)
    ·
      refine ⟨17665364118972916647547715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47107637650594444393460573 17665364118972916647547715)
      ·
        refine ⟨26498046178459374971321573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17665364118972916647547715 26498046178459374971321573)
        ·
          refine ⟨4968383658461132807122795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26498046178459374971321573 4968383658461132807122795)
          ·
            refine ⟨7452575487691699210684193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968383658461132807122795 7452575487691699210684193)
            ·
              refine ⟨5589431615768774408013145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452575487691699210684193 5589431615768774408013145)
              ·
                refine ⟨4192073711826580806009859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589431615768774408013145 4192073711826580806009859)
                ·
                  refine ⟨6288110567739871209014789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192073711826580806009859 6288110567739871209014789)
                  ·
                    refine ⟨1179020731451225851690273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288110567739871209014789 1179020731451225851690273)
                    ·
                      rfl

theorem cell22_3444202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_3444202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444202 prefixEnd_3444202 := by exact prefixLift 3444202
  have htrace : WordTrace (prefixWord ++ tailWord_3444202) baseStart_3444202 baseEnd_3444202 := by
    simpa [prefixWord, tailWord_3444202, baseEnd_3444202] using wordTrace_append hprefix tailTrace_3444202
  have hstable : (prefixWord ++ tailWord_3444202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444202).length < 2 ^ (prefixWord ++ tailWord_3444202).sum := by decide
  have hdescent : baseEnd_3444202 < baseStart_3444202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444288 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_3444288 : Nat := 118140960795 + 3444288 * 2 ^ 59
def prefixEnd_3444288 : Nat := 4983230072969 + 3 ^ 40 * 3444288 * 2
def baseEnd_3444288 : Nat := 1179050171008750294040009

theorem tailTrace_3444288 : CollatzResearch.WordTrace tailWord_3444288 prefixEnd_3444288 1179050171008750294040009 := by
  unfold tailWord_3444288
  simp only [CollatzResearch.WordTrace]
  refine ⟨62811751872970144201762759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83749002497293525602350345 62811751872970144201762759)
  ·
    refine ⟨94217627809455216302644139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62811751872970144201762759 94217627809455216302644139)
    ·
      refine ⟨141326441714182824453966209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94217627809455216302644139 141326441714182824453966209)
      ·
        refine ⟨105994831285637118340474657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141326441714182824453966209 105994831285637118340474657)
        ·
          refine ⟨79496123464227838755355993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105994831285637118340474657 79496123464227838755355993)
          ·
            refine ⟨59622092598170879066516995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79496123464227838755355993 59622092598170879066516995)
            ·
              refine ⟨89433138897256318599775493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59622092598170879066516995 89433138897256318599775493)
              ·
                refine ⟨16768713543235559737457905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89433138897256318599775493 16768713543235559737457905)
                ·
                  refine ⟨12576535157426669803093429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16768713543235559737457905 12576535157426669803093429)
                  ·
                    refine ⟨1179050171008750294040009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12576535157426669803093429 1179050171008750294040009)
                    ·
                      rfl

theorem cell22_3444288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_3444288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444288 prefixEnd_3444288 := by exact prefixLift 3444288
  have htrace : WordTrace (prefixWord ++ tailWord_3444288) baseStart_3444288 baseEnd_3444288 := by
    simpa [prefixWord, tailWord_3444288, baseEnd_3444288] using wordTrace_append hprefix tailTrace_3444288
  have hstable : (prefixWord ++ tailWord_3444288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444288).length < 2 ^ (prefixWord ++ tailWord_3444288).sum := by decide
  have hdescent : baseEnd_3444288 < baseStart_3444288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444320 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_3444320 : Nat := 118140960795 + 3444320 * 2 ^ 59
def prefixEnd_3444320 : Nat := 4983230072969 + 3 ^ 40 * 3444320 * 2
def baseEnd_3444320 : Nat := 1179061125262712877239911

theorem tailTrace_3444320 : CollatzResearch.WordTrace tailWord_3444320 prefixEnd_3444320 1179061125262712877239911 := by
  unfold tailWord_3444320
  simp only [CollatzResearch.WordTrace]
  refine ⟨62812335440912178934345207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83749780587882905245793609 62812335440912178934345207)
  ·
    refine ⟨94218503161368268401517811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62812335440912178934345207 94218503161368268401517811)
    ·
      refine ⟨141327754742052402602276717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94218503161368268401517811 141327754742052402602276717)
      ·
        refine ⟨52997908028269650975853769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141327754742052402602276717 52997908028269650975853769)
        ·
          refine ⟨39748431021202238231890327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52997908028269650975853769 39748431021202238231890327)
          ·
            refine ⟨59622646531803357347835491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39748431021202238231890327 59622646531803357347835491)
            ·
              refine ⟨89433969797705036021753237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59622646531803357347835491 89433969797705036021753237)
              ·
                refine ⟨4192217334267423563519683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89433969797705036021753237 4192217334267423563519683)
                ·
                  refine ⟨6288326001401135345279525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192217334267423563519683 6288326001401135345279525)
                  ·
                    refine ⟨1179061125262712877239911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288326001401135345279525 1179061125262712877239911)
                    ·
                      rfl

theorem cell22_3444320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_3444320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444320 prefixEnd_3444320 := by exact prefixLift 3444320
  have htrace : WordTrace (prefixWord ++ tailWord_3444320) baseStart_3444320 baseEnd_3444320 := by
    simpa [prefixWord, tailWord_3444320, baseEnd_3444320] using wordTrace_append hprefix tailTrace_3444320
  have hstable : (prefixWord ++ tailWord_3444320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444320).length < 2 ^ (prefixWord ++ tailWord_3444320).sum := by decide
  have hdescent : baseEnd_3444320 < baseStart_3444320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444363 : List Nat := [1, 1, 1, 1, 4, 1, 4, 9]
def baseStart_3444363 : Nat := 118140960795 + 3444363 * 2 ^ 59
def prefixEnd_3444363 : Nat := 4983230072969 + 3 ^ 40 * 3444363 * 2
def baseEnd_3444363 : Nat := 131008427226830566490531

theorem tailTrace_3444363 : CollatzResearch.WordTrace tailWord_3444363 prefixEnd_3444363 131008427226830566490531 := by
  unfold tailWord_3444363
  simp only [CollatzResearch.WordTrace]
  refine ⟨125626239220668576212505743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83750826147112384141670495 125626239220668576212505743)
  ·
    refine ⟨188439358831002864318758615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125626239220668576212505743 188439358831002864318758615)
    ·
      refine ⟨282659038246504296478137923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188439358831002864318758615 282659038246504296478137923)
      ·
        refine ⟨423988557369756444717206885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282659038246504296478137923 423988557369756444717206885)
        ·
          refine ⟨79497854506829333384476291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423988557369756444717206885 79497854506829333384476291)
          ·
            refine ⟨119246781760244000076714437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79497854506829333384476291 119246781760244000076714437)
            ·
              refine ⟨22358771580045750014383957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119246781760244000076714437 22358771580045750014383957)
              ·
                refine ⟨131008427226830566490531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22358771580045750014383957 131008427226830566490531)
                ·
                  rfl

theorem cell22_3444363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 9].length) (baseStart_3444363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444363 prefixEnd_3444363 := by exact prefixLift 3444363
  have htrace : WordTrace (prefixWord ++ tailWord_3444363) baseStart_3444363 baseEnd_3444363 := by
    simpa [prefixWord, tailWord_3444363, baseEnd_3444363] using wordTrace_append hprefix tailTrace_3444363
  have hstable : (prefixWord ++ tailWord_3444363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444363).length < 2 ^ (prefixWord ++ tailWord_3444363).sum := by decide
  have hdescent : baseEnd_3444363 < baseStart_3444363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444382 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3444382 : Nat := 118140960795 + 3444382 * 2 ^ 59
def prefixEnd_3444382 : Nat := 4983230072969 + 3 ^ 40 * 3444382 * 2
def baseEnd_3444382 : Nat := 1179082349129765382189721

theorem tailTrace_3444382 : CollatzResearch.WordTrace tailWord_3444382 prefixEnd_3444382 1179082349129765382189721 := by
  unfold tailWord_3444382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703366525949967807180925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83751288138399828304964933 15703366525949967807180925)
  ·
    refine ⟨5888762447231237927692847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15703366525949967807180925 5888762447231237927692847)
    ·
      refine ⟨8833143670846856891539271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5888762447231237927692847 8833143670846856891539271)
      ·
        refine ⟨13249715506270285337308907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8833143670846856891539271 13249715506270285337308907)
        ·
          refine ⟨19874573259405428005963361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13249715506270285337308907 19874573259405428005963361)
          ·
            refine ⟨14905929944554071004472521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19874573259405428005963361 14905929944554071004472521)
            ·
              refine ⟨11179447458415553253354391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14905929944554071004472521 11179447458415553253354391)
              ·
                refine ⟨16769171187623329880031587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11179447458415553253354391 16769171187623329880031587)
                ·
                  refine ⟨25153756781434994820047381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16769171187623329880031587 25153756781434994820047381)
                  ·
                    refine ⟨1179082349129765382189721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25153756781434994820047381 1179082349129765382189721)
                    ·
                      rfl

theorem cell22_3444382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3444382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444382 prefixEnd_3444382 := by exact prefixLift 3444382
  have htrace : WordTrace (prefixWord ++ tailWord_3444382) baseStart_3444382 baseEnd_3444382 := by
    simpa [prefixWord, tailWord_3444382, baseEnd_3444382] using wordTrace_append hprefix tailTrace_3444382
  have hstable : (prefixWord ++ tailWord_3444382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444382).length < 2 ^ (prefixWord ++ tailWord_3444382).sum := by decide
  have hdescent : baseEnd_3444382 < baseStart_3444382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444506 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_3444506 : Nat := 118140960795 + 3444506 * 2 ^ 59
def prefixEnd_3444506 : Nat := 4983230072969 + 3 ^ 40 * 3444506 * 2
def baseEnd_3444506 : Nat := 1179124796863870392089341

theorem tailTrace_3444506 : CollatzResearch.WordTrace tailWord_3444506 prefixEnd_3444506 1179124796863870392089341 := by
  unfold tailWord_3444506
  simp only [CollatzResearch.WordTrace]
  refine ⟨31407863714787627908740343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83754303239433674423307581 31407863714787627908740343)
  ·
    refine ⟨47111795572181441863110515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31407863714787627908740343 47111795572181441863110515)
    ·
      refine ⟨70667693358272162794665773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47111795572181441863110515 70667693358272162794665773)
      ·
        refine ⟨26500385009352061047999665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70667693358272162794665773 26500385009352061047999665)
        ·
          refine ⟨19875288757014045785999749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26500385009352061047999665 19875288757014045785999749)
          ·
            refine ⟨3726616641940133584874953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19875288757014045785999749 3726616641940133584874953)
            ·
              refine ⟨2794962481455100188656215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726616641940133584874953 2794962481455100188656215)
              ·
                refine ⟨4192443722182650282984323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794962481455100188656215 4192443722182650282984323)
                ·
                  refine ⟨6288665583273975424476485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4192443722182650282984323 6288665583273975424476485)
                  ·
                    refine ⟨1179124796863870392089341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288665583273975424476485 1179124796863870392089341)
                    ·
                      rfl

theorem cell22_3444506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_3444506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444506 prefixEnd_3444506 := by exact prefixLift 3444506
  have htrace : WordTrace (prefixWord ++ tailWord_3444506) baseStart_3444506 baseEnd_3444506 := by
    simpa [prefixWord, tailWord_3444506, baseEnd_3444506] using wordTrace_append hprefix tailTrace_3444506
  have hstable : (prefixWord ++ tailWord_3444506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444506).length < 2 ^ (prefixWord ++ tailWord_3444506).sum := by decide
  have hdescent : baseEnd_3444506 < baseStart_3444506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444510 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3444510 : Nat := 118140960795 + 3444510 * 2 ^ 59
def prefixEnd_3444510 : Nat := 4983230072969 + 3 ^ 40 * 3444510 * 2
def baseEnd_3444510 : Nat := 393042055381871904996443

theorem tailTrace_3444510 : CollatzResearch.WordTrace tailWord_3444510 prefixEnd_3444510 393042055381871904996443 := by
  unfold tailWord_3444510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703950093892002539763373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83754400500757346878737989 15703950093892002539763373)
  ·
    refine ⟨5888981285209500952411265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15703950093892002539763373 5888981285209500952411265)
    ·
      refine ⟨4416735963907125714308449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5888981285209500952411265 4416735963907125714308449)
      ·
        refine ⟨3312551972930344285731337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4416735963907125714308449 3312551972930344285731337)
        ·
          refine ⟨2484413979697758214298503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3312551972930344285731337 2484413979697758214298503)
          ·
            refine ⟨3726620969546637321447755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484413979697758214298503 3726620969546637321447755)
            ·
              refine ⟨5589931454319955982171633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726620969546637321447755 5589931454319955982171633)
              ·
                refine ⟨4192448590739966986628725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589931454319955982171633 4192448590739966986628725)
                ·
                  refine ⟨393042055381871904996443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4192448590739966986628725 393042055381871904996443)
                  ·
                    rfl

theorem cell22_3444510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3444510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444510 prefixEnd_3444510 := by exact prefixLift 3444510
  have htrace : WordTrace (prefixWord ++ tailWord_3444510) baseStart_3444510 baseEnd_3444510 := by
    simpa [prefixWord, tailWord_3444510, baseEnd_3444510] using wordTrace_append hprefix tailTrace_3444510
  have hstable : (prefixWord ++ tailWord_3444510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444510).length < 2 ^ (prefixWord ++ tailWord_3444510).sum := by decide
  have hdescent : baseEnd_3444510 < baseStart_3444510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444534 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3444534 : Nat := 118140960795 + 3444534 * 2 ^ 59
def prefixEnd_3444534 : Nat := 4983230072969 + 3 ^ 40 * 3444534 * 2
def baseEnd_3444534 : Nat := 1179134381836087652389255

theorem tailTrace_3444534 : CollatzResearch.WordTrace tailWord_3444534 prefixEnd_3444534 1179134381836087652389255 := by
  unfold tailWord_3444534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7852029756440567026061291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83754984068699381611320437 7852029756440567026061291)
  ·
    refine ⟨11778044634660850539091937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7852029756440567026061291 11778044634660850539091937)
    ·
      refine ⟨8833533475995637904318953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11778044634660850539091937 8833533475995637904318953)
      ·
        refine ⟨6625150106996728428239215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8833533475995637904318953 6625150106996728428239215)
        ·
          refine ⟨9937725160495092642358823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625150106996728428239215 9937725160495092642358823)
          ·
            refine ⟨14906587740742638963538235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9937725160495092642358823 14906587740742638963538235)
            ·
              refine ⟨22359881611113958445307353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14906587740742638963538235 22359881611113958445307353)
              ·
                refine ⟨16769911208335468833980515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22359881611113958445307353 16769911208335468833980515)
                ·
                  refine ⟨25154866812503203250970773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16769911208335468833980515 25154866812503203250970773)
                  ·
                    refine ⟨1179134381836087652389255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25154866812503203250970773 1179134381836087652389255)
                    ·
                      rfl

theorem cell22_3444534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3444534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444534 prefixEnd_3444534 := by exact prefixLift 3444534
  have htrace : WordTrace (prefixWord ++ tailWord_3444534) baseStart_3444534 baseEnd_3444534 := by
    simpa [prefixWord, tailWord_3444534, baseEnd_3444534] using wordTrace_append hprefix tailTrace_3444534
  have hstable : (prefixWord ++ tailWord_3444534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444534).length < 2 ^ (prefixWord ++ tailWord_3444534).sum := by decide
  have hdescent : baseEnd_3444534 < baseStart_3444534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444536 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 2, 3]
def baseStart_3444536 : Nat := 118140960795 + 3444536 * 2 ^ 59
def prefixEnd_3444536 : Nat := 4983230072969 + 3 ^ 40 * 3444536 * 2
def baseEnd_3444536 : Nat := 1179135066476960313839249

theorem tailTrace_3444536 : CollatzResearch.WordTrace tailWord_3444536 prefixEnd_3444536 1179135066476960313839249 := by
  unfold tailWord_3444536
  simp only [CollatzResearch.WordTrace]
  refine ⟨62816274524520913379276731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83755032699361217839035641 62816274524520913379276731)
  ·
    refine ⟨94224411786781370068915097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62816274524520913379276731 94224411786781370068915097)
    ·
      refine ⟨70668308840086027551686323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94224411786781370068915097 70668308840086027551686323)
      ·
        refine ⟨106002463260129041327529485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70668308840086027551686323 106002463260129041327529485)
        ·
          refine ⟨39750923722548390497823557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106002463260129041327529485 39750923722548390497823557)
          ·
            refine ⟨7453298197977823218341917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39750923722548390497823557 7453298197977823218341917)
            ·
              refine ⟨2794986824241683706878219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7453298197977823218341917 2794986824241683706878219)
              ·
                refine ⟨4192480236362525560317329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2794986824241683706878219 4192480236362525560317329)
                ·
                  refine ⟨3144360177271894170237997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192480236362525560317329 3144360177271894170237997)
                  ·
                    refine ⟨1179135066476960313839249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144360177271894170237997 1179135066476960313839249)
                    ·
                      rfl

theorem cell22_3444536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_3444536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444536 prefixEnd_3444536 := by exact prefixLift 3444536
  have htrace : WordTrace (prefixWord ++ tailWord_3444536) baseStart_3444536 baseEnd_3444536 := by
    simpa [prefixWord, tailWord_3444536, baseEnd_3444536] using wordTrace_append hprefix tailTrace_3444536
  have hstable : (prefixWord ++ tailWord_3444536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444536).length < 2 ^ (prefixWord ++ tailWord_3444536).sum := by decide
  have hdescent : baseEnd_3444536 < baseStart_3444536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444577 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 5]
def baseStart_3444577 : Nat := 118140960795 + 3444577 * 2 ^ 59
def prefixEnd_3444577 : Nat := 4983230072969 + 3 ^ 40 * 3444577 * 2
def baseEnd_3444577 : Nat := 393049700538283291188041

theorem tailTrace_3444577 : CollatzResearch.WordTrace tailWord_3444577 prefixEnd_3444577 393049700538283291188041 := by
  unfold tailWord_3444577
  simp only [CollatzResearch.WordTrace]
  refine ⟨125634044441893290760795985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83756029627928860507197323 125634044441893290760795985)
  ·
    refine ⟨94225533331419968070596989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125634044441893290760795985 94225533331419968070596989)
    ·
      refine ⟨35334574999282488026473871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94225533331419968070596989 35334574999282488026473871)
      ·
        refine ⟨53001862498923732039710807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35334574999282488026473871 53001862498923732039710807)
        ·
          refine ⟨79502793748385598059566211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53001862498923732039710807 79502793748385598059566211)
          ·
            refine ⟨119254190622578397089349317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79502793748385598059566211 119254190622578397089349317)
            ·
              refine ⟨22360160741733449454252997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119254190622578397089349317 22360160741733449454252997)
              ·
                refine ⟨4192530139075021772672437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22360160741733449454252997 4192530139075021772672437)
                ·
                  refine ⟨393049700538283291188041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4192530139075021772672437 393049700538283291188041)
                  ·
                    rfl

theorem cell22_3444577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_3444577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444577 prefixEnd_3444577 := by exact prefixLift 3444577
  have htrace : WordTrace (prefixWord ++ tailWord_3444577) baseStart_3444577 baseEnd_3444577 := by
    simpa [prefixWord, tailWord_3444577, baseEnd_3444577] using wordTrace_append hprefix tailTrace_3444577
  have hstable : (prefixWord ++ tailWord_3444577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444577).length < 2 ^ (prefixWord ++ tailWord_3444577).sum := by decide
  have hdescent : baseEnd_3444577 < baseStart_3444577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444632 : List Nat := [2, 1, 2, 6, 1, 2, 2, 2, 1, 3]
def baseStart_3444632 : Nat := 118140960795 + 3444632 * 2 ^ 59
def prefixEnd_3444632 : Nat := 4983230072969 + 3 ^ 40 * 3444632 * 2
def baseEnd_3444632 : Nat := 1179167929238848063438955

theorem tailTrace_3444632 : CollatzResearch.WordTrace tailWord_3444632 prefixEnd_3444632 1179167929238848063438955 := by
  unfold tailWord_3444632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62818025228347017577024075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83757366971129356769365433 62818025228347017577024075)
  ·
    refine ⟨94227037842520526365536113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62818025228347017577024075 94227037842520526365536113)
    ·
      refine ⟨70670278381890394774152085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94227037842520526365536113 70670278381890394774152085)
      ·
        refine ⟨3312669299151112255038379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70670278381890394774152085 3312669299151112255038379)
        ·
          refine ⟨4969003948726668382557569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312669299151112255038379 4969003948726668382557569)
          ·
            refine ⟨3726752961545001286918177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4969003948726668382557569 3726752961545001286918177)
            ·
              refine ⟨2795064721158750965188633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726752961545001286918177 2795064721158750965188633)
              ·
                refine ⟨2096298540869063223891475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795064721158750965188633 2096298540869063223891475)
                ·
                  refine ⟨3144447811303594835837213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096298540869063223891475 3144447811303594835837213)
                  ·
                    refine ⟨1179167929238848063438955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144447811303594835837213 1179167929238848063438955)
                    ·
                      rfl

theorem cell22_3444632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_3444632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444632 prefixEnd_3444632 := by exact prefixLift 3444632
  have htrace : WordTrace (prefixWord ++ tailWord_3444632) baseStart_3444632 baseEnd_3444632 := by
    simpa [prefixWord, tailWord_3444632, baseEnd_3444632] using wordTrace_append hprefix tailTrace_3444632
  have hstable : (prefixWord ++ tailWord_3444632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444632).length < 2 ^ (prefixWord ++ tailWord_3444632).sum := by decide
  have hdescent : baseEnd_3444632 < baseStart_3444632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444669 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_3444669 : Nat := 118140960795 + 3444669 * 2 ^ 59
def prefixEnd_3444669 : Nat := 4983230072969 + 3 ^ 40 * 3444669 * 2
def baseEnd_3444669 : Nat := 1179180595094992300263841

theorem tailTrace_3444669 : CollatzResearch.WordTrace tailWord_3444669 prefixEnd_3444669 1179180595094992300263841 := by
  unfold tailWord_3444669
  simp only [CollatzResearch.WordTrace]
  refine ⟨125637399957559990473145061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83758266638373326982096707 125637399957559990473145061)
  ·
    refine ⟨23557012492042498213714699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125637399957559990473145061 23557012492042498213714699)
    ·
      refine ⟨35335518738063747320572049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23557012492042498213714699 35335518738063747320572049)
      ·
        refine ⟨26501639053547810490429037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35335518738063747320572049 26501639053547810490429037)
        ·
          refine ⟨9938114645080428933910889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26501639053547810490429037 9938114645080428933910889)
          ·
            refine ⟨7453585983810321700433167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9938114645080428933910889 7453585983810321700433167)
            ·
              refine ⟨11180378975715482550649751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7453585983810321700433167 11180378975715482550649751)
              ·
                refine ⟨16770568463573223825974627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11180378975715482550649751 16770568463573223825974627)
                ·
                  refine ⟨25155852695359835738961941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16770568463573223825974627 25155852695359835738961941)
                  ·
                    refine ⟨1179180595094992300263841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25155852695359835738961941 1179180595094992300263841)
                    ·
                      rfl

theorem cell22_3444669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_3444669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444669 prefixEnd_3444669 := by exact prefixLift 3444669
  have htrace : WordTrace (prefixWord ++ tailWord_3444669) baseStart_3444669 baseEnd_3444669 := by
    simpa [prefixWord, tailWord_3444669, baseEnd_3444669] using wordTrace_append hprefix tailTrace_3444669
  have hstable : (prefixWord ++ tailWord_3444669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444669).length < 2 ^ (prefixWord ++ tailWord_3444669).sum := by decide
  have hdescent : baseEnd_3444669 < baseStart_3444669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444733 : List Nat := [1, 4, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_3444733 : Nat := 118140960795 + 3444733 * 2 ^ 59
def prefixEnd_3444733 : Nat := 4983230072969 + 3 ^ 40 * 3444733 * 2
def baseEnd_3444733 : Nat := 1179202503602917466663645

theorem tailTrace_3444733 : CollatzResearch.WordTrace tailWord_3444733 prefixEnd_3444733 1179202503602917466663645 := by
  unfold tailWord_3444733
  simp only [CollatzResearch.WordTrace]
  refine ⟨125639734229328129403474853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83759822819552086268983235 125639734229328129403474853)
  ·
    refine ⟨23557450167999024263151535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125639734229328129403474853 23557450167999024263151535)
    ·
      refine ⟨35336175251998536394727303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23557450167999024263151535 35336175251998536394727303)
      ·
        refine ⟨53004262877997804592090955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35336175251998536394727303 53004262877997804592090955)
        ·
          refine ⟨79506394316996706888136433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53004262877997804592090955 79506394316996706888136433)
          ·
            refine ⟨59629795737747530166102325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79506394316996706888136433 59629795737747530166102325)
            ·
              refine ⟨5590293350413830953072093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59629795737747530166102325 5590293350413830953072093)
              ·
                refine ⟨2096360006405186607402035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5590293350413830953072093 2096360006405186607402035)
                ·
                  refine ⟨3144540009607779911103053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096360006405186607402035 3144540009607779911103053)
                  ·
                    refine ⟨1179202503602917466663645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144540009607779911103053 1179202503602917466663645)
                    ·
                      rfl

theorem cell22_3444733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_3444733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444733 prefixEnd_3444733 := by exact prefixLift 3444733
  have htrace : WordTrace (prefixWord ++ tailWord_3444733) baseStart_3444733 baseEnd_3444733 := by
    simpa [prefixWord, tailWord_3444733, baseEnd_3444733] using wordTrace_append hprefix tailTrace_3444733
  have hstable : (prefixWord ++ tailWord_3444733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444733).length < 2 ^ (prefixWord ++ tailWord_3444733).sum := by decide
  have hdescent : baseEnd_3444733 < baseStart_3444733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444750 : List Nat := [4, 1, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_3444750 : Nat := 118140960795 + 3444750 * 2 ^ 59
def prefixEnd_3444750 : Nat := 4983230072969 + 3 ^ 40 * 3444750 * 2
def baseEnd_3444750 : Nat := 1179208323050335088988593

theorem tailTrace_3444750 : CollatzResearch.WordTrace tailWord_3444750 prefixEnd_3444750 1179208323050335088988593 := by
  unfold tailWord_3444750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705044283783317663355463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83760236180177694204562469 15705044283783317663355463)
  ·
    refine ⟨23557566425674976495033195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15705044283783317663355463 23557566425674976495033195)
    ·
      refine ⟨35336349638512464742549793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23557566425674976495033195 35336349638512464742549793)
      ·
        refine ⟨26502262228884348556912345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35336349638512464742549793 26502262228884348556912345)
        ·
          refine ⟨19876696671663261417684259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26502262228884348556912345 19876696671663261417684259)
          ·
            refine ⟨29815045007494892126526389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19876696671663261417684259 29815045007494892126526389)
            ·
              refine ⟨2795160469452646136861849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29815045007494892126526389 2795160469452646136861849)
              ·
                refine ⟨2096370352089484602646387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795160469452646136861849 2096370352089484602646387)
                ·
                  refine ⟨3144555528134226903969581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096370352089484602646387 3144555528134226903969581)
                  ·
                    refine ⟨1179208323050335088988593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144555528134226903969581 1179208323050335088988593)
                    ·
                      rfl

theorem cell22_3444750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_3444750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444750 prefixEnd_3444750 := by exact prefixLift 3444750
  have htrace : WordTrace (prefixWord ++ tailWord_3444750) baseStart_3444750 baseEnd_3444750 := by
    simpa [prefixWord, tailWord_3444750, baseEnd_3444750] using wordTrace_append hprefix tailTrace_3444750
  have hstable : (prefixWord ++ tailWord_3444750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444750).length < 2 ^ (prefixWord ++ tailWord_3444750).sum := by decide
  have hdescent : baseEnd_3444750 < baseStart_3444750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444789 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3444789 : Nat := 118140960795 + 3444789 * 2 ^ 59
def prefixEnd_3444789 : Nat := 4983230072969 + 3 ^ 40 * 3444789 * 2
def baseEnd_3444789 : Nat := 1179221673547351987263473

theorem tailTrace_3444789 : CollatzResearch.WordTrace tailWord_3444789 prefixEnd_3444789 1179221673547351987263473 := by
  unfold tailWord_3444789
  simp only [CollatzResearch.WordTrace]
  refine ⟨125641776717125250967513421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83761184478083500645008947 125641776717125250967513421)
  ·
    refine ⟨47115666268921969112817533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125641776717125250967513421 47115666268921969112817533)
    ·
      refine ⟨17668374850845738417306575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47115666268921969112817533 17668374850845738417306575)
      ·
        refine ⟨26502562276268607625959863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17668374850845738417306575 26502562276268607625959863)
        ·
          refine ⟨39753843414402911438939795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26502562276268607625959863 39753843414402911438939795)
          ·
            refine ⟨59630765121604367158409693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39753843414402911438939795 59630765121604367158409693)
            ·
              refine ⟨22361536920601637684403635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59630765121604367158409693 22361536920601637684403635)
              ·
                refine ⟨33542305380902456526605453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22361536920601637684403635 33542305380902456526605453)
                ·
                  refine ⟨12578364517838421197477045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33542305380902456526605453 12578364517838421197477045)
                  ·
                    refine ⟨1179221673547351987263473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12578364517838421197477045 1179221673547351987263473)
                    ·
                      rfl

theorem cell22_3444789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3444789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444789 prefixEnd_3444789 := by exact prefixLift 3444789
  have htrace : WordTrace (prefixWord ++ tailWord_3444789) baseStart_3444789 baseEnd_3444789 := by
    simpa [prefixWord, tailWord_3444789, baseEnd_3444789] using wordTrace_append hprefix tailTrace_3444789
  have hstable : (prefixWord ++ tailWord_3444789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444789).length < 2 ^ (prefixWord ++ tailWord_3444789).sum := by decide
  have hdescent : baseEnd_3444789 < baseStart_3444789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444868 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3444868 : Nat := 118140960795 + 3444868 * 2 ^ 59
def prefixEnd_3444868 : Nat := 4983230072969 + 3 ^ 40 * 3444868 * 2
def baseEnd_3444868 : Nat := 1179248716861822114538231

theorem tailTrace_3444868 : CollatzResearch.WordTrace tailWord_3444868 prefixEnd_3444868 1179248716861822114538231 := by
  unfold tailWord_3444868
  simp only [CollatzResearch.WordTrace]
  refine ⟨62822329041919523729819629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83763105389226031639759505 62822329041919523729819629)
  ·
    refine ⟨23558373390719821398682361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62822329041919523729819629 23558373390719821398682361)
    ·
      refine ⟨17668780043039866049011771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23558373390719821398682361 17668780043039866049011771)
      ·
        refine ⟨26503170064559799073517657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17668780043039866049011771 26503170064559799073517657)
        ·
          refine ⟨19877377548419849305138243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26503170064559799073517657 19877377548419849305138243)
          ·
            refine ⟨29816066322629773957707365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19877377548419849305138243 29816066322629773957707365)
            ·
              refine ⟨5590512435493082617070131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29816066322629773957707365 5590512435493082617070131)
              ·
                refine ⟨8385768653239623925605197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590512435493082617070131 8385768653239623925605197)
                ·
                  refine ⟨3144663244964858972101949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8385768653239623925605197 3144663244964858972101949)
                  ·
                    refine ⟨1179248716861822114538231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144663244964858972101949 1179248716861822114538231)
                    ·
                      rfl

theorem cell22_3444868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3444868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444868 prefixEnd_3444868 := by exact prefixLift 3444868
  have htrace : WordTrace (prefixWord ++ tailWord_3444868) baseStart_3444868 baseEnd_3444868 := by
    simpa [prefixWord, tailWord_3444868, baseEnd_3444868] using wordTrace_append hprefix tailTrace_3444868
  have hstable : (prefixWord ++ tailWord_3444868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444868).length < 2 ^ (prefixWord ++ tailWord_3444868).sum := by decide
  have hdescent : baseEnd_3444868 < baseStart_3444868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444975 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 2, 3]
def baseStart_3444975 : Nat := 118140960795 + 3444975 * 2 ^ 59
def prefixEnd_3444975 : Nat := 4983230072969 + 3 ^ 40 * 3444975 * 2
def baseEnd_3444975 : Nat := 1179285345148509502112903

theorem tailTrace_3444975 : CollatzResearch.WordTrace tailWord_3444975 prefixEnd_3444975 1179285345148509502112903 := by
  unfold tailWord_3444975
  simp only [CollatzResearch.WordTrace]
  refine ⟨125648560694451404733784379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83765707129634269822522919 125648560694451404733784379)
  ·
    refine ⟨188472841041677107100676569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125648560694451404733784379 188472841041677107100676569)
    ·
      refine ⟨141354630781257830325507427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188472841041677107100676569 141354630781257830325507427)
      ·
        refine ⟨212031946171886745488261141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141354630781257830325507427 212031946171886745488261141)
        ·
          refine ⟨9938997476807191194762241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 212031946171886745488261141 9938997476807191194762241)
          ·
            refine ⟨7454248107605393396071681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9938997476807191194762241 7454248107605393396071681)
            ·
              refine ⟨5590686080704045047053761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7454248107605393396071681 5590686080704045047053761)
              ·
                refine ⟨4193014560528033785290321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5590686080704045047053761 4193014560528033785290321)
                ·
                  refine ⟨3144760920396025338967741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193014560528033785290321 3144760920396025338967741)
                  ·
                    refine ⟨1179285345148509502112903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144760920396025338967741 1179285345148509502112903)
                    ·
                      rfl

theorem cell22_3444975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_3444975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444975 prefixEnd_3444975 := by exact prefixLift 3444975
  have htrace : WordTrace (prefixWord ++ tailWord_3444975) baseStart_3444975 baseEnd_3444975 := by
    simpa [prefixWord, tailWord_3444975, baseEnd_3444975] using wordTrace_append hprefix tailTrace_3444975
  have hstable : (prefixWord ++ tailWord_3444975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444975).length < 2 ^ (prefixWord ++ tailWord_3444975).sum := by decide
  have hdescent : baseEnd_3444975 < baseStart_3444975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3444988 : List Nat := [2, 2, 2, 1, 4, 3, 1, 7]
def baseStart_3444988 : Nat := 118140960795 + 3444988 * 2 ^ 59
def prefixEnd_3444988 : Nat := 4983230072969 + 3 ^ 40 * 3444988 * 2
def baseEnd_3444988 : Nat := 131032199479353533504207

theorem tailTrace_3444988 : CollatzResearch.WordTrace tailWord_3444988 prefixEnd_3444988 131032199479353533504207 := by
  unfold tailWord_3444988
  simp only [CollatzResearch.WordTrace]
  refine ⟨62824517421702153977003809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83766023228936205302671745 62824517421702153977003809)
  ·
    refine ⟨47118388066276615482752857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62824517421702153977003809 47118388066276615482752857)
    ·
      refine ⟨35338791049707461612064643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47118388066276615482752857 35338791049707461612064643)
      ·
        refine ⟨53008186574561192418096965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35338791049707461612064643 53008186574561192418096965)
        ·
          refine ⟨9939034982730223578393181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53008186574561192418096965 9939034982730223578393181)
          ·
            refine ⟨3727138118523833841897443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9939034982730223578393181 3727138118523833841897443)
            ·
              refine ⟨5590707177785750762846165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727138118523833841897443 5590707177785750762846165)
              ·
                refine ⟨131032199479353533504207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5590707177785750762846165 131032199479353533504207)
                ·
                  rfl

theorem cell22_3444988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 7].length) (baseStart_3444988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3444988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3444988 prefixEnd_3444988 := by exact prefixLift 3444988
  have htrace : WordTrace (prefixWord ++ tailWord_3444988) baseStart_3444988 baseEnd_3444988 := by
    simpa [prefixWord, tailWord_3444988, baseEnd_3444988] using wordTrace_append hprefix tailTrace_3444988
  have hstable : (prefixWord ++ tailWord_3444988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3444988).length < 2 ^ (prefixWord ++ tailWord_3444988).sum := by decide
  have hdescent : baseEnd_3444988 < baseStart_3444988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3444988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445003 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 3, 3]
def baseStart_3445003 : Nat := 118140960795 + 3445003 * 2 ^ 59
def prefixEnd_3445003 : Nat := 4983230072969 + 3 ^ 40 * 3445003 * 2
def baseEnd_3445003 : Nat := 1179294930120726762412817

theorem tailTrace_3445003 : CollatzResearch.WordTrace tailWord_3445003 prefixEnd_3445003 1179294930120726762412817 := by
  unfold tailWord_3445003
  simp only [CollatzResearch.WordTrace]
  refine ⟨125649581938349965515803663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83766387958899977010535775 125649581938349965515803663)
  ·
    refine ⟨188474372907524948273705495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125649581938349965515803663 188474372907524948273705495)
    ·
      refine ⟨282711559361287422410558243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188474372907524948273705495 282711559361287422410558243)
      ·
        refine ⟨424067339041931133615837365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282711559361287422410558243 424067339041931133615837365)
        ·
          refine ⟨39756313035181043776484753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 424067339041931133615837365 39756313035181043776484753)
          ·
            refine ⟨29817234776385782832363565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39756313035181043776484753 29817234776385782832363565)
            ·
              refine ⟨11181463041144668562136337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29817234776385782832363565 11181463041144668562136337)
              ·
                refine ⟨8386097280858501421602253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11181463041144668562136337 8386097280858501421602253)
                ·
                  refine ⟨3144786480321938033100845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8386097280858501421602253 3144786480321938033100845)
                  ·
                    refine ⟨1179294930120726762412817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144786480321938033100845 1179294930120726762412817)
                    ·
                      rfl

theorem cell22_3445003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 3].length) (baseStart_3445003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445003 prefixEnd_3445003 := by exact prefixLift 3445003
  have htrace : WordTrace (prefixWord ++ tailWord_3445003) baseStart_3445003 baseEnd_3445003 := by
    simpa [prefixWord, tailWord_3445003, baseEnd_3445003] using wordTrace_append hprefix tailTrace_3445003
  have hstable : (prefixWord ++ tailWord_3445003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445003).length < 2 ^ (prefixWord ++ tailWord_3445003).sum := by decide
  have hdescent : baseEnd_3445003 < baseStart_3445003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445016 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 7]
def baseStart_3445016 : Nat := 118140960795 + 3445016 * 2 ^ 59
def prefixEnd_3445016 : Nat := 4983230072969 + 3 ^ 40 * 3445016 * 2
def baseEnd_3445016 : Nat := 393099793428799687279259

theorem tailTrace_3445016 : CollatzResearch.WordTrace tailWord_3445016 prefixEnd_3445016 393099793428799687279259 := by
  unfold tailWord_3445016
  simp only [CollatzResearch.WordTrace]
  refine ⟨62825028043651434368013451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83766704058201912490684601 62825028043651434368013451)
  ·
    refine ⟨94237542065477151552020177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62825028043651434368013451 94237542065477151552020177)
    ·
      refine ⟨70678156549107863664015133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94237542065477151552020177 70678156549107863664015133)
      ·
        refine ⟨26504308705915448874005675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70678156549107863664015133 26504308705915448874005675)
        ·
          refine ⟨39756463058873173311008513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26504308705915448874005675 39756463058873173311008513)
          ·
            refine ⟨29817347294154879983256385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39756463058873173311008513 29817347294154879983256385)
            ·
              refine ⟨22363010470616159987442289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29817347294154879983256385 22363010470616159987442289)
              ·
                refine ⟨16772257852962119990581717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22363010470616159987442289 16772257852962119990581717)
                ·
                  refine ⟨393099793428799687279259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16772257852962119990581717 393099793428799687279259)
                  ·
                    rfl

theorem cell22_3445016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_3445016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445016 prefixEnd_3445016 := by exact prefixLift 3445016
  have htrace : WordTrace (prefixWord ++ tailWord_3445016) baseStart_3445016 baseEnd_3445016 := by
    simpa [prefixWord, tailWord_3445016, baseEnd_3445016] using wordTrace_append hprefix tailTrace_3445016
  have hstable : (prefixWord ++ tailWord_3445016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445016).length < 2 ^ (prefixWord ++ tailWord_3445016).sum := by decide
  have hdescent : baseEnd_3445016 < baseStart_3445016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445050 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_3445050 : Nat := 118140960795 + 3445050 * 2 ^ 59
def prefixEnd_3445050 : Nat := 4983230072969 + 3 ^ 40 * 3445050 * 2
def baseEnd_3445050 : Nat := 393103673060411435495891

theorem tailTrace_3445050 : CollatzResearch.WordTrace tailWord_3445050 prefixEnd_3445050 393103673060411435495891 := by
  unfold tailWord_3445050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31412824042294923135691151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83767530779453128361843069 31412824042294923135691151)
  ·
    refine ⟨47119236063442384703536727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31412824042294923135691151 47119236063442384703536727)
    ·
      refine ⟨70678854095163577055305091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47119236063442384703536727 70678854095163577055305091)
      ·
        refine ⟨106018281142745365582957637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70678854095163577055305091 106018281142745365582957637)
        ·
          refine ⟨19878427714264756046804557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106018281142745365582957637 19878427714264756046804557)
          ·
            refine ⟨7454410392849283517551709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19878427714264756046804557 7454410392849283517551709)
            ·
              refine ⟨2795403897318481319081891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7454410392849283517551709 2795403897318481319081891)
              ·
                refine ⟨4193105845977721978622837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795403897318481319081891 4193105845977721978622837)
                ·
                  refine ⟨393103673060411435495891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4193105845977721978622837 393103673060411435495891)
                  ·
                    rfl

theorem cell22_3445050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_3445050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445050 prefixEnd_3445050 := by exact prefixLift 3445050
  have htrace : WordTrace (prefixWord ++ tailWord_3445050) baseStart_3445050 baseEnd_3445050 := by
    simpa [prefixWord, tailWord_3445050, baseEnd_3445050] using wordTrace_append hprefix tailTrace_3445050
  have hstable : (prefixWord ++ tailWord_3445050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445050).length < 2 ^ (prefixWord ++ tailWord_3445050).sum := by decide
  have hdescent : baseEnd_3445050 < baseStart_3445050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445095 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 6]
def baseStart_3445095 : Nat := 118140960795 + 3445095 * 2 ^ 59
def prefixEnd_3445095 : Nat := 4983230072969 + 3 ^ 40 * 3445095 * 2
def baseEnd_3445095 : Nat := 393108807866956396370845

theorem tailTrace_3445095 : CollatzResearch.WordTrace tailWord_3445095 prefixEnd_3445095 393108807866956396370845 := by
  unfold tailWord_3445095
  simp only [CollatzResearch.WordTrace]
  refine ⟨125652937454016665228152739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83768624969344443485435159 125652937454016665228152739)
  ·
    refine ⟨188479406181024997842229109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125652937454016665228152739 188479406181024997842229109)
    ·
      refine ⟨17669944329471093547708979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188479406181024997842229109 17669944329471093547708979)
      ·
        refine ⟨26504916494206640321563469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17669944329471093547708979 26504916494206640321563469)
        ·
          refine ⟨9939343685327490120586301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26504916494206640321563469 9939343685327490120586301)
          ·
            refine ⟨3727253881997808795219863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9939343685327490120586301 3727253881997808795219863)
            ·
              refine ⟨5590880822996713192829795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727253881997808795219863 5590880822996713192829795)
              ·
                refine ⟨8386321234495069789244693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590880822996713192829795 8386321234495069789244693)
                ·
                  refine ⟨393108807866956396370845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8386321234495069789244693 393108807866956396370845)
                  ·
                    rfl

theorem cell22_3445095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 6].length) (baseStart_3445095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445095 prefixEnd_3445095 := by exact prefixLift 3445095
  have htrace : WordTrace (prefixWord ++ tailWord_3445095) baseStart_3445095 baseEnd_3445095 := by
    simpa [prefixWord, tailWord_3445095, baseEnd_3445095] using wordTrace_append hprefix tailTrace_3445095
  have hstable : (prefixWord ++ tailWord_3445095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445095).length < 2 ^ (prefixWord ++ tailWord_3445095).sum := by decide
  have hdescent : baseEnd_3445095 < baseStart_3445095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445140 : List Nat := [2, 4, 2, 1, 4, 9]
def baseStart_3445140 : Nat := 118140960795 + 3445140 * 2 ^ 59
def prefixEnd_3445140 : Nat := 4983230072969 + 3 ^ 40 * 3445140 * 2
def baseEnd_3445140 : Nat := 14559775654574124342437

theorem tailTrace_3445140 : CollatzResearch.WordTrace tailWord_3445140 prefixEnd_3445140 14559775654574124342437 := by
  unfold tailWord_3445140
  simp only [CollatzResearch.WordTrace]
  refine ⟨62827289369426818956770437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83769719159235758609027249 62827289369426818956770437)
  ·
    refine ⟨11780116756767528554394457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62827289369426818956770437 11780116756767528554394457)
    ·
      refine ⟨8835087567575646415795843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11780116756767528554394457 8835087567575646415795843)
      ·
        refine ⟨13252631351363469623693765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8835087567575646415795843 13252631351363469623693765)
        ·
          refine ⟨2484868378380650554442581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13252631351363469623693765 2484868378380650554442581)
          ·
            refine ⟨14559775654574124342437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2484868378380650554442581 14559775654574124342437)
            ·
              rfl

theorem cell22_3445140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 9].length) (baseStart_3445140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445140 prefixEnd_3445140 := by exact prefixLift 3445140
  have htrace : WordTrace (prefixWord ++ tailWord_3445140) baseStart_3445140 baseEnd_3445140 := by
    simpa [prefixWord, tailWord_3445140, baseEnd_3445140] using wordTrace_append hprefix tailTrace_3445140
  have hstable : (prefixWord ++ tailWord_3445140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445140).length < 2 ^ (prefixWord ++ tailWord_3445140).sum := by decide
  have hdescent : baseEnd_3445140 < baseStart_3445140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445202 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_3445202 : Nat := 118140960795 + 3445202 * 2 ^ 59
def prefixEnd_3445202 : Nat := 4983230072969 + 3 ^ 40 * 3445202 * 2
def baseEnd_3445202 : Nat := 393121017295852192229069

theorem tailTrace_3445202 : CollatzResearch.WordTrace tailWord_3445202 prefixEnd_3445202 393121017295852192229069 := by
  unfold tailWord_3445202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31414210016157255625574465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83771226709752681668198573 31414210016157255625574465)
  ·
    refine ⟨23560657512117941719180849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31414210016157255625574465 23560657512117941719180849)
    ·
      refine ⟨17670493134088456289385637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23560657512117941719180849 17670493134088456289385637)
      ·
        refine ⟨3313217462641585554259807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17670493134088456289385637 3313217462641585554259807)
        ·
          refine ⟨4969826193962378331389711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313217462641585554259807 4969826193962378331389711)
          ·
            refine ⟨7454739290943567497084567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969826193962378331389711 7454739290943567497084567)
            ·
              refine ⟨11182108936415351245626851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7454739290943567497084567 11182108936415351245626851)
              ·
                refine ⟨16773163404623026868440277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11182108936415351245626851 16773163404623026868440277)
                ·
                  refine ⟨393121017295852192229069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16773163404623026868440277 393121017295852192229069)
                  ·
                    rfl

theorem cell22_3445202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_3445202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445202 prefixEnd_3445202 := by exact prefixLift 3445202
  have htrace : WordTrace (prefixWord ++ tailWord_3445202) baseStart_3445202 baseEnd_3445202 := by
    simpa [prefixWord, tailWord_3445202, baseEnd_3445202] using wordTrace_append hprefix tailTrace_3445202
  have hstable : (prefixWord ++ tailWord_3445202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445202).length < 2 ^ (prefixWord ++ tailWord_3445202).sum := by decide
  have hdescent : baseEnd_3445202 < baseStart_3445202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445230 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_3445230 : Nat := 118140960795 + 3445230 * 2 ^ 59
def prefixEnd_3445230 : Nat := 4983230072969 + 3 ^ 40 * 3445230 * 2
def baseEnd_3445230 : Nat := 393124212286591278995707

theorem tailTrace_3445230 : CollatzResearch.WordTrace tailWord_3445230 prefixEnd_3445230 393124212286591278995707 := by
  unfold tailWord_3445230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707232663565947910539643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83771907539018388856211429 15707232663565947910539643)
  ·
    refine ⟨23560848995348921865809465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15707232663565947910539643 23560848995348921865809465)
    ·
      refine ⟨17670636746511691399357099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23560848995348921865809465 17670636746511691399357099)
      ·
        refine ⟨26505955119767537099035649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17670636746511691399357099 26505955119767537099035649)
        ·
          refine ⟨19879466339825652824276737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26505955119767537099035649 19879466339825652824276737)
          ·
            refine ⟨14909599754869239618207553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19879466339825652824276737 14909599754869239618207553)
            ·
              refine ⟨11182199816151929713655665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14909599754869239618207553 11182199816151929713655665)
              ·
                refine ⟨8386649862113947285241749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11182199816151929713655665 8386649862113947285241749)
                ·
                  refine ⟨393124212286591278995707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8386649862113947285241749 393124212286591278995707)
                  ·
                    rfl

theorem cell22_3445230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_3445230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445230 prefixEnd_3445230 := by exact prefixLift 3445230
  have htrace : WordTrace (prefixWord ++ tailWord_3445230) baseStart_3445230 baseEnd_3445230 := by
    simpa [prefixWord, tailWord_3445230, baseEnd_3445230] using wordTrace_append hprefix tailTrace_3445230
  have hstable : (prefixWord ++ tailWord_3445230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445230).length < 2 ^ (prefixWord ++ tailWord_3445230).sum := by decide
  have hdescent : baseEnd_3445230 < baseStart_3445230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445245 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_3445245 : Nat := 118140960795 + 3445245 * 2 ^ 59
def prefixEnd_3445245 : Nat := 4983230072969 + 3 ^ 40 * 3445245 * 2
def baseEnd_3445245 : Nat := 1179377771666318797862075

theorem tailTrace_3445245 : CollatzResearch.WordTrace tailWord_3445245 prefixEnd_3445245 1179377771666318797862075 := by
  unfold tailWord_3445245
  simp only [CollatzResearch.WordTrace]
  refine ⟨125658408403473240846113189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83772272268982160564075459 125658408403473240846113189)
  ·
    refine ⟨23560951575651232658646223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125658408403473240846113189 23560951575651232658646223)
    ·
      refine ⟨35341427363476848987969335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23560951575651232658646223 35341427363476848987969335)
      ·
        refine ⟨53012141045215273481954003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35341427363476848987969335 53012141045215273481954003)
        ·
          refine ⟨79518211567822910222931005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53012141045215273481954003 79518211567822910222931005)
          ·
            refine ⟨29819329337933591333599127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79518211567822910222931005 29819329337933591333599127)
            ·
              refine ⟨44728994006900387000398691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29819329337933591333599127 44728994006900387000398691)
              ·
                refine ⟨67093491010350580500598037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44728994006900387000398691 67093491010350580500598037)
                ·
                  refine ⟨3145007391110183460965533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67093491010350580500598037 3145007391110183460965533)
                  ·
                    refine ⟨1179377771666318797862075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3145007391110183460965533 1179377771666318797862075)
                    ·
                      rfl

theorem cell22_3445245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_3445245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445245 prefixEnd_3445245 := by exact prefixLift 3445245
  have htrace : WordTrace (prefixWord ++ tailWord_3445245) baseStart_3445245 baseEnd_3445245 := by
    simpa [prefixWord, tailWord_3445245, baseEnd_3445245] using wordTrace_append hprefix tailTrace_3445245
  have hstable : (prefixWord ++ tailWord_3445245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445245).length < 2 ^ (prefixWord ++ tailWord_3445245).sum := by decide
  have hdescent : baseEnd_3445245 < baseStart_3445245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445260 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_3445260 : Nat := 118140960795 + 3445260 * 2 ^ 59
def prefixEnd_3445260 : Nat := 4983230072969 + 3 ^ 40 * 3445260 * 2
def baseEnd_3445260 : Nat := 1179382906472863758737029

theorem tailTrace_3445260 : CollatzResearch.WordTrace tailWord_3445260 prefixEnd_3445260 1179382906472863758737029 := by
  unfold tailWord_3445260
  simp only [CollatzResearch.WordTrace]
  refine ⟨62829477749209449203954617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83772636998945932271939489 62829477749209449203954617)
  ·
    refine ⟨47122108311907086902965963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62829477749209449203954617 47122108311907086902965963)
    ·
      refine ⟨70683162467860630354448945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47122108311907086902965963 70683162467860630354448945)
      ·
        refine ⟨53012371850895472765836709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70683162467860630354448945 53012371850895472765836709)
        ·
          refine ⟨9939819722042901143594383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53012371850895472765836709 9939819722042901143594383)
          ·
            refine ⟨14909729583064351715391575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9939819722042901143594383 14909729583064351715391575)
            ·
              refine ⟨22364594374596527573087363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14909729583064351715391575 22364594374596527573087363)
              ·
                refine ⟨33546891561894791359631045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22364594374596527573087363 33546891561894791359631045)
                ·
                  refine ⟨6290042167855273379930821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33546891561894791359631045 6290042167855273379930821)
                  ·
                    refine ⟨1179382906472863758737029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6290042167855273379930821 1179382906472863758737029)
                    ·
                      rfl

theorem cell22_3445260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_3445260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445260 prefixEnd_3445260 := by exact prefixLift 3445260
  have htrace : WordTrace (prefixWord ++ tailWord_3445260) baseStart_3445260 baseEnd_3445260 := by
    simpa [prefixWord, tailWord_3445260, baseEnd_3445260] using wordTrace_append hprefix tailTrace_3445260
  have hstable : (prefixWord ++ tailWord_3445260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445260).length < 2 ^ (prefixWord ++ tailWord_3445260).sum := by decide
  have hdescent : baseEnd_3445260 < baseStart_3445260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445262 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_3445262 : Nat := 118140960795 + 3445262 * 2 ^ 59
def prefixEnd_3445262 : Nat := 4983230072969 + 3 ^ 40 * 3445262 * 2
def baseEnd_3445262 : Nat := 1179383591113736420187023

theorem tailTrace_3445262 : CollatzResearch.WordTrace tailWord_3445262 prefixEnd_3445262 1179383591113736420187023 := by
  unfold tailWord_3445262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707378555551456593685255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83772685629607768499654693 15707378555551456593685255)
  ·
    refine ⟨23561067833327184890527883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15707378555551456593685255 23561067833327184890527883)
    ·
      refine ⟨35341601749990777335791825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23561067833327184890527883 35341601749990777335791825)
      ·
        refine ⟨26506201312493083001843869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35341601749990777335791825 26506201312493083001843869)
        ·
          refine ⟨9939825492184906125691451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26506201312493083001843869 9939825492184906125691451)
          ·
            refine ⟨14909738238277359188537177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9939825492184906125691451 14909738238277359188537177)
            ·
              refine ⟨11182303678708019391402883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14909738238277359188537177 11182303678708019391402883)
              ·
                refine ⟨16773455518062029087104325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11182303678708019391402883 16773455518062029087104325)
                ·
                  refine ⟨3145022909636630453832061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16773455518062029087104325 3145022909636630453832061)
                  ·
                    refine ⟨1179383591113736420187023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3145022909636630453832061 1179383591113736420187023)
                    ·
                      rfl

theorem cell22_3445262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_3445262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445262 prefixEnd_3445262 := by exact prefixLift 3445262
  have htrace : WordTrace (prefixWord ++ tailWord_3445262) baseStart_3445262 baseEnd_3445262 := by
    simpa [prefixWord, tailWord_3445262, baseEnd_3445262] using wordTrace_append hprefix tailTrace_3445262
  have hstable : (prefixWord ++ tailWord_3445262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445262).length < 2 ^ (prefixWord ++ tailWord_3445262).sum := by decide
  have hdescent : baseEnd_3445262 < baseStart_3445262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445294 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3445294 : Nat := 118140960795 + 3445294 * 2 ^ 59
def prefixEnd_3445294 : Nat := 4983230072969 + 3 ^ 40 * 3445294 * 2
def baseEnd_3445294 : Nat := 1179394545367699003386925

theorem tailTrace_3445294 : CollatzResearch.WordTrace tailWord_3445294 prefixEnd_3445294 1179394545367699003386925 := by
  unfold tailWord_3445294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707524447536965276830867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83773463720197148143097957 15707524447536965276830867)
  ·
    refine ⟨23561286671305447915246301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15707524447536965276830867 23561286671305447915246301)
    ·
      refine ⟨8835482501739542968217363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23561286671305447915246301 8835482501739542968217363)
      ·
        refine ⟨13253223752609314452326045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8835482501739542968217363 13253223752609314452326045)
        ·
          refine ⟨4969958907228492919622267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13253223752609314452326045 4969958907228492919622267)
          ·
            refine ⟨7454938360842739379433401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969958907228492919622267 7454938360842739379433401)
            ·
              refine ⟨5591203770632054534575051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7454938360842739379433401 5591203770632054534575051)
              ·
                refine ⟨8386805655948081801862577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5591203770632054534575051 8386805655948081801862577)
                ·
                  refine ⟨6290104241961061351396933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8386805655948081801862577 6290104241961061351396933)
                  ·
                    refine ⟨1179394545367699003386925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6290104241961061351396933 1179394545367699003386925)
                    ·
                      rfl

theorem cell22_3445294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3445294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445294 prefixEnd_3445294 := by exact prefixLift 3445294
  have htrace : WordTrace (prefixWord ++ tailWord_3445294) baseStart_3445294 baseEnd_3445294 := by
    simpa [prefixWord, tailWord_3445294, baseEnd_3445294] using wordTrace_append hprefix tailTrace_3445294
  have hstable : (prefixWord ++ tailWord_3445294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445294).length < 2 ^ (prefixWord ++ tailWord_3445294).sum := by decide
  have hdescent : baseEnd_3445294 < baseStart_3445294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445324 : List Nat := [2, 2, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_3445324 : Nat := 118140960795 + 3445324 * 2 ^ 59
def prefixEnd_3445324 : Nat := 4983230072969 + 3 ^ 40 * 3445324 * 2
def baseEnd_3445324 : Nat := 1179404814980788925136833

theorem tailTrace_3445324 : CollatzResearch.WordTrace tailWord_3445324 prefixEnd_3445324 1179404814980788925136833 := by
  unfold tailWord_3445324
  simp only [CollatzResearch.WordTrace]
  refine ⟨62830644885093518669119513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83774193180124691558826017 62830644885093518669119513)
  ·
    refine ⟨47122983663820139001839635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62830644885093518669119513 47122983663820139001839635)
    ·
      refine ⟨70684475495730208502759453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47122983663820139001839635 70684475495730208502759453)
      ·
        refine ⟨26506678310898828188534795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70684475495730208502759453 26506678310898828188534795)
        ·
          refine ⟨39760017466348242282802193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26506678310898828188534795 39760017466348242282802193)
          ·
            refine ⟨29820013099761181712101645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39760017466348242282802193 29820013099761181712101645)
            ·
              refine ⟨11182504912410443142038117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29820013099761181712101645 11182504912410443142038117)
              ·
                refine ⟨2096719671076958089132147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11182504912410443142038117 2096719671076958089132147)
                ·
                  refine ⟨3145079506615437133698221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096719671076958089132147 3145079506615437133698221)
                  ·
                    refine ⟨1179404814980788925136833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3145079506615437133698221 1179404814980788925136833)
                    ·
                      rfl

theorem cell22_3445324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_3445324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445324 prefixEnd_3445324 := by exact prefixLift 3445324
  have htrace : WordTrace (prefixWord ++ tailWord_3445324) baseStart_3445324 baseEnd_3445324 := by
    simpa [prefixWord, tailWord_3445324, baseEnd_3445324] using wordTrace_append hprefix tailTrace_3445324
  have hstable : (prefixWord ++ tailWord_3445324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445324).length < 2 ^ (prefixWord ++ tailWord_3445324).sum := by decide
  have hdescent : baseEnd_3445324 < baseStart_3445324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445335 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3445335 : Nat := 118140960795 + 3445335 * 2 ^ 59
def prefixEnd_3445335 : Nat := 4983230072969 + 3 ^ 40 * 3445335 * 2
def baseEnd_3445335 : Nat := 1179408580505588563111799

theorem tailTrace_3445335 : CollatzResearch.WordTrace tailWord_3445335 prefixEnd_3445335 1179408580505588563111799 := by
  unfold tailWord_3445335
  simp only [CollatzResearch.WordTrace]
  refine ⟨125661690973147186216889459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83774460648764790811259639 125661690973147186216889459)
  ·
    refine ⟨188492536459720779325334189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125661690973147186216889459 188492536459720779325334189)
    ·
      refine ⟨70684701172395292247000321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188492536459720779325334189 70684701172395292247000321)
      ·
        refine ⟨53013525879296469185250241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70684701172395292247000321 53013525879296469185250241)
        ·
          refine ⟨39760144409472351888937681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53013525879296469185250241 39760144409472351888937681)
          ·
            refine ⟨29820108307104263916703261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39760144409472351888937681 29820108307104263916703261)
            ·
              refine ⟨11182540615164098968763723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29820108307104263916703261 11182540615164098968763723)
              ·
                refine ⟨16773810922746148453145585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11182540615164098968763723 16773810922746148453145585)
                ·
                  refine ⟨12580358192059611339859189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16773810922746148453145585 12580358192059611339859189)
                  ·
                    refine ⟨1179408580505588563111799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12580358192059611339859189 1179408580505588563111799)
                    ·
                      rfl

theorem cell22_3445335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3445335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445335 prefixEnd_3445335 := by exact prefixLift 3445335
  have htrace : WordTrace (prefixWord ++ tailWord_3445335) baseStart_3445335 baseEnd_3445335 := by
    simpa [prefixWord, tailWord_3445335, baseEnd_3445335] using wordTrace_append hprefix tailTrace_3445335
  have hstable : (prefixWord ++ tailWord_3445335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445335).length < 2 ^ (prefixWord ++ tailWord_3445335).sum := by decide
  have hdescent : baseEnd_3445335 < baseStart_3445335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445395 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 4, 4]
def baseStart_3445395 : Nat := 118140960795 + 3445395 * 2 ^ 59
def prefixEnd_3445395 : Nat := 4983230072969 + 3 ^ 40 * 3445395 * 2
def baseEnd_3445395 : Nat := 1179429119731768406611615

theorem tailTrace_3445395 : CollatzResearch.WordTrace tailWord_3445395 prefixEnd_3445395 1179429119731768406611615 := by
  unfold tailWord_3445395
  simp only [CollatzResearch.WordTrace]
  refine ⟨125663879352929816464073639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83775919568619877642715759 125663879352929816464073639)
  ·
    refine ⟨188495819029394724696110459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125663879352929816464073639 188495819029394724696110459)
    ·
      refine ⟨282743728544092087044165689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188495819029394724696110459 282743728544092087044165689)
      ·
        refine ⟨212057796408069065283124267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282743728544092087044165689 212057796408069065283124267)
        ·
          refine ⟨318086694612103597924686401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212057796408069065283124267 318086694612103597924686401)
          ·
            refine ⟨238565020959077698443514801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318086694612103597924686401 238565020959077698443514801)
            ·
              refine ⟨178923765719308273832636101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238565020959077698443514801 178923765719308273832636101)
              ·
                refine ⟨33548206072370301343619269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178923765719308273832636101 33548206072370301343619269)
                ·
                  refine ⟨6290288638569431501928613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33548206072370301343619269 6290288638569431501928613)
                  ·
                    refine ⟨1179429119731768406611615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6290288638569431501928613 1179429119731768406611615)
                    ·
                      rfl

theorem cell22_3445395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_3445395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445395 prefixEnd_3445395 := by exact prefixLift 3445395
  have htrace : WordTrace (prefixWord ++ tailWord_3445395) baseStart_3445395 baseEnd_3445395 := by
    simpa [prefixWord, tailWord_3445395, baseEnd_3445395] using wordTrace_append hprefix tailTrace_3445395
  have hstable : (prefixWord ++ tailWord_3445395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445395).length < 2 ^ (prefixWord ++ tailWord_3445395).sum := by decide
  have hdescent : baseEnd_3445395 < baseStart_3445395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445412 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_3445412 : Nat := 118140960795 + 3445412 * 2 ^ 59
def prefixEnd_3445412 : Nat := 4983230072969 + 3 ^ 40 * 3445412 * 2
def baseEnd_3445412 : Nat := 1179434939179186028936563

theorem tailTrace_3445412 : CollatzResearch.WordTrace tailWord_3445412 prefixEnd_3445412 1179434939179186028936563 := by
  unfold tailWord_3445412
  simp only [CollatzResearch.WordTrace]
  refine ⟨62832249696934114183721245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83776332929245485578294993 62832249696934114183721245)
  ·
    refine ⟨23562093636350292818895467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62832249696934114183721245 23562093636350292818895467)
    ·
      refine ⟨35343140454525439228343201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23562093636350292818895467 35343140454525439228343201)
      ·
        refine ⟨26507355340894079421257401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35343140454525439228343201 26507355340894079421257401)
        ·
          refine ⟨19880516505670559565943051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26507355340894079421257401 19880516505670559565943051)
          ·
            refine ⟨29820774758505839348914577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19880516505670559565943051 29820774758505839348914577)
            ·
              refine ⟨22365581068879379511685933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29820774758505839348914577 22365581068879379511685933)
              ·
                refine ⟨8387092900829767316882225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22365581068879379511685933 8387092900829767316882225)
                ·
                  refine ⟨6290319675622325487661669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8387092900829767316882225 6290319675622325487661669)
                  ·
                    refine ⟨1179434939179186028936563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6290319675622325487661669 1179434939179186028936563)
                    ·
                      rfl

theorem cell22_3445412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_3445412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445412 prefixEnd_3445412 := by exact prefixLift 3445412
  have htrace : WordTrace (prefixWord ++ tailWord_3445412) baseStart_3445412 baseEnd_3445412 := by
    simpa [prefixWord, tailWord_3445412, baseEnd_3445412] using wordTrace_append hprefix tailTrace_3445412
  have hstable : (prefixWord ++ tailWord_3445412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445412).length < 2 ^ (prefixWord ++ tailWord_3445412).sum := by decide
  have hdescent : baseEnd_3445412 < baseStart_3445412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445429 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3445429 : Nat := 118140960795 + 3445429 * 2 ^ 59
def prefixEnd_3445429 : Nat := 4983230072969 + 3 ^ 40 * 3445429 * 2
def baseEnd_3445429 : Nat := 1179440758626603651261511

theorem tailTrace_3445429 : CollatzResearch.WordTrace tailWord_3445429 prefixEnd_3445429 1179440758626603651261511 := by
  unfold tailWord_3445429
  simp only [CollatzResearch.WordTrace]
  refine ⟨125665119434806640270811341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83776746289871093513874227 125665119434806640270811341)
  ·
    refine ⟨47124419788052490101554253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125665119434806640270811341 47124419788052490101554253)
    ·
      refine ⟨17671657420519683788082845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47124419788052490101554253 17671657420519683788082845)
      ·
        refine ⟨6626871532694881420531067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17671657420519683788082845 6626871532694881420531067)
        ·
          refine ⟨9940307299042322130796601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6626871532694881420531067 9940307299042322130796601)
          ·
            refine ⟨7455230474281741598097451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9940307299042322130796601 7455230474281741598097451)
            ·
              refine ⟨11182845711422612397146177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7455230474281741598097451 11182845711422612397146177)
              ·
                refine ⟨8387134283566959297859633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11182845711422612397146177 8387134283566959297859633)
                ·
                  refine ⟨6290350712675219473394725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8387134283566959297859633 6290350712675219473394725)
                  ·
                    refine ⟨1179440758626603651261511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6290350712675219473394725 1179440758626603651261511)
                    ·
                      rfl

theorem cell22_3445429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3445429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445429 prefixEnd_3445429 := by exact prefixLift 3445429
  have htrace : WordTrace (prefixWord ++ tailWord_3445429) baseStart_3445429 baseEnd_3445429 := by
    simpa [prefixWord, tailWord_3445429, baseEnd_3445429] using wordTrace_append hprefix tailTrace_3445429
  have hstable : (prefixWord ++ tailWord_3445429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445429).length < 2 ^ (prefixWord ++ tailWord_3445429).sum := by decide
  have hdescent : baseEnd_3445429 < baseStart_3445429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445536 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 1, 4]
def baseStart_3445536 : Nat := 118140960795 + 3445536 * 2 ^ 59
def prefixEnd_3445536 : Nat := 4983230072969 + 3 ^ 40 * 3445536 * 2
def baseEnd_3445536 : Nat := 1179477386913291038836183

theorem tailTrace_3445536 : CollatzResearch.WordTrace tailWord_3445536 prefixEnd_3445536 1179477386913291038836183 := by
  unfold tailWord_3445536
  simp only [CollatzResearch.WordTrace]
  refine ⟨62834511022709498772478231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83779348030279331696637641 62834511022709498772478231)
  ·
    refine ⟨94251766534064248158717347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62834511022709498772478231 94251766534064248158717347)
    ·
      refine ⟨141377649801096372238076021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94251766534064248158717347 141377649801096372238076021)
      ·
        refine ⟨13254154668852784897319627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141377649801096372238076021 13254154668852784897319627)
        ·
          refine ⟨19881232003279177345979441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13254154668852784897319627 19881232003279177345979441)
          ·
            refine ⟨14910924002459383009484581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19881232003279177345979441 14910924002459383009484581)
            ·
              refine ⟨2795798250461134314278359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14910924002459383009484581 2795798250461134314278359)
              ·
                refine ⟨4193697375691701471417539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795798250461134314278359 4193697375691701471417539)
                ·
                  refine ⟨6290546063537552207126309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193697375691701471417539 6290546063537552207126309)
                  ·
                    refine ⟨1179477386913291038836183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6290546063537552207126309 1179477386913291038836183)
                    ·
                      rfl

theorem cell22_3445536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_3445536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445536 prefixEnd_3445536 := by exact prefixLift 3445536
  have htrace : WordTrace (prefixWord ++ tailWord_3445536) baseStart_3445536 baseEnd_3445536 := by
    simpa [prefixWord, tailWord_3445536, baseEnd_3445536] using wordTrace_append hprefix tailTrace_3445536
  have hstable : (prefixWord ++ tailWord_3445536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445536).length < 2 ^ (prefixWord ++ tailWord_3445536).sum := by decide
  have hdescent : baseEnd_3445536 < baseStart_3445536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445611 : List Nat := [1, 1, 1, 1, 2, 2, 4, 6, 1, 3]
def baseStart_3445611 : Nat := 118140960795 + 3445611 * 2 ^ 59
def prefixEnd_3445611 : Nat := 4983230072969 + 3 ^ 40 * 3445611 * 2
def baseEnd_3445611 : Nat := 1179503060946015843210953

theorem tailTrace_3445611 : CollatzResearch.WordTrace tailWord_3445611 prefixEnd_3445611 1179503060946015843210953 := by
  unfold tailWord_3445611
  simp only [CollatzResearch.WordTrace]
  refine ⟨125671757520147285353936687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83781171680098190235957791 125671757520147285353936687)
  ·
    refine ⟨188507636280220928030905031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125671757520147285353936687 188507636280220928030905031)
    ·
      refine ⟨282761454420331392046357547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188507636280220928030905031 282761454420331392046357547)
      ·
        refine ⟨424142181630497088069536321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282761454420331392046357547 424142181630497088069536321)
        ·
          refine ⟨318106636222872816052152241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424142181630497088069536321 318106636222872816052152241)
          ·
            refine ⟨238579977167154612039114181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318106636222872816052152241 238579977167154612039114181)
            ·
              refine ⟨44733745718841489757333909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238579977167154612039114181 44733745718841489757333909)
              ·
                refine ⟨2096894330570694832375027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44733745718841489757333909 2096894330570694832375027)
                ·
                  refine ⟨3145341495856042248562541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096894330570694832375027 3145341495856042248562541)
                  ·
                    refine ⟨1179503060946015843210953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3145341495856042248562541 1179503060946015843210953)
                    ·
                      rfl

theorem cell22_3445611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 3].length) (baseStart_3445611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445611 prefixEnd_3445611 := by exact prefixLift 3445611
  have htrace : WordTrace (prefixWord ++ tailWord_3445611) baseStart_3445611 baseEnd_3445611 := by
    simpa [prefixWord, tailWord_3445611, baseEnd_3445611] using wordTrace_append hprefix tailTrace_3445611
  have hstable : (prefixWord ++ tailWord_3445611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445611).length < 2 ^ (prefixWord ++ tailWord_3445611).sum := by decide
  have hdescent : baseEnd_3445611 < baseStart_3445611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445709 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3445709 : Nat := 118140960795 + 3445709 * 2 ^ 59
def prefixEnd_3445709 : Nat := 4983230072969 + 3 ^ 40 * 3445709 * 2
def baseEnd_3445709 : Nat := 393178869449592084753551

theorem tailTrace_3445709 : CollatzResearch.WordTrace tailWord_3445709 prefixEnd_3445709 393178869449592084753551 := by
  unfold tailWord_3445709
  simp only [CollatzResearch.WordTrace]
  refine ⟨125675331873792248091004181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83783554582528165394002787 125675331873792248091004181)
  ·
    refine ⟨5891031181584011629265821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125675331873792248091004181 5891031181584011629265821)
    ·
      refine ⟨2209136693094004360974683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5891031181584011629265821 2209136693094004360974683)
      ·
        refine ⟨3313705039641006541462025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209136693094004360974683 3313705039641006541462025)
        ·
          refine ⟨2485278779730754906096519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313705039641006541462025 2485278779730754906096519)
          ·
            refine ⟨3727918169596132359144779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485278779730754906096519 3727918169596132359144779)
            ·
              refine ⟨5591877254394198538717169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727918169596132359144779 5591877254394198538717169)
              ·
                refine ⟨4193907940795648904037877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5591877254394198538717169 4193907940795648904037877)
                ·
                  refine ⟨393178869449592084753551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4193907940795648904037877 393178869449592084753551)
                  ·
                    rfl

theorem cell22_3445709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3445709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445709 prefixEnd_3445709 := by exact prefixLift 3445709
  have htrace : WordTrace (prefixWord ++ tailWord_3445709) baseStart_3445709 baseEnd_3445709 := by
    simpa [prefixWord, tailWord_3445709, baseEnd_3445709] using wordTrace_append hprefix tailTrace_3445709
  have hstable : (prefixWord ++ tailWord_3445709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445709).length < 2 ^ (prefixWord ++ tailWord_3445709).sum := by decide
  have hdescent : baseEnd_3445709 < baseStart_3445709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445735 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3445735 : Nat := 118140960795 + 3445735 * 2 ^ 59
def prefixEnd_3445735 : Nat := 4983230072969 + 3 ^ 40 * 3445735 * 2
def baseEnd_3445735 : Nat := 1179545508680120853110573

theorem tailTrace_3445735 : CollatzResearch.WordTrace tailWord_3445735 prefixEnd_3445735 1179545508680120853110573 := by
  unfold tailWord_3445735
  simp only [CollatzResearch.WordTrace]
  refine ⟨125676280171698054531450659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83784186781132036354300439 125676280171698054531450659)
  ·
    refine ⟨188514420257547081797175989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125676280171698054531450659 188514420257547081797175989)
    ·
      refine ⟨17673226899145038918485249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188514420257547081797175989 17673226899145038918485249)
      ·
        refine ⟨13254920174358779188863937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17673226899145038918485249 13254920174358779188863937)
        ·
          refine ⟨9941190130769084391647953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13254920174358779188863937 9941190130769084391647953)
          ·
            refine ⟨7455892598076813293735965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9941190130769084391647953 7455892598076813293735965)
            ·
              refine ⟨2795959724278804985150987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7455892598076813293735965 2795959724278804985150987)
              ·
                refine ⟨4193939586418207477726481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795959724278804985150987 4193939586418207477726481)
                ·
                  refine ⟨3145454689813655608294861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193939586418207477726481 3145454689813655608294861)
                  ·
                    refine ⟨1179545508680120853110573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3145454689813655608294861 1179545508680120853110573)
                    ·
                      rfl

theorem cell22_3445735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3445735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445735 prefixEnd_3445735 := by exact prefixLift 3445735
  have htrace : WordTrace (prefixWord ++ tailWord_3445735) baseStart_3445735 baseEnd_3445735 := by
    simpa [prefixWord, tailWord_3445735, baseEnd_3445735] using wordTrace_append hprefix tailTrace_3445735
  have hstable : (prefixWord ++ tailWord_3445735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445735).length < 2 ^ (prefixWord ++ tailWord_3445735).sum := by decide
  have hdescent : baseEnd_3445735 < baseStart_3445735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445793 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 5]
def baseStart_3445793 : Nat := 118140960795 + 3445793 * 2 ^ 59
def prefixEnd_3445793 : Nat := 4983230072969 + 3 ^ 40 * 3445793 * 2
def baseEnd_3445793 : Nat := 393188454421809345053465

theorem tailTrace_3445793 : CollatzResearch.WordTrace tailWord_3445793 prefixEnd_3445793 393188454421809345053465 := by
  unfold tailWord_3445793
  simp only [CollatzResearch.WordTrace]
  refine ⟨125678395605487930437062033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83785597070325286958041355 125678395605487930437062033)
  ·
    refine ⟨94258796704115947827796525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125678395605487930437062033 94258796704115947827796525)
    ·
      refine ⟨35347048764043480435423697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94258796704115947827796525 35347048764043480435423697)
      ·
        refine ⟨26510286573032610326567773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35347048764043480435423697 26510286573032610326567773)
        ·
          refine ⟨9941357464887228872462915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26510286573032610326567773 9941357464887228872462915)
          ·
            refine ⟨14912036197330843308694373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9941357464887228872462915 14912036197330843308694373)
            ·
              refine ⟨2796006786999533120380195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14912036197330843308694373 2796006786999533120380195)
              ·
                refine ⟨4194010180499299680570293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796006786999533120380195 4194010180499299680570293)
                ·
                  refine ⟨393188454421809345053465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4194010180499299680570293 393188454421809345053465)
                  ·
                    rfl

theorem cell22_3445793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_3445793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445793 prefixEnd_3445793 := by exact prefixLift 3445793
  have htrace : WordTrace (prefixWord ++ tailWord_3445793) baseStart_3445793 baseEnd_3445793 := by
    simpa [prefixWord, tailWord_3445793, baseEnd_3445793] using wordTrace_append hprefix tailTrace_3445793
  have hstable : (prefixWord ++ tailWord_3445793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445793).length < 2 ^ (prefixWord ++ tailWord_3445793).sum := by decide
  have hdescent : baseEnd_3445793 < baseStart_3445793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445804 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 8]
def baseStart_3445804 : Nat := 118140960795 + 3445804 * 2 ^ 59
def prefixEnd_3445804 : Nat := 4983230072969 + 3 ^ 40 * 3445804 * 2
def baseEnd_3445804 : Nat := 393189709596742557711787

theorem tailTrace_3445804 : CollatzResearch.WordTrace tailWord_3445804 prefixEnd_3445804 393189709596742557711787 := by
  unfold tailWord_3445804
  simp only [CollatzResearch.WordTrace]
  refine ⟨62839398404224039657856233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83785864538965386210474977 62839398404224039657856233)
  ·
    refine ⟨47129548803168029743392175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62839398404224039657856233 47129548803168029743392175)
    ·
      refine ⟨70694323204752044615088263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47129548803168029743392175 70694323204752044615088263)
      ·
        refine ⟨106041484807128066922632395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70694323204752044615088263 106041484807128066922632395)
        ·
          refine ⟨159062227210692100383948593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106041484807128066922632395 159062227210692100383948593)
          ·
            refine ⟨119296670408019075287961445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159062227210692100383948593 119296670408019075287961445)
            ·
              refine ⟨22368125701503576616492771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119296670408019075287961445 22368125701503576616492771)
              ·
                refine ⟨33552188552255364924739157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22368125701503576616492771 33552188552255364924739157)
                ·
                  refine ⟨393189709596742557711787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33552188552255364924739157 393189709596742557711787)
                  ·
                    rfl

theorem cell22_3445804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_3445804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445804 prefixEnd_3445804 := by exact prefixLift 3445804
  have htrace : WordTrace (prefixWord ++ tailWord_3445804) baseStart_3445804 baseEnd_3445804 := by
    simpa [prefixWord, tailWord_3445804, baseEnd_3445804] using wordTrace_append hprefix tailTrace_3445804
  have hstable : (prefixWord ++ tailWord_3445804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445804).length < 2 ^ (prefixWord ++ tailWord_3445804).sum := by decide
  have hdescent : baseEnd_3445804 < baseStart_3445804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445838 : List Nat := [4, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_3445838 : Nat := 118140960795 + 3445838 * 2 ^ 59
def prefixEnd_3445838 : Nat := 4983230072969 + 3 ^ 40 * 3445838 * 2
def baseEnd_3445838 : Nat := 393193589228354305928419

theorem tailTrace_3445838 : CollatzResearch.WordTrace tailWord_3445838 prefixEnd_3445838 393193589228354305928419 := by
  unfold tailWord_3445838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15710004611290612890306271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83786691260216602081633445 15710004611290612890306271)
  ·
    refine ⟨23565006916935919335459407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15710004611290612890306271 23565006916935919335459407)
    ·
      refine ⟨35347510375403879003189111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23565006916935919335459407 35347510375403879003189111)
      ·
        refine ⟨53021265563105818504783667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35347510375403879003189111 53021265563105818504783667)
        ·
          refine ⟨79531898344658727757175501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53021265563105818504783667 79531898344658727757175501)
          ·
            refine ⟨29824461879247022908940813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79531898344658727757175501 29824461879247022908940813)
            ·
              refine ⟨11184173204717633590852805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29824461879247022908940813 11184173204717633590852805)
              ·
                refine ⟨2097032475884556298284901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11184173204717633590852805 2097032475884556298284901)
                ·
                  refine ⟨393193589228354305928419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097032475884556298284901 393193589228354305928419)
                  ·
                    rfl

theorem cell22_3445838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_3445838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445838 prefixEnd_3445838 := by exact prefixLift 3445838
  have htrace : WordTrace (prefixWord ++ tailWord_3445838) baseStart_3445838 baseEnd_3445838 := by
    simpa [prefixWord, tailWord_3445838, baseEnd_3445838] using wordTrace_append hprefix tailTrace_3445838
  have hstable : (prefixWord ++ tailWord_3445838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445838).length < 2 ^ (prefixWord ++ tailWord_3445838).sum := by decide
  have hdescent : baseEnd_3445838 < baseStart_3445838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445849 : List Nat := [1, 2, 1, 2, 2, 1, 2, 11]
def baseStart_3445849 : Nat := 118140960795 + 3445849 * 2 ^ 59
def prefixEnd_3445849 : Nat := 4983230072969 + 3 ^ 40 * 3445849 * 2
def baseEnd_3445849 : Nat := 131064948134429172862247

theorem tailTrace_3445849 : CollatzResearch.WordTrace tailWord_3445849 prefixEnd_3445849 131064948134429172862247 := by
  unfold tailWord_3445849
  simp only [CollatzResearch.WordTrace]
  refine ⟨125680438093285052001100601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83786958728856701334067067 125680438093285052001100601)
  ·
    refine ⟨94260328569963789000825451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125680438093285052001100601 94260328569963789000825451)
    ·
      refine ⟨141390492854945683501238177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94260328569963789000825451 141390492854945683501238177)
      ·
        refine ⟨106042869641209262625928633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141390492854945683501238177 106042869641209262625928633)
        ·
          refine ⟨79532152230906946969446475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106042869641209262625928633 79532152230906946969446475)
          ·
            refine ⟨119298228346360420454169713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79532152230906946969446475 119298228346360420454169713)
            ·
              refine ⟨89473671259770315340627285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119298228346360420454169713 89473671259770315340627285)
              ·
                refine ⟨131064948134429172862247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 89473671259770315340627285 131064948134429172862247)
                ·
                  rfl

theorem cell22_3445849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 11].length) (baseStart_3445849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445849 prefixEnd_3445849 := by exact prefixLift 3445849
  have htrace : WordTrace (prefixWord ++ tailWord_3445849) baseStart_3445849 baseEnd_3445849 := by
    simpa [prefixWord, tailWord_3445849, baseEnd_3445849] using wordTrace_append hprefix tailTrace_3445849
  have hstable : (prefixWord ++ tailWord_3445849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445849).length < 2 ^ (prefixWord ++ tailWord_3445849).sum := by decide
  have hdescent : baseEnd_3445849 < baseStart_3445849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3445988 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_3445988 : Nat := 118140960795 + 3445988 * 2 ^ 59
def prefixEnd_3445988 : Nat := 4983230072969 + 3 ^ 40 * 3445988 * 2
def baseEnd_3445988 : Nat := 1179632115750512526534797

theorem tailTrace_3445988 : CollatzResearch.WordTrace tailWord_3445988 prefixEnd_3445988 1179632115750512526534797 := by
  unfold tailWord_3445988
  simp only [CollatzResearch.WordTrace]
  refine ⟨62842753919890739370205309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83790338559854319160273745 62842753919890739370205309)
  ·
    refine ⟨23566032719959027263826991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62842753919890739370205309 23566032719959027263826991)
    ·
      refine ⟨35349049079938540895740487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23566032719959027263826991 35349049079938540895740487)
      ·
        refine ⟨53023573619907811343610731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35349049079938540895740487 53023573619907811343610731)
        ·
          refine ⟨79535360429861717015416097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53023573619907811343610731 79535360429861717015416097)
          ·
            refine ⟨59651520322396287761562073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79535360429861717015416097 59651520322396287761562073)
            ·
              refine ⟨44738640241797215821171555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59651520322396287761562073 44738640241797215821171555)
              ·
                refine ⟨67107960362695823731757333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44738640241797215821171555 67107960362695823731757333)
                ·
                  refine ⟨3145685642001366737426125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67107960362695823731757333 3145685642001366737426125)
                  ·
                    refine ⟨1179632115750512526534797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3145685642001366737426125 1179632115750512526534797)
                    ·
                      rfl

theorem cell22_3445988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_3445988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3445988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3445988 prefixEnd_3445988 := by exact prefixLift 3445988
  have htrace : WordTrace (prefixWord ++ tailWord_3445988) baseStart_3445988 baseEnd_3445988 := by
    simpa [prefixWord, tailWord_3445988, baseEnd_3445988] using wordTrace_append hprefix tailTrace_3445988
  have hstable : (prefixWord ++ tailWord_3445988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3445988).length < 2 ^ (prefixWord ++ tailWord_3445988).sum := by decide
  have hdescent : baseEnd_3445988 < baseStart_3445988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3445988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446003 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 2, 4]
def baseStart_3446003 : Nat := 118140960795 + 3446003 * 2 ^ 59
def prefixEnd_3446003 : Nat := 4983230072969 + 3 ^ 40 * 3446003 * 2
def baseEnd_3446003 : Nat := 1179637250557057487409751

theorem tailTrace_3446003 : CollatzResearch.WordTrace tailWord_3446003 prefixEnd_3446003 1179637250557057487409751 := by
  unfold tailWord_3446003
  simp only [CollatzResearch.WordTrace]
  refine ⟨125686054934727136302206663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83790703289818090868137775 125686054934727136302206663)
  ·
    refine ⟨188529082402090704453309995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125686054934727136302206663 188529082402090704453309995)
    ·
      refine ⟨282793623603136056679964993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188529082402090704453309995 282793623603136056679964993)
      ·
        refine ⟨212095217702352042509973745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282793623603136056679964993 212095217702352042509973745)
        ·
          refine ⟨159071413276764031882480309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212095217702352042509973745 159071413276764031882480309)
          ·
            refine ⟨14912944994696627988982529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159071413276764031882480309 14912944994696627988982529)
            ·
              refine ⟨11184708746022470991736897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14912944994696627988982529 11184708746022470991736897)
              ·
                refine ⟨8388531559516853243802673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11184708746022470991736897 8388531559516853243802673)
                ·
                  refine ⟨6291398669637639932852005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388531559516853243802673 6291398669637639932852005)
                  ·
                    refine ⟨1179637250557057487409751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6291398669637639932852005 1179637250557057487409751)
                    ·
                      rfl

theorem cell22_3446003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_3446003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446003 prefixEnd_3446003 := by exact prefixLift 3446003
  have htrace : WordTrace (prefixWord ++ tailWord_3446003) baseStart_3446003 baseEnd_3446003 := by
    simpa [prefixWord, tailWord_3446003, baseEnd_3446003] using wordTrace_append hprefix tailTrace_3446003
  have hstable : (prefixWord ++ tailWord_3446003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446003).length < 2 ^ (prefixWord ++ tailWord_3446003).sum := by decide
  have hdescent : baseEnd_3446003 < baseStart_3446003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446016 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_3446016 : Nat := 118140960795 + 3446016 * 2 ^ 59
def prefixEnd_3446016 : Nat := 4983230072969 + 3 ^ 40 * 3446016 * 2
def baseEnd_3446016 : Nat := 1179641700722729786834711

theorem tailTrace_3446016 : CollatzResearch.WordTrace tailWord_3446016 prefixEnd_3446016 1179641700722729786834711 := by
  unfold tailWord_3446016
  simp only [CollatzResearch.WordTrace]
  refine ⟨62843264541840019761214951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83791019389120026348286601 62843264541840019761214951)
  ·
    refine ⟨94264896812760029641822427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62843264541840019761214951 94264896812760029641822427)
    ·
      refine ⟨141397345219140044462733641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94264896812760029641822427 141397345219140044462733641)
      ·
        refine ⟨106048008914355033347050231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141397345219140044462733641 106048008914355033347050231)
        ·
          refine ⟨159072013371532550020575347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106048008914355033347050231 159072013371532550020575347)
          ·
            refine ⟨238608020057298825030863021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159072013371532550020575347 238608020057298825030863021)
            ·
              refine ⟨89478007521487059386573633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238608020057298825030863021 89478007521487059386573633)
              ·
                refine ⟨67108505641115294539930225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89478007521487059386573633 67108505641115294539930225)
                ·
                  refine ⟨50331379230836470904947669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67108505641115294539930225 50331379230836470904947669)
                  ·
                    refine ⟨1179641700722729786834711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50331379230836470904947669 1179641700722729786834711)
                    ·
                      rfl

theorem cell22_3446016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_3446016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446016 prefixEnd_3446016 := by exact prefixLift 3446016
  have htrace : WordTrace (prefixWord ++ tailWord_3446016) baseStart_3446016 baseEnd_3446016 := by
    simpa [prefixWord, tailWord_3446016, baseEnd_3446016] using wordTrace_append hprefix tailTrace_3446016
  have hstable : (prefixWord ++ tailWord_3446016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446016).length < 2 ^ (prefixWord ++ tailWord_3446016).sum := by decide
  have hdescent : baseEnd_3446016 < baseStart_3446016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446067 : List Nat := [1, 1, 1, 2, 5, 2, 2, 4, 1, 3]
def baseStart_3446067 : Nat := 118140960795 + 3446067 * 2 ^ 59
def prefixEnd_3446067 : Nat := 4983230072969 + 3 ^ 40 * 3446067 * 2
def baseEnd_3446067 : Nat := 1179659159064982653809555

theorem tailTrace_3446067 : CollatzResearch.WordTrace tailWord_3446067 prefixEnd_3446067 1179659159064982653809555 := by
  unfold tailWord_3446067
  simp only [CollatzResearch.WordTrace]
  refine ⟨125688389206495275232536455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83792259470996850155024303 125688389206495275232536455)
  ·
    refine ⟨188532583809742912848804683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125688389206495275232536455 188532583809742912848804683)
    ·
      refine ⟨282798875714614369273207025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188532583809742912848804683 282798875714614369273207025)
      ·
        refine ⟨212099156785960776954905269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282798875714614369273207025 212099156785960776954905269)
        ·
          refine ⟨19884295948683822839522369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212099156785960776954905269 19884295948683822839522369)
          ·
            refine ⟨14913221961512867129641777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19884295948683822839522369 14913221961512867129641777)
            ·
              refine ⟨11184916471134650347231333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14913221961512867129641777 11184916471134650347231333)
              ·
                refine ⟨2097171838337746940105875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11184916471134650347231333 2097171838337746940105875)
                ·
                  refine ⟨3145757757506620410158813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097171838337746940105875 3145757757506620410158813)
                  ·
                    refine ⟨1179659159064982653809555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3145757757506620410158813 1179659159064982653809555)
                    ·
                      rfl

theorem cell22_3446067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 3].length) (baseStart_3446067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446067 prefixEnd_3446067 := by exact prefixLift 3446067
  have htrace : WordTrace (prefixWord ++ tailWord_3446067) baseStart_3446067 baseEnd_3446067 := by
    simpa [prefixWord, tailWord_3446067, baseEnd_3446067] using wordTrace_append hprefix tailTrace_3446067
  have hstable : (prefixWord ++ tailWord_3446067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446067).length < 2 ^ (prefixWord ++ tailWord_3446067).sum := by decide
  have hdescent : baseEnd_3446067 < baseStart_3446067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446080 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 5]
def baseStart_3446080 : Nat := 118140960795 + 3446080 * 2 ^ 59
def prefixEnd_3446080 : Nat := 4983230072969 + 3 ^ 40 * 3446080 * 2
def baseEnd_3446080 : Nat := 393221203076884984411505

theorem tailTrace_3446080 : CollatzResearch.WordTrace tailWord_3446080 prefixEnd_3446080 393221203076884984411505 := by
  unfold tailWord_3446080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62844431677724089226379847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83792575570298785635173129 62844431677724089226379847)
  ·
    refine ⟨94266647516586133839569771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62844431677724089226379847 94266647516586133839569771)
    ·
      refine ⟨141399971274879200759354657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94266647516586133839569771 141399971274879200759354657)
      ·
        refine ⟨106049978456159400569515993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141399971274879200759354657 106049978456159400569515993)
        ·
          refine ⟨79537483842119550427136995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106049978456159400569515993 79537483842119550427136995)
          ·
            refine ⟨119306225763179325640705493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79537483842119550427136995 119306225763179325640705493)
            ·
              refine ⟨2796239666324515444704035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119306225763179325640705493 2796239666324515444704035)
              ·
                refine ⟨4194359499486773167056053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796239666324515444704035 4194359499486773167056053)
                ·
                  refine ⟨393221203076884984411505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4194359499486773167056053 393221203076884984411505)
                  ·
                    rfl

theorem cell22_3446080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_3446080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446080 prefixEnd_3446080 := by exact prefixLift 3446080
  have htrace : WordTrace (prefixWord ++ tailWord_3446080) baseStart_3446080 baseEnd_3446080 := by
    simpa [prefixWord, tailWord_3446080, baseEnd_3446080] using wordTrace_append hprefix tailTrace_3446080
  have hstable : (prefixWord ++ tailWord_3446080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446080).length < 2 ^ (prefixWord ++ tailWord_3446080).sum := by decide
  have hdescent : baseEnd_3446080 < baseStart_3446080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446086 : List Nat := [6, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3446086 : Nat := 118140960795 + 3446086 * 2 ^ 59
def prefixEnd_3446086 : Nat := 4983230072969 + 3 ^ 40 * 3446086 * 2
def baseEnd_3446086 : Nat := 131073962572585881953833

theorem tailTrace_3446086 : CollatzResearch.WordTrace tailWord_3446086 prefixEnd_3446086 131073962572585881953833 := by
  unfold tailWord_3446086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927783818544576296171191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83792721462284294318318741 3927783818544576296171191)
  ·
    refine ⟨5891675727816864444256787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3927783818544576296171191 5891675727816864444256787)
    ·
      refine ⟨8837513591725296666385181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5891675727816864444256787 8837513591725296666385181)
      ·
        refine ⟨3314067596896986249894443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8837513591725296666385181 3314067596896986249894443)
        ·
          refine ⟨4971101395345479374841665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314067596896986249894443 4971101395345479374841665)
          ·
            refine ⟨3728326046509109531131249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4971101395345479374841665 3728326046509109531131249)
            ·
              refine ⟨2796244534881832148348437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728326046509109531131249 2796244534881832148348437)
              ·
                refine ⟨131073962572585881953833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2796244534881832148348437 131073962572585881953833)
                ·
                  rfl

theorem cell22_3446086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3446086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446086 prefixEnd_3446086 := by exact prefixLift 3446086
  have htrace : WordTrace (prefixWord ++ tailWord_3446086) baseStart_3446086 baseEnd_3446086 := by
    simpa [prefixWord, tailWord_3446086, baseEnd_3446086] using wordTrace_append hprefix tailTrace_3446086
  have hstable : (prefixWord ++ tailWord_3446086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446086).length < 2 ^ (prefixWord ++ tailWord_3446086).sum := by decide
  have hdescent : baseEnd_3446086 < baseStart_3446086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446125 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3446125 : Nat := 118140960795 + 3446125 * 2 ^ 59
def prefixEnd_3446125 : Nat := 4983230072969 + 3 ^ 40 * 3446125 * 2
def baseEnd_3446125 : Nat := 393226337883429945286459

theorem tailTrace_3446125 : CollatzResearch.WordTrace tailWord_3446125 prefixEnd_3446125 393226337883429945286459 := by
  unfold tailWord_3446125
  simp only [CollatzResearch.WordTrace]
  refine ⟨125690504640285151138147829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83793669760190100758765219 125690504640285151138147829)
  ·
    refine ⟨11783484810026732919201359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125690504640285151138147829 11783484810026732919201359)
    ·
      refine ⟨17675227215040099378802039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783484810026732919201359 17675227215040099378802039)
      ·
        refine ⟨26512840822560149068203059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17675227215040099378802039 26512840822560149068203059)
        ·
          refine ⟨39769261233840223602304589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26512840822560149068203059 39769261233840223602304589)
          ·
            refine ⟨14913472962690083850864221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39769261233840223602304589 14913472962690083850864221)
            ·
              refine ⟨5592552361008781444074083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14913472962690083850864221 5592552361008781444074083)
              ·
                refine ⟨8388828541513172166111125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5592552361008781444074083 8388828541513172166111125)
                ·
                  refine ⟨393226337883429945286459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8388828541513172166111125 393226337883429945286459)
                  ·
                    rfl

theorem cell22_3446125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3446125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446125 prefixEnd_3446125 := by exact prefixLift 3446125
  have htrace : WordTrace (prefixWord ++ tailWord_3446125) baseStart_3446125 baseEnd_3446125 := by
    simpa [prefixWord, tailWord_3446125, baseEnd_3446125] using wordTrace_append hprefix tailTrace_3446125
  have hstable : (prefixWord ++ tailWord_3446125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446125).length < 2 ^ (prefixWord ++ tailWord_3446125).sum := by decide
  have hdescent : baseEnd_3446125 < baseStart_3446125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446155 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 2, 4]
def baseStart_3446155 : Nat := 118140960795 + 3446155 * 2 ^ 59
def prefixEnd_3446155 : Nat := 4983230072969 + 3 ^ 40 * 3446155 * 2
def baseEnd_3446155 : Nat := 1179689283263379757609285

theorem tailTrace_3446155 : CollatzResearch.WordTrace tailWord_3446155 prefixEnd_3446155 1179689283263379757609285 := by
  unfold tailWord_3446155
  simp only [CollatzResearch.WordTrace]
  refine ⟨125691598830176466261739919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83794399220117644174493279 125691598830176466261739919)
  ·
    refine ⟨188537398245264699392609879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125691598830176466261739919 188537398245264699392609879)
    ·
      refine ⟨282806097367897049088914819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188537398245264699392609879 282806097367897049088914819)
      ·
        refine ⟨424209146051845573633372229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282806097367897049088914819 424209146051845573633372229)
        ·
          refine ⟨79539214884721045056257293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424209146051845573633372229 79539214884721045056257293)
          ·
            refine ⟨29827205581770391896096485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79539214884721045056257293 29827205581770391896096485)
            ·
              refine ⟨5592601046581948480518091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29827205581770391896096485 5592601046581948480518091)
              ·
                refine ⟨8388901569872922720777137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5592601046581948480518091 8388901569872922720777137)
                ·
                  refine ⟨6291676177404692040582853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8388901569872922720777137 6291676177404692040582853)
                  ·
                    refine ⟨1179689283263379757609285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6291676177404692040582853 1179689283263379757609285)
                    ·
                      rfl

theorem cell22_3446155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 4].length) (baseStart_3446155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446155 prefixEnd_3446155 := by exact prefixLift 3446155
  have htrace : WordTrace (prefixWord ++ tailWord_3446155) baseStart_3446155 baseEnd_3446155 := by
    simpa [prefixWord, tailWord_3446155, baseEnd_3446155] using wordTrace_append hprefix tailTrace_3446155
  have hstable : (prefixWord ++ tailWord_3446155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446155).length < 2 ^ (prefixWord ++ tailWord_3446155).sum := by decide
  have hdescent : baseEnd_3446155 < baseStart_3446155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446210 : List Nat := [3, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3446210 : Nat := 118140960795 + 3446210 * 2 ^ 59
def prefixEnd_3446210 : Nat := 4983230072969 + 3 ^ 40 * 3446210 * 2
def baseEnd_3446210 : Nat := 393236036962459315828039

theorem tailTrace_3446210 : CollatzResearch.WordTrace tailWord_3446210 prefixEnd_3446210 393236036962459315828039 := by
  unfold tailWord_3446210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31423401211244302663748021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83795736563318140436661389 31423401211244302663748021)
  ·
    refine ⟨2945943863554153374726377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31423401211244302663748021 2945943863554153374726377)
    ·
      refine ⟨2209457897665615031044783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2945943863554153374726377 2209457897665615031044783)
      ·
        refine ⟨3314186846498422546567175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209457897665615031044783 3314186846498422546567175)
        ·
          refine ⟨4971280269747633819850763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314186846498422546567175 4971280269747633819850763)
          ·
            refine ⟨7456920404621450729776145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971280269747633819850763 7456920404621450729776145)
            ·
              refine ⟨5592690303466088047332109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7456920404621450729776145 5592690303466088047332109)
              ·
                refine ⟨2097258863799783017749541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5592690303466088047332109 2097258863799783017749541)
                ·
                  refine ⟨393236036962459315828039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097258863799783017749541 393236036962459315828039)
                  ·
                    rfl

theorem cell22_3446210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3446210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446210 prefixEnd_3446210 := by exact prefixLift 3446210
  have htrace : WordTrace (prefixWord ++ tailWord_3446210) baseStart_3446210 baseEnd_3446210 := by
    simpa [prefixWord, tailWord_3446210, baseEnd_3446210] using wordTrace_append hprefix tailTrace_3446210
  have hstable : (prefixWord ++ tailWord_3446210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446210).length < 2 ^ (prefixWord ++ tailWord_3446210).sum := by decide
  have hdescent : baseEnd_3446210 < baseStart_3446210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446270 : List Nat := [4, 2, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3446270 : Nat := 118140960795 + 3446270 * 2 ^ 59
def prefixEnd_3446270 : Nat := 4983230072969 + 3 ^ 40 * 3446270 * 2
def baseEnd_3446270 : Nat := 1179728650113557790983933

theorem tailTrace_3446270 : CollatzResearch.WordTrace tailWord_3446270 prefixEnd_3446270 1179728650113557790983933 := by
  unfold tailWord_3446270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15711974153094980112772033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83797195483173227268117509 15711974153094980112772033)
  ·
    refine ⟨11783980614821235084579025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15711974153094980112772033 11783980614821235084579025)
    ·
      refine ⟨8837985461115926313434269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11783980614821235084579025 8837985461115926313434269)
      ·
        refine ⟨3314244547918472367537851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8837985461115926313434269 3314244547918472367537851)
        ·
          refine ⟨4971366821877708551306777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314244547918472367537851 4971366821877708551306777)
          ·
            refine ⟨3728525116408281413480083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4971366821877708551306777 3728525116408281413480083)
            ·
              refine ⟨5592787674612422120220125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728525116408281413480083 5592787674612422120220125)
              ·
                refine ⟨2097295377979658295082547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5592787674612422120220125 2097295377979658295082547)
                ·
                  refine ⟨3145943066969487442623821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097295377979658295082547 3145943066969487442623821)
                  ·
                    refine ⟨1179728650113557790983933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3145943066969487442623821 1179728650113557790983933)
                    ·
                      rfl

theorem cell22_3446270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3446270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446270 prefixEnd_3446270 := by exact prefixLift 3446270
  have htrace : WordTrace (prefixWord ++ tailWord_3446270) baseStart_3446270 baseEnd_3446270 := by
    simpa [prefixWord, tailWord_3446270, baseEnd_3446270] using wordTrace_append hprefix tailTrace_3446270
  have hstable : (prefixWord ++ tailWord_3446270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446270).length < 2 ^ (prefixWord ++ tailWord_3446270).sum := by decide
  have hdescent : baseEnd_3446270 < baseStart_3446270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446305 : List Nat := [1, 2, 3, 2, 2, 2, 1, 9]
def baseStart_3446305 : Nat := 118140960795 + 3446305 * 2 ^ 59
def prefixEnd_3446305 : Nat := 4983230072969 + 3 ^ 40 * 3446305 * 2
def baseEnd_3446305 : Nat := 131082292369869929595425

theorem tailTrace_3446305 : CollatzResearch.WordTrace tailWord_3446305 prefixEnd_3446305 131082292369869929595425 := by
  unfold tailWord_3446305
  simp only [CollatzResearch.WordTrace]
  refine ⟨125697069779633041879700369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83798046519755361253133579 125697069779633041879700369)
  ·
    refine ⟨94272802334724781409775277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125697069779633041879700369 94272802334724781409775277)
    ·
      refine ⟨35352300875521793028665729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94272802334724781409775277 35352300875521793028665729)
      ·
        refine ⟨26514225656641344771499297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35352300875521793028665729 26514225656641344771499297)
        ·
          refine ⟨19885669242481008578624473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26514225656641344771499297 19885669242481008578624473)
          ·
            refine ⟨14914251931860756433968355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19885669242481008578624473 14914251931860756433968355)
            ·
              refine ⟨22371377897791134650952533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14914251931860756433968355 22371377897791134650952533)
              ·
                refine ⟨131082292369869929595425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22371377897791134650952533 131082292369869929595425)
                ·
                  rfl

theorem cell22_3446305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 9].length) (baseStart_3446305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446305 prefixEnd_3446305 := by exact prefixLift 3446305
  have htrace : WordTrace (prefixWord ++ tailWord_3446305) baseStart_3446305 baseEnd_3446305 := by
    simpa [prefixWord, tailWord_3446305, baseEnd_3446305] using wordTrace_append hprefix tailTrace_3446305
  have hstable : (prefixWord ++ tailWord_3446305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446305).length < 2 ^ (prefixWord ++ tailWord_3446305).sum := by decide
  have hdescent : baseEnd_3446305 < baseStart_3446305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446395 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 8]
def baseStart_3446395 : Nat := 118140960795 + 3446395 * 2 ^ 59
def prefixEnd_3446395 : Nat := 4983230072969 + 3 ^ 40 * 3446395 * 2
def baseEnd_3446395 : Nat := 393257146722699710536183

theorem tailTrace_3446395 : CollatzResearch.WordTrace tailWord_3446395 prefixEnd_3446395 393257146722699710536183 := by
  unfold tailWord_3446395
  simp only [CollatzResearch.WordTrace]
  refine ⟨125700352349306987250476639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83800234899537991500317759 125700352349306987250476639)
  ·
    refine ⟨188550528523960480875714959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125700352349306987250476639 188550528523960480875714959)
    ·
      refine ⟨282825792785940721313572439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188550528523960480875714959 282825792785940721313572439)
      ·
        refine ⟨424238689178911081970358659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282825792785940721313572439 424238689178911081970358659)
        ·
          refine ⟨636358033768366622955537989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424238689178911081970358659 636358033768366622955537989)
          ·
            refine ⟨119317131331568741804163373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 636358033768366622955537989 119317131331568741804163373)
            ·
              refine ⟨44743924249338278176561265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119317131331568741804163373 44743924249338278176561265)
              ·
                refine ⟨33557943187003708632420949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44743924249338278176561265 33557943187003708632420949)
                ·
                  refine ⟨393257146722699710536183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33557943187003708632420949 393257146722699710536183)
                  ·
                    rfl

theorem cell22_3446395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_3446395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446395 prefixEnd_3446395 := by exact prefixLift 3446395
  have htrace : WordTrace (prefixWord ++ tailWord_3446395) baseStart_3446395 baseEnd_3446395 := by
    simpa [prefixWord, tailWord_3446395, baseEnd_3446395] using wordTrace_append hprefix tailTrace_3446395
  have hstable : (prefixWord ++ tailWord_3446395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446395).length < 2 ^ (prefixWord ++ tailWord_3446395).sum := by decide
  have hdescent : baseEnd_3446395 < baseStart_3446395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446412 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 6]
def baseStart_3446412 : Nat := 118140960795 + 3446412 * 2 ^ 59
def prefixEnd_3446412 : Nat := 4983230072969 + 3 ^ 40 * 3446412 * 2
def baseEnd_3446412 : Nat := 393259086538505584644499

theorem tailTrace_3446412 : CollatzResearch.WordTrace tailWord_3446412 prefixEnd_3446412 393259086538505584644499 := by
  unfold tailWord_3446412
  simp only [CollatzResearch.WordTrace]
  refine ⟨62850486195122699576922745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83800648260163599435896993 62850486195122699576922745)
  ·
    refine ⟨47137864646342024682692059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62850486195122699576922745 47137864646342024682692059)
    ·
      refine ⟨70706796969513037024038089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47137864646342024682692059 70706796969513037024038089)
      ·
        refine ⟨53030097727134777768028567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70706796969513037024038089 53030097727134777768028567)
        ·
          refine ⟨79545146590702166652042851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53030097727134777768028567 79545146590702166652042851)
          ·
            refine ⟨119317719886053249978064277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79545146590702166652042851 119317719886053249978064277)
            ·
              refine ⟨5593018119658746092721763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119317719886053249978064277 5593018119658746092721763)
              ·
                refine ⟨8389527179488119139082645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593018119658746092721763 8389527179488119139082645)
                ·
                  refine ⟨393259086538505584644499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8389527179488119139082645 393259086538505584644499)
                  ·
                    rfl

theorem cell22_3446412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_3446412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446412 prefixEnd_3446412 := by exact prefixLift 3446412
  have htrace : WordTrace (prefixWord ++ tailWord_3446412) baseStart_3446412 baseEnd_3446412 := by
    simpa [prefixWord, tailWord_3446412, baseEnd_3446412] using wordTrace_append hprefix tailTrace_3446412
  have hstable : (prefixWord ++ tailWord_3446412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446412).length < 2 ^ (prefixWord ++ tailWord_3446412).sum := by decide
  have hdescent : baseEnd_3446412 < baseStart_3446412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446474 : List Nat := [3, 1, 2, 1, 5, 1, 2, 7]
def baseStart_3446474 : Nat := 118140960795 + 3446474 * 2 ^ 59
def prefixEnd_3446474 : Nat := 4983230072969 + 3 ^ 40 * 3446474 * 2
def baseEnd_3446474 : Nat := 131088720386952139875923

theorem tailTrace_3446474 : CollatzResearch.WordTrace tailWord_3446474 prefixEnd_3446474 131088720386952139875923 := by
  unfold tailWord_3446474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31425808429005195935650619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83802155810680522495068317 31425808429005195935650619)
  ·
    refine ⟨47138712643507793903475929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31425808429005195935650619 47138712643507793903475929)
    ·
      refine ⟨35354034482630845427606947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47138712643507793903475929 35354034482630845427606947)
      ·
        refine ⟨53031051723946268141410421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35354034482630845427606947 53031051723946268141410421)
        ·
          refine ⟨4971661099119962638257227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53031051723946268141410421 4971661099119962638257227)
          ·
            refine ⟨7457491648679943957385841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971661099119962638257227 7457491648679943957385841)
            ·
              refine ⟨5593118736509957968039381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7457491648679943957385841 5593118736509957968039381)
              ·
                refine ⟨131088720386952139875923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5593118736509957968039381 131088720386952139875923)
                ·
                  rfl

theorem cell22_3446474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_3446474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446474 prefixEnd_3446474 := by exact prefixLift 3446474
  have htrace : WordTrace (prefixWord ++ tailWord_3446474) baseStart_3446474 baseEnd_3446474 := by
    simpa [prefixWord, tailWord_3446474, baseEnd_3446474] using wordTrace_append hprefix tailTrace_3446474
  have hstable : (prefixWord ++ tailWord_3446474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446474).length < 2 ^ (prefixWord ++ tailWord_3446474).sum := by decide
  have hdescent : baseEnd_3446474 < baseStart_3446474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446493 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3446493 : Nat := 118140960795 + 3446493 * 2 ^ 59
def prefixEnd_3446493 : Nat := 4983230072969 + 3 ^ 40 * 3446493 * 2
def baseEnd_3446493 : Nat := 1179804987570859542658249

theorem tailTrace_3446493 : CollatzResearch.WordTrace tailWord_3446493 prefixEnd_3446493 1179804987570859542658249 := by
  unfold tailWord_3446493
  simp only [CollatzResearch.WordTrace]
  refine ⟨125703926702951949987544133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83802617801967966658362755 125703926702951949987544133)
  ·
    refine ⟨23569486256803490622664525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125703926702951949987544133 23569486256803490622664525)
    ·
      refine ⟨8838557346301308983499197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23569486256803490622664525 8838557346301308983499197)
      ·
        refine ⟨3314459004862990868812199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8838557346301308983499197 3314459004862990868812199)
        ·
          refine ⟨4971688507294486303218299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314459004862990868812199 4971688507294486303218299)
          ·
            refine ⟨7457532760941729454827449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971688507294486303218299 7457532760941729454827449)
            ·
              refine ⟨5593149570706297091120587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7457532760941729454827449 5593149570706297091120587)
              ·
                refine ⟨8389724356059445636680881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593149570706297091120587 8389724356059445636680881)
                ·
                  refine ⟨6292293267044584227510661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8389724356059445636680881 6292293267044584227510661)
                  ·
                    refine ⟨1179804987570859542658249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292293267044584227510661 1179804987570859542658249)
                    ·
                      rfl

theorem cell22_3446493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3446493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446493 prefixEnd_3446493 := by exact prefixLift 3446493
  have htrace : WordTrace (prefixWord ++ tailWord_3446493) baseStart_3446493 baseEnd_3446493 := by
    simpa [prefixWord, tailWord_3446493, baseEnd_3446493] using wordTrace_append hprefix tailTrace_3446493
  have hstable : (prefixWord ++ tailWord_3446493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446493).length < 2 ^ (prefixWord ++ tailWord_3446493).sum := by decide
  have hdescent : baseEnd_3446493 < baseStart_3446493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446549 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3446549 : Nat := 118140960795 + 3446549 * 2 ^ 59
def prefixEnd_3446549 : Nat := 4983230072969 + 3 ^ 40 * 3446549 * 2
def baseEnd_3446549 : Nat := 1179824157515294063258077

theorem tailTrace_3446549 : CollatzResearch.WordTrace tailWord_3446549 prefixEnd_3446549 1179824157515294063258077 := by
  unfold tailWord_3446549
  simp only [CollatzResearch.WordTrace]
  refine ⟨125705969190749071551582701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83803979460499381034388467 125705969190749071551582701)
  ·
    refine ⟨47139738446530901831843513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125705969190749071551582701 47139738446530901831843513)
    ·
      refine ⟨35354803834898176373882635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47139738446530901831843513 35354803834898176373882635)
      ·
        refine ⟨53032205752347264560823953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35354803834898176373882635 53032205752347264560823953)
        ·
          refine ⟨39774154314260448420617965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53032205752347264560823953 39774154314260448420617965)
          ·
            refine ⟨14915307867847668157731737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39774154314260448420617965 14915307867847668157731737)
            ·
              refine ⟨11186480900885751118298803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14915307867847668157731737 11186480900885751118298803)
              ·
                refine ⟨16779721351328626677448205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11186480900885751118298803 16779721351328626677448205)
                ·
                  refine ⟨6292395506748235004043077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16779721351328626677448205 6292395506748235004043077)
                  ·
                    refine ⟨1179824157515294063258077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6292395506748235004043077 1179824157515294063258077)
                    ·
                      rfl

theorem cell22_3446549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3446549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446549 prefixEnd_3446549 := by exact prefixLift 3446549
  have htrace : WordTrace (prefixWord ++ tailWord_3446549) baseStart_3446549 baseEnd_3446549 := by
    simpa [prefixWord, tailWord_3446549, baseEnd_3446549] using wordTrace_append hprefix tailTrace_3446549
  have hstable : (prefixWord ++ tailWord_3446549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446549).length < 2 ^ (prefixWord ++ tailWord_3446549).sum := by decide
  have hdescent : baseEnd_3446549 < baseStart_3446549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446581 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 6]
def baseStart_3446581 : Nat := 118140960795 + 3446581 * 2 ^ 59
def prefixEnd_3446581 : Nat := 4983230072969 + 3 ^ 40 * 3446581 * 2
def baseEnd_3446581 : Nat := 393278370589752215485993

theorem tailTrace_3446581 : CollatzResearch.WordTrace tailWord_3446581 prefixEnd_3446581 393278370589752215485993 := by
  unfold tailWord_3446581
  simp only [CollatzResearch.WordTrace]
  refine ⟨125707136326633141016747597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83804757551088760677831731 125707136326633141016747597)
  ·
    refine ⟨47140176122487427881280349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125707136326633141016747597 47140176122487427881280349)
    ·
      refine ⟨17677566045932785455480131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47140176122487427881280349 17677566045932785455480131)
      ·
        refine ⟨26516349068899178183220197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17677566045932785455480131 26516349068899178183220197)
        ·
          refine ⟨4971815450418595909353787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26516349068899178183220197 4971815450418595909353787)
          ·
            refine ⟨7457723175627893864030681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971815450418595909353787 7457723175627893864030681)
            ·
              refine ⟨5593292381720920398023011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7457723175627893864030681 5593292381720920398023011)
              ·
                refine ⟨8389938572581380597034517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593292381720920398023011 8389938572581380597034517)
                ·
                  refine ⟨393278370589752215485993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8389938572581380597034517 393278370589752215485993)
                  ·
                    rfl

theorem cell22_3446581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_3446581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446581 prefixEnd_3446581 := by exact prefixLift 3446581
  have htrace : WordTrace (prefixWord ++ tailWord_3446581) baseStart_3446581 baseEnd_3446581 := by
    simpa [prefixWord, tailWord_3446581, baseEnd_3446581] using wordTrace_append hprefix tailTrace_3446581
  have hstable : (prefixWord ++ tailWord_3446581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446581).length < 2 ^ (prefixWord ++ tailWord_3446581).sum := by decide
  have hdescent : baseEnd_3446581 < baseStart_3446581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446598 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3446598 : Nat := 118140960795 + 3446598 * 2 ^ 59
def prefixEnd_3446598 : Nat := 4983230072969 + 3 ^ 40 * 3446598 * 2
def baseEnd_3446598 : Nat := 393280310405558089594309

theorem tailTrace_3446598 : CollatzResearch.WordTrace tailWord_3446598 prefixEnd_3446598 393280310405558089594309 := by
  unfold tailWord_3446598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928367386486611028753639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83805170911714368613410965 3928367386486611028753639)
  ·
    refine ⟨5892551079729916543130459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3928367386486611028753639 5892551079729916543130459)
    ·
      refine ⟨8838826619594874814695689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892551079729916543130459 8838826619594874814695689)
      ·
        refine ⟨6629119964696156111021767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8838826619594874814695689 6629119964696156111021767)
        ·
          refine ⟨9943679947044234166532651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629119964696156111021767 9943679947044234166532651)
          ·
            refine ⟨14915519920566351249798977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943679947044234166532651 14915519920566351249798977)
            ·
              refine ⟨11186639940424763437349233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14915519920566351249798977 11186639940424763437349233)
              ·
                refine ⟨8389979955318572578011925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11186639940424763437349233 8389979955318572578011925)
                ·
                  refine ⟨393280310405558089594309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8389979955318572578011925 393280310405558089594309)
                  ·
                    rfl

theorem cell22_3446598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3446598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446598 prefixEnd_3446598 := by exact prefixLift 3446598
  have htrace : WordTrace (prefixWord ++ tailWord_3446598) baseStart_3446598 baseEnd_3446598 := by
    simpa [prefixWord, tailWord_3446598, baseEnd_3446598] using wordTrace_append hprefix tailTrace_3446598
  have hstable : (prefixWord ++ tailWord_3446598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446598).length < 2 ^ (prefixWord ++ tailWord_3446598).sum := by decide
  have hdescent : baseEnd_3446598 < baseStart_3446598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446609 : List Nat := [1, 2, 2, 1, 5, 2, 1, 8]
def baseStart_3446609 : Nat := 118140960795 + 3446609 * 2 ^ 59
def prefixEnd_3446609 : Nat := 4983230072969 + 3 ^ 40 * 3446609 * 2
def baseEnd_3446609 : Nat := 131093855193497100750877

theorem tailTrace_3446609 : CollatzResearch.WordTrace tailWord_3446609 prefixEnd_3446609 131093855193497100750877 := by
  unfold tailWord_3446609
  simp only [CollatzResearch.WordTrace]
  refine ⟨125708157570531701798766881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83805438380354467865844587 125708157570531701798766881)
  ·
    refine ⟨94281118177898776349075161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125708157570531701798766881 94281118177898776349075161)
    ·
      refine ⟨70710838633424082261806371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94281118177898776349075161 70710838633424082261806371)
      ·
        refine ⟨106066257950136123392709557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70710838633424082261806371 106066257950136123392709557)
        ·
          refine ⟨9943711682825261568066521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106066257950136123392709557 9943711682825261568066521)
          ·
            refine ⟨7457783762118946176049891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9943711682825261568066521 7457783762118946176049891)
            ·
              refine ⟨11186675643178419264074837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457783762118946176049891 11186675643178419264074837)
              ·
                refine ⟨131093855193497100750877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11186675643178419264074837 131093855193497100750877)
                ·
                  rfl

theorem cell22_3446609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 8].length) (baseStart_3446609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446609 prefixEnd_3446609 := by exact prefixLift 3446609
  have htrace : WordTrace (prefixWord ++ tailWord_3446609) baseStart_3446609 baseEnd_3446609 := by
    simpa [prefixWord, tailWord_3446609, baseEnd_3446609] using wordTrace_append hprefix tailTrace_3446609
  have hstable : (prefixWord ++ tailWord_3446609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446609).length < 2 ^ (prefixWord ++ tailWord_3446609).sum := by decide
  have hdescent : baseEnd_3446609 < baseStart_3446609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446615 : List Nat := [1, 1, 3, 2, 6, 1, 1, 3, 4]
def baseStart_3446615 : Nat := 118140960795 + 3446615 * 2 ^ 59
def prefixEnd_3446615 : Nat := 4983230072969 + 3 ^ 40 * 3446615 * 2
def baseEnd_3446615 : Nat := 393282250221363963702625

theorem tailTrace_3446615 : CollatzResearch.WordTrace tailWord_3446615 prefixEnd_3446615 393282250221363963702625 := by
  unfold tailWord_3446615
  simp only [CollatzResearch.WordTrace]
  refine ⟨125708376408509964823485299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83805584272339976548990199 125708376408509964823485299)
  ·
    refine ⟨188562564612764947235227949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125708376408509964823485299 188562564612764947235227949)
    ·
      refine ⟨70710961729786855213210481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188562564612764947235227949 70710961729786855213210481)
      ·
        refine ⟨53033221297340141409907861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70710961729786855213210481 53033221297340141409907861)
        ·
          refine ⟨2485932248312819128589431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53033221297340141409907861 2485932248312819128589431)
          ·
            refine ⟨3728898372469228692884147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485932248312819128589431 3728898372469228692884147)
            ·
              refine ⟨5593347558703843039326221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728898372469228692884147 5593347558703843039326221)
              ·
                refine ⟨2097505334513941139747333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5593347558703843039326221 2097505334513941139747333)
                ·
                  refine ⟨393282250221363963702625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097505334513941139747333 393282250221363963702625)
                  ·
                    rfl

theorem cell22_3446615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 4].length) (baseStart_3446615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446615 prefixEnd_3446615 := by exact prefixLift 3446615
  have htrace : WordTrace (prefixWord ++ tailWord_3446615) baseStart_3446615 baseEnd_3446615 := by
    simpa [prefixWord, tailWord_3446615, baseEnd_3446615] using wordTrace_append hprefix tailTrace_3446615
  have hstable : (prefixWord ++ tailWord_3446615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446615).length < 2 ^ (prefixWord ++ tailWord_3446615).sum := by decide
  have hdescent : baseEnd_3446615 < baseStart_3446615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446626 : List Nat := [3, 3, 2, 1, 2, 3, 8]
def baseStart_3446626 : Nat := 118140960795 + 3446626 * 2 ^ 59
def prefixEnd_3446626 : Nat := 4983230072969 + 3 ^ 40 * 3446626 * 2
def baseEnd_3446626 : Nat := 43698167266255241817883

theorem tailTrace_3446626 : CollatzResearch.WordTrace tailWord_3446626 prefixEnd_3446626 43698167266255241817883 := by
  unfold tailWord_3446626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31427194402867528425533933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83805851740980075801423821 31427194402867528425533933)
  ·
    refine ⟨11785197901075323159575225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31427194402867528425533933 11785197901075323159575225)
    ·
      refine ⟨8838898425806492369681419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11785197901075323159575225 8838898425806492369681419)
      ·
        refine ⟨13258347638709738554522129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8838898425806492369681419 13258347638709738554522129)
        ·
          refine ⟨9943760729032303915891597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13258347638709738554522129 9943760729032303915891597)
          ·
            refine ⟨3728910273387113968459349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9943760729032303915891597 3728910273387113968459349)
            ·
              refine ⟨43698167266255241817883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3728910273387113968459349 43698167266255241817883)
              ·
                rfl

theorem cell22_3446626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 8].length) (baseStart_3446626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446626 prefixEnd_3446626 := by exact prefixLift 3446626
  have htrace : WordTrace (prefixWord ++ tailWord_3446626) baseStart_3446626 baseEnd_3446626 := by
    simpa [prefixWord, tailWord_3446626, baseEnd_3446626] using wordTrace_append hprefix tailTrace_3446626
  have hstable : (prefixWord ++ tailWord_3446626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446626).length < 2 ^ (prefixWord ++ tailWord_3446626).sum := by decide
  have hdescent : baseEnd_3446626 < baseStart_3446626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446692 : List Nat := [2, 3, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_3446692 : Nat := 118140960795 + 3446692 * 2 ^ 59
def prefixEnd_3446692 : Nat := 4983230072969 + 3 ^ 40 * 3446692 * 2
def baseEnd_3446692 : Nat := 1179873109337689356932639

theorem tailTrace_3446692 : CollatzResearch.WordTrace tailWord_3446692 prefixEnd_3446692 1179873109337689356932639 := by
  unfold tailWord_3446692
  simp only [CollatzResearch.WordTrace]
  refine ⟨62855592414615503487019165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83807456552820671316025553 62855592414615503487019165)
  ·
    refine ⟨23570847155480813807632187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62855592414615503487019165 23570847155480813807632187)
    ·
      refine ⟨35356270733221220711448281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23570847155480813807632187 35356270733221220711448281)
      ·
        refine ⟨26517203049915915533586211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35356270733221220711448281 26517203049915915533586211)
        ·
          refine ⟨39775804574873873300379317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26517203049915915533586211 39775804574873873300379317)
          ·
            refine ⟨3728981678894425621910561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39775804574873873300379317 3728981678894425621910561)
            ·
              refine ⟨2796736259170819216432921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728981678894425621910561 2796736259170819216432921)
              ·
                refine ⟨2097552194378114412324691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796736259170819216432921 2097552194378114412324691)
                ·
                  refine ⟨3146328291567171618487037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097552194378114412324691 3146328291567171618487037)
                  ·
                    refine ⟨1179873109337689356932639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3146328291567171618487037 1179873109337689356932639)
                    ·
                      rfl

theorem cell22_3446692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_3446692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446692 prefixEnd_3446692 := by exact prefixLift 3446692
  have htrace : WordTrace (prefixWord ++ tailWord_3446692) baseStart_3446692 baseEnd_3446692 := by
    simpa [prefixWord, tailWord_3446692, baseEnd_3446692] using wordTrace_append hprefix tailTrace_3446692
  have hstable : (prefixWord ++ tailWord_3446692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446692).length < 2 ^ (prefixWord ++ tailWord_3446692).sum := by decide
  have hdescent : baseEnd_3446692 < baseStart_3446692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446729 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_3446729 : Nat := 118140960795 + 3446729 * 2 ^ 59
def prefixEnd_3446729 : Nat := 4983230072969 + 3 ^ 40 * 3446729 * 2
def baseEnd_3446729 : Nat := 1179885775193833593757525

theorem tailTrace_3446729 : CollatzResearch.WordTrace tailWord_3446729 prefixEnd_3446729 1179885775193833593757525 := by
  unfold tailWord_3446729
  simp only [CollatzResearch.WordTrace]
  refine ⟨125712534330096962293135241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83808356220064641528756827 125712534330096962293135241)
  ·
    refine ⟨94284400747572721719851431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125712534330096962293135241 94284400747572721719851431)
    ·
      refine ⟨141426601121359082579777147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94284400747572721719851431 141426601121359082579777147)
      ·
        refine ⟨212139901682038623869665721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141426601121359082579777147 212139901682038623869665721)
        ·
          refine ⟨159104926261528967902249291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212139901682038623869665721 159104926261528967902249291)
          ·
            refine ⟨238657389392293451853373937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159104926261528967902249291 238657389392293451853373937)
            ·
              refine ⟨178993042044220088890030453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238657389392293451853373937 178993042044220088890030453)
              ·
                refine ⟨16780597691645633333440355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178993042044220088890030453 16780597691645633333440355)
                ·
                  refine ⟨25170896537468450000160533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16780597691645633333440355 25170896537468450000160533)
                  ·
                    refine ⟨1179885775193833593757525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25170896537468450000160533 1179885775193833593757525)
                    ·
                      rfl

theorem cell22_3446729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_3446729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446729 prefixEnd_3446729 := by exact prefixLift 3446729
  have htrace : WordTrace (prefixWord ++ tailWord_3446729) baseStart_3446729 baseEnd_3446729 := by
    simpa [prefixWord, tailWord_3446729, baseEnd_3446729] using wordTrace_append hprefix tailTrace_3446729
  have hstable : (prefixWord ++ tailWord_3446729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446729).length < 2 ^ (prefixWord ++ tailWord_3446729).sum := by decide
  have hdescent : baseEnd_3446729 < baseStart_3446729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446731 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 4, 3]
def baseStart_3446731 : Nat := 118140960795 + 3446731 * 2 ^ 59
def prefixEnd_3446731 : Nat := 4983230072969 + 3 ^ 40 * 3446731 * 2
def baseEnd_3446731 : Nat := 1179886459834706255207519

theorem tailTrace_3446731 : CollatzResearch.WordTrace tailWord_3446731 prefixEnd_3446731 1179886459834706255207519 := by
  unfold tailWord_3446731
  simp only [CollatzResearch.WordTrace]
  refine ⟨125712607276089716634708047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83808404850726477756472031 125712607276089716634708047)
  ·
    refine ⟨188568910914134574952062071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125712607276089716634708047 188568910914134574952062071)
    ·
      refine ⟨282853366371201862428093107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188568910914134574952062071 282853366371201862428093107)
      ·
        refine ⟨424280049556802793642139661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282853366371201862428093107 424280049556802793642139661)
        ·
          refine ⟨159105018583801047615802373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424280049556802793642139661 159105018583801047615802373)
          ·
            refine ⟨29832190984462696427962945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159105018583801047615802373 29832190984462696427962945)
            ·
              refine ⟨22374143238347022320972209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29832190984462696427962945 22374143238347022320972209)
              ·
                refine ⟨16780607428760266740729157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22374143238347022320972209 16780607428760266740729157)
                ·
                  refine ⟨3146363892892550013886717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16780607428760266740729157 3146363892892550013886717)
                  ·
                    refine ⟨1179886459834706255207519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3146363892892550013886717 1179886459834706255207519)
                    ·
                      rfl

theorem cell22_3446731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 3].length) (baseStart_3446731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446731 prefixEnd_3446731 := by exact prefixLift 3446731
  have htrace : WordTrace (prefixWord ++ tailWord_3446731) baseStart_3446731 baseEnd_3446731 := by
    simpa [prefixWord, tailWord_3446731, baseEnd_3446731] using wordTrace_append hprefix tailTrace_3446731
  have hstable : (prefixWord ++ tailWord_3446731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446731).length < 2 ^ (prefixWord ++ tailWord_3446731).sum := by decide
  have hdescent : baseEnd_3446731 < baseStart_3446731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446744 : List Nat := [2, 1, 2, 2, 2, 2, 11]
def baseStart_3446744 : Nat := 118140960795 + 3446744 * 2 ^ 59
def prefixEnd_3446744 : Nat := 4983230072969 + 3 ^ 40 * 3446744 * 2
def baseEnd_3446744 : Nat := 43699663333347353875277

theorem tailTrace_3446744 : CollatzResearch.WordTrace tailWord_3446744 prefixEnd_3446744 43699663333347353875277 := by
  unfold tailWord_3446744
  simp only [CollatzResearch.WordTrace]
  refine ⟨62856540712521309927465643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83808720950028413236620857 62856540712521309927465643)
  ·
    refine ⟨94284811068781964891198465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62856540712521309927465643 94284811068781964891198465)
    ·
      refine ⟨70713608301586473668398849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94284811068781964891198465 70713608301586473668398849)
      ·
        refine ⟨53035206226189855251299137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70713608301586473668398849 53035206226189855251299137)
        ·
          refine ⟨39776404669642391438474353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53035206226189855251299137 39776404669642391438474353)
          ·
            refine ⟨29832303502231793578855765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39776404669642391438474353 29832303502231793578855765)
            ·
              refine ⟨43699663333347353875277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29832303502231793578855765 43699663333347353875277)
              ·
                rfl

theorem cell22_3446744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 11].length) (baseStart_3446744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446744 prefixEnd_3446744 := by exact prefixLift 3446744
  have htrace : WordTrace (prefixWord ++ tailWord_3446744) baseStart_3446744 baseEnd_3446744 := by
    simpa [prefixWord, tailWord_3446744, baseEnd_3446744] using wordTrace_append hprefix tailTrace_3446744
  have hstable : (prefixWord ++ tailWord_3446744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446744).length < 2 ^ (prefixWord ++ tailWord_3446744).sum := by decide
  have hdescent : baseEnd_3446744 < baseStart_3446744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446810 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_3446810 : Nat := 118140960795 + 3446810 * 2 ^ 59
def prefixEnd_3446810 : Nat := 4983230072969 + 3 ^ 40 * 3446810 * 2
def baseEnd_3446810 : Nat := 1179913503149176382482277

theorem tailTrace_3446810 : CollatzResearch.WordTrace tailWord_3446810 prefixEnd_3446810 1179913503149176382482277 := by
  unfold tailWord_3446810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31428872160700878281708471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83810325761869008751222589 31428872160700878281708471)
  ·
    refine ⟨47143308241051317422562707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31428872160700878281708471 47143308241051317422562707)
    ·
      refine ⟨70714962361576976133844061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47143308241051317422562707 70714962361576976133844061)
      ·
        refine ⟨26518110885591366050191523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70714962361576976133844061 26518110885591366050191523)
        ·
          refine ⟨39777166328387049075287285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26518110885591366050191523 39777166328387049075287285)
          ·
            refine ⟨3729109343286285850808183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39777166328387049075287285 3729109343286285850808183)
            ·
              refine ⟨5593664014929428776212275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729109343286285850808183 5593664014929428776212275)
              ·
                refine ⟨8390496022394143164318413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593664014929428776212275 8390496022394143164318413)
                ·
                  refine ⟨3146436008397803686619405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8390496022394143164318413 3146436008397803686619405)
                  ·
                    refine ⟨1179913503149176382482277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3146436008397803686619405 1179913503149176382482277)
                    ·
                      rfl

theorem cell22_3446810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_3446810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446810 prefixEnd_3446810 := by exact prefixLift 3446810
  have htrace : WordTrace (prefixWord ++ tailWord_3446810) baseStart_3446810 baseEnd_3446810 := by
    simpa [prefixWord, tailWord_3446810, baseEnd_3446810] using wordTrace_append hprefix tailTrace_3446810
  have hstable : (prefixWord ++ tailWord_3446810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446810).length < 2 ^ (prefixWord ++ tailWord_3446810).sum := by decide
  have hdescent : baseEnd_3446810 < baseStart_3446810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446881 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3446881 : Nat := 118140960795 + 3446881 * 2 ^ 59
def prefixEnd_3446881 : Nat := 4983230072969 + 3 ^ 40 * 3446881 * 2
def baseEnd_3446881 : Nat := 1179937807900155863957059

theorem tailTrace_3446881 : CollatzResearch.WordTrace tailWord_3446881 prefixEnd_3446881 1179937807900155863957059 := by
  unfold tailWord_3446881
  simp only [CollatzResearch.WordTrace]
  refine ⟨125718078225546292252668497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83812052150364194835112331 125718078225546292252668497)
  ·
    refine ⟨94288558669159719189501373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125718078225546292252668497 94288558669159719189501373)
    ·
      refine ⟨35358209500934894696063015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94288558669159719189501373 35358209500934894696063015)
      ·
        refine ⟨53037314251402342044094523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35358209500934894696063015 53037314251402342044094523)
        ·
          refine ⟨79555971377103513066141785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53037314251402342044094523 79555971377103513066141785)
          ·
            refine ⟨59666978532827634799606339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79555971377103513066141785 59666978532827634799606339)
            ·
              refine ⟨89500467799241452199409509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59666978532827634799606339 89500467799241452199409509)
              ·
                refine ⟨16781337712357772287389283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89500467799241452199409509 16781337712357772287389283)
                ·
                  refine ⟨25172006568536658431083925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16781337712357772287389283 25172006568536658431083925)
                  ·
                    refine ⟨1179937807900155863957059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25172006568536658431083925 1179937807900155863957059)
                    ·
                      rfl

theorem cell22_3446881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3446881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446881 prefixEnd_3446881 := by exact prefixLift 3446881
  have htrace : WordTrace (prefixWord ++ tailWord_3446881) baseStart_3446881 baseEnd_3446881 := by
    simpa [prefixWord, tailWord_3446881, baseEnd_3446881] using wordTrace_append hprefix tailTrace_3446881
  have hstable : (prefixWord ++ tailWord_3446881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446881).length < 2 ^ (prefixWord ++ tailWord_3446881).sum := by decide
  have hdescent : baseEnd_3446881 < baseStart_3446881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446898 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_3446898 : Nat := 118140960795 + 3446898 * 2 ^ 59
def prefixEnd_3446898 : Nat := 4983230072969 + 3 ^ 40 * 3446898 * 2
def baseEnd_3446898 : Nat := 1179943627347573486282007

theorem tailTrace_3446898 : CollatzResearch.WordTrace tailWord_3446898 prefixEnd_3446898 1179943627347573486282007 := by
  unfold tailWord_3446898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31429674566621176039009337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83812465510989802770691565 31429674566621176039009337)
  ·
    refine ⟨23572255924965882029257003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31429674566621176039009337 23572255924965882029257003)
    ·
      refine ⟨35358383887448823043885505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23572255924965882029257003 35358383887448823043885505)
      ·
        refine ⟨26518787915586617282914129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35358383887448823043885505 26518787915586617282914129)
        ·
          refine ⟨19889090936689962962185597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26518787915586617282914129 19889090936689962962185597)
          ·
            refine ⟨7458409101258736110819599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19889090936689962962185597 7458409101258736110819599)
            ·
              refine ⟨11187613651888104166229399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7458409101258736110819599 11187613651888104166229399)
              ·
                refine ⟨16781420477832156249344099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11187613651888104166229399 16781420477832156249344099)
                ·
                  refine ⟨25172130716748234374016149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16781420477832156249344099 25172130716748234374016149)
                  ·
                    refine ⟨1179943627347573486282007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25172130716748234374016149 1179943627347573486282007)
                    ·
                      rfl

theorem cell22_3446898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_3446898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446898 prefixEnd_3446898 := by exact prefixLift 3446898
  have htrace : WordTrace (prefixWord ++ tailWord_3446898) baseStart_3446898 baseEnd_3446898 := by
    simpa [prefixWord, tailWord_3446898, baseEnd_3446898] using wordTrace_append hprefix tailTrace_3446898
  have hstable : (prefixWord ++ tailWord_3446898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446898).length < 2 ^ (prefixWord ++ tailWord_3446898).sum := by decide
  have hdescent : baseEnd_3446898 < baseStart_3446898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446902 : List Nat := [5, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3446902 : Nat := 118140960795 + 3446902 * 2 ^ 59
def prefixEnd_3446902 : Nat := 4983230072969 + 3 ^ 40 * 3446902 * 2
def baseEnd_3446902 : Nat := 393314998876439603060665

theorem tailTrace_3446902 : CollatzResearch.WordTrace tailWord_3446902 prefixEnd_3446902 393314998876439603060665 := by
  unfold tailWord_3446902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857427759904388302448935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83812562772313475226121973 7857427759904388302448935)
  ·
    refine ⟨11786141639856582453673403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7857427759904388302448935 11786141639856582453673403)
    ·
      refine ⟨17679212459784873680510105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11786141639856582453673403 17679212459784873680510105)
      ·
        refine ⟨13259409344838655260382579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17679212459784873680510105 13259409344838655260382579)
        ·
          refine ⟨19889114017257982890573869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13259409344838655260382579 19889114017257982890573869)
          ·
            refine ⟨7458417756471743583965201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19889114017257982890573869 7458417756471743583965201)
            ·
              refine ⟨5593813317353807687973901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7458417756471743583965201 5593813317353807687973901)
              ·
                refine ⟨2097679994007677882990213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5593813317353807687973901 2097679994007677882990213)
                ·
                  refine ⟨393314998876439603060665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097679994007677882990213 393314998876439603060665)
                  ·
                    rfl

theorem cell22_3446902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3446902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446902 prefixEnd_3446902 := by exact prefixLift 3446902
  have htrace : WordTrace (prefixWord ++ tailWord_3446902) baseStart_3446902 baseEnd_3446902 := by
    simpa [prefixWord, tailWord_3446902, baseEnd_3446902] using wordTrace_append hprefix tailTrace_3446902
  have hstable : (prefixWord ++ tailWord_3446902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446902).length < 2 ^ (prefixWord ++ tailWord_3446902).sum := by decide
  have hdescent : baseEnd_3446902 < baseStart_3446902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446913 : List Nat := [1, 2, 4, 2, 3, 1, 9]
def baseStart_3446913 : Nat := 118140960795 + 3446913 * 2 ^ 59
def prefixEnd_3446913 : Nat := 4983230072969 + 3 ^ 40 * 3446913 * 2
def baseEnd_3446913 : Nat := 43701806005708090635443

theorem tailTrace_3446913 : CollatzResearch.WordTrace tailWord_3446913 prefixEnd_3446913 43701806005708090635443 := by
  unfold tailWord_3446913
  simp only [CollatzResearch.WordTrace]
  refine ⟨125719245361430361717833393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83812830240953574478555595 125719245361430361717833393)
  ·
    refine ⟨94289434021072771288375045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125719245361430361717833393 94289434021072771288375045)
    ·
      refine ⟨17679268878951144616570321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94289434021072771288375045 17679268878951144616570321)
      ·
        refine ⟨13259451659213358462427741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17679268878951144616570321 13259451659213358462427741)
        ·
          refine ⟨4972294372205009423410403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13259451659213358462427741 4972294372205009423410403)
          ·
            refine ⟨7458441558307514135115605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4972294372205009423410403 7458441558307514135115605)
            ·
              refine ⟨43701806005708090635443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7458441558307514135115605 43701806005708090635443)
              ·
                rfl

theorem cell22_3446913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 9].length) (baseStart_3446913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446913 prefixEnd_3446913 := by exact prefixLift 3446913
  have htrace : WordTrace (prefixWord ++ tailWord_3446913) baseStart_3446913 baseEnd_3446913 := by
    simpa [prefixWord, tailWord_3446913, baseEnd_3446913] using wordTrace_append hprefix tailTrace_3446913
  have hstable : (prefixWord ++ tailWord_3446913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446913).length < 2 ^ (prefixWord ++ tailWord_3446913).sum := by decide
  have hdescent : baseEnd_3446913 < baseStart_3446913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446917 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_3446917 : Nat := 118140960795 + 3446917 * 2 ^ 59
def prefixEnd_3446917 : Nat := 4983230072969 + 3 ^ 40 * 3446917 * 2
def baseEnd_3446917 : Nat := 1179950131435863770056949

theorem tailTrace_3446917 : CollatzResearch.WordTrace tailWord_3446917 prefixEnd_3446917 1179950131435863770056949 := by
  unfold tailWord_3446917
  simp only [CollatzResearch.WordTrace]
  refine ⟨125719391253415870400979005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83812927502277246933986003 125719391253415870400979005)
  ·
    refine ⟨47144771720030951400367127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125719391253415870400979005 47144771720030951400367127)
    ·
      refine ⟨70717157580046427100550691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47144771720030951400367127 70717157580046427100550691)
      ·
        refine ⟨106075736370069640650826037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70717157580046427100550691 106075736370069640650826037)
        ·
          refine ⟨9944600284694028811014941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106075736370069640650826037 9944600284694028811014941)
          ·
            refine ⟨3729225106760260804130603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9944600284694028811014941 3729225106760260804130603)
            ·
              refine ⟨5593837660140391206195905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729225106760260804130603 5593837660140391206195905)
              ·
                refine ⟨4195378245105293404646929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5593837660140391206195905 4195378245105293404646929)
                ·
                  refine ⟨3146533683828970053485197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4195378245105293404646929 3146533683828970053485197)
                  ·
                    refine ⟨1179950131435863770056949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3146533683828970053485197 1179950131435863770056949)
                    ·
                      rfl

theorem cell22_3446917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_3446917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446917 prefixEnd_3446917 := by exact prefixLift 3446917
  have htrace : WordTrace (prefixWord ++ tailWord_3446917) baseStart_3446917 baseEnd_3446917 := by
    simpa [prefixWord, tailWord_3446917, baseEnd_3446917] using wordTrace_append hprefix tailTrace_3446917
  have hstable : (prefixWord ++ tailWord_3446917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446917).length < 2 ^ (prefixWord ++ tailWord_3446917).sum := by decide
  have hdescent : baseEnd_3446917 < baseStart_3446917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446945 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 3, 3]
def baseStart_3446945 : Nat := 118140960795 + 3446945 * 2 ^ 59
def prefixEnd_3446945 : Nat := 4983230072969 + 3 ^ 40 * 3446945 * 2
def baseEnd_3446945 : Nat := 1179959716408081030356863

theorem tailTrace_3446945 : CollatzResearch.WordTrace tailWord_3446945 prefixEnd_3446945 1179959716408081030356863 := by
  unfold tailWord_3446945
  simp only [CollatzResearch.WordTrace]
  refine ⟨125720412497314431182998289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83813608331542954121998859 125720412497314431182998289)
  ·
    refine ⟨94290309372985823387248717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125720412497314431182998289 94290309372985823387248717)
    ·
      refine ⟨35358866014869683770218269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94290309372985823387248717 35358866014869683770218269)
      ·
        refine ⟨13259574755576131413831851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35358866014869683770218269 13259574755576131413831851)
        ·
          refine ⟨19889362133364197120747777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13259574755576131413831851 19889362133364197120747777)
          ·
            refine ⟨14917021600023147840560833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19889362133364197120747777 14917021600023147840560833)
            ·
              refine ⟨11187766200017360880420625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14917021600023147840560833 11187766200017360880420625)
              ·
                refine ⟨8390824650013020660315469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11187766200017360880420625 8390824650013020660315469)
                ·
                  refine ⟨3146559243754882747618301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8390824650013020660315469 3146559243754882747618301)
                  ·
                    refine ⟨1179959716408081030356863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3146559243754882747618301 1179959716408081030356863)
                    ·
                      rfl

theorem cell22_3446945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_3446945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446945 prefixEnd_3446945 := by exact prefixLift 3446945
  have htrace : WordTrace (prefixWord ++ tailWord_3446945) baseStart_3446945 baseEnd_3446945 := by
    simpa [prefixWord, tailWord_3446945, baseEnd_3446945] using wordTrace_append hprefix tailTrace_3446945
  have hstable : (prefixWord ++ tailWord_3446945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446945).length < 2 ^ (prefixWord ++ tailWord_3446945).sum := by decide
  have hdescent : baseEnd_3446945 < baseStart_3446945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3446964 : List Nat := [2, 5, 3, 1, 1, 2, 8]
def baseStart_3446964 : Nat := 118140960795 + 3446964 * 2 ^ 59
def prefixEnd_3446964 : Nat := 4983230072969 + 3 ^ 40 * 3446964 * 2
def baseEnd_3446964 : Nat := 43702452610976715338215

theorem tailTrace_3446964 : CollatzResearch.WordTrace tailWord_3446964 prefixEnd_3446964 43702452610976715338215 := by
  unfold tailWord_3446964
  simp only [CollatzResearch.WordTrace]
  refine ⟨62860552742122798713969973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83814070322830398285293297 62860552742122798713969973)
  ·
    refine ⟨5893176819574012379434685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62860552742122798713969973 5893176819574012379434685)
    ·
      refine ⟨2209941307340254642288007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5893176819574012379434685 2209941307340254642288007)
      ·
        refine ⟨3314911961010381963432011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209941307340254642288007 3314911961010381963432011)
        ·
          refine ⟨4972367941515572945148017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314911961010381963432011 4972367941515572945148017)
          ·
            refine ⟨3729275956136679708861013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4972367941515572945148017 3729275956136679708861013)
            ·
              refine ⟨43702452610976715338215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3729275956136679708861013 43702452610976715338215)
              ·
                rfl

theorem cell22_3446964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 8].length) (baseStart_3446964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3446964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3446964 prefixEnd_3446964 := by exact prefixLift 3446964
  have htrace : WordTrace (prefixWord ++ tailWord_3446964) baseStart_3446964 baseEnd_3446964 := by
    simpa [prefixWord, tailWord_3446964, baseEnd_3446964] using wordTrace_append hprefix tailTrace_3446964
  have hstable : (prefixWord ++ tailWord_3446964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3446964).length < 2 ^ (prefixWord ++ tailWord_3446964).sum := by decide
  have hdescent : baseEnd_3446964 < baseStart_3446964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3446964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447020 : List Nat := [2, 2, 1, 1, 2, 3, 2, 5, 4]
def baseStart_3447020 : Nat := 118140960795 + 3447020 * 2 ^ 59
def prefixEnd_3447020 : Nat := 4983230072969 + 3 ^ 40 * 3447020 * 2
def baseEnd_3447020 : Nat := 393328463480268611577211

theorem tailTrace_3447020 : CollatzResearch.WordTrace tailWord_3447020 prefixEnd_3447020 393328463480268611577211 := by
  unfold tailWord_3447020
  simp only [CollatzResearch.WordTrace]
  refine ⟨62861573986021359495989257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83815431981361812661319009 62861573986021359495989257)
  ·
    refine ⟨47146180489516019621991943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62861573986021359495989257 47146180489516019621991943)
    ·
      refine ⟨70719270734274029432987915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47146180489516019621991943 70719270734274029432987915)
      ·
        refine ⟨106078906101411044149481873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70719270734274029432987915 106078906101411044149481873)
        ·
          refine ⟨79559179576058283112111405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106078906101411044149481873 79559179576058283112111405)
          ·
            refine ⟨29834692341021856167041777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79559179576058283112111405 29834692341021856167041777)
            ·
              refine ⟨22376019255766392125281333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29834692341021856167041777 22376019255766392125281333)
              ·
                refine ⟨2097751805228099261745125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22376019255766392125281333 2097751805228099261745125)
                ·
                  refine ⟨393328463480268611577211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2097751805228099261745125 393328463480268611577211)
                  ·
                    rfl

theorem cell22_3447020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_3447020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447020 prefixEnd_3447020 := by exact prefixLift 3447020
  have htrace : WordTrace (prefixWord ++ tailWord_3447020) baseStart_3447020 baseEnd_3447020 := by
    simpa [prefixWord, tailWord_3447020, baseEnd_3447020] using wordTrace_append hprefix tailTrace_3447020
  have hstable : (prefixWord ++ tailWord_3447020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447020).length < 2 ^ (prefixWord ++ tailWord_3447020).sum := by decide
  have hdescent : baseEnd_3447020 < baseStart_3447020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447033 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_3447033 : Nat := 118140960795 + 3447033 * 2 ^ 59
def prefixEnd_3447033 : Nat := 4983230072969 + 3 ^ 40 * 3447033 * 2
def baseEnd_3447033 : Nat := 1179989840606478134156593

theorem tailTrace_3447033 : CollatzResearch.WordTrace tailWord_3447033 prefixEnd_3447033 1179989840606478134156593 := by
  unfold tailWord_3447033
  simp only [CollatzResearch.WordTrace]
  refine ⟨125723622120995622212201753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83815748080663748141467835 125723622120995622212201753)
  ·
    refine ⟨94292716590746716659151315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125723622120995622212201753 94292716590746716659151315)
    ·
      refine ⟨141439074886120074988726973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94292716590746716659151315 141439074886120074988726973)
      ·
        refine ⟨53039653082295028120772615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141439074886120074988726973 53039653082295028120772615)
        ·
          refine ⟨79559479623442542181158923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53039653082295028120772615 79559479623442542181158923)
          ·
            refine ⟨119339219435163813271738385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79559479623442542181158923 119339219435163813271738385)
            ·
              refine ⟨89504414576372859953803789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119339219435163813271738385 89504414576372859953803789)
              ·
                refine ⟨33564155466139822482676421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89504414576372859953803789 33564155466139822482676421)
                ·
                  refine ⟨6293279149901216715501829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33564155466139822482676421 6293279149901216715501829)
                  ·
                    refine ⟨1179989840606478134156593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6293279149901216715501829 1179989840606478134156593)
                    ·
                      rfl

theorem cell22_3447033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_3447033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447033 prefixEnd_3447033 := by exact prefixLift 3447033
  have htrace : WordTrace (prefixWord ++ tailWord_3447033) baseStart_3447033 baseEnd_3447033 := by
    simpa [prefixWord, tailWord_3447033, baseEnd_3447033] using wordTrace_append hprefix tailTrace_3447033
  have hstable : (prefixWord ++ tailWord_3447033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447033).length < 2 ^ (prefixWord ++ tailWord_3447033).sum := by decide
  have hdescent : baseEnd_3447033 < baseStart_3447033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447097 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 3, 3]
def baseStart_3447097 : Nat := 118140960795 + 3447097 * 2 ^ 59
def prefixEnd_3447097 : Nat := 4983230072969 + 3 ^ 40 * 3447097 * 2
def baseEnd_3447097 : Nat := 1180011749114403300556397

theorem tailTrace_3447097 : CollatzResearch.WordTrace tailWord_3447097 prefixEnd_3447097 1180011749114403300556397 := by
  unfold tailWord_3447097
  simp only [CollatzResearch.WordTrace]
  refine ⟨125725956392763761142531545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83817304261842507428354363 125725956392763761142531545)
  ·
    refine ⟨94294467294572820856898659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125725956392763761142531545 94294467294572820856898659)
    ·
      refine ⟨141441700941859231285347989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94294467294572820856898659 141441700941859231285347989)
      ·
        refine ⟨6630079731649651466500687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141441700941859231285347989 6630079731649651466500687)
        ·
          refine ⟨9945119597474477199751031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630079731649651466500687 9945119597474477199751031)
          ·
            refine ⟨14917679396211715799626547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9945119597474477199751031 14917679396211715799626547)
            ·
              refine ⟨22376519094317573699439821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14917679396211715799626547 22376519094317573699439821)
              ·
                refine ⟨8391194660369090137289933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22376519094317573699439821 8391194660369090137289933)
                ·
                  refine ⟨3146697997638408801483725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8391194660369090137289933 3146697997638408801483725)
                  ·
                    refine ⟨1180011749114403300556397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3146697997638408801483725 1180011749114403300556397)
                    ·
                      rfl

theorem cell22_3447097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_3447097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447097 prefixEnd_3447097 := by exact prefixLift 3447097
  have htrace : WordTrace (prefixWord ++ tailWord_3447097) baseStart_3447097 baseEnd_3447097 := by
    simpa [prefixWord, tailWord_3447097, baseEnd_3447097] using wordTrace_append hprefix tailTrace_3447097
  have hstable : (prefixWord ++ tailWord_3447097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447097).length < 2 ^ (prefixWord ++ tailWord_3447097).sum := by decide
  have hdescent : baseEnd_3447097 < baseStart_3447097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447202 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3447202 : Nat := 118140960795 + 3447202 * 2 ^ 59
def prefixEnd_3447202 : Nat := 4983230072969 + 3 ^ 40 * 3447202 * 2
def baseEnd_3447202 : Nat := 1180047692760218026681075

theorem tailTrace_3447202 : CollatzResearch.WordTrace tailWord_3447202 prefixEnd_3447202 1180047692760218026681075 := by
  unfold tailWord_3447202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31432446514345841018775965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83819857371588909383402573 31432446514345841018775965)
  ·
    refine ⟨11787167442879690382040987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31432446514345841018775965 11787167442879690382040987)
    ·
      refine ⟨17680751164319535573061481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11787167442879690382040987 17680751164319535573061481)
      ·
        refine ⟨13260563373239651679796111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17680751164319535573061481 13260563373239651679796111)
        ·
          refine ⟨19890845059859477519694167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13260563373239651679796111 19890845059859477519694167)
          ·
            refine ⟨29836267589789216279541251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19890845059859477519694167 29836267589789216279541251)
            ·
              refine ⟨44754401384683824419311877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29836267589789216279541251 44754401384683824419311877)
              ·
                refine ⟨8391450259628217078620977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44754401384683824419311877 8391450259628217078620977)
                ·
                  refine ⟨6293587694721162808965733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8391450259628217078620977 6293587694721162808965733)
                  ·
                    refine ⟨1180047692760218026681075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6293587694721162808965733 1180047692760218026681075)
                    ·
                      rfl

theorem cell22_3447202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3447202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447202 prefixEnd_3447202 := by exact prefixLift 3447202
  have htrace : WordTrace (prefixWord ++ tailWord_3447202) baseStart_3447202 baseEnd_3447202 := by
    simpa [prefixWord, tailWord_3447202, baseEnd_3447202] using wordTrace_append hprefix tailTrace_3447202
  have hstable : (prefixWord ++ tailWord_3447202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447202).length < 2 ^ (prefixWord ++ tailWord_3447202).sum := by decide
  have hdescent : baseEnd_3447202 < baseStart_3447202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447217 : List Nat := [1, 2, 2, 4, 1, 4, 1, 7]
def baseStart_3447217 : Nat := 118140960795 + 3447217 * 2 ^ 59
def prefixEnd_3447217 : Nat := 4983230072969 + 3 ^ 40 * 3447217 * 2
def baseEnd_3447217 : Nat := 131116980840751443061781

theorem tailTrace_3447217 : CollatzResearch.WordTrace tailWord_3447217 prefixEnd_3447217 131116980840751443061781 := by
  unfold tailWord_3447217
  simp only [CollatzResearch.WordTrace]
  refine ⟨125730333152329021636899905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83820222101552681091266603 125730333152329021636899905)
  ·
    refine ⟨94297749864246766227674929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125730333152329021636899905 94297749864246766227674929)
    ·
      refine ⟨70723312398185074670756197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94297749864246766227674929 70723312398185074670756197)
      ·
        refine ⟨13260621074659701500766787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70723312398185074670756197 13260621074659701500766787)
        ·
          refine ⟨19890931611989552251150181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13260621074659701500766787 19890931611989552251150181)
          ·
            refine ⟨3729549677248041047090659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19890931611989552251150181 3729549677248041047090659)
            ·
              refine ⟨5594324515872061570635989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729549677248041047090659 5594324515872061570635989)
              ·
                refine ⟨131116980840751443061781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5594324515872061570635989 131116980840751443061781)
                ·
                  rfl

theorem cell22_3447217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 7].length) (baseStart_3447217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447217 prefixEnd_3447217 := by exact prefixLift 3447217
  have htrace : WordTrace (prefixWord ++ tailWord_3447217) baseStart_3447217 baseEnd_3447217 := by
    simpa [prefixWord, tailWord_3447217, baseEnd_3447217] using wordTrace_append hprefix tailTrace_3447217
  have hstable : (prefixWord ++ tailWord_3447217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447217).length < 2 ^ (prefixWord ++ tailWord_3447217).sum := by decide
  have hdescent : baseEnd_3447217 < baseStart_3447217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447236 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3447236 : Nat := 118140960795 + 3447236 * 2 ^ 59
def prefixEnd_3447236 : Nat := 4983230072969 + 3 ^ 40 * 3447236 * 2
def baseEnd_3447236 : Nat := 1180059331655053271330971

theorem tailTrace_3447236 : CollatzResearch.WordTrace tailWord_3447236 prefixEnd_3447236 1180059331655053271330971 := by
  unfold tailWord_3447236
  simp only [CollatzResearch.WordTrace]
  refine ⟨62865513069630093940920781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83820684092840125254561041 62865513069630093940920781)
  ·
    refine ⟨23574567401111285227845293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62865513069630093940920781 23574567401111285227845293)
    ·
      refine ⟨8840462775416731960441985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23574567401111285227845293 8840462775416731960441985)
      ·
        refine ⟨6630347081562548970331489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8840462775416731960441985 6630347081562548970331489)
        ·
          refine ⟨4972760311171911727748617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6630347081562548970331489 4972760311171911727748617)
          ·
            refine ⟨3729570233378933795811463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4972760311171911727748617 3729570233378933795811463)
            ·
              refine ⟨5594355350068400693717195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729570233378933795811463 5594355350068400693717195)
              ·
                refine ⟨8391533025102601040575793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594355350068400693717195 8391533025102601040575793)
                ·
                  refine ⟨6293649768826950780431845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8391533025102601040575793 6293649768826950780431845)
                  ·
                    refine ⟨1180059331655053271330971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6293649768826950780431845 1180059331655053271330971)
                    ·
                      rfl

theorem cell22_3447236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3447236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447236 prefixEnd_3447236 := by exact prefixLift 3447236
  have htrace : WordTrace (prefixWord ++ tailWord_3447236) baseStart_3447236 baseEnd_3447236 := by
    simpa [prefixWord, tailWord_3447236, baseEnd_3447236] using wordTrace_append hprefix tailTrace_3447236
  have hstable : (prefixWord ++ tailWord_3447236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447236).length < 2 ^ (prefixWord ++ tailWord_3447236).sum := by decide
  have hdescent : baseEnd_3447236 < baseStart_3447236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447290 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_3447290 : Nat := 118140960795 + 3447290 * 2 ^ 59
def prefixEnd_3447290 : Nat := 4983230072969 + 3 ^ 40 * 3447290 * 2
def baseEnd_3447290 : Nat := 393359272319538376826935

theorem tailTrace_3447290 : CollatzResearch.WordTrace tailWord_3447290 prefixEnd_3447290 393359272319538376826935 := by
  unfold tailWord_3447290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31433248920266138776076831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83821997120709703402871549 31433248920266138776076831)
  ·
    refine ⟨47149873380399208164115247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31433248920266138776076831 47149873380399208164115247)
    ·
      refine ⟨70724810070598812246172871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47149873380399208164115247 70724810070598812246172871)
      ·
        refine ⟨106087215105898218369259307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70724810070598812246172871 106087215105898218369259307)
        ·
          refine ⟨159130822658847327553888961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106087215105898218369259307 159130822658847327553888961)
          ·
            refine ⟨119348116994135495665416721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159130822658847327553888961 119348116994135495665416721)
            ·
              refine ⟨89511087745601621749062541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119348116994135495665416721 89511087745601621749062541)
              ·
                refine ⟨33566657904600608155898453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89511087745601621749062541 33566657904600608155898453)
                ·
                  refine ⟨393359272319538376826935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33566657904600608155898453 393359272319538376826935)
                  ·
                    rfl

theorem cell22_3447290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_3447290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447290 prefixEnd_3447290 := by exact prefixLift 3447290
  have htrace : WordTrace (prefixWord ++ tailWord_3447290) baseStart_3447290 baseEnd_3447290 := by
    simpa [prefixWord, tailWord_3447290, baseEnd_3447290] using wordTrace_append hprefix tailTrace_3447290
  have hstable : (prefixWord ++ tailWord_3447290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447290).length < 2 ^ (prefixWord ++ tailWord_3447290).sum := by decide
  have hdescent : baseEnd_3447290 < baseStart_3447290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447324 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 6]
def baseStart_3447324 : Nat := 118140960795 + 3447324 * 2 ^ 59
def prefixEnd_3447324 : Nat := 4983230072969 + 3 ^ 40 * 3447324 * 2
def baseEnd_3447324 : Nat := 393363151951150125043567

theorem tailTrace_3447324 : CollatzResearch.WordTrace tailWord_3447324 prefixEnd_3447324 393363151951150125043567 := by
  unfold tailWord_3447324
  simp only [CollatzResearch.WordTrace]
  refine ⟨62867117881470689455522513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83822823841960919274030017 62867117881470689455522513)
  ·
    refine ⟨47150338411103017091641885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62867117881470689455522513 47150338411103017091641885)
    ·
      refine ⟨17681376904163631409365707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47150338411103017091641885 17681376904163631409365707)
      ·
        refine ⟨26522065356245447114048561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17681376904163631409365707 26522065356245447114048561)
        ·
          refine ⟨19891549017184085335536421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26522065356245447114048561 19891549017184085335536421)
          ·
            refine ⟨3729665440722016000413079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19891549017184085335536421 3729665440722016000413079)
            ·
              refine ⟨5594498161083024000619619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729665440722016000413079 5594498161083024000619619)
              ·
                refine ⟨8391747241624536000929429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594498161083024000619619 8391747241624536000929429)
                ·
                  refine ⟨393363151951150125043567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8391747241624536000929429 393363151951150125043567)
                  ·
                    rfl

theorem cell22_3447324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_3447324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447324 prefixEnd_3447324 := by exact prefixLift 3447324
  have htrace : WordTrace (prefixWord ++ tailWord_3447324) baseStart_3447324 baseEnd_3447324 := by
    simpa [prefixWord, tailWord_3447324, baseEnd_3447324] using wordTrace_append hprefix tailTrace_3447324
  have hstable : (prefixWord ++ tailWord_3447324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447324).length < 2 ^ (prefixWord ++ tailWord_3447324).sum := by decide
  have hdescent : baseEnd_3447324 < baseStart_3447324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447354 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_3447354 : Nat := 118140960795 + 3447354 * 2 ^ 59
def prefixEnd_3447354 : Nat := 4983230072969 + 3 ^ 40 * 3447354 * 2
def baseEnd_3447354 : Nat := 1180099725466540296880609

theorem tailTrace_3447354 : CollatzResearch.WordTrace tailWord_3447354 prefixEnd_3447354 1180099725466540296880609 := by
  unfold tailWord_3447354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31433832488208173508659279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83823553301888462689758077 31433832488208173508659279)
  ·
    refine ⟨47150748732312260262988919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31433832488208173508659279 47150748732312260262988919)
    ·
      refine ⟨70726123098468390394483379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47150748732312260262988919 70726123098468390394483379)
      ·
        refine ⟨106089184647702585591725069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70726123098468390394483379 106089184647702585591725069)
        ·
          refine ⟨39783444242888469596896901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106089184647702585591725069 39783444242888469596896901)
          ·
            refine ⟨7459395795541588049418169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39783444242888469596896901 7459395795541588049418169)
            ·
              refine ⟨5594546846656191037063627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7459395795541588049418169 5594546846656191037063627)
              ·
                refine ⟨8391820269984286555595441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594546846656191037063627 8391820269984286555595441)
                ·
                  refine ⟨6293865202488214916696581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8391820269984286555595441 6293865202488214916696581)
                  ·
                    refine ⟨1180099725466540296880609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6293865202488214916696581 1180099725466540296880609)
                    ·
                      rfl

theorem cell22_3447354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_3447354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447354 prefixEnd_3447354 := by exact prefixLift 3447354
  have htrace : WordTrace (prefixWord ++ tailWord_3447354) baseStart_3447354 baseEnd_3447354 := by
    simpa [prefixWord, tailWord_3447354, baseEnd_3447354] using wordTrace_append hprefix tailTrace_3447354
  have hstable : (prefixWord ++ tailWord_3447354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447354).length < 2 ^ (prefixWord ++ tailWord_3447354).sum := by decide
  have hdescent : baseEnd_3447354 < baseStart_3447354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447373 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3447373 : Nat := 118140960795 + 3447373 * 2 ^ 59
def prefixEnd_3447373 : Nat := 4983230072969 + 3 ^ 40 * 3447373 * 2
def baseEnd_3447373 : Nat := 1180106229554830580655551

theorem tailTrace_3447373 : CollatzResearch.WordTrace tailWord_3447373 prefixEnd_3447373 1180106229554830580655551 := by
  unfold tailWord_3447373
  simp only [CollatzResearch.WordTrace]
  refine ⟨125736022939763860279578773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83824015293175906853052515 125736022939763860279578773)
  ·
    refine ⟨5893876075301430950605255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125736022939763860279578773 5893876075301430950605255)
    ·
      refine ⟨8840814112952146425907883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5893876075301430950605255 8840814112952146425907883)
      ·
        refine ⟨13261221169428219638861825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840814112952146425907883 13261221169428219638861825)
        ·
          refine ⟨9945915877071164729146369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13261221169428219638861825 9945915877071164729146369)
          ·
            refine ⟨7459436907803373546859777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9945915877071164729146369 7459436907803373546859777)
            ·
              refine ⟨5594577680852530160144833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7459436907803373546859777 5594577680852530160144833)
              ·
                refine ⟨4195933260639397620108625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5594577680852530160144833 4195933260639397620108625)
                ·
                  refine ⟨3146949945479548215081469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4195933260639397620108625 3146949945479548215081469)
                  ·
                    refine ⟨1180106229554830580655551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3146949945479548215081469 1180106229554830580655551)
                    ·
                      rfl

theorem cell22_3447373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3447373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447373 prefixEnd_3447373 := by exact prefixLift 3447373
  have htrace : WordTrace (prefixWord ++ tailWord_3447373) baseStart_3447373 baseEnd_3447373 := by
    simpa [prefixWord, tailWord_3447373, baseEnd_3447373] using wordTrace_append hprefix tailTrace_3447373
  have hstable : (prefixWord ++ tailWord_3447373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447373).length < 2 ^ (prefixWord ++ tailWord_3447373).sum := by decide
  have hdescent : baseEnd_3447373 < baseStart_3447373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447390 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3447390 : Nat := 118140960795 + 3447390 * 2 ^ 59
def prefixEnd_3447390 : Nat := 4983230072969 + 3 ^ 40 * 3447390 * 2
def baseEnd_3447390 : Nat := 1180112049002248202980499

theorem tailTrace_3447390 : CollatzResearch.WordTrace tailWord_3447390 prefixEnd_3447390 1180112049002248202980499 := by
  unfold tailWord_3447390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15717080372587784022868453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83824428653801514788631749 15717080372587784022868453)
  ·
    refine ⟨2946952569860209504287835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15717080372587784022868453 2946952569860209504287835)
    ·
      refine ⟨4420428854790314256431753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946952569860209504287835 4420428854790314256431753)
      ·
        refine ⟨3315321641092735692323815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4420428854790314256431753 3315321641092735692323815)
        ·
          refine ⟨4972982461639103538485723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3315321641092735692323815 4972982461639103538485723)
          ·
            refine ⟨7459473692458655307728585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4972982461639103538485723 7459473692458655307728585)
            ·
              refine ⟨5594605269343991480796439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7459473692458655307728585 5594605269343991480796439)
              ·
                refine ⟨8391907904015987221194659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594605269343991480796439 8391907904015987221194659)
                ·
                  refine ⟨12587861856023980831791989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8391907904015987221194659 12587861856023980831791989)
                  ·
                    refine ⟨1180112049002248202980499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12587861856023980831791989 1180112049002248202980499)
                    ·
                      rfl

theorem cell22_3447390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3447390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447390 prefixEnd_3447390 := by exact prefixLift 3447390
  have htrace : WordTrace (prefixWord ++ tailWord_3447390) baseStart_3447390 baseEnd_3447390 := by
    simpa [prefixWord, tailWord_3447390, baseEnd_3447390] using wordTrace_append hprefix tailTrace_3447390
  have hstable : (prefixWord ++ tailWord_3447390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447390).length < 2 ^ (prefixWord ++ tailWord_3447390).sum := by decide
  have hdescent : baseEnd_3447390 < baseStart_3447390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447487 : List Nat := [1, 1, 2, 2, 2, 4, 10]
def baseStart_3447487 : Nat := 118140960795 + 3447487 * 2 ^ 59
def prefixEnd_3447487 : Nat := 4983230072969 + 3 ^ 40 * 3447487 * 2
def baseEnd_3447487 : Nat := 43709083484613788270563

theorem tailTrace_3447487 : CollatzResearch.WordTrace tailWord_3447487 prefixEnd_3447487 43709083484613788270563 := by
  unfold tailWord_3447487
  simp only [CollatzResearch.WordTrace]
  refine ⟨125740180861350857749228715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83826787240900571832819143 125740180861350857749228715)
  ·
    refine ⟨188610271292026286623843073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125740180861350857749228715 188610271292026286623843073)
    ·
      refine ⟨141457703469019714967882305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188610271292026286623843073 141457703469019714967882305)
      ·
        refine ⟨106093277601764786225911729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141457703469019714967882305 106093277601764786225911729)
        ·
          refine ⟨79569958201323589669433797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106093277601764786225911729 79569958201323589669433797)
          ·
            refine ⟨14919367162748173063018837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79569958201323589669433797 14919367162748173063018837)
            ·
              refine ⟨43709083484613788270563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14919367162748173063018837 43709083484613788270563)
              ·
                rfl

theorem cell22_3447487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 10].length) (baseStart_3447487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447487 prefixEnd_3447487 := by exact prefixLift 3447487
  have htrace : WordTrace (prefixWord ++ tailWord_3447487) baseStart_3447487 baseEnd_3447487 := by
    simpa [prefixWord, tailWord_3447487, baseEnd_3447487] using wordTrace_append hprefix tailTrace_3447487
  have hstable : (prefixWord ++ tailWord_3447487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447487).length < 2 ^ (prefixWord ++ tailWord_3447487).sum := by decide
  have hdescent : baseEnd_3447487 < baseStart_3447487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447570 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3447570 : Nat := 118140960795 + 3447570 * 2 ^ 59
def prefixEnd_3447570 : Nat := 4983230072969 + 3 ^ 40 * 3447570 * 2
def baseEnd_3447570 : Nat := 1180173666680787733479947

theorem tailTrace_3447570 : CollatzResearch.WordTrace tailWord_3447570 prefixEnd_3447570 1180173666680787733479947 := by
  unfold tailWord_3447570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31435802030012540731125041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83828805413366775283000109 31435802030012540731125041)
  ·
    refine ⟨23576851522509405548343781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31435802030012540731125041 23576851522509405548343781)
    ·
      refine ⟨4420659660470513540314459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23576851522509405548343781 4420659660470513540314459)
      ·
        refine ⟨6630989490705770310471689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420659660470513540314459 6630989490705770310471689)
        ·
          refine ⟨4973242118029327732853767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6630989490705770310471689 4973242118029327732853767)
          ·
            refine ⟨7459863177043991599280651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973242118029327732853767 7459863177043991599280651)
            ·
              refine ⟨11189794765565987398920977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7459863177043991599280651 11189794765565987398920977)
              ·
                refine ⟨8392346074174490549190733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11189794765565987398920977 8392346074174490549190733)
                ·
                  refine ⟨3147129777815433955946525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8392346074174490549190733 3147129777815433955946525)
                  ·
                    refine ⟨1180173666680787733479947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3147129777815433955946525 1180173666680787733479947)
                    ·
                      rfl

theorem cell22_3447570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3447570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447570 prefixEnd_3447570 := by exact prefixLift 3447570
  have htrace : WordTrace (prefixWord ++ tailWord_3447570) baseStart_3447570 baseEnd_3447570 := by
    simpa [prefixWord, tailWord_3447570, baseEnd_3447570] using wordTrace_append hprefix tailTrace_3447570
  have hstable : (prefixWord ++ tailWord_3447570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447570).length < 2 ^ (prefixWord ++ tailWord_3447570).sum := by decide
  have hdescent : baseEnd_3447570 < baseStart_3447570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447596 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_3447596 : Nat := 118140960795 + 3447596 * 2 ^ 59
def prefixEnd_3447596 : Nat := 4983230072969 + 3 ^ 40 * 3447596 * 2
def baseEnd_3447596 : Nat := 1180182567012132332329867

theorem tailTrace_3447596 : CollatzResearch.WordTrace tailWord_3447596 prefixEnd_3447596 1180182567012132332329867 := by
  unfold tailWord_3447596
  simp only [CollatzResearch.WordTrace]
  refine ⟨62872078208977984682473321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83829437611970646243297761 62872078208977984682473321)
  ·
    refine ⟨47154058656733488511854991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62872078208977984682473321 47154058656733488511854991)
    ·
      refine ⟨70731087985100232767782487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47154058656733488511854991 70731087985100232767782487)
      ·
        refine ⟨106096631977650349151673731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70731087985100232767782487 106096631977650349151673731)
        ·
          refine ⟨159144947966475523727510597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106096631977650349151673731 159144947966475523727510597)
          ·
            refine ⟨29839677743714160698908237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159144947966475523727510597 29839677743714160698908237)
            ·
              refine ⟨11189879153892810262090589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29839677743714160698908237 11189879153892810262090589)
              ·
                refine ⟨4196204682709803848283971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11189879153892810262090589 4196204682709803848283971)
                ·
                  refine ⟨6294307024064705772425957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196204682709803848283971 6294307024064705772425957)
                  ·
                    refine ⟨1180182567012132332329867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6294307024064705772425957 1180182567012132332329867)
                    ·
                      rfl

theorem cell22_3447596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_3447596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447596 prefixEnd_3447596 := by exact prefixLift 3447596
  have htrace : WordTrace (prefixWord ++ tailWord_3447596) baseStart_3447596 baseEnd_3447596 := by
    simpa [prefixWord, tailWord_3447596, baseEnd_3447596] using wordTrace_append hprefix tailTrace_3447596
  have hstable : (prefixWord ++ tailWord_3447596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447596).length < 2 ^ (prefixWord ++ tailWord_3447596).sum := by decide
  have hdescent : baseEnd_3447596 < baseStart_3447596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447624 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3447624 : Nat := 118140960795 + 3447624 * 2 ^ 59
def prefixEnd_3447624 : Nat := 4983230072969 + 3 ^ 40 * 3447624 * 2
def baseEnd_3447624 : Nat := 1180192151984349592629781

theorem tailTrace_3447624 : CollatzResearch.WordTrace tailWord_3447624 prefixEnd_3447624 1180192151984349592629781 := by
  unfold tailWord_3447624
  simp only [CollatzResearch.WordTrace]
  refine ⟨62872588830927265073482963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83830118441236353431310617 62872588830927265073482963)
  ·
    refine ⟨94308883246390897610224445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62872588830927265073482963 94308883246390897610224445)
    ·
      refine ⟨35365831217396586603834167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94308883246390897610224445 35365831217396586603834167)
      ·
        refine ⟨53048746826094879905751251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35365831217396586603834167 53048746826094879905751251)
        ·
          refine ⟨79573120239142319858626877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53048746826094879905751251 79573120239142319858626877)
          ·
            refine ⟨29839920089678369946985079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79573120239142319858626877 29839920089678369946985079)
            ·
              refine ⟨44759880134517554920477619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29839920089678369946985079 44759880134517554920477619)
              ·
                refine ⟨67139820201776332380716429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44759880134517554920477619 67139820201776332380716429)
                ·
                  refine ⟨25177432575666124642768661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67139820201776332380716429 25177432575666124642768661)
                  ·
                    refine ⟨1180192151984349592629781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25177432575666124642768661 1180192151984349592629781)
                    ·
                      rfl

theorem cell22_3447624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3447624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447624 prefixEnd_3447624 := by exact prefixLift 3447624
  have htrace : WordTrace (prefixWord ++ tailWord_3447624) baseStart_3447624 baseEnd_3447624 := by
    simpa [prefixWord, tailWord_3447624, baseEnd_3447624] using wordTrace_append hprefix tailTrace_3447624
  have hstable : (prefixWord ++ tailWord_3447624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447624).length < 2 ^ (prefixWord ++ tailWord_3447624).sum := by decide
  have hdescent : baseEnd_3447624 < baseStart_3447624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447656 : List Nat := [2, 1, 4, 2, 1, 4, 8]
def baseStart_3447656 : Nat := 118140960795 + 3447656 * 2 ^ 59
def prefixEnd_3447656 : Nat := 4983230072969 + 3 ^ 40 * 3447656 * 2
def baseEnd_3447656 : Nat := 43711226156974525030729

theorem tailTrace_3447656 : CollatzResearch.WordTrace tailWord_3447656 prefixEnd_3447656 43711226156974525030729 := by
  unfold tailWord_3447656
  simp only [CollatzResearch.WordTrace]
  refine ⟨62873172398869299806065411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83830896531825733074753881 62873172398869299806065411)
  ·
    refine ⟨94309758598303949709098117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62873172398869299806065411 94309758598303949709098117)
    ·
      refine ⟨17683079737181990570455897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94309758598303949709098117 17683079737181990570455897)
      ·
        refine ⟨13262309802886492927841923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17683079737181990570455897 13262309802886492927841923)
        ·
          refine ⟨19893464704329739391762885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13262309802886492927841923 19893464704329739391762885)
          ·
            refine ⟨3730024632061826135955541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19893464704329739391762885 3730024632061826135955541)
            ·
              refine ⟨43711226156974525030729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3730024632061826135955541 43711226156974525030729)
              ·
                rfl

theorem cell22_3447656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 8].length) (baseStart_3447656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447656 prefixEnd_3447656 := by exact prefixLift 3447656
  have htrace : WordTrace (prefixWord ++ tailWord_3447656) baseStart_3447656 baseEnd_3447656 := by
    simpa [prefixWord, tailWord_3447656, baseEnd_3447656] using wordTrace_append hprefix tailTrace_3447656
  have hstable : (prefixWord ++ tailWord_3447656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447656).length < 2 ^ (prefixWord ++ tailWord_3447656).sum := by decide
  have hdescent : baseEnd_3447656 < baseStart_3447656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447662 : List Nat := [4, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_3447662 : Nat := 118140960795 + 3447662 * 2 ^ 59
def prefixEnd_3447662 : Nat := 4983230072969 + 3 ^ 40 * 3447662 * 2
def baseEnd_3447662 : Nat := 393401720053643386726555

theorem tailTrace_3447662 : CollatzResearch.WordTrace tailWord_3447662 prefixEnd_3447662 393401720053643386726555 := by
  unfold tailWord_3447662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15718320454464607829606155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83831042423811241757899493 15718320454464607829606155)
  ·
    refine ⟨23577480681696911744409233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15718320454464607829606155 23577480681696911744409233)
    ·
      refine ⟨17683110511272683808306925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23577480681696911744409233 17683110511272683808306925)
      ·
        refine ⟨6631166441727256428115097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17683110511272683808306925 6631166441727256428115097)
        ·
          refine ⟨4973374831295442321086323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6631166441727256428115097 4973374831295442321086323)
          ·
            refine ⟨7460062246943163481629485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973374831295442321086323 7460062246943163481629485)
            ·
              refine ⟨2797523342603686305611057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7460062246943163481629485 2797523342603686305611057)
              ·
                refine ⟨2098142506952764729208293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797523342603686305611057 2098142506952764729208293)
                ·
                  refine ⟨393401720053643386726555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098142506952764729208293 393401720053643386726555)
                  ·
                    rfl

theorem cell22_3447662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_3447662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447662 prefixEnd_3447662 := by exact prefixLift 3447662
  have htrace : WordTrace (prefixWord ++ tailWord_3447662) baseStart_3447662 baseEnd_3447662 := by
    simpa [prefixWord, tailWord_3447662, baseEnd_3447662] using wordTrace_append hprefix tailTrace_3447662
  have hstable : (prefixWord ++ tailWord_3447662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447662).length < 2 ^ (prefixWord ++ tailWord_3447662).sum := by decide
  have hdescent : baseEnd_3447662 < baseStart_3447662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447699 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 3, 7]
def baseStart_3447699 : Nat := 118140960795 + 3447699 * 2 ^ 59
def prefixEnd_3447699 : Nat := 4983230072969 + 3 ^ 40 * 3447699 * 2
def baseEnd_3447699 : Nat := 1180217826017074397004551

theorem tailTrace_3447699 : CollatzResearch.WordTrace tailWord_3447699 prefixEnd_3447699 1180217826017074397004551 := by
  unfold tailWord_3447699
  simp only [CollatzResearch.WordTrace]
  refine ⟨125747913136582817955946151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83831942091055211970630767 125747913136582817955946151)
  ·
    refine ⟨188621869704874226933919227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125747913136582817955946151 188621869704874226933919227)
    ·
      refine ⟨282932804557311340400878841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188621869704874226933919227 282932804557311340400878841)
      ·
        refine ⟨212199603417983505300659131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282932804557311340400878841 212199603417983505300659131)
        ·
          refine ⟨318299405126975257950988697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212199603417983505300659131 318299405126975257950988697)
          ·
            refine ⟨238724553845231443463241523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318299405126975257950988697 238724553845231443463241523)
            ·
              refine ⟨358086830767847165194862285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238724553845231443463241523 358086830767847165194862285)
              ·
                refine ⟨134282561537942686948073357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358086830767847165194862285 134282561537942686948073357)
                ·
                  refine ⟨50355960576728507605527509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134282561537942686948073357 50355960576728507605527509)
                  ·
                    refine ⟨1180217826017074397004551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50355960576728507605527509 1180217826017074397004551)
                    ·
                      rfl

theorem cell22_3447699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_3447699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447699 prefixEnd_3447699 := by exact prefixLift 3447699
  have htrace : WordTrace (prefixWord ++ tailWord_3447699) baseStart_3447699 baseEnd_3447699 := by
    simpa [prefixWord, tailWord_3447699, baseEnd_3447699] using wordTrace_append hprefix tailTrace_3447699
  have hstable : (prefixWord ++ tailWord_3447699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447699).length < 2 ^ (prefixWord ++ tailWord_3447699).sum := by decide
  have hdescent : baseEnd_3447699 < baseStart_3447699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447716 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_3447716 : Nat := 118140960795 + 3447716 * 2 ^ 59
def prefixEnd_3447716 : Nat := 4983230072969 + 3 ^ 40 * 3447716 * 2
def baseEnd_3447716 : Nat := 1180223645464492019329499

theorem tailTrace_3447716 : CollatzResearch.WordTrace tailWord_3447716 prefixEnd_3447716 1180223645464492019329499 := by
  unfold tailWord_3447716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62874266588760614929657501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83832355451680819906210001 62874266588760614929657501)
  ·
    refine ⟨23577849970785230598621563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62874266588760614929657501 23577849970785230598621563)
    ·
      refine ⟨35366774956177845897932345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23577849970785230598621563 35366774956177845897932345)
      ·
        refine ⟨26525081217133384423449259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35366774956177845897932345 26525081217133384423449259)
        ·
          refine ⟨39787621825700076635173889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26525081217133384423449259 39787621825700076635173889)
          ·
            refine ⟨29840716369275057476380417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39787621825700076635173889 29840716369275057476380417)
            ·
              refine ⟨22380537276956293107285313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29840716369275057476380417 22380537276956293107285313)
              ·
                refine ⟨16785402957717219830463985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22380537276956293107285313 16785402957717219830463985)
                ·
                  refine ⟨12589052218287914872847989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16785402957717219830463985 12589052218287914872847989)
                  ·
                    refine ⟨1180223645464492019329499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12589052218287914872847989 1180223645464492019329499)
                    ·
                      rfl

theorem cell22_3447716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_3447716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447716 prefixEnd_3447716 := by exact prefixLift 3447716
  have htrace : WordTrace (prefixWord ++ tailWord_3447716) baseStart_3447716 baseEnd_3447716 := by
    simpa [prefixWord, tailWord_3447716, baseEnd_3447716] using wordTrace_append hprefix tailTrace_3447716
  have hstable : (prefixWord ++ tailWord_3447716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447716).length < 2 ^ (prefixWord ++ tailWord_3447716).sum := by decide
  have hdescent : baseEnd_3447716 < baseStart_3447716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447761 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_3447761 : Nat := 118140960795 + 3447761 * 2 ^ 59
def prefixEnd_3447761 : Nat := 4983230072969 + 3 ^ 40 * 3447761 * 2
def baseEnd_3447761 : Nat := 1180239049884126901954361

theorem tailTrace_3447761 : CollatzResearch.WordTrace tailWord_3447761 prefixEnd_3447761 1180239049884126901954361 := by
  unfold tailWord_3447761
  simp only [CollatzResearch.WordTrace]
  refine ⟨125750174462358202544703137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83833449641572135029802091 125750174462358202544703137)
  ·
    refine ⟨94312630846768651908527353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125750174462358202544703137 94312630846768651908527353)
    ·
      refine ⟨70734473135076488931395515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94312630846768651908527353 70734473135076488931395515)
      ·
        refine ⟨106101709702614733397093273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70734473135076488931395515 106101709702614733397093273)
        ·
          refine ⟨79576282276961050047819955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106101709702614733397093273 79576282276961050047819955)
          ·
            refine ⟨119364423415441575071729933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79576282276961050047819955 119364423415441575071729933)
            ·
              refine ⟨44761658780790590651898725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119364423415441575071729933 44761658780790590651898725)
              ·
                refine ⟨8392811021398235747231011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44761658780790590651898725 8392811021398235747231011)
                ·
                  refine ⟨12589216532097353620846517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8392811021398235747231011 12589216532097353620846517)
                  ·
                    refine ⟨1180239049884126901954361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12589216532097353620846517 1180239049884126901954361)
                    ·
                      rfl

theorem cell22_3447761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_3447761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447761 prefixEnd_3447761 := by exact prefixLift 3447761
  have htrace : WordTrace (prefixWord ++ tailWord_3447761) baseStart_3447761 baseEnd_3447761 := by
    simpa [prefixWord, tailWord_3447761, baseEnd_3447761] using wordTrace_append hprefix tailTrace_3447761
  have hstable : (prefixWord ++ tailWord_3447761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447761).length < 2 ^ (prefixWord ++ tailWord_3447761).sum := by decide
  have hdescent : baseEnd_3447761 < baseStart_3447761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447765 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3447765 : Nat := 118140960795 + 3447765 * 2 ^ 59
def prefixEnd_3447765 : Nat := 4983230072969 + 3 ^ 40 * 3447765 * 2
def baseEnd_3447765 : Nat := 1180240419165872224854349

theorem tailTrace_3447765 : CollatzResearch.WordTrace tailWord_3447765 prefixEnd_3447765 1180240419165872224854349 := by
  unfold tailWord_3447765
  simp only [CollatzResearch.WordTrace]
  refine ⟨125750320354343711227848749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83833546902895807485232499 125750320354343711227848749)
  ·
    refine ⟨47156370132878891710443281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125750320354343711227848749 47156370132878891710443281)
    ·
      refine ⟨35367277599659168782832461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47156370132878891710443281 35367277599659168782832461)
      ·
        refine ⟨13262729099872188293562173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35367277599659168782832461 13262729099872188293562173)
        ·
          refine ⟨4973523412452070610085815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13262729099872188293562173 4973523412452070610085815)
          ·
            refine ⟨7460285118678105915128723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973523412452070610085815 7460285118678105915128723)
            ·
              refine ⟨11190427678017158872693085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460285118678105915128723 11190427678017158872693085)
              ·
                refine ⟨4196410379256434577259907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11190427678017158872693085 4196410379256434577259907)
                ·
                  refine ⟨6294615568884651865889861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196410379256434577259907 6294615568884651865889861)
                  ·
                    refine ⟨1180240419165872224854349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6294615568884651865889861 1180240419165872224854349)
                    ·
                      rfl

theorem cell22_3447765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3447765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447765 prefixEnd_3447765 := by exact prefixLift 3447765
  have htrace : WordTrace (prefixWord ++ tailWord_3447765) baseStart_3447765 baseEnd_3447765 := by
    simpa [prefixWord, tailWord_3447765, baseEnd_3447765] using wordTrace_append hprefix tailTrace_3447765
  have hstable : (prefixWord ++ tailWord_3447765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447765).length < 2 ^ (prefixWord ++ tailWord_3447765).sum := by decide
  have hdescent : baseEnd_3447765 < baseStart_3447765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447851 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 1, 7]
def baseStart_3447851 : Nat := 118140960795 + 3447851 * 2 ^ 59
def prefixEnd_3447851 : Nat := 4983230072969 + 3 ^ 40 * 3447851 * 2
def baseEnd_3447851 : Nat := 1180269858723396667204085

theorem tailTrace_3447851 : CollatzResearch.WordTrace tailWord_3447851 prefixEnd_3447851 1180269858723396667204085 := by
  unfold tailWord_3447851
  simp only [CollatzResearch.WordTrace]
  refine ⟨125753457032032147915479407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83835638021354765276986271 125753457032032147915479407)
  ·
    refine ⟨188630185548048221873219111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125753457032032147915479407 188630185548048221873219111)
    ·
      refine ⟨282945278322072332809828667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188630185548048221873219111 282945278322072332809828667)
      ·
        refine ⟨424417917483108499214743001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282945278322072332809828667 424417917483108499214743001)
        ·
          refine ⟨318313438112331374411057251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424417917483108499214743001 318313438112331374411057251)
          ·
            refine ⟨477470157168497061616585877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318313438112331374411057251 477470157168497061616585877)
            ·
              refine ⟨22381413617273299763277463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 477470157168497061616585877 22381413617273299763277463)
              ·
                refine ⟨33572120425909949644916195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22381413617273299763277463 33572120425909949644916195)
                ·
                  refine ⟨50358180638864924467374293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33572120425909949644916195 50358180638864924467374293)
                  ·
                    refine ⟨1180269858723396667204085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50358180638864924467374293 1180269858723396667204085)
                    ·
                      rfl

theorem cell22_3447851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_3447851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447851 prefixEnd_3447851 := by exact prefixLift 3447851
  have htrace : WordTrace (prefixWord ++ tailWord_3447851) baseStart_3447851 baseEnd_3447851 := by
    simpa [prefixWord, tailWord_3447851, baseEnd_3447851] using wordTrace_append hprefix tailTrace_3447851
  have hstable : (prefixWord ++ tailWord_3447851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447851).length < 2 ^ (prefixWord ++ tailWord_3447851).sum := by decide
  have hdescent : baseEnd_3447851 < baseStart_3447851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447881 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 10]
def baseStart_3447881 : Nat := 118140960795 + 3447881 * 2 ^ 59
def prefixEnd_3447881 : Nat := 4983230072969 + 3 ^ 40 * 3447881 * 2
def baseEnd_3447881 : Nat := 393426709445495529651331

theorem tailTrace_3447881 : CollatzResearch.WordTrace tailWord_3447881 prefixEnd_3447881 393426709445495529651331 := by
  unfold tailWord_3447881
  simp only [CollatzResearch.WordTrace]
  refine ⟨125754551221923463039071497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83836367481282308692714331 125754551221923463039071497)
  ·
    refine ⟨94315913416442597279303623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125754551221923463039071497 94315913416442597279303623)
    ·
      refine ⟨141473870124663895918955435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94315913416442597279303623 141473870124663895918955435)
      ·
        refine ⟨212210805186995843878433153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141473870124663895918955435 212210805186995843878433153)
        ·
          refine ⟨159158103890246882908824865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212210805186995843878433153 159158103890246882908824865)
          ·
            refine ⟨119368577917685162181618649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159158103890246882908824865 119368577917685162181618649)
            ·
              refine ⟨89526433438263871636213987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119368577917685162181618649 89526433438263871636213987)
              ·
                refine ⟨134289650157395807454320981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89526433438263871636213987 134289650157395807454320981)
                ·
                  refine ⟨393426709445495529651331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 134289650157395807454320981 393426709445495529651331)
                  ·
                    rfl

theorem cell22_3447881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_3447881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447881 prefixEnd_3447881 := by exact prefixLift 3447881
  have htrace : WordTrace (prefixWord ++ tailWord_3447881) baseStart_3447881 baseEnd_3447881 := by
    simpa [prefixWord, tailWord_3447881, baseEnd_3447881] using wordTrace_append hprefix tailTrace_3447881
  have hstable : (prefixWord ++ tailWord_3447881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447881).length < 2 ^ (prefixWord ++ tailWord_3447881).sum := by decide
  have hdescent : baseEnd_3447881 < baseStart_3447881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447902 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3447902 : Nat := 118140960795 + 3447902 * 2 ^ 59
def prefixEnd_3447902 : Nat := 4983230072969 + 3 ^ 40 * 3447902 * 2
def baseEnd_3447902 : Nat := 1180287317065649534178929

theorem tailTrace_3447902 : CollatzResearch.WordTrace tailWord_3447902 prefixEnd_3447902 1180287317065649534178929 := by
  unfold tailWord_3447902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719414644355922953198245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83836878103231589083723973 15719414644355922953198245)
  ·
    refine ⟨2947390245816735553724671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15719414644355922953198245 2947390245816735553724671)
    ·
      refine ⟨4421085368725103330587007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947390245816735553724671 4421085368725103330587007)
      ·
        refine ⟨6631628053087654995880511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4421085368725103330587007 6631628053087654995880511)
        ·
          refine ⟨9947442079631482493820767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631628053087654995880511 9947442079631482493820767)
          ·
            refine ⟨14921163119447223740731151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9947442079631482493820767 14921163119447223740731151)
            ·
              refine ⟨22381744679170835611096727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921163119447223740731151 22381744679170835611096727)
              ·
                refine ⟨33572617018756253416645091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22381744679170835611096727 33572617018756253416645091)
                ·
                  refine ⟨50358925528134380124967637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33572617018756253416645091 50358925528134380124967637)
                  ·
                    refine ⟨1180287317065649534178929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50358925528134380124967637 1180287317065649534178929)
                    ·
                      rfl

theorem cell22_3447902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3447902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447902 prefixEnd_3447902 := by exact prefixLift 3447902
  have htrace : WordTrace (prefixWord ++ tailWord_3447902) baseStart_3447902 baseEnd_3447902 := by
    simpa [prefixWord, tailWord_3447902, baseEnd_3447902] using wordTrace_append hprefix tailTrace_3447902
  have hstable : (prefixWord ++ tailWord_3447902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447902).length < 2 ^ (prefixWord ++ tailWord_3447902).sum := by decide
  have hdescent : baseEnd_3447902 < baseStart_3447902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447913 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_3447913 : Nat := 118140960795 + 3447913 * 2 ^ 59
def prefixEnd_3447913 : Nat := 4983230072969 + 3 ^ 40 * 3447913 * 2
def baseEnd_3447913 : Nat := 1180291082590449172153895

theorem tailTrace_3447913 : CollatzResearch.WordTrace tailWord_3447913 prefixEnd_3447913 1180291082590449172153895 := by
  unfold tailWord_3447913
  simp only [CollatzResearch.WordTrace]
  refine ⟨125755718357807532504236393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83837145571871688336157595 125755718357807532504236393)
  ·
    refine ⟨94316788768355649378177295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125755718357807532504236393 94316788768355649378177295)
    ·
      refine ⟨141475183152533474067265943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94316788768355649378177295 141475183152533474067265943)
      ·
        refine ⟨212212774728800211100898915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141475183152533474067265943 212212774728800211100898915)
        ·
          refine ⟨318319162093200316651348373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212212774728800211100898915 318319162093200316651348373)
          ·
            refine ⟨14921210723118764843031955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 318319162093200316651348373 14921210723118764843031955)
            ·
              refine ⟨22381816084678147264547933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921210723118764843031955 22381816084678147264547933)
              ·
                refine ⟨8393181031754305224205475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22381816084678147264547933 8393181031754305224205475)
                ·
                  refine ⟨12589771547631457836308213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8393181031754305224205475 12589771547631457836308213)
                  ·
                    refine ⟨1180291082590449172153895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12589771547631457836308213 1180291082590449172153895)
                    ·
                      rfl

theorem cell22_3447913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_3447913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447913 prefixEnd_3447913 := by exact prefixLift 3447913
  have htrace : WordTrace (prefixWord ++ tailWord_3447913) baseStart_3447913 baseEnd_3447913 := by
    simpa [prefixWord, tailWord_3447913, baseEnd_3447913] using wordTrace_append hprefix tailTrace_3447913
  have hstable : (prefixWord ++ tailWord_3447913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447913).length < 2 ^ (prefixWord ++ tailWord_3447913).sum := by decide
  have hdescent : baseEnd_3447913 < baseStart_3447913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447964 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_3447964 : Nat := 118140960795 + 3447964 * 2 ^ 59
def prefixEnd_3447964 : Nat := 4983230072969 + 3 ^ 40 * 3447964 * 2
def baseEnd_3447964 : Nat := 1180308540932702039128739

theorem tailTrace_3447964 : CollatzResearch.WordTrace tailWord_3447964 prefixEnd_3447964 1180308540932702039128739 := by
  unfold tailWord_3447964
  simp only [CollatzResearch.WordTrace]
  refine ⟨62878789240311384107171473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83838385653748512142895297 62878789240311384107171473)
  ·
    refine ⟨47159091930233538080378605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62878789240311384107171473 47159091930233538080378605)
    ·
      refine ⟨17684659473837576780141977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47159091930233538080378605 17684659473837576780141977)
      ·
        refine ⟨13263494605378182585106483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17684659473837576780141977 13263494605378182585106483)
        ·
          refine ⟨19895241908067273877659725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263494605378182585106483 19895241908067273877659725)
          ·
            refine ⟨7460715715525227704122397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19895241908067273877659725 7460715715525227704122397)
            ·
              refine ⟨2797768393321960389045899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7460715715525227704122397 2797768393321960389045899)
              ·
                refine ⟨4196652589982940583568849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797768393321960389045899 4196652589982940583568849)
                ·
                  refine ⟨3147489442487205437676637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196652589982940583568849 3147489442487205437676637)
                  ·
                    refine ⟨1180308540932702039128739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3147489442487205437676637 1180308540932702039128739)
                    ·
                      rfl

theorem cell22_3447964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_3447964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447964 prefixEnd_3447964 := by exact prefixLift 3447964
  have htrace : WordTrace (prefixWord ++ tailWord_3447964) baseStart_3447964 baseEnd_3447964 := by
    simpa [prefixWord, tailWord_3447964, baseEnd_3447964] using wordTrace_append hprefix tailTrace_3447964
  have hstable : (prefixWord ++ tailWord_3447964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447964).length < 2 ^ (prefixWord ++ tailWord_3447964).sum := by decide
  have hdescent : baseEnd_3447964 < baseStart_3447964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447992 : List Nat := [2, 1, 2, 1, 2, 1, 2, 7, 1, 3]
def baseStart_3447992 : Nat := 118140960795 + 3447992 * 2 ^ 59
def prefixEnd_3447992 : Nat := 4983230072969 + 3 ^ 40 * 3447992 * 2
def baseEnd_3447992 : Nat := 1180318125904919299428653

theorem tailTrace_3447992 : CollatzResearch.WordTrace tailWord_3447992 prefixEnd_3447992 1180318125904919299428653 := by
  unfold tailWord_3447992
  simp only [CollatzResearch.WordTrace]
  refine ⟨62879299862260664498181115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83839066483014219330908153 62879299862260664498181115)
  ·
    refine ⟨94318949793390996747271673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62879299862260664498181115 94318949793390996747271673)
    ·
      refine ⟨70739212345043247560453755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94318949793390996747271673 70739212345043247560453755)
      ·
        refine ⟨106108818517564871340680633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70739212345043247560453755 106108818517564871340680633)
        ·
          refine ⟨79581613888173653505510475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106108818517564871340680633 79581613888173653505510475)
          ·
            refine ⟨119372420832260480258265713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79581613888173653505510475 119372420832260480258265713)
            ·
              refine ⟨89529315624195360193699285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119372420832260480258265713 89529315624195360193699285)
              ·
                refine ⟨2098343334942078754539827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89529315624195360193699285 2098343334942078754539827)
                ·
                  refine ⟨3147515002413118131809741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098343334942078754539827 3147515002413118131809741)
                  ·
                    refine ⟨1180318125904919299428653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3147515002413118131809741 1180318125904919299428653)
                    ·
                      rfl

theorem cell22_3447992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_3447992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3447992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3447992 prefixEnd_3447992 := by exact prefixLift 3447992
  have htrace : WordTrace (prefixWord ++ tailWord_3447992) baseStart_3447992 baseEnd_3447992 := by
    simpa [prefixWord, tailWord_3447992, baseEnd_3447992] using wordTrace_append hprefix tailTrace_3447992
  have hstable : (prefixWord ++ tailWord_3447992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447992).length < 2 ^ (prefixWord ++ tailWord_3447992).sum := by decide
  have hdescent : baseEnd_3447992 < baseStart_3447992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448003 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 2, 5]
def baseStart_3448003 : Nat := 118140960795 + 3448003 * 2 ^ 59
def prefixEnd_3448003 : Nat := 4983230072969 + 3 ^ 40 * 3448003 * 2
def baseEnd_3448003 : Nat := 1180321891429718937403619

theorem tailTrace_3448003 : CollatzResearch.WordTrace tailWord_3448003 prefixEnd_3448003 1180321891429718937403619 := by
  unfold tailWord_3448003
  simp only [CollatzResearch.WordTrace]
  refine ⟨125759000927481477875012663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83839333951654318583341775 125759000927481477875012663)
  ·
    refine ⟨188638501391222216812518995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125759000927481477875012663 188638501391222216812518995)
    ·
      refine ⟨282957752086833325218778493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188638501391222216812518995 282957752086833325218778493)
      ·
        refine ⟨106109157032562496957041935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282957752086833325218778493 106109157032562496957041935)
        ·
          refine ⟨159163735548843745435562903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106109157032562496957041935 159163735548843745435562903)
          ·
            refine ⟨238745603323265618153344355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159163735548843745435562903 238745603323265618153344355)
            ·
              refine ⟨358118404984898427230016533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238745603323265618153344355 358118404984898427230016533)
              ·
                refine ⟨16786800233667113776407025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 358118404984898427230016533 16786800233667113776407025)
                ·
                  refine ⟨12590100175250335332305269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16786800233667113776407025 12590100175250335332305269)
                  ·
                    refine ⟨1180321891429718937403619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12590100175250335332305269 1180321891429718937403619)
                    ·
                      rfl

theorem cell22_3448003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_3448003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448003 prefixEnd_3448003 := by exact prefixLift 3448003
  have htrace : WordTrace (prefixWord ++ tailWord_3448003) baseStart_3448003 baseEnd_3448003 := by
    simpa [prefixWord, tailWord_3448003, baseEnd_3448003] using wordTrace_append hprefix tailTrace_3448003
  have hstable : (prefixWord ++ tailWord_3448003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448003).length < 2 ^ (prefixWord ++ tailWord_3448003).sum := by decide
  have hdescent : baseEnd_3448003 < baseStart_3448003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448067 : List Nat := [1, 1, 1, 3, 2, 5, 1, 4, 4]
def baseStart_3448067 : Nat := 118140960795 + 3448067 * 2 ^ 59
def prefixEnd_3448067 : Nat := 4983230072969 + 3 ^ 40 * 3448067 * 2
def baseEnd_3448067 : Nat := 393447933312548034601141

theorem tailTrace_3448067 : CollatzResearch.WordTrace tailWord_3448067 prefixEnd_3448067 393447933312548034601141 := by
  unfold tailWord_3448067
  simp only [CollatzResearch.WordTrace]
  refine ⟨125761335199249616805342455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83840890132833077870228303 125761335199249616805342455)
  ·
    refine ⟨188642002798874425208013683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125761335199249616805342455 188642002798874425208013683)
    ·
      refine ⟨282963004198311637812020525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188642002798874425208013683 282963004198311637812020525)
      ·
        refine ⟨106111126574366864179507697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282963004198311637812020525 106111126574366864179507697)
        ·
          refine ⟨79583344930775148134630773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106111126574366864179507697 79583344930775148134630773)
          ·
            refine ⟨7460938587260170137621635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79583344930775148134630773 7460938587260170137621635)
            ·
              refine ⟨11191407880890255206432453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460938587260170137621635 11191407880890255206432453)
              ·
                refine ⟨2098388977666922851206085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11191407880890255206432453 2098388977666922851206085)
                ·
                  refine ⟨393447933312548034601141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098388977666922851206085 393447933312548034601141)
                  ·
                    rfl

theorem cell22_3448067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 4].length) (baseStart_3448067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448067 prefixEnd_3448067 := by exact prefixLift 3448067
  have htrace : WordTrace (prefixWord ++ tailWord_3448067) baseStart_3448067 baseEnd_3448067 := by
    simpa [prefixWord, tailWord_3448067, baseEnd_3448067] using wordTrace_append hprefix tailTrace_3448067
  have hstable : (prefixWord ++ tailWord_3448067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448067).length < 2 ^ (prefixWord ++ tailWord_3448067).sum := by decide
  have hdescent : baseEnd_3448067 < baseStart_3448067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448127 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 3, 3]
def baseStart_3448127 : Nat := 118140960795 + 3448127 * 2 ^ 59
def prefixEnd_3448127 : Nat := 4983230072969 + 3 ^ 40 * 3448127 * 2
def baseEnd_3448127 : Nat := 1180364339163823947303239

theorem tailTrace_3448127 : CollatzResearch.WordTrace tailWord_3448127 prefixEnd_3448127 1180364339163823947303239 := by
  unfold tailWord_3448127
  simp only [CollatzResearch.WordTrace]
  refine ⟨125763523579032247052526635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83842349052688164701684423 125763523579032247052526635)
  ·
    refine ⟨188645285368548370578789953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125763523579032247052526635 188645285368548370578789953)
    ·
      refine ⟨141483964026411277934092465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188645285368548370578789953 141483964026411277934092465)
      ·
        refine ⟨106112973019808458450569349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141483964026411277934092465 106112973019808458450569349)
        ·
          refine ⟨19896182441214085959481753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106112973019808458450569349 19896182441214085959481753)
          ·
            refine ⟨14922136830910564469611315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19896182441214085959481753 14922136830910564469611315)
            ·
              refine ⟨22383205246365846704416973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14922136830910564469611315 22383205246365846704416973)
              ·
                refine ⟨8393701967387192514156365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22383205246365846704416973 8393701967387192514156365)
                ·
                  refine ⟨3147638237770197192808637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8393701967387192514156365 3147638237770197192808637)
                  ·
                    refine ⟨1180364339163823947303239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3147638237770197192808637 1180364339163823947303239)
                    ·
                      rfl

theorem cell22_3448127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_3448127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448127 prefixEnd_3448127 := by exact prefixLift 3448127
  have htrace : WordTrace (prefixWord ++ tailWord_3448127) baseStart_3448127 baseEnd_3448127 := by
    simpa [prefixWord, tailWord_3448127, baseEnd_3448127] using wordTrace_append hprefix tailTrace_3448127
  have hstable : (prefixWord ++ tailWord_3448127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448127).length < 2 ^ (prefixWord ++ tailWord_3448127).sum := by decide
  have hdescent : baseEnd_3448127 < baseStart_3448127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448217 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_3448217 : Nat := 118140960795 + 3448217 * 2 ^ 59
def prefixEnd_3448217 : Nat := 4983230072969 + 3 ^ 40 * 3448217 * 2
def baseEnd_3448217 : Nat := 1180395148003093712552963

theorem tailTrace_3448217 : CollatzResearch.WordTrace tailWord_3448217 prefixEnd_3448217 1180395148003093712552963 := by
  unfold tailWord_3448217
  simp only [CollatzResearch.WordTrace]
  refine ⟨125766806148706192423302905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83844537432470794948868603 125766806148706192423302905)
  ·
    refine ⟨94325104611529644317477179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125766806148706192423302905 94325104611529644317477179)
    ·
      refine ⟨141487656917294466476215769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94325104611529644317477179 141487656917294466476215769)
      ·
        refine ⟨106115742687970849857161827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141487656917294466476215769 106115742687970849857161827)
        ·
          refine ⟨159173614031956274785742741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106115742687970849857161827 159173614031956274785742741)
          ·
            refine ⟨7461263157747950380581691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159173614031956274785742741 7461263157747950380581691)
            ·
              refine ⟨11191894736621925570872537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461263157747950380581691 11191894736621925570872537)
              ·
                refine ⟨8393921052466444178154403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11191894736621925570872537 8393921052466444178154403)
                ·
                  refine ⟨12590881578699666267231605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8393921052466444178154403 12590881578699666267231605)
                  ·
                    refine ⟨1180395148003093712552963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12590881578699666267231605 1180395148003093712552963)
                    ·
                      rfl

theorem cell22_3448217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_3448217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448217 prefixEnd_3448217 := by exact prefixLift 3448217
  have htrace : WordTrace (prefixWord ++ tailWord_3448217) baseStart_3448217 baseEnd_3448217 := by
    simpa [prefixWord, tailWord_3448217, baseEnd_3448217] using wordTrace_append hprefix tailTrace_3448217
  have hstable : (prefixWord ++ tailWord_3448217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448217).length < 2 ^ (prefixWord ++ tailWord_3448217).sum := by decide
  have hdescent : baseEnd_3448217 < baseStart_3448217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448221 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3448221 : Nat := 118140960795 + 3448221 * 2 ^ 59
def prefixEnd_3448221 : Nat := 4983230072969 + 3 ^ 40 * 3448221 * 2
def baseEnd_3448221 : Nat := 1180396517284839035452951

theorem tailTrace_3448221 : CollatzResearch.WordTrace tailWord_3448221 prefixEnd_3448221 1180396517284839035452951 := by
  unfold tailWord_3448221
  simp only [CollatzResearch.WordTrace]
  refine ⟨125766952040691701106448517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83844634693794467404299011 125766952040691701106448517)
  ·
    refine ⟨23581303507629693957459097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125766952040691701106448517 23581303507629693957459097)
    ·
      refine ⟨17685977630722270468094323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23581303507629693957459097 17685977630722270468094323)
      ·
        refine ⟨26528966446083405702141485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17685977630722270468094323 26528966446083405702141485)
        ·
          refine ⟨9948362417281277138303057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26528966446083405702141485 9948362417281277138303057)
          ·
            refine ⟨7461271812960957853727293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9948362417281277138303057 7461271812960957853727293)
            ·
              refine ⟨2797976929860359195147735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7461271812960957853727293 2797976929860359195147735)
              ·
                refine ⟨4196965394790538792721603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797976929860359195147735 4196965394790538792721603)
                ·
                  refine ⟨6295448092185808189082405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196965394790538792721603 6295448092185808189082405)
                  ·
                    refine ⟨1180396517284839035452951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6295448092185808189082405 1180396517284839035452951)
                    ·
                      rfl

theorem cell22_3448221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3448221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448221 prefixEnd_3448221 := by exact prefixLift 3448221
  have htrace : WordTrace (prefixWord ++ tailWord_3448221) baseStart_3448221 baseEnd_3448221 := by
    simpa [prefixWord, tailWord_3448221, baseEnd_3448221] using wordTrace_append hprefix tailTrace_3448221
  have hstable : (prefixWord ++ tailWord_3448221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448221).length < 2 ^ (prefixWord ++ tailWord_3448221).sum := by decide
  have hdescent : baseEnd_3448221 < baseStart_3448221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448296 : List Nat := [2, 1, 4, 1, 1, 2, 1, 6, 1, 3]
def baseStart_3448296 : Nat := 118140960795 + 3448296 * 2 ^ 59
def prefixEnd_3448296 : Nat := 4983230072969 + 3 ^ 40 * 3448296 * 2
def baseEnd_3448296 : Nat := 1180422191317563839827721

theorem tailTrace_3448296 : CollatzResearch.WordTrace tailWord_3448296 prefixEnd_3448296 1180422191317563839827721 := by
  unfold tailWord_3448296
  simp only [CollatzResearch.WordTrace]
  refine ⟨62884843757709994457714371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83846458343613325943619161 62884843757709994457714371)
  ·
    refine ⟨94327265636564991686571557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62884843757709994457714371 94327265636564991686571557)
    ·
      refine ⟨17686362306855935941232167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94327265636564991686571557 17686362306855935941232167)
      ·
        refine ⟨26529543460283903911848251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17686362306855935941232167 26529543460283903911848251)
        ·
          refine ⟨39794315190425855867772377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26529543460283903911848251 39794315190425855867772377)
          ·
            refine ⟨29845736392819391900829283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39794315190425855867772377 29845736392819391900829283)
            ·
              refine ⟨44768604589229087851243925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29845736392819391900829283 44768604589229087851243925)
              ·
                refine ⟨2098528340120113493027059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44768604589229087851243925 2098528340120113493027059)
                ·
                  refine ⟨3147792510180170239540589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098528340120113493027059 3147792510180170239540589)
                  ·
                    refine ⟨1180422191317563839827721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3147792510180170239540589 1180422191317563839827721)
                    ·
                      rfl

theorem cell22_3448296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_3448296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448296 prefixEnd_3448296 := by exact prefixLift 3448296
  have htrace : WordTrace (prefixWord ++ tailWord_3448296) baseStart_3448296 baseEnd_3448296 := by
    simpa [prefixWord, tailWord_3448296, baseEnd_3448296] using wordTrace_append hprefix tailTrace_3448296
  have hstable : (prefixWord ++ tailWord_3448296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448296).length < 2 ^ (prefixWord ++ tailWord_3448296).sum := by decide
  have hdescent : baseEnd_3448296 < baseStart_3448296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448339 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 1, 4]
def baseStart_3448339 : Nat := 118140960795 + 3448339 * 2 ^ 59
def prefixEnd_3448339 : Nat := 4983230072969 + 3 ^ 40 * 3448339 * 2
def baseEnd_3448339 : Nat := 1180436911096326061002589

theorem tailTrace_3448339 : CollatzResearch.WordTrace tailWord_3448339 prefixEnd_3448339 1180436911096326061002589 := by
  unfold tailWord_3448339
  simp only [CollatzResearch.WordTrace]
  refine ⟨125771255854264207259244071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83847503902842804839496047 125771255854264207259244071)
  ·
    refine ⟨188656883781396310888866107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125771255854264207259244071 188656883781396310888866107)
    ·
      refine ⟨282985325672094466333299161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188656883781396310888866107 282985325672094466333299161)
      ·
        refine ⟨212238994254070849749974371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282985325672094466333299161 212238994254070849749974371)
        ·
          refine ⟨318358491381106274624961557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212238994254070849749974371 318358491381106274624961557)
          ·
            refine ⟨14923054283489356623045073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 318358491381106274624961557 14923054283489356623045073)
            ·
              refine ⟨11192290712617017467283805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14923054283489356623045073 11192290712617017467283805)
              ·
                refine ⟨4197109017231381550231427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11192290712617017467283805 4197109017231381550231427)
                ·
                  refine ⟨6295663525847072325347141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197109017231381550231427 6295663525847072325347141)
                  ·
                    refine ⟨1180436911096326061002589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6295663525847072325347141 1180436911096326061002589)
                    ·
                      rfl

theorem cell22_3448339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 4].length) (baseStart_3448339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448339 prefixEnd_3448339 := by exact prefixLift 3448339
  have htrace : WordTrace (prefixWord ++ tailWord_3448339) baseStart_3448339 baseEnd_3448339 := by
    simpa [prefixWord, tailWord_3448339, baseEnd_3448339] using wordTrace_append hprefix tailTrace_3448339
  have hstable : (prefixWord ++ tailWord_3448339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448339).length < 2 ^ (prefixWord ++ tailWord_3448339).sum := by decide
  have hdescent : baseEnd_3448339 < baseStart_3448339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448354 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3448354 : Nat := 118140960795 + 3448354 * 2 ^ 59
def prefixEnd_3448354 : Nat := 4983230072969 + 3 ^ 40 * 3448354 * 2
def baseEnd_3448354 : Nat := 393480681967623673959181

theorem tailTrace_3448354 : CollatzResearch.WordTrace tailWord_3448354 prefixEnd_3448354 393480681967623673959181 := by
  unfold tailWord_3448354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31442950737302466205260029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83847868632806576547360077 31442950737302466205260029)
  ·
    refine ⟨11791106526488424826972511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31442950737302466205260029 11791106526488424826972511)
    ·
      refine ⟨17686659789732637240458767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11791106526488424826972511 17686659789732637240458767)
      ·
        refine ⟨26529989684598955860688151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17686659789732637240458767 26529989684598955860688151)
        ·
          refine ⟨39794984526898433791032227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26529989684598955860688151 39794984526898433791032227)
          ·
            refine ⟨59692476790347650686548341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39794984526898433791032227 59692476790347650686548341)
            ·
              refine ⟨5596169699095092251863907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59692476790347650686548341 5596169699095092251863907)
              ·
                refine ⟨8394254548642638377795861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596169699095092251863907 8394254548642638377795861)
                ·
                  refine ⟨393480681967623673959181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8394254548642638377795861 393480681967623673959181)
                  ·
                    rfl

theorem cell22_3448354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3448354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448354 prefixEnd_3448354 := by exact prefixLift 3448354
  have htrace : WordTrace (prefixWord ++ tailWord_3448354) baseStart_3448354 baseEnd_3448354 := by
    simpa [prefixWord, tailWord_3448354, baseEnd_3448354] using wordTrace_append hprefix tailTrace_3448354
  have hstable : (prefixWord ++ tailWord_3448354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448354).length < 2 ^ (prefixWord ++ tailWord_3448354).sum := by decide
  have hdescent : baseEnd_3448354 < baseStart_3448354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448360 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 5]
def baseStart_3448360 : Nat := 118140960795 + 3448360 * 2 ^ 59
def prefixEnd_3448360 : Nat := 4983230072969 + 3 ^ 40 * 3448360 * 2
def baseEnd_3448360 : Nat := 393481366608496335409175

theorem tailTrace_3448360 : CollatzResearch.WordTrace tailWord_3448360 prefixEnd_3448360 393481366608496335409175 := by
  unfold tailWord_3448360
  simp only [CollatzResearch.WordTrace]
  refine ⟨62886010893594063922879267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83848014524792085230505689 62886010893594063922879267)
  ·
    refine ⟨94329016340391095884318901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62886010893594063922879267 94329016340391095884318901)
    ·
      refine ⟨8843345281911665239154897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94329016340391095884318901 8843345281911665239154897)
      ·
        refine ⟨6632508961433748929366173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8843345281911665239154897 6632508961433748929366173)
        ·
          refine ⟨2487190860537655848512315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6632508961433748929366173 2487190860537655848512315)
          ·
            refine ⟨3730786290806483772768473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487190860537655848512315 3730786290806483772768473)
            ·
              refine ⟨2798089718104862829576355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730786290806483772768473 2798089718104862829576355)
              ·
                refine ⟨4197134577157294244364533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798089718104862829576355 4197134577157294244364533)
                ·
                  refine ⟨393481366608496335409175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4197134577157294244364533 393481366608496335409175)
                  ·
                    rfl

theorem cell22_3448360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_3448360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448360 prefixEnd_3448360 := by exact prefixLift 3448360
  have htrace : WordTrace (prefixWord ++ tailWord_3448360) baseStart_3448360 baseEnd_3448360 := by
    simpa [prefixWord, tailWord_3448360, baseEnd_3448360] using wordTrace_append hprefix tailTrace_3448360
  have hstable : (prefixWord ++ tailWord_3448360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448360).length < 2 ^ (prefixWord ++ tailWord_3448360).sum := by decide
  have hdescent : baseEnd_3448360 < baseStart_3448360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448448 : List Nat := [2, 1, 1, 2, 1, 4, 4, 3, 1, 3]
def baseStart_3448448 : Nat := 118140960795 + 3448448 * 2 ^ 59
def prefixEnd_3448448 : Nat := 4983230072969 + 3 ^ 40 * 3448448 * 2
def baseEnd_3448448 : Nat := 1180474224023886110027255

theorem tailTrace_3448448 : CollatzResearch.WordTrace tailWord_3448448 prefixEnd_3448448 1180474224023886110027255 := by
  unfold tailWord_3448448
  simp only [CollatzResearch.WordTrace]
  refine ⟨62887615705434659437480999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83850154273912879249974665 62887615705434659437480999)
  ·
    refine ⟨94331423558151989156221499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62887615705434659437480999 94331423558151989156221499)
    ·
      refine ⟨141497135337227983734332249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94331423558151989156221499 141497135337227983734332249)
      ·
        refine ⟨106122851502920987800749187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141497135337227983734332249 106122851502920987800749187)
        ·
          refine ⟨159184277254381481701123781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106122851502920987800749187 159184277254381481701123781)
          ·
            refine ⟨29847051985196527818960709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159184277254381481701123781 29847051985196527818960709)
            ·
              refine ⟨5596322247224348966055133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29847051985196527818960709 5596322247224348966055133)
              ·
                refine ⟨2098620842709130862270675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5596322247224348966055133 2098620842709130862270675)
                ·
                  refine ⟨3147931264063696293406013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098620842709130862270675 3147931264063696293406013)
                  ·
                    refine ⟨1180474224023886110027255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3147931264063696293406013 1180474224023886110027255)
                    ·
                      rfl

theorem cell22_3448448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 3].length) (baseStart_3448448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448448 prefixEnd_3448448 := by exact prefixLift 3448448
  have htrace : WordTrace (prefixWord ++ tailWord_3448448) baseStart_3448448 baseEnd_3448448 := by
    simpa [prefixWord, tailWord_3448448, baseEnd_3448448] using wordTrace_append hprefix tailTrace_3448448
  have hstable : (prefixWord ++ tailWord_3448448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448448).length < 2 ^ (prefixWord ++ tailWord_3448448).sum := by decide
  have hdescent : baseEnd_3448448 < baseStart_3448448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448504 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_3448504 : Nat := 118140960795 + 3448504 * 2 ^ 59
def prefixEnd_3448504 : Nat := 4983230072969 + 3 ^ 40 * 3448504 * 2
def baseEnd_3448504 : Nat := 1180493393968320630627083

theorem tailTrace_3448504 : CollatzResearch.WordTrace tailWord_3448504 prefixEnd_3448504 1180493393968320630627083 := by
  unfold tailWord_3448504
  simp only [CollatzResearch.WordTrace]
  refine ⟨62888636949333220219500283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83851515932444293626000377 62888636949333220219500283)
  ·
    refine ⟨94332955423999830329250425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62888636949333220219500283 94332955423999830329250425)
    ·
      refine ⟨70749716567999872746937819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94332955423999830329250425 70749716567999872746937819)
      ·
        refine ⟨106124574851999809120406729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70749716567999872746937819 106124574851999809120406729)
        ·
          refine ⟨79593431138999856840305047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106124574851999809120406729 79593431138999856840305047)
          ·
            refine ⟨119390146708499785260457571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79593431138999856840305047 119390146708499785260457571)
            ·
              refine ⟨179085220062749677890686357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119390146708499785260457571 179085220062749677890686357)
              ·
                refine ⟨8394619690441391151125923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179085220062749677890686357 8394619690441391151125923)
                ·
                  refine ⟨12591929535662086726688885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394619690441391151125923 12591929535662086726688885)
                  ·
                    refine ⟨1180493393968320630627083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12591929535662086726688885 1180493393968320630627083)
                    ·
                      rfl

theorem cell22_3448504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_3448504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448504 prefixEnd_3448504 := by exact prefixLift 3448504
  have htrace : WordTrace (prefixWord ++ tailWord_3448504) baseStart_3448504 baseEnd_3448504 := by
    simpa [prefixWord, tailWord_3448504, baseEnd_3448504] using wordTrace_append hprefix tailTrace_3448504
  have hstable : (prefixWord ++ tailWord_3448504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448504).length < 2 ^ (prefixWord ++ tailWord_3448504).sum := by decide
  have hdescent : baseEnd_3448504 < baseStart_3448504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448538 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_3448538 : Nat := 118140960795 + 3448538 * 2 ^ 59
def prefixEnd_3448538 : Nat := 4983230072969 + 3 ^ 40 * 3448538 * 2
def baseEnd_3448538 : Nat := 1180505032863155875276979

theorem tailTrace_3448538 : CollatzResearch.WordTrace tailWord_3448538 prefixEnd_3448538 1180505032863155875276979 := by
  unfold tailWord_3448538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31444628495135816061434567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83852342653695509497158845 31444628495135816061434567)
  ·
    refine ⟨47166942742703724092151851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31444628495135816061434567 47166942742703724092151851)
    ·
      refine ⟨70750414114055586138227777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47166942742703724092151851 70750414114055586138227777)
      ·
        refine ⟨53062810585541689603670833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70750414114055586138227777 53062810585541689603670833)
        ·
          refine ⟨39797107939156267202753125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53062810585541689603670833 39797107939156267202753125)
          ·
            refine ⟨7461957738591800100516211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39797107939156267202753125 7461957738591800100516211)
            ·
              refine ⟨11192936607887700150774317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461957738591800100516211 11192936607887700150774317)
              ·
                refine ⟨4197351227957887556540369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11192936607887700150774317 4197351227957887556540369)
                ·
                  refine ⟨3148013420968415667405277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4197351227957887556540369 3148013420968415667405277)
                  ·
                    refine ⟨1180505032863155875276979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148013420968415667405277 1180505032863155875276979)
                    ·
                      rfl

theorem cell22_3448538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_3448538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448538 prefixEnd_3448538 := by exact prefixLift 3448538
  have htrace : WordTrace (prefixWord ++ tailWord_3448538) baseStart_3448538 baseEnd_3448538 := by
    simpa [prefixWord, tailWord_3448538, baseEnd_3448538] using wordTrace_append hprefix tailTrace_3448538
  have hstable : (prefixWord ++ tailWord_3448538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448538).length < 2 ^ (prefixWord ++ tailWord_3448538).sum := by decide
  have hdescent : baseEnd_3448538 < baseStart_3448538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448574 : List Nat := [4, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_3448574 : Nat := 118140960795 + 3448574 * 2 ^ 59
def prefixEnd_3448574 : Nat := 4983230072969 + 3 ^ 40 * 3448574 * 2
def baseEnd_3448574 : Nat := 393505785466287927125623

theorem tailTrace_3448574 : CollatzResearch.WordTrace tailWord_3448574 prefixEnd_3448574 393505785466287927125623 := by
  unfold tailWord_3448574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722478376051605299256097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83853218005608561596032517 15722478376051605299256097)
  ·
    refine ⟨11791858782038703974442073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15722478376051605299256097 11791858782038703974442073)
    ·
      refine ⟨8843894086529027980831555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11791858782038703974442073 8843894086529027980831555)
      ·
        refine ⟨13265841129793541971247333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8843894086529027980831555 13265841129793541971247333)
        ·
          refine ⟨2487345211836289119608875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13265841129793541971247333 2487345211836289119608875)
          ·
            refine ⟨3731017817754433679413313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487345211836289119608875 3731017817754433679413313)
            ·
              refine ⟨2798263363315825259559985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731017817754433679413313 2798263363315825259559985)
              ·
                refine ⟨2098697522486868944669989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798263363315825259559985 2098697522486868944669989)
                ·
                  refine ⟨393505785466287927125623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098697522486868944669989 393505785466287927125623)
                  ·
                    rfl

theorem cell22_3448574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_3448574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448574 prefixEnd_3448574 := by exact prefixLift 3448574
  have htrace : WordTrace (prefixWord ++ tailWord_3448574) baseStart_3448574 baseEnd_3448574 := by
    simpa [prefixWord, tailWord_3448574, baseEnd_3448574] using wordTrace_append hprefix tailTrace_3448574
  have hstable : (prefixWord ++ tailWord_3448574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448574).length < 2 ^ (prefixWord ++ tailWord_3448574).sum := by decide
  have hdescent : baseEnd_3448574 < baseStart_3448574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448579 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 7]
def baseStart_3448579 : Nat := 118140960795 + 3448579 * 2 ^ 59
def prefixEnd_3448579 : Nat := 4983230072969 + 3 ^ 40 * 3448579 * 2
def baseEnd_3448579 : Nat := 393506356000348478333951

theorem tailTrace_3448579 : CollatzResearch.WordTrace tailWord_3448579 prefixEnd_3448579 393506356000348478333951 := by
  unfold tailWord_3448579
  simp only [CollatzResearch.WordTrace]
  refine ⟨125780009373394728247980791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83853339582263152165320527 125780009373394728247980791)
  ·
    refine ⟨188670014060092092371971187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125780009373394728247980791 188670014060092092371971187)
    ·
      refine ⟨283005021090138138557956781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188670014060092092371971187 283005021090138138557956781)
      ·
        refine ⟨106126882908801801959233793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283005021090138138557956781 106126882908801801959233793)
        ·
          refine ⟨79595162181601351469425345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106126882908801801959233793 79595162181601351469425345)
          ·
            refine ⟨59696371636201013602069009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79595162181601351469425345 59696371636201013602069009)
            ·
              refine ⟨44772278727150760201551757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59696371636201013602069009 44772278727150760201551757)
              ·
                refine ⟨16789604522681535075581909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44772278727150760201551757 16789604522681535075581909)
                ·
                  refine ⟨393506356000348478333951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16789604522681535075581909 393506356000348478333951)
                  ·
                    rfl

theorem cell22_3448579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_3448579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448579 prefixEnd_3448579 := by exact prefixLift 3448579
  have htrace : WordTrace (prefixWord ++ tailWord_3448579) baseStart_3448579 baseEnd_3448579 := by
    simpa [prefixWord, tailWord_3448579, baseEnd_3448579] using wordTrace_append hprefix tailTrace_3448579
  have hstable : (prefixWord ++ tailWord_3448579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448579).length < 2 ^ (prefixWord ++ tailWord_3448579).sum := by decide
  have hdescent : baseEnd_3448579 < baseStart_3448579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448589 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3448589 : Nat := 118140960795 + 3448589 * 2 ^ 59
def prefixEnd_3448589 : Nat := 4983230072969 + 3 ^ 40 * 3448589 * 2
def baseEnd_3448589 : Nat := 1180522491205408742251823

theorem tailTrace_3448589 : CollatzResearch.WordTrace tailWord_3448589 prefixEnd_3448589 1180522491205408742251823 := by
  unfold tailWord_3448589
  simp only [CollatzResearch.WordTrace]
  refine ⟨125780374103358499955844821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83853582735572333303896547 125780374103358499955844821)
  ·
    refine ⟨2947977518047464842715113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 125780374103358499955844821 2947977518047464842715113)
    ·
      refine ⟨2210983138535598632036335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2947977518047464842715113 2210983138535598632036335)
      ·
        refine ⟨3316474707803397948054503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210983138535598632036335 3316474707803397948054503)
        ·
          refine ⟨4974712061705096922081755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316474707803397948054503 4974712061705096922081755)
          ·
            refine ⟨7462068092557645383122633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974712061705096922081755 7462068092557645383122633)
            ·
              refine ⟨5596551069418234037341975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462068092557645383122633 5596551069418234037341975)
              ·
                refine ⟨8394826604127351056012963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596551069418234037341975 8394826604127351056012963)
                ·
                  refine ⟨12592239906191026584019445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394826604127351056012963 12592239906191026584019445)
                  ·
                    refine ⟨1180522491205408742251823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12592239906191026584019445 1180522491205408742251823)
                    ·
                      rfl

theorem cell22_3448589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3448589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448589 prefixEnd_3448589 := by exact prefixLift 3448589
  have htrace : WordTrace (prefixWord ++ tailWord_3448589) baseStart_3448589 baseEnd_3448589 := by
    simpa [prefixWord, tailWord_3448589, baseEnd_3448589] using wordTrace_append hprefix tailTrace_3448589
  have hstable : (prefixWord ++ tailWord_3448589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448589).length < 2 ^ (prefixWord ++ tailWord_3448589).sum := by decide
  have hdescent : baseEnd_3448589 < baseStart_3448589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448628 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3448628 : Nat := 118140960795 + 3448628 * 2 ^ 59
def prefixEnd_3448628 : Nat := 4983230072969 + 3 ^ 40 * 3448628 * 2
def baseEnd_3448628 : Nat := 1180535841702425640526703

theorem tailTrace_3448628 : CollatzResearch.WordTrace tailWord_3448628 prefixEnd_3448628 1180535841702425640526703 := by
  unfold tailWord_3448628
  simp only [CollatzResearch.WordTrace]
  refine ⟨62890898275108604808257269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83854531033478139744343025 62890898275108604808257269)
  ·
    refine ⟨5896021713291431700774119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62890898275108604808257269 5896021713291431700774119)
    ·
      refine ⟨8844032569937147551161179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896021713291431700774119 8844032569937147551161179)
      ·
        refine ⟨13266048854905721326741769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8844032569937147551161179 13266048854905721326741769)
        ·
          refine ⟨9949536641179290995056327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13266048854905721326741769 9949536641179290995056327)
          ·
            refine ⟨14924304961768936492584491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949536641179290995056327 14924304961768936492584491)
            ·
              refine ⟨22386457442653404738876737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14924304961768936492584491 22386457442653404738876737)
              ·
                refine ⟨16789843081990053554157553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22386457442653404738876737 16789843081990053554157553)
                ·
                  refine ⟨12592382311492540165618165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16789843081990053554157553 12592382311492540165618165)
                  ·
                    refine ⟨1180535841702425640526703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12592382311492540165618165 1180535841702425640526703)
                    ·
                      rfl

theorem cell22_3448628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3448628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448628 prefixEnd_3448628 := by exact prefixLift 3448628
  have htrace : WordTrace (prefixWord ++ tailWord_3448628) baseStart_3448628 baseEnd_3448628 := by
    simpa [prefixWord, tailWord_3448628, baseEnd_3448628] using wordTrace_append hprefix tailTrace_3448628
  have hstable : (prefixWord ++ tailWord_3448628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448628).length < 2 ^ (prefixWord ++ tailWord_3448628).sum := by decide
  have hdescent : baseEnd_3448628 < baseStart_3448628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448630 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3448630 : Nat := 118140960795 + 3448630 * 2 ^ 59
def prefixEnd_3448630 : Nat := 4983230072969 + 3 ^ 40 * 3448630 * 2
def baseEnd_3448630 : Nat := 393512175447766100658899

theorem tailTrace_3448630 : CollatzResearch.WordTrace tailWord_3448630 prefixEnd_3448630 393512175447766100658899 := by
  unfold tailWord_3448630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7861366843513122747380459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83854579664139975972058229 7861366843513122747380459)
  ·
    refine ⟨11792050265269684121070689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7861366843513122747380459 11792050265269684121070689)
    ·
      refine ⟨8844037698952263090803017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11792050265269684121070689 8844037698952263090803017)
      ·
        refine ⟨6633028274214197318102263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8844037698952263090803017 6633028274214197318102263)
        ·
          refine ⟨9949542411321295977153395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633028274214197318102263 9949542411321295977153395)
          ·
            refine ⟨14924313616981943965730093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949542411321295977153395 14924313616981943965730093)
            ·
              refine ⟨5596617606368228987148785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14924313616981943965730093 5596617606368228987148785)
              ·
                refine ⟨4197463204776171740361589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5596617606368228987148785 4197463204776171740361589)
                ·
                  refine ⟨393512175447766100658899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4197463204776171740361589 393512175447766100658899)
                  ·
                    rfl

theorem cell22_3448630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3448630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448630 prefixEnd_3448630 := by exact prefixLift 3448630
  have htrace : WordTrace (prefixWord ++ tailWord_3448630) baseStart_3448630 baseEnd_3448630 := by
    simpa [prefixWord, tailWord_3448630, baseEnd_3448630] using wordTrace_append hprefix tailTrace_3448630
  have hstable : (prefixWord ++ tailWord_3448630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448630).length < 2 ^ (prefixWord ++ tailWord_3448630).sum := by decide
  have hdescent : baseEnd_3448630 < baseStart_3448630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448660 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3448660 : Nat := 118140960795 + 3448660 * 2 ^ 59
def prefixEnd_3448660 : Nat := 4983230072969 + 3 ^ 40 * 3448660 * 2
def baseEnd_3448660 : Nat := 1180546795956388223726605

theorem tailTrace_3448660 : CollatzResearch.WordTrace tailWord_3448660 prefixEnd_3448660 1180546795956388223726605 := by
  unfold tailWord_3448660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62891481843050639540839717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83855309124067519387786289 62891481843050639540839717)
  ·
    refine ⟨11792152845571994913907447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62891481843050639540839717 11792152845571994913907447)
    ·
      refine ⟨17688229268357992370861171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11792152845571994913907447 17688229268357992370861171)
      ·
        refine ⟨26532343902536988556291757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17688229268357992370861171 26532343902536988556291757)
        ·
          refine ⟨9949628963451370708609409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26532343902536988556291757 9949628963451370708609409)
          ·
            refine ⟨7462221722588528031457057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9949628963451370708609409 7462221722588528031457057)
            ·
              refine ⟨5596666291941396023592793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462221722588528031457057 5596666291941396023592793)
              ·
                refine ⟨4197499718956047017694595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5596666291941396023592793 4197499718956047017694595)
                ·
                  refine ⟨6296249578434070526541893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197499718956047017694595 6296249578434070526541893)
                  ·
                    refine ⟨1180546795956388223726605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296249578434070526541893 1180546795956388223726605)
                    ·
                      rfl

theorem cell22_3448660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3448660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448660 prefixEnd_3448660 := by exact prefixLift 3448660
  have htrace : WordTrace (prefixWord ++ tailWord_3448660) baseStart_3448660 baseEnd_3448660 := by
    simpa [prefixWord, tailWord_3448660, baseEnd_3448660] using wordTrace_append hprefix tailTrace_3448660
  have hstable : (prefixWord ++ tailWord_3448660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448660).length < 2 ^ (prefixWord ++ tailWord_3448660).sum := by decide
  have hdescent : baseEnd_3448660 < baseStart_3448660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448671 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 1, 6]
def baseStart_3448671 : Nat := 118140960795 + 3448671 * 2 ^ 59
def prefixEnd_3448671 : Nat := 4983230072969 + 3 ^ 40 * 3448671 * 2
def baseEnd_3448671 : Nat := 1180550561481187861701571

theorem tailTrace_3448671 : CollatzResearch.WordTrace tailWord_3448671 prefixEnd_3448671 1180550561481187861701571 := by
  unfold tailWord_3448671
  simp only [CollatzResearch.WordTrace]
  refine ⟨125783364889061427960329867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83855576592707618640219911 125783364889061427960329867)
  ·
    refine ⟨188675047333592141940494801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125783364889061427960329867 188675047333592141940494801)
    ·
      refine ⟨141506285500194106455371101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188675047333592141940494801 141506285500194106455371101)
      ·
        refine ⟨53064857062572789920764163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141506285500194106455371101 53064857062572789920764163)
        ·
          refine ⟨79597285593859184881146245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53064857062572789920764163 79597285593859184881146245)
          ·
            refine ⟨14924491048848597165214921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79597285593859184881146245 14924491048848597165214921)
            ·
              refine ⟨11193368286636447873911191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14924491048848597165214921 11193368286636447873911191)
              ·
                refine ⟨16790052429954671810866787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193368286636447873911191 16790052429954671810866787)
                ·
                  refine ⟨25185078644932007716300181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16790052429954671810866787 25185078644932007716300181)
                  ·
                    refine ⟨1180550561481187861701571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25185078644932007716300181 1180550561481187861701571)
                    ·
                      rfl

theorem cell22_3448671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_3448671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448671 prefixEnd_3448671 := by exact prefixLift 3448671
  have htrace : WordTrace (prefixWord ++ tailWord_3448671) baseStart_3448671 baseEnd_3448671 := by
    simpa [prefixWord, tailWord_3448671, baseEnd_3448671] using wordTrace_append hprefix tailTrace_3448671
  have hstable : (prefixWord ++ tailWord_3448671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448671).length < 2 ^ (prefixWord ++ tailWord_3448671).sum := by decide
  have hdescent : baseEnd_3448671 < baseStart_3448671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448707 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 2, 3]
def baseStart_3448707 : Nat := 118140960795 + 3448707 * 2 ^ 59
def prefixEnd_3448707 : Nat := 4983230072969 + 3 ^ 40 * 3448707 * 2
def baseEnd_3448707 : Nat := 1180562885016895767801461

theorem tailTrace_3448707 : CollatzResearch.WordTrace tailWord_3448707 prefixEnd_3448707 1180562885016895767801461 := by
  unfold tailWord_3448707
  simp only [CollatzResearch.WordTrace]
  refine ⟨125784677916931006108640375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83856451944620670739093583 125784677916931006108640375)
  ·
    refine ⟨188677016875396509162960563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125784677916931006108640375 188677016875396509162960563)
    ·
      refine ⟨283015525313094763744440845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188677016875396509162960563 283015525313094763744440845)
      ·
        refine ⟨106130821992410536404165317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283015525313094763744440845 106130821992410536404165317)
        ·
          refine ⟨19899529123576975575780997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106130821992410536404165317 19899529123576975575780997)
          ·
            refine ⟨3731161710670682920458937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19899529123576975575780997 3731161710670682920458937)
            ·
              refine ⟨2798371283003012190344203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731161710670682920458937 2798371283003012190344203)
              ·
                refine ⟨4197556924504518285516305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798371283003012190344203 4197556924504518285516305)
                ·
                  refine ⟨3148167693378388714137229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4197556924504518285516305 3148167693378388714137229)
                  ·
                    refine ⟨1180562885016895767801461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148167693378388714137229 1180562885016895767801461)
                    ·
                      rfl

theorem cell22_3448707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 2, 3].length) (baseStart_3448707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448707 prefixEnd_3448707 := by exact prefixLift 3448707
  have htrace : WordTrace (prefixWord ++ tailWord_3448707) baseStart_3448707 baseEnd_3448707 := by
    simpa [prefixWord, tailWord_3448707, baseEnd_3448707] using wordTrace_append hprefix tailTrace_3448707
  have hstable : (prefixWord ++ tailWord_3448707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448707).length < 2 ^ (prefixWord ++ tailWord_3448707).sum := by decide
  have hdescent : baseEnd_3448707 < baseStart_3448707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448778 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_3448778 : Nat := 118140960795 + 3448778 * 2 ^ 59
def prefixEnd_3448778 : Nat := 4983230072969 + 3 ^ 40 * 3448778 * 2
def baseEnd_3448778 : Nat := 1180587189767875249276243

theorem tailTrace_3448778 : CollatzResearch.WordTrace tailWord_3448778 prefixEnd_3448778 1180587189767875249276243 := by
  unfold tailWord_3448778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446816874918446308618747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83858178333115856822983325 31446816874918446308618747)
  ·
    refine ⟨47170225312377669462928121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31446816874918446308618747 47170225312377669462928121)
    ·
      refine ⟨35377668984283252097196091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47170225312377669462928121 35377668984283252097196091)
      ·
        refine ⟨53066503476424878145794137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35377668984283252097196091 53066503476424878145794137)
        ·
          refine ⟨39799877607318658609345603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53066503476424878145794137 39799877607318658609345603)
          ·
            refine ⟨59699816410977987914018405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39799877607318658609345603 59699816410977987914018405)
            ·
              refine ⟨11193715577058372733878451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59699816410977987914018405 11193715577058372733878451)
              ·
                refine ⟨16790573365587559100817677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193715577058372733878451 16790573365587559100817677)
                ·
                  refine ⟨6296465012095334662806629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16790573365587559100817677 6296465012095334662806629)
                  ·
                    refine ⟨1180587189767875249276243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296465012095334662806629 1180587189767875249276243)
                    ·
                      rfl

theorem cell22_3448778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_3448778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448778 prefixEnd_3448778 := by exact prefixLift 3448778
  have htrace : WordTrace (prefixWord ++ tailWord_3448778) baseStart_3448778 baseEnd_3448778 := by
    simpa [prefixWord, tailWord_3448778, baseEnd_3448778] using wordTrace_append hprefix tailTrace_3448778
  have hstable : (prefixWord ++ tailWord_3448778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448778).length < 2 ^ (prefixWord ++ tailWord_3448778).sum := by decide
  have hdescent : baseEnd_3448778 < baseStart_3448778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448810 : List Nat := [3, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_3448810 : Nat := 118140960795 + 3448810 * 2 ^ 59
def prefixEnd_3448810 : Nat := 4983230072969 + 3 ^ 40 * 3448810 * 2
def baseEnd_3448810 : Nat := 393532714673945944158715

theorem tailTrace_3448810 : CollatzResearch.WordTrace tailWord_3448810 prefixEnd_3448810 393532714673945944158715 := by
  unfold tailWord_3448810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31447108658889463674909971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83858956423705236466426589 31447108658889463674909971)
  ·
    refine ⟨47170662988334195512364957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31447108658889463674909971 47170662988334195512364957)
    ·
      refine ⟨17688998620625323317136859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47170662988334195512364957 17688998620625323317136859)
      ·
        refine ⟨26533497930937984975705289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17688998620625323317136859 26533497930937984975705289)
        ·
          refine ⟨19900123448203488731778967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26533497930937984975705289 19900123448203488731778967)
          ·
            refine ⟨29850185172305233097668451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19900123448203488731778967 29850185172305233097668451)
            ·
              refine ⟨44775277758457849646502677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29850185172305233097668451 44775277758457849646502677)
              ·
                refine ⟨2098841144927711702179813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44775277758457849646502677 2098841144927711702179813)
                ·
                  refine ⟨393532714673945944158715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098841144927711702179813 393532714673945944158715)
                  ·
                    rfl

theorem cell22_3448810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_3448810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448810 prefixEnd_3448810 := by exact prefixLift 3448810
  have htrace : WordTrace (prefixWord ++ tailWord_3448810) baseStart_3448810 baseEnd_3448810 := by
    simpa [prefixWord, tailWord_3448810, baseEnd_3448810] using wordTrace_append hprefix tailTrace_3448810
  have hstable : (prefixWord ++ tailWord_3448810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448810).length < 2 ^ (prefixWord ++ tailWord_3448810).sum := by decide
  have hdescent : baseEnd_3448810 < baseStart_3448810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448825 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 1, 5]
def baseStart_3448825 : Nat := 118140960795 + 3448825 * 2 ^ 59
def prefixEnd_3448825 : Nat := 4983230072969 + 3 ^ 40 * 3448825 * 2
def baseEnd_3448825 : Nat := 1180603278828382793351099

theorem tailTrace_3448825 : CollatzResearch.WordTrace tailWord_3448825 prefixEnd_3448825 1180603278828382793351099 := by
  unfold tailWord_3448825
  simp only [CollatzResearch.WordTrace]
  refine ⟨125788981730503512261435929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83859321153669008174290619 125788981730503512261435929)
  ·
    refine ⟨94341736297877634196076947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125788981730503512261435929 94341736297877634196076947)
    ·
      refine ⟨141512604446816451294115421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94341736297877634196076947 141512604446816451294115421)
      ·
        refine ⟨53067226667556169235293283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141512604446816451294115421 53067226667556169235293283)
        ·
          refine ⟨79600840001334253852939925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53067226667556169235293283 79600840001334253852939925)
          ·
            refine ⟨3731289375062543149356559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79600840001334253852939925 3731289375062543149356559)
            ·
              refine ⟨5596934062593814724034839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731289375062543149356559 5596934062593814724034839)
              ·
                refine ⟨8395401093890722086052259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596934062593814724034839 8395401093890722086052259)
                ·
                  refine ⟨12593101640836083129078389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395401093890722086052259 12593101640836083129078389)
                  ·
                    refine ⟨1180603278828382793351099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12593101640836083129078389 1180603278828382793351099)
                    ·
                      rfl

theorem cell22_3448825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_3448825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448825 prefixEnd_3448825 := by exact prefixLift 3448825
  have htrace : WordTrace (prefixWord ++ tailWord_3448825) baseStart_3448825 baseEnd_3448825 := by
    simpa [prefixWord, tailWord_3448825, baseEnd_3448825] using wordTrace_append hprefix tailTrace_3448825
  have hstable : (prefixWord ++ tailWord_3448825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448825).length < 2 ^ (prefixWord ++ tailWord_3448825).sum := by decide
  have hdescent : baseEnd_3448825 < baseStart_3448825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448855 : List Nat := [1, 1, 3, 5, 2, 2, 8]
def baseStart_3448855 : Nat := 118140960795 + 3448855 * 2 ^ 59
def prefixEnd_3448855 : Nat := 4983230072969 + 3 ^ 40 * 3448855 * 2
def baseEnd_3448855 : Nat := 43726427720054545003741

theorem tailTrace_3448855 : CollatzResearch.WordTrace tailWord_3448855 prefixEnd_3448855 43726427720054545003741 := by
  unfold tailWord_3448855
  simp only [CollatzResearch.WordTrace]
  refine ⟨125790075920394827385028019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83860050613596551590018679 125790075920394827385028019)
  ·
    refine ⟨188685113880592241077542029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125790075920394827385028019 188685113880592241077542029)
    ·
      refine ⟨70756917705222090404078261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188685113880592241077542029 70756917705222090404078261)
      ·
        refine ⟨6633461034864570975382337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70756917705222090404078261 6633461034864570975382337)
        ·
          refine ⟨4975095776148428231536753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6633461034864570975382337 4975095776148428231536753)
          ·
            refine ⟨3731321832111321173652565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4975095776148428231536753 3731321832111321173652565)
            ·
              refine ⟨43726427720054545003741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3731321832111321173652565 43726427720054545003741)
              ·
                rfl

theorem cell22_3448855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 8].length) (baseStart_3448855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448855 prefixEnd_3448855 := by exact prefixLift 3448855
  have htrace : WordTrace (prefixWord ++ tailWord_3448855) baseStart_3448855 baseEnd_3448855 := by
    simpa [prefixWord, tailWord_3448855, baseEnd_3448855] using wordTrace_append hprefix tailTrace_3448855
  have hstable : (prefixWord ++ tailWord_3448855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448855).length < 2 ^ (prefixWord ++ tailWord_3448855).sum := by decide
  have hdescent : baseEnd_3448855 < baseStart_3448855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448872 : List Nat := [2, 1, 5, 3, 1, 1, 2, 7]
def baseStart_3448872 : Nat := 118140960795 + 3448872 * 2 ^ 59
def prefixEnd_3448872 : Nat := 4983230072969 + 3 ^ 40 * 3448872 * 2
def baseEnd_3448872 : Nat := 131179929765432259713995

theorem tailTrace_3448872 : CollatzResearch.WordTrace tailWord_3448872 prefixEnd_3448872 131179929765432259713995 := by
  unfold tailWord_3448872
  simp only [CollatzResearch.WordTrace]
  refine ⟨62895347980666619644198435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83860463974222159525597913 62895347980666619644198435)
  ·
    refine ⟨94343021970999929466297653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62895347980666619644198435 94343021970999929466297653)
    ·
      refine ⟨8844658309781243387465405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94343021970999929466297653 8844658309781243387465405)
      ·
        refine ⟨3316746866167966270299527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8844658309781243387465405 3316746866167966270299527)
        ·
          refine ⟨4975120299251949405449291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316746866167966270299527 4975120299251949405449291)
          ·
            refine ⟨7462680448877924108173937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975120299251949405449291 7462680448877924108173937)
            ·
              refine ⟨5597010336658443081130453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462680448877924108173937 5597010336658443081130453)
              ·
                refine ⟨131179929765432259713995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5597010336658443081130453 131179929765432259713995)
                ·
                  rfl

theorem cell22_3448872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 7].length) (baseStart_3448872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448872 prefixEnd_3448872 := by exact prefixLift 3448872
  have htrace : WordTrace (prefixWord ++ tailWord_3448872) baseStart_3448872 baseEnd_3448872 := by
    simpa [prefixWord, tailWord_3448872, baseEnd_3448872] using wordTrace_append hprefix tailTrace_3448872
  have hstable : (prefixWord ++ tailWord_3448872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448872).length < 2 ^ (prefixWord ++ tailWord_3448872).sum := by decide
  have hdescent : baseEnd_3448872 < baseStart_3448872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448960 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 4, 3]
def baseStart_3448960 : Nat := 118140960795 + 3448960 * 2 ^ 59
def prefixEnd_3448960 : Nat := 4983230072969 + 3 ^ 40 * 3448960 * 2
def baseEnd_3448960 : Nat := 1180649492087287441225685

theorem tailTrace_3448960 : CollatzResearch.WordTrace tailWord_3448960 prefixEnd_3448960 1180649492087287441225685 := by
  unfold tailWord_3448960
  simp only [CollatzResearch.WordTrace]
  refine ⟨62896952792507215158800167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83862603723342953545066889 62896952792507215158800167)
  ·
    refine ⟨94345429188760822738200251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62896952792507215158800167 94345429188760822738200251)
    ·
      refine ⟨141518143783141234107300377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94345429188760822738200251 141518143783141234107300377)
      ·
        refine ⟨106138607837355925580475283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141518143783141234107300377 106138607837355925580475283)
        ·
          refine ⟨159207911756033888370712925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106138607837355925580475283 159207911756033888370712925)
          ·
            refine ⟨59702966908512708139017347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159207911756033888370712925 59702966908512708139017347)
            ·
              refine ⟨89554450362769062208526021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59702966908512708139017347 89554450362769062208526021)
              ·
                refine ⟨16791459443019199164098629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89554450362769062208526021 16791459443019199164098629)
                ·
                  refine ⟨3148398645566099843268493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16791459443019199164098629 3148398645566099843268493)
                  ·
                    refine ⟨1180649492087287441225685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148398645566099843268493 1180649492087287441225685)
                    ·
                      rfl

theorem cell22_3448960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_3448960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448960 prefixEnd_3448960 := by exact prefixLift 3448960
  have htrace : WordTrace (prefixWord ++ tailWord_3448960) baseStart_3448960 baseEnd_3448960 := by
    simpa [prefixWord, tailWord_3448960, baseEnd_3448960] using wordTrace_append hprefix tailTrace_3448960
  have hstable : (prefixWord ++ tailWord_3448960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448960).length < 2 ^ (prefixWord ++ tailWord_3448960).sum := by decide
  have hdescent : baseEnd_3448960 < baseStart_3448960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448994 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3448994 : Nat := 118140960795 + 3448994 * 2 ^ 59
def prefixEnd_3448994 : Nat := 4983230072969 + 3 ^ 40 * 3448994 * 2
def baseEnd_3448994 : Nat := 1180661130982122685875581

theorem tailTrace_3448994 : CollatzResearch.WordTrace tailWord_3448994 prefixEnd_3448994 1180661130982122685875581 := by
  unfold tailWord_3448994
  simp only [CollatzResearch.WordTrace]
  refine ⟨31448786416722813531084509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83863430444594169416225357 31448786416722813531084509)
  ·
    refine ⟨11793294906271055074156691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31448786416722813531084509 11793294906271055074156691)
    ·
      refine ⟨17689942359406582611235037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11793294906271055074156691 17689942359406582611235037)
      ·
        refine ⟨6633728384777468479213139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17689942359406582611235037 6633728384777468479213139)
        ·
          refine ⟨9950592577166202718819709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633728384777468479213139 9950592577166202718819709)
          ·
            refine ⟨3731472216437326019557391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9950592577166202718819709 3731472216437326019557391)
            ·
              refine ⟨5597208324655989029336087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731472216437326019557391 5597208324655989029336087)
              ·
                refine ⟨8395812486983983544004131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597208324655989029336087 8395812486983983544004131)
                ·
                  refine ⟨12593718730475975316006197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395812486983983544004131 12593718730475975316006197)
                  ·
                    refine ⟨1180661130982122685875581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12593718730475975316006197 1180661130982122685875581)
                    ·
                      rfl

theorem cell22_3448994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3448994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3448994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3448994 prefixEnd_3448994 := by exact prefixLift 3448994
  have htrace : WordTrace (prefixWord ++ tailWord_3448994) baseStart_3448994 baseEnd_3448994 := by
    simpa [prefixWord, tailWord_3448994, baseEnd_3448994] using wordTrace_append hprefix tailTrace_3448994
  have hstable : (prefixWord ++ tailWord_3448994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448994).length < 2 ^ (prefixWord ++ tailWord_3448994).sum := by decide
  have hdescent : baseEnd_3448994 < baseStart_3448994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 8]
def baseStart_3449003 : Nat := 118140960795 + 3449003 * 2 ^ 59
def prefixEnd_3449003 : Nat := 4983230072969 + 3 ^ 40 * 3449003 * 2
def baseEnd_3449003 : Nat := 1180664211866049662400553

theorem tailTrace_3449003 : CollatzResearch.WordTrace tailWord_3449003 prefixEnd_3449003 1180664211866049662400553 := by
  unfold tailWord_3449003
  simp only [CollatzResearch.WordTrace]
  refine ⟨125795473923858648661415663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83863649282572432440943775 125795473923858648661415663)
  ·
    refine ⟨188693210885787972992123495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125795473923858648661415663 188693210885787972992123495)
    ·
      refine ⟨283039816328681959488185243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188693210885787972992123495 283039816328681959488185243)
      ·
        refine ⟨424559724493022939232277865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283039816328681959488185243 424559724493022939232277865)
        ·
          refine ⟨318419793369767204424208399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424559724493022939232277865 318419793369767204424208399)
          ·
            refine ⟨477629690054650806636312599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318419793369767204424208399 477629690054650806636312599)
            ·
              refine ⟨716444535081976209954468899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477629690054650806636312599 716444535081976209954468899)
              ·
                refine ⟨1074666802622964314931703349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716444535081976209954468899 1074666802622964314931703349)
                ·
                  refine ⟨100750012745902904524847189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1074666802622964314931703349 100750012745902904524847189)
                  ·
                    refine ⟨1180664211866049662400553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100750012745902904524847189 1180664211866049662400553)
                    ·
                      rfl

theorem cell22_3449003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_3449003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449003 prefixEnd_3449003 := by exact prefixLift 3449003
  have htrace : WordTrace (prefixWord ++ tailWord_3449003) baseStart_3449003 baseEnd_3449003 := by
    simpa [prefixWord, tailWord_3449003, baseEnd_3449003] using wordTrace_append hprefix tailTrace_3449003
  have hstable : (prefixWord ++ tailWord_3449003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449003).length < 2 ^ (prefixWord ++ tailWord_3449003).sum := by decide
  have hdescent : baseEnd_3449003 < baseStart_3449003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449013 : List Nat := [1, 3, 3, 4, 2, 1, 1, 3, 4]
def baseStart_3449013 : Nat := 118140960795 + 3449013 * 2 ^ 59
def prefixEnd_3449013 : Nat := 4983230072969 + 3 ^ 40 * 3449013 * 2
def baseEnd_3449013 : Nat := 393555878356804323216841

theorem tailTrace_3449013 : CollatzResearch.WordTrace tailWord_3449013 prefixEnd_3449013 393555878356804323216841 := by
  unfold tailWord_3449013
  simp only [CollatzResearch.WordTrace]
  refine ⟨125795838653822420369279693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83863892435881613579519795 125795838653822420369279693)
  ·
    refine ⟨47173439495183407638479885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125795838653822420369279693 47173439495183407638479885)
    ·
      refine ⟨17690039810693777864429957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47173439495183407638479885 17690039810693777864429957)
      ·
        refine ⟨3316882464505083349580617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17690039810693777864429957 3316882464505083349580617)
        ·
          refine ⟨2487661848378812512185463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3316882464505083349580617 2487661848378812512185463)
          ·
            refine ⟨3731492772568218768278195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487661848378812512185463 3731492772568218768278195)
            ·
              refine ⟨5597239158852328152417293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731492772568218768278195 5597239158852328152417293)
              ·
                refine ⟨2098964684569623057156485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5597239158852328152417293 2098964684569623057156485)
                ·
                  refine ⟨393555878356804323216841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2098964684569623057156485 393555878356804323216841)
                  ·
                    rfl

theorem cell22_3449013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_3449013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449013 prefixEnd_3449013 := by exact prefixLift 3449013
  have htrace : WordTrace (prefixWord ++ tailWord_3449013) baseStart_3449013 baseEnd_3449013 := by
    simpa [prefixWord, tailWord_3449013, baseEnd_3449013] using wordTrace_append hprefix tailTrace_3449013
  have hstable : (prefixWord ++ tailWord_3449013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449013).length < 2 ^ (prefixWord ++ tailWord_3449013).sum := by decide
  have hdescent : baseEnd_3449013 < baseStart_3449013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449026 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3449026 : Nat := 118140960795 + 3449026 * 2 ^ 59
def prefixEnd_3449026 : Nat := 4983230072969 + 3 ^ 40 * 3449026 * 2
def baseEnd_3449026 : Nat := 1180672085236085269075483

theorem tailTrace_3449026 : CollatzResearch.WordTrace tailWord_3449026 prefixEnd_3449026 1180672085236085269075483 := by
  unfold tailWord_3449026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31449078200693830897375733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83864208535183549059668621 31449078200693830897375733)
  ·
    refine ⟨2948351081315046646628975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31449078200693830897375733 2948351081315046646628975)
    ·
      refine ⟨4422526621972569969943463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948351081315046646628975 4422526621972569969943463)
      ·
        refine ⟨6633789932958854954915195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422526621972569969943463 6633789932958854954915195)
        ·
          refine ⟨9950684899438282432372793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633789932958854954915195 9950684899438282432372793)
          ·
            refine ⟨7463013674578711824279595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9950684899438282432372793 7463013674578711824279595)
            ·
              refine ⟨11194520511868067736419393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7463013674578711824279595 11194520511868067736419393)
              ·
                refine ⟨8395890383901050802314545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11194520511868067736419393 8395890383901050802314545)
                ·
                  refine ⟨6296917787925788101735909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8395890383901050802314545 6296917787925788101735909)
                  ·
                    refine ⟨1180672085236085269075483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296917787925788101735909 1180672085236085269075483)
                    ·
                      rfl

theorem cell22_3449026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3449026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449026 prefixEnd_3449026 := by exact prefixLift 3449026
  have htrace : WordTrace (prefixWord ++ tailWord_3449026) baseStart_3449026 baseEnd_3449026 := by
    simpa [prefixWord, tailWord_3449026, baseEnd_3449026] using wordTrace_append hprefix tailTrace_3449026
  have hstable : (prefixWord ++ tailWord_3449026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449026).length < 2 ^ (prefixWord ++ tailWord_3449026).sum := by decide
  have hdescent : baseEnd_3449026 < baseStart_3449026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449035 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 5]
def baseStart_3449035 : Nat := 118140960795 + 3449035 * 2 ^ 59
def prefixEnd_3449035 : Nat := 4983230072969 + 3 ^ 40 * 3449035 * 2
def baseEnd_3449035 : Nat := 393558388706670748533485

theorem tailTrace_3449035 : CollatzResearch.WordTrace tailWord_3449035 prefixEnd_3449035 393558388706670748533485 := by
  unfold tailWord_3449035
  simp only [CollatzResearch.WordTrace]
  refine ⟨125796641059742718126580559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83864427373161812084387039 125796641059742718126580559)
  ·
    refine ⟨188694961589614077189870839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125796641059742718126580559 188694961589614077189870839)
    ·
      refine ⟨283042442384421115784806259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188694961589614077189870839 283042442384421115784806259)
      ·
        refine ⟨424563663576631673677209389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283042442384421115784806259 424563663576631673677209389)
        ·
          refine ⟨159211373841236877628953521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424563663576631673677209389 159211373841236877628953521)
          ·
            refine ⟨119408530380927658221715141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159211373841236877628953521 119408530380927658221715141)
            ·
              refine ⟨22389099446423935916571589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119408530380927658221715141 22389099446423935916571589)
              ·
                refine ⟨4197956146204487984357173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22389099446423935916571589 4197956146204487984357173)
                ·
                  refine ⟨393558388706670748533485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4197956146204487984357173 393558388706670748533485)
                  ·
                    rfl

theorem cell22_3449035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 5].length) (baseStart_3449035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449035 prefixEnd_3449035 := by exact prefixLift 3449035
  have htrace : WordTrace (prefixWord ++ tailWord_3449035) baseStart_3449035 baseEnd_3449035 := by
    simpa [prefixWord, tailWord_3449035, baseEnd_3449035] using wordTrace_append hprefix tailTrace_3449035
  have hstable : (prefixWord ++ tailWord_3449035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449035).length < 2 ^ (prefixWord ++ tailWord_3449035).sum := by decide
  have hdescent : baseEnd_3449035 < baseStart_3449035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449050 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_3449050 : Nat := 118140960795 + 3449050 * 2 ^ 59
def prefixEnd_3449050 : Nat := 4983230072969 + 3 ^ 40 * 3449050 * 2
def baseEnd_3449050 : Nat := 1180680300926557206475409

theorem tailTrace_3449050 : CollatzResearch.WordTrace tailWord_3449050 prefixEnd_3449050 1180680300926557206475409 := by
  unfold tailWord_3449050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31449297038672093922094151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83864792103125583792251069 31449297038672093922094151)
  ·
    refine ⟨47173945558008140883141227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31449297038672093922094151 47173945558008140883141227)
    ·
      refine ⟨70760918337012211324711841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47173945558008140883141227 70760918337012211324711841)
      ·
        refine ⟨53070688752759158493533881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70760918337012211324711841 53070688752759158493533881)
        ·
          refine ⟨39803016564569368870150411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53070688752759158493533881 39803016564569368870150411)
          ·
            refine ⟨59704524846854053305225617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39803016564569368870150411 59704524846854053305225617)
            ·
              refine ⟨44778393635140539978919213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59704524846854053305225617 44778393635140539978919213)
              ·
                refine ⟨16791897613177702492094705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44778393635140539978919213 16791897613177702492094705)
                ·
                  refine ⟨12593923209883276869071029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16791897613177702492094705 12593923209883276869071029)
                  ·
                    refine ⟨1180680300926557206475409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12593923209883276869071029 1180680300926557206475409)
                    ·
                      rfl

theorem cell22_3449050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_3449050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449050 prefixEnd_3449050 := by exact prefixLift 3449050
  have htrace : WordTrace (prefixWord ++ tailWord_3449050) baseStart_3449050 baseEnd_3449050 := by
    simpa [prefixWord, tailWord_3449050, baseEnd_3449050] using wordTrace_append hprefix tailTrace_3449050
  have hstable : (prefixWord ++ tailWord_3449050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449050).length < 2 ^ (prefixWord ++ tailWord_3449050).sum := by decide
  have hdescent : baseEnd_3449050 < baseStart_3449050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449065 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_3449065 : Nat := 118140960795 + 3449065 * 2 ^ 59
def prefixEnd_3449065 : Nat := 4983230072969 + 3 ^ 40 * 3449065 * 2
def baseEnd_3449065 : Nat := 1180685435733102167350363

theorem tailTrace_3449065 : CollatzResearch.WordTrace tailWord_3449065 prefixEnd_3449065 1180685435733102167350363 := by
  unfold tailWord_3449065
  simp only [CollatzResearch.WordTrace]
  refine ⟨125797735249634033250172649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83865156833089355500115099 125797735249634033250172649)
  ·
    refine ⟨94348301437225524937629487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125797735249634033250172649 94348301437225524937629487)
    ·
      refine ⟨141522452155838287406444231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94348301437225524937629487 141522452155838287406444231)
      ·
        refine ⟨212283678233757431109666347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141522452155838287406444231 212283678233757431109666347)
        ·
          refine ⟨318425517350636146664499521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212283678233757431109666347 318425517350636146664499521)
          ·
            refine ⟨238819138012977109998374641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318425517350636146664499521 238819138012977109998374641)
            ·
              refine ⟨179114353509732832498780981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238819138012977109998374641 179114353509732832498780981)
              ·
                refine ⟨16791970641537453046760717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179114353509732832498780981 16791970641537453046760717)
                ·
                  refine ⟨6296988990576544892535269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16791970641537453046760717 6296988990576544892535269)
                  ·
                    refine ⟨1180685435733102167350363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6296988990576544892535269 1180685435733102167350363)
                    ·
                      rfl

theorem cell22_3449065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_3449065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449065 prefixEnd_3449065 := by exact prefixLift 3449065
  have htrace : WordTrace (prefixWord ++ tailWord_3449065) baseStart_3449065 baseEnd_3449065 := by
    simpa [prefixWord, tailWord_3449065, baseEnd_3449065] using wordTrace_append hprefix tailTrace_3449065
  have hstable : (prefixWord ++ tailWord_3449065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449065).length < 2 ^ (prefixWord ++ tailWord_3449065).sum := by decide
  have hdescent : baseEnd_3449065 < baseStart_3449065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449090 : List Nat := [3, 4, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3449090 : Nat := 118140960795 + 3449090 * 2 ^ 59
def prefixEnd_3449090 : Nat := 4983230072969 + 3 ^ 40 * 3449090 * 2
def baseEnd_3449090 : Nat := 1180693993744010435475287

theorem tailTrace_3449090 : CollatzResearch.WordTrace tailWord_3449090 prefixEnd_3449090 1180693993744010435475287 := by
  unfold tailWord_3449090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31449661768635865629958181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83865764716362308346555149 31449661768635865629958181)
  ·
    refine ⟨5896811581619224805617159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31449661768635865629958181 5896811581619224805617159)
    ·
      refine ⟨8845217372428837208425739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896811581619224805617159 8845217372428837208425739)
      ·
        refine ⟨13267826058643255812638609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845217372428837208425739 13267826058643255812638609)
        ·
          refine ⟨9950869543982441859478957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13267826058643255812638609 9950869543982441859478957)
          ·
            refine ⟨3731576078993415697304609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9950869543982441859478957 3731576078993415697304609)
            ·
              refine ⟨2798682059245061772978457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731576078993415697304609 2798682059245061772978457)
              ·
                refine ⟨2099011544433796329733843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798682059245061772978457 2099011544433796329733843)
                ·
                  refine ⟨3148517316650694494600765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099011544433796329733843 3148517316650694494600765)
                  ·
                    refine ⟨1180693993744010435475287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148517316650694494600765 1180693993744010435475287)
                    ·
                      rfl

theorem cell22_3449090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3449090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449090 prefixEnd_3449090 := by exact prefixLift 3449090
  have htrace : WordTrace (prefixWord ++ tailWord_3449090) baseStart_3449090 baseEnd_3449090 := by
    simpa [prefixWord, tailWord_3449090, baseEnd_3449090] using wordTrace_append hprefix tailTrace_3449090
  have hstable : (prefixWord ++ tailWord_3449090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449090).length < 2 ^ (prefixWord ++ tailWord_3449090).sum := by decide
  have hdescent : baseEnd_3449090 < baseStart_3449090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449112 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_3449112 : Nat := 118140960795 + 3449112 * 2 ^ 59
def prefixEnd_3449112 : Nat := 4983230072969 + 3 ^ 40 * 3449112 * 2
def baseEnd_3449112 : Nat := 1180701524793609711425219

theorem tailTrace_3449112 : CollatzResearch.WordTrace tailWord_3449112 prefixEnd_3449112 1180701524793609711425219 := by
  unfold tailWord_3449112
  simp only [CollatzResearch.WordTrace]
  refine ⟨62899724740231880138566795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83866299653642506851422393 62899724740231880138566795)
  ·
    refine ⟨94349587110347820207850193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62899724740231880138566795 94349587110347820207850193)
    ·
      refine ⟨70762190332760865155887645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94349587110347820207850193 70762190332760865155887645)
      ·
        refine ⟨26535821374785324433457867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70762190332760865155887645 26535821374785324433457867)
        ·
          refine ⟨39803732062177986650186801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26535821374785324433457867 39803732062177986650186801)
          ·
            refine ⟨29852799046633489987640101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39803732062177986650186801 29852799046633489987640101)
            ·
              refine ⟨5597399821243779372682519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29852799046633489987640101 5597399821243779372682519)
              ·
                refine ⟨8396099731865669059023779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597399821243779372682519 8396099731865669059023779)
                ·
                  refine ⟨12594149597798503588535669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396099731865669059023779 12594149597798503588535669)
                  ·
                    refine ⟨1180701524793609711425219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12594149597798503588535669 1180701524793609711425219)
                    ·
                      rfl

theorem cell22_3449112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_3449112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449112 prefixEnd_3449112 := by exact prefixLift 3449112
  have htrace : WordTrace (prefixWord ++ tailWord_3449112) baseStart_3449112 baseEnd_3449112 := by
    simpa [prefixWord, tailWord_3449112, baseEnd_3449112] using wordTrace_append hprefix tailTrace_3449112
  have hstable : (prefixWord ++ tailWord_3449112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449112).length < 2 ^ (prefixWord ++ tailWord_3449112).sum := by decide
  have hdescent : baseEnd_3449112 < baseStart_3449112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449146 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_3449146 : Nat := 118140960795 + 3449146 * 2 ^ 59
def prefixEnd_3449146 : Nat := 4983230072969 + 3 ^ 40 * 3449146 * 2
def baseEnd_3449146 : Nat := 1180713163688444956075115

theorem tailTrace_3449146 : CollatzResearch.WordTrace tailWord_3449146 prefixEnd_3449146 1180713163688444956075115 := by
  unfold tailWord_3449146
  simp only [CollatzResearch.WordTrace]
  refine ⟨31450172390585146020967823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83867126374893722722580861 31450172390585146020967823)
  ·
    refine ⟨47175258585877719031451735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31450172390585146020967823 47175258585877719031451735)
    ·
      refine ⟨70762887878816578547177603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47175258585877719031451735 70762887878816578547177603)
      ·
        refine ⟨106144331818224867820766405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70762887878816578547177603 106144331818224867820766405)
        ·
          refine ⟨19902062215917162716393701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106144331818224867820766405 19902062215917162716393701)
          ·
            refine ⟨3731636665484468009323819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19902062215917162716393701 3731636665484468009323819)
            ·
              refine ⟨5597454998226702013985729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731636665484468009323819 5597454998226702013985729)
              ·
                refine ⟨4198091248670026510489297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5597454998226702013985729 4198091248670026510489297)
                ·
                  refine ⟨3148568436502519882866973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4198091248670026510489297 3148568436502519882866973)
                  ·
                    refine ⟨1180713163688444956075115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148568436502519882866973 1180713163688444956075115)
                    ·
                      rfl

theorem cell22_3449146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_3449146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449146 prefixEnd_3449146 := by exact prefixLift 3449146
  have htrace : WordTrace (prefixWord ++ tailWord_3449146) baseStart_3449146 baseEnd_3449146 := by
    simpa [prefixWord, tailWord_3449146, baseEnd_3449146] using wordTrace_append hprefix tailTrace_3449146
  have hstable : (prefixWord ++ tailWord_3449146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449146).length < 2 ^ (prefixWord ++ tailWord_3449146).sum := by decide
  have hdescent : baseEnd_3449146 < baseStart_3449146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449155 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 8]
def baseStart_3449155 : Nat := 118140960795 + 3449155 * 2 ^ 59
def prefixEnd_3449155 : Nat := 4983230072969 + 3 ^ 40 * 3449155 * 2
def baseEnd_3449155 : Nat := 1180716244572371932600087

theorem tailTrace_3449155 : CollatzResearch.WordTrace tailWord_3449155 prefixEnd_3449155 1180716244572371932600087 := by
  unfold tailWord_3449155
  simp only [CollatzResearch.WordTrace]
  refine ⟨125801017819307978620948919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83867345212871985747299279 125801017819307978620948919)
  ·
    refine ⟨188701526728961967931423379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125801017819307978620948919 188701526728961967931423379)
    ·
      refine ⟨283052290093442951897135069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188701526728961967931423379 283052290093442951897135069)
      ·
        refine ⟨106144608785041106961425651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283052290093442951897135069 106144608785041106961425651)
        ·
          refine ⟨159216913177561660442138477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106144608785041106961425651 159216913177561660442138477)
          ·
            refine ⟨59706342441585622665801929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159216913177561660442138477 59706342441585622665801929)
            ·
              refine ⟨44779756831189216999351447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59706342441585622665801929 44779756831189216999351447)
              ·
                refine ⟨67169635246783825499027171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44779756831189216999351447 67169635246783825499027171)
                ·
                  refine ⟨100754452870175738248540757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67169635246783825499027171 100754452870175738248540757)
                  ·
                    refine ⟨1180716244572371932600087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100754452870175738248540757 1180716244572371932600087)
                    ·
                      rfl

theorem cell22_3449155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_3449155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449155 prefixEnd_3449155 := by exact prefixLift 3449155
  have htrace : WordTrace (prefixWord ++ tailWord_3449155) baseStart_3449155 baseEnd_3449155 := by
    simpa [prefixWord, tailWord_3449155, baseEnd_3449155] using wordTrace_append hprefix tailTrace_3449155
  have hstable : (prefixWord ++ tailWord_3449155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449155).length < 2 ^ (prefixWord ++ tailWord_3449155).sum := by decide
  have hdescent : baseEnd_3449155 < baseStart_3449155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449251 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 1, 4]
def baseStart_3449251 : Nat := 118140960795 + 3449251 * 2 ^ 59
def prefixEnd_3449251 : Nat := 4983230072969 + 3 ^ 40 * 3449251 * 2
def baseEnd_3449251 : Nat := 1180749107334259682199793

theorem tailTrace_3449251 : CollatzResearch.WordTrace tailWord_3449251 prefixEnd_3449251 1180749107334259682199793 := by
  unfold tailWord_3449251
  simp only [CollatzResearch.WordTrace]
  refine ⟨125804519226960187016443607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83869679484640124677629071 125804519226960187016443607)
  ·
    refine ⟨188706778840440280524665411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125804519226960187016443607 188706778840440280524665411)
    ·
      refine ⟨283060168260660420786998117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188706778840440280524665411 283060168260660420786998117)
      ·
        refine ⟨53073781548873828897562147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283060168260660420786998117 53073781548873828897562147)
        ·
          refine ⟨79610672323310743346343221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53073781548873828897562147 79610672323310743346343221)
          ·
            refine ⟨7463500530310382188719677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79610672323310743346343221 7463500530310382188719677)
            ·
              refine ⟨2798812698866393320769879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7463500530310382188719677 2798812698866393320769879)
              ·
                refine ⟨4198219048299589981154819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798812698866393320769879 4198219048299589981154819)
                ·
                  refine ⟨6297328572449384971732229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198219048299589981154819 6297328572449384971732229)
                  ·
                    refine ⟨1180749107334259682199793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6297328572449384971732229 1180749107334259682199793)
                    ·
                      rfl

theorem cell22_3449251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 4].length) (baseStart_3449251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449251 prefixEnd_3449251 := by exact prefixLift 3449251
  have htrace : WordTrace (prefixWord ++ tailWord_3449251) baseStart_3449251 baseEnd_3449251 := by
    simpa [prefixWord, tailWord_3449251, baseEnd_3449251] using wordTrace_append hprefix tailTrace_3449251
  have hstable : (prefixWord ++ tailWord_3449251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449251).length < 2 ^ (prefixWord ++ tailWord_3449251).sum := by decide
  have hdescent : baseEnd_3449251 < baseStart_3449251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449315 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 2, 3]
def baseStart_3449315 : Nat := 118140960795 + 3449315 * 2 ^ 59
def prefixEnd_3449315 : Nat := 4983230072969 + 3 ^ 40 * 3449315 * 2
def baseEnd_3449315 : Nat := 1180771015842184848599597

theorem tailTrace_3449315 : CollatzResearch.WordTrace tailWord_3449315 prefixEnd_3449315 1180771015842184848599597 := by
  unfold tailWord_3449315
  simp only [CollatzResearch.WordTrace]
  refine ⟨125806853498728325946773399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83871235665818883964515599 125806853498728325946773399)
  ·
    refine ⟨188710280248092488920160099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125806853498728325946773399 188710280248092488920160099)
    ·
      refine ⟨283065420372138733380240149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188710280248092488920160099 283065420372138733380240149)
      ·
        refine ⟨13268691579944003127198757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 283065420372138733380240149 13268691579944003127198757)
        ·
          refine ⟨2487879671239500586349767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13268691579944003127198757 2487879671239500586349767)
          ·
            refine ⟨3731819506859250879524651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487879671239500586349767 3731819506859250879524651)
            ·
              refine ⟨5597729260288876319286977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731819506859250879524651 5597729260288876319286977)
              ·
                refine ⟨4198296945216657239465233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5597729260288876319286977 4198296945216657239465233)
                ·
                  refine ⟨3148722708912492929598925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4198296945216657239465233 3148722708912492929598925)
                  ·
                    refine ⟨1180771015842184848599597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148722708912492929598925 1180771015842184848599597)
                    ·
                      rfl

theorem cell22_3449315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 2, 3].length) (baseStart_3449315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449315 prefixEnd_3449315 := by exact prefixLift 3449315
  have htrace : WordTrace (prefixWord ++ tailWord_3449315) baseStart_3449315 baseEnd_3449315 := by
    simpa [prefixWord, tailWord_3449315, baseEnd_3449315] using wordTrace_append hprefix tailTrace_3449315
  have hstable : (prefixWord ++ tailWord_3449315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449315).length < 2 ^ (prefixWord ++ tailWord_3449315).sum := by decide
  have hdescent : baseEnd_3449315 < baseStart_3449315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449326 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3449326 : Nat := 118140960795 + 3449326 * 2 ^ 59
def prefixEnd_3449326 : Nat := 4983230072969 + 3 ^ 40 * 3449326 * 2
def baseEnd_3449326 : Nat := 1180774781366984486574563

theorem tailTrace_3449326 : CollatzResearch.WordTrace tailWord_3449326 prefixEnd_3449326 1180774781366984486574563 := by
  unfold tailWord_3449326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15725906837711059353177979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83871503134458983216949221 15725906837711059353177979)
  ·
    refine ⟨23588860256566589029766969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15725906837711059353177979 23588860256566589029766969)
    ·
      refine ⟨17691645192424941772325227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23588860256566589029766969 17691645192424941772325227)
      ·
        refine ⟨26537467788637412658487841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17691645192424941772325227 26537467788637412658487841)
        ·
          refine ⟨19903100841478059493865881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26537467788637412658487841 19903100841478059493865881)
          ·
            refine ⟨14927325631108544620399411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19903100841478059493865881 14927325631108544620399411)
            ·
              refine ⟨22390988446662816930599117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14927325631108544620399411 22390988446662816930599117)
              ·
                refine ⟨8396620667498556348974669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22390988446662816930599117 8396620667498556348974669)
                ·
                  refine ⟨3148732750311958630865501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8396620667498556348974669 3148732750311958630865501)
                  ·
                    refine ⟨1180774781366984486574563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148732750311958630865501 1180774781366984486574563)
                    ·
                      rfl

theorem cell22_3449326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3449326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449326 prefixEnd_3449326 := by exact prefixLift 3449326
  have htrace : WordTrace (prefixWord ++ tailWord_3449326) baseStart_3449326 baseEnd_3449326 := by
    simpa [prefixWord, tailWord_3449326, baseEnd_3449326] using wordTrace_append hprefix tailTrace_3449326
  have hstable : (prefixWord ++ tailWord_3449326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449326).length < 2 ^ (prefixWord ++ tailWord_3449326).sum := by decide
  have hdescent : baseEnd_3449326 < baseStart_3449326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449390 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_3449390 : Nat := 118140960795 + 3449390 * 2 ^ 59
def prefixEnd_3449390 : Nat := 4983230072969 + 3 ^ 40 * 3449390 * 2
def baseEnd_3449390 : Nat := 393598896624969884324789

theorem tailTrace_3449390 : CollatzResearch.WordTrace tailWord_3449390 prefixEnd_3449390 393598896624969884324789 := by
  unfold tailWord_3449390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15726198621682076719469203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83873059315637742503835749 15726198621682076719469203)
  ·
    refine ⟨23589297932523115079203805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15726198621682076719469203 23589297932523115079203805)
    ·
      refine ⟨8845986724696168154701427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23589297932523115079203805 8845986724696168154701427)
      ·
        refine ⟨13268980087044252232052141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845986724696168154701427 13268980087044252232052141)
        ·
          refine ⟨4975867532641594587019553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13268980087044252232052141 4975867532641594587019553)
          ·
            refine ⟨3731900649481195940264665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4975867532641594587019553 3731900649481195940264665)
            ·
              refine ⟨2798925487110896955198499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731900649481195940264665 2798925487110896955198499)
              ·
                refine ⟨4198388230666345432797749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798925487110896955198499 4198388230666345432797749)
                ·
                  refine ⟨393598896624969884324789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4198388230666345432797749 393598896624969884324789)
                  ·
                    rfl

theorem cell22_3449390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_3449390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449390 prefixEnd_3449390 := by exact prefixLift 3449390
  have htrace : WordTrace (prefixWord ++ tailWord_3449390) baseStart_3449390 baseEnd_3449390 := by
    simpa [prefixWord, tailWord_3449390, baseEnd_3449390] using wordTrace_append hprefix tailTrace_3449390
  have hstable : (prefixWord ++ tailWord_3449390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449390).length < 2 ^ (prefixWord ++ tailWord_3449390).sum := by decide
  have hdescent : baseEnd_3449390 < baseStart_3449390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449399 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 1, 5]
def baseStart_3449399 : Nat := 118140960795 + 3449399 * 2 ^ 59
def prefixEnd_3449399 : Nat := 4983230072969 + 3 ^ 40 * 3449399 * 2
def baseEnd_3449399 : Nat := 1180799770758836629499339

theorem tailTrace_3449399 : CollatzResearch.WordTrace tailWord_3449399 prefixEnd_3449399 1180799770758836629499339 := by
  unfold tailWord_3449399
  simp only [CollatzResearch.WordTrace]
  refine ⟨125809917230424008292831251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83873278153616005528554167 125809917230424008292831251)
  ·
    refine ⟨188714875845636012439246877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125809917230424008292831251 188714875845636012439246877)
    ·
      refine ⟨70768078442113504664717579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188714875845636012439246877 70768078442113504664717579)
      ·
        refine ⟨106152117663170256997076369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70768078442113504664717579 106152117663170256997076369)
        ·
          refine ⟨79614088247377692747807277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106152117663170256997076369 79614088247377692747807277)
          ·
            refine ⟨29855283092766634780427729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79614088247377692747807277 29855283092766634780427729)
            ·
              refine ⟨22391462319574976085320797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29855283092766634780427729 22391462319574976085320797)
              ·
                refine ⟨8396798369840616031995299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22391462319574976085320797 8396798369840616031995299)
                ·
                  refine ⟨12595197554760924047992949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396798369840616031995299 12595197554760924047992949)
                  ·
                    refine ⟨1180799770758836629499339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12595197554760924047992949 1180799770758836629499339)
                    ·
                      rfl

theorem cell22_3449399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_3449399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449399 prefixEnd_3449399 := by exact prefixLift 3449399
  have htrace : WordTrace (prefixWord ++ tailWord_3449399) baseStart_3449399 baseEnd_3449399 := by
    simpa [prefixWord, tailWord_3449399, baseEnd_3449399] using wordTrace_append hprefix tailTrace_3449399
  have hstable : (prefixWord ++ tailWord_3449399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449399).length < 2 ^ (prefixWord ++ tailWord_3449399).sum := by decide
  have hdescent : baseEnd_3449399 < baseStart_3449399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449508 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 5]
def baseStart_3449508 : Nat := 118140960795 + 3449508 * 2 ^ 59
def prefixEnd_3449508 : Nat := 4983230072969 + 3 ^ 40 * 3449508 * 2
def baseEnd_3449508 : Nat := 393612361228798892841335

theorem tailTrace_3449508 : CollatzResearch.WordTrace tailWord_3449508 prefixEnd_3449508 393612361228798892841335 := by
  unfold tailWord_3449508
  simp only [CollatzResearch.WordTrace]
  refine ⟨62906946393514559954274589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83875928524686079939032785 62906946393514559954274589)
  ·
    refine ⟨23590104897567959982852971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62906946393514559954274589 23590104897567959982852971)
    ·
      refine ⟨35385157346351939974279457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23590104897567959982852971 35385157346351939974279457)
      ·
        refine ⟨26538868009763954980709593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35385157346351939974279457 26538868009763954980709593)
        ·
          refine ⟨19904151007322966235532195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26538868009763954980709593 19904151007322966235532195)
          ·
            refine ⟨29856226510984449353298293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19904151007322966235532195 29856226510984449353298293)
            ·
              refine ⟨2799021235404792126871715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29856226510984449353298293 2799021235404792126871715)
              ·
                refine ⟨4198531853107188190307573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799021235404792126871715 4198531853107188190307573)
                ·
                  refine ⟨393612361228798892841335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4198531853107188190307573 393612361228798892841335)
                  ·
                    rfl

theorem cell22_3449508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_3449508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449508 prefixEnd_3449508 := by exact prefixLift 3449508
  have htrace : WordTrace (prefixWord ++ tailWord_3449508) baseStart_3449508 baseEnd_3449508 := by
    simpa [prefixWord, tailWord_3449508, baseEnd_3449508] using wordTrace_append hprefix tailTrace_3449508
  have hstable : (prefixWord ++ tailWord_3449508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449508).length < 2 ^ (prefixWord ++ tailWord_3449508).sum := by decide
  have hdescent : baseEnd_3449508 < baseStart_3449508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449581 : List Nat := [1, 5, 1, 2, 1, 1, 1, 10]
def baseStart_3449581 : Nat := 118140960795 + 3449581 * 2 ^ 59
def prefixEnd_3449581 : Nat := 4983230072969 + 3 ^ 40 * 3449581 * 2
def baseEnd_3449581 : Nat := 131206897008694313494309

theorem tailTrace_3449581 : CollatzResearch.WordTrace tailWord_3449581 prefixEnd_3449581 131206897008694313494309 := by
  unfold tailWord_3449581
  simp only [CollatzResearch.WordTrace]
  refine ⟨125816555315764653375956597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83877703543843102250637731 125816555315764653375956597)
  ·
    refine ⟨11795302060852936253995931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125816555315764653375956597 11795302060852936253995931)
    ·
      refine ⟨17692953091279404380993897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795302060852936253995931 17692953091279404380993897)
      ·
        refine ⟨13269714818459553285745423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17692953091279404380993897 13269714818459553285745423)
        ·
          refine ⟨19904572227689329928618135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13269714818459553285745423 19904572227689329928618135)
          ·
            refine ⟨29856858341533994892927203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19904572227689329928618135 29856858341533994892927203)
            ·
              refine ⟨44785287512300992339390805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29856858341533994892927203 44785287512300992339390805)
              ·
                refine ⟨131206897008694313494309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44785287512300992339390805 131206897008694313494309)
                ·
                  rfl

theorem cell22_3449581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 10].length) (baseStart_3449581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449581 prefixEnd_3449581 := by exact prefixLift 3449581
  have htrace : WordTrace (prefixWord ++ tailWord_3449581) baseStart_3449581 baseEnd_3449581 := by
    simpa [prefixWord, tailWord_3449581, baseEnd_3449581] using wordTrace_append hprefix tailTrace_3449581
  have hstable : (prefixWord ++ tailWord_3449581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449581).length < 2 ^ (prefixWord ++ tailWord_3449581).sum := by decide
  have hdescent : baseEnd_3449581 < baseStart_3449581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449583 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 2, 4]
def baseStart_3449583 : Nat := 118140960795 + 3449583 * 2 ^ 59
def prefixEnd_3449583 : Nat := 4983230072969 + 3 ^ 40 * 3449583 * 2
def baseEnd_3449583 : Nat := 1180862757719121482898775

theorem tailTrace_3449583 : CollatzResearch.WordTrace tailWord_3449583 prefixEnd_3449583 1180862757719121482898775 := by
  unfold tailWord_3449583
  simp only [CollatzResearch.WordTrace]
  refine ⟨125816628261757407717529403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83877752174504938478352935 125816628261757407717529403)
  ·
    refine ⟨188724942392636111576294105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125816628261757407717529403 188724942392636111576294105)
    ·
      refine ⟨141543706794477083682220579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188724942392636111576294105 141543706794477083682220579)
      ·
        refine ⟨212315560191715625523330869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141543706794477083682220579 212315560191715625523330869)
        ·
          refine ⟨19904583767973339892812269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212315560191715625523330869 19904583767973339892812269)
          ·
            refine ⟨7464218912990002459804601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19904583767973339892812269 7464218912990002459804601)
            ·
              refine ⟨5598164184742501844853451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7464218912990002459804601 5598164184742501844853451)
              ·
                refine ⟨8397246277113752767280177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5598164184742501844853451 8397246277113752767280177)
                ·
                  refine ⟨6297934707835314575460133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8397246277113752767280177 6297934707835314575460133)
                  ·
                    refine ⟨1180862757719121482898775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6297934707835314575460133 1180862757719121482898775)
                    ·
                      rfl

theorem cell22_3449583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_3449583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449583 prefixEnd_3449583 := by exact prefixLift 3449583
  have htrace : WordTrace (prefixWord ++ tailWord_3449583) baseStart_3449583 baseEnd_3449583 := by
    simpa [prefixWord, tailWord_3449583, baseEnd_3449583] using wordTrace_append hprefix tailTrace_3449583
  have hstable : (prefixWord ++ tailWord_3449583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449583).length < 2 ^ (prefixWord ++ tailWord_3449583).sum := by decide
  have hdescent : baseEnd_3449583 < baseStart_3449583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449602 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3449602 : Nat := 118140960795 + 3449602 * 2 ^ 59
def prefixEnd_3449602 : Nat := 4983230072969 + 3 ^ 40 * 3449602 * 2
def baseEnd_3449602 : Nat := 1180869261807411766673717

theorem tailTrace_3449602 : CollatzResearch.WordTrace tailWord_3449602 prefixEnd_3449602 1180869261807411766673717 := by
  unfold tailWord_3449602
  simp only [CollatzResearch.WordTrace]
  refine ⟨31454330312172143490617765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83878214165792382641647373 31454330312172143490617765)
  ·
    refine ⟨5897686933532276904490831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31454330312172143490617765 5897686933532276904490831)
    ·
      refine ⟨8846530400298415356736247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5897686933532276904490831 8846530400298415356736247)
      ·
        refine ⟨13269795600447623035104371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8846530400298415356736247 13269795600447623035104371)
        ·
          refine ⟨19904693400671434552656557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13269795600447623035104371 19904693400671434552656557)
          ·
            refine ⟨7464260025251787957246209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19904693400671434552656557 7464260025251787957246209)
            ·
              refine ⟨5598195018938840967934657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7464260025251787957246209 5598195018938840967934657)
              ·
                refine ⟨4198646264204130725950993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598195018938840967934657 4198646264204130725950993)
                ·
                  refine ⟨3148984698153098044463245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4198646264204130725950993 3148984698153098044463245)
                  ·
                    refine ⟨1180869261807411766673717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3148984698153098044463245 1180869261807411766673717)
                    ·
                      rfl

theorem cell22_3449602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3449602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449602 prefixEnd_3449602 := by exact prefixLift 3449602
  have htrace : WordTrace (prefixWord ++ tailWord_3449602) baseStart_3449602 baseEnd_3449602 := by
    simpa [prefixWord, tailWord_3449602, baseEnd_3449602] using wordTrace_append hprefix tailTrace_3449602
  have hstable : (prefixWord ++ tailWord_3449602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449602).length < 2 ^ (prefixWord ++ tailWord_3449602).sum := by decide
  have hdescent : baseEnd_3449602 < baseStart_3449602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449690 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_3449690 : Nat := 118140960795 + 3449690 * 2 ^ 59
def prefixEnd_3449690 : Nat := 4983230072969 + 3 ^ 40 * 3449690 * 2
def baseEnd_3449690 : Nat := 1180899386005808870473447

theorem tailTrace_3449690 : CollatzResearch.WordTrace tailWord_3449690 prefixEnd_3449690 1180899386005808870473447 := by
  unfold tailWord_3449690
  simp only [CollatzResearch.WordTrace]
  refine ⟨31455132718092441247918631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83880353914913176661116349 31455132718092441247918631)
  ·
    refine ⟨47182699077138661871877947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31455132718092441247918631 47182699077138661871877947)
    ·
      refine ⟨70774048615707992807816921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47182699077138661871877947 70774048615707992807816921)
      ·
        refine ⟨53080536461780994605862691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70774048615707992807816921 53080536461780994605862691)
        ·
          refine ⟨79620804692671491908794037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53080536461780994605862691 79620804692671491908794037)
          ·
            refine ⟨7464450439937952366449441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79620804692671491908794037 7464450439937952366449441)
            ·
              refine ⟨5598337829953464274837081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7464450439937952366449441 5598337829953464274837081)
              ·
                refine ⟨4198753372465098206127811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598337829953464274837081 4198753372465098206127811)
                ·
                  refine ⟨6298130058697647309191717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198753372465098206127811 6298130058697647309191717)
                  ·
                    refine ⟨1180899386005808870473447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6298130058697647309191717 1180899386005808870473447)
                    ·
                      rfl

theorem cell22_3449690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_3449690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449690 prefixEnd_3449690 := by exact prefixLift 3449690
  have htrace : WordTrace (prefixWord ++ tailWord_3449690) baseStart_3449690 baseEnd_3449690 := by
    simpa [prefixWord, tailWord_3449690, baseEnd_3449690] using wordTrace_append hprefix tailTrace_3449690
  have hstable : (prefixWord ++ tailWord_3449690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449690).length < 2 ^ (prefixWord ++ tailWord_3449690).sum := by decide
  have hdescent : baseEnd_3449690 < baseStart_3449690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449733 : List Nat := [1, 3, 1, 1, 3, 4, 2, 7]
def baseStart_3449733 : Nat := 118140960795 + 3449733 * 2 ^ 59
def prefixEnd_3449733 : Nat := 4983230072969 + 3 ^ 40 * 3449733 * 2
def baseEnd_3449733 : Nat := 131212678420507899072035

theorem tailTrace_3449733 : CollatzResearch.WordTrace tailWord_3449733 prefixEnd_3449733 131212678420507899072035 := by
  unfold tailWord_3449733
  simp only [CollatzResearch.WordTrace]
  refine ⟨125822099211213983335489853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83881399474142655556993235 125822099211213983335489853)
  ·
    refine ⟨47183287204205243750808695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125822099211213983335489853 47183287204205243750808695)
    ·
      refine ⟨70774930806307865626213043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47183287204205243750808695 70774930806307865626213043)
      ·
        refine ⟨106162396209461798439319565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70774930806307865626213043 106162396209461798439319565)
        ·
          refine ⟨39810898578548174414744837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106162396209461798439319565 39810898578548174414744837)
          ·
            refine ⟨7464543483477782702764657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39810898578548174414744837 7464543483477782702764657)
            ·
              refine ⟨5598407612608337027073493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7464543483477782702764657 5598407612608337027073493)
              ·
                refine ⟨131212678420507899072035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5598407612608337027073493 131212678420507899072035)
                ·
                  rfl

theorem cell22_3449733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 7].length) (baseStart_3449733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449733 prefixEnd_3449733 := by exact prefixLift 3449733
  have htrace : WordTrace (prefixWord ++ tailWord_3449733) baseStart_3449733 baseEnd_3449733 := by
    simpa [prefixWord, tailWord_3449733, baseEnd_3449733] using wordTrace_append hprefix tailTrace_3449733
  have hstable : (prefixWord ++ tailWord_3449733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449733).length < 2 ^ (prefixWord ++ tailWord_3449733).sum := by decide
  have hdescent : baseEnd_3449733 < baseStart_3449733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449737 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 2, 3]
def baseStart_3449737 : Nat := 118140960795 + 3449737 * 2 ^ 59
def prefixEnd_3449737 : Nat := 4983230072969 + 3 ^ 40 * 3449737 * 2
def baseEnd_3449737 : Nat := 1180915475066316414548303

theorem tailTrace_3449737 : CollatzResearch.WordTrace tailWord_3449737 prefixEnd_3449737 1180915475066316414548303 := by
  unfold tailWord_3449737
  simp only [CollatzResearch.WordTrace]
  refine ⟨125822245103199492018635465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83881496735466328012423643 125822245103199492018635465)
  ·
    refine ⟨94366683827399619013976599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125822245103199492018635465 94366683827399619013976599)
    ·
      refine ⟨141550025741099428520964899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94366683827399619013976599 141550025741099428520964899)
      ·
        refine ⟨212325038611649142781447349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141550025741099428520964899 212325038611649142781447349)
        ·
          refine ⟨19905472369842107135760689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212325038611649142781447349 19905472369842107135760689)
          ·
            refine ⟨14929104277381580351820517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19905472369842107135760689 14929104277381580351820517)
            ·
              refine ⟨2799207052009046315966347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14929104277381580351820517 2799207052009046315966347)
              ·
                refine ⟨4198810578013569473949521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799207052009046315966347 4198810578013569473949521)
                ·
                  refine ⟨3149107933510177105462141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4198810578013569473949521 3149107933510177105462141)
                  ·
                    refine ⟨1180915475066316414548303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3149107933510177105462141 1180915475066316414548303)
                    ·
                      rfl

theorem cell22_3449737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_3449737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449737 prefixEnd_3449737 := by exact prefixLift 3449737
  have htrace : WordTrace (prefixWord ++ tailWord_3449737) baseStart_3449737 baseEnd_3449737 := by
    simpa [prefixWord, tailWord_3449737, baseEnd_3449737] using wordTrace_append hprefix tailTrace_3449737
  have hstable : (prefixWord ++ tailWord_3449737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449737).length < 2 ^ (prefixWord ++ tailWord_3449737).sum := by decide
  have hdescent : baseEnd_3449737 < baseStart_3449737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449773 : List Nat := [1, 5, 2, 3, 2, 1, 2, 2, 4]
def baseStart_3449773 : Nat := 118140960795 + 3449773 * 2 ^ 59
def prefixEnd_3449773 : Nat := 4983230072969 + 3 ^ 40 * 3449773 * 2
def baseEnd_3449773 : Nat := 393642599534008106882731

theorem tailTrace_3449773 : CollatzResearch.WordTrace tailWord_3449773 prefixEnd_3449773 393642599534008106882731 := by
  unfold tailWord_3449773
  simp only [CollatzResearch.WordTrace]
  refine ⟨125823558131069070166945973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83882372087379380111297315 125823558131069070166945973)
  ·
    refine ⟨11795958574787725328151185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125823558131069070166945973 11795958574787725328151185)
    ·
      refine ⟨8846968931090793996113389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11795958574787725328151185 8846968931090793996113389)
      ·
        refine ⟨3317613349159047748542521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8846968931090793996113389 3317613349159047748542521)
        ·
          refine ⟨2488210011869285811406891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3317613349159047748542521 2488210011869285811406891)
          ·
            refine ⟨3732315017803928717110337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488210011869285811406891 3732315017803928717110337)
            ·
              refine ⟨2799236263352946537832753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3732315017803928717110337 2799236263352946537832753)
              ·
                refine ⟨2099427197514709903374565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2799236263352946537832753 2099427197514709903374565)
                ·
                  refine ⟨393642599534008106882731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2099427197514709903374565 393642599534008106882731)
                  ·
                    rfl

theorem cell22_3449773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_3449773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449773 prefixEnd_3449773 := by exact prefixLift 3449773
  have htrace : WordTrace (prefixWord ++ tailWord_3449773) baseStart_3449773 baseEnd_3449773 := by
    simpa [prefixWord, tailWord_3449773, baseEnd_3449773] using wordTrace_append hprefix tailTrace_3449773
  have hstable : (prefixWord ++ tailWord_3449773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449773).length < 2 ^ (prefixWord ++ tailWord_3449773).sum := by decide
  have hdescent : baseEnd_3449773 < baseStart_3449773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449829 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 5]
def baseStart_3449829 : Nat := 118140960795 + 3449829 * 2 ^ 59
def prefixEnd_3449829 : Nat := 4983230072969 + 3 ^ 40 * 3449829 * 2
def baseEnd_3449829 : Nat := 393648989515486280416007

theorem tailTrace_3449829 : CollatzResearch.WordTrace tailWord_3449829 prefixEnd_3449829 393648989515486280416007 := by
  unfold tailWord_3449829
  simp only [CollatzResearch.WordTrace]
  refine ⟨125825600618866191730984541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83883733745910794487323027 125825600618866191730984541)
  ·
    refine ⟨47184600232074821899119203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125825600618866191730984541 47184600232074821899119203)
    ·
      refine ⟨70776900348112232848678805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47184600232074821899119203 70776900348112232848678805)
      ·
        refine ⟨3317667203817760914781819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70776900348112232848678805 3317667203817760914781819)
        ·
          refine ⟨4976500805726641372172729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317667203817760914781819 4976500805726641372172729)
          ·
            refine ⟨3732375604294981029129547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4976500805726641372172729 3732375604294981029129547)
            ·
              refine ⟨5598563406442471543694321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3732375604294981029129547 5598563406442471543694321)
              ·
                refine ⟨4198922554831853657770741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598563406442471543694321 4198922554831853657770741)
                ·
                  refine ⟨393648989515486280416007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4198922554831853657770741 393648989515486280416007)
                  ·
                    rfl

theorem cell22_3449829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_3449829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449829 prefixEnd_3449829 := by exact prefixLift 3449829
  have htrace : WordTrace (prefixWord ++ tailWord_3449829) baseStart_3449829 baseEnd_3449829 := by
    simpa [prefixWord, tailWord_3449829, baseEnd_3449829] using wordTrace_append hprefix tailTrace_3449829
  have hstable : (prefixWord ++ tailWord_3449829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449829).length < 2 ^ (prefixWord ++ tailWord_3449829).sum := by decide
  have hdescent : baseEnd_3449829 < baseStart_3449829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449870 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3449870 : Nat := 118140960795 + 3449870 * 2 ^ 59
def prefixEnd_3449870 : Nat := 4983230072969 + 3 ^ 40 * 3449870 * 2
def baseEnd_3449870 : Nat := 1180961003684348400972895

theorem tailTrace_3449870 : CollatzResearch.WordTrace tailWord_3449870 prefixEnd_3449870 1180961003684348400972895 := by
  unfold tailWord_3449870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728387001464706966653383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83884730674478437155484709 15728387001464706966653383)
  ·
    refine ⟨23592580502197060449980075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15728387001464706966653383 23592580502197060449980075)
    ·
      refine ⟨35388870753295590674970113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23592580502197060449980075 35388870753295590674970113)
      ·
        refine ⟨26541653064971693006227585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35388870753295590674970113 26541653064971693006227585)
        ·
          refine ⟨19906239798728769754670689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26541653064971693006227585 19906239798728769754670689)
          ·
            refine ⟨14929679849046577316003017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19906239798728769754670689 14929679849046577316003017)
            ·
              refine ⟨11197259886784932987002263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14929679849046577316003017 11197259886784932987002263)
              ·
                refine ⟨16795889830177399480503395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11197259886784932987002263 16795889830177399480503395)
                ·
                  refine ⟨25193834745266099220755093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16795889830177399480503395 25193834745266099220755093)
                  ·
                    refine ⟨1180961003684348400972895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25193834745266099220755093 1180961003684348400972895)
                    ·
                      rfl

theorem cell22_3449870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3449870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449870 prefixEnd_3449870 := by exact prefixLift 3449870
  have htrace : WordTrace (prefixWord ++ tailWord_3449870) baseStart_3449870 baseEnd_3449870 := by
    simpa [prefixWord, tailWord_3449870, baseEnd_3449870] using wordTrace_append hprefix tailTrace_3449870
  have hstable : (prefixWord ++ tailWord_3449870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449870).length < 2 ^ (prefixWord ++ tailWord_3449870).sum := by decide
  have hdescent : baseEnd_3449870 < baseStart_3449870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449934 : List Nat := [4, 1, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_3449934 : Nat := 118140960795 + 3449934 * 2 ^ 59
def prefixEnd_3449934 : Nat := 4983230072969 + 3 ^ 40 * 3449934 * 2
def baseEnd_3449934 : Nat := 1180982912192273567372699

theorem tailTrace_3449934 : CollatzResearch.WordTrace tailWord_3449934 prefixEnd_3449934 1180982912192273567372699 := by
  unfold tailWord_3449934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728678785435724332944607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83886286855657196442371237 15728678785435724332944607)
  ·
    refine ⟨23593018178153586499416911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15728678785435724332944607 23593018178153586499416911)
    ·
      refine ⟨35389527267230379749125367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23593018178153586499416911 35389527267230379749125367)
      ·
        refine ⟨53084290900845569623688051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35389527267230379749125367 53084290900845569623688051)
        ·
          refine ⟨79626436351268354435532077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53084290900845569623688051 79626436351268354435532077)
          ·
            refine ⟨29859913631725632913324529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79626436351268354435532077 29859913631725632913324529)
            ·
              refine ⟨22394935223794224684993397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29859913631725632913324529 22394935223794224684993397)
              ·
                refine ⟨2099525177230708564218131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22394935223794224684993397 2099525177230708564218131)
                ·
                  refine ⟨3149287765846062846327197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099525177230708564218131 3149287765846062846327197)
                  ·
                    refine ⟨1180982912192273567372699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3149287765846062846327197 1180982912192273567372699)
                    ·
                      rfl

theorem cell22_3449934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_3449934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449934 prefixEnd_3449934 := by exact prefixLift 3449934
  have htrace : WordTrace (prefixWord ++ tailWord_3449934) baseStart_3449934 baseEnd_3449934 := by
    simpa [prefixWord, tailWord_3449934, baseEnd_3449934] using wordTrace_append hprefix tailTrace_3449934
  have hstable : (prefixWord ++ tailWord_3449934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449934).length < 2 ^ (prefixWord ++ tailWord_3449934).sum := by decide
  have hdescent : baseEnd_3449934 < baseStart_3449934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449962 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_3449962 : Nat := 118140960795 + 3449962 * 2 ^ 59
def prefixEnd_3449962 : Nat := 4983230072969 + 3 ^ 40 * 3449962 * 2
def baseEnd_3449962 : Nat := 1180992497164490827672613

theorem tailTrace_3449962 : CollatzResearch.WordTrace tailWord_3449962 prefixEnd_3449962 1180992497164490827672613 := by
  unfold tailWord_3449962
  simp only [CollatzResearch.WordTrace]
  refine ⟨31457612881846088861394035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83886967684922903630384093 31457612881846088861394035)
  ·
    refine ⟨47186419322769133292091053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31457612881846088861394035 47186419322769133292091053)
    ·
      refine ⟨17694907246038424984534145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47186419322769133292091053 17694907246038424984534145)
      ·
        refine ⟨13271180434528818738400609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17694907246038424984534145 13271180434528818738400609)
        ·
          refine ⟨9953385325896614053800457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13271180434528818738400609 9953385325896614053800457)
          ·
            refine ⟨7465038994422460540350343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9953385325896614053800457 7465038994422460540350343)
            ·
              refine ⟨11197558491633690810525515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465038994422460540350343 11197558491633690810525515)
              ·
                refine ⟨16796337737450536215788273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11197558491633690810525515 16796337737450536215788273)
                ·
                  refine ⟨12597253303087902161841205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16796337737450536215788273 12597253303087902161841205)
                  ·
                    refine ⟨1180992497164490827672613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12597253303087902161841205 1180992497164490827672613)
                    ·
                      rfl

theorem cell22_3449962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_3449962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449962 prefixEnd_3449962 := by exact prefixLift 3449962
  have htrace : WordTrace (prefixWord ++ tailWord_3449962) baseStart_3449962 baseEnd_3449962 := by
    simpa [prefixWord, tailWord_3449962, baseEnd_3449962] using wordTrace_append hprefix tailTrace_3449962
  have hstable : (prefixWord ++ tailWord_3449962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449962).length < 2 ^ (prefixWord ++ tailWord_3449962).sum := by decide
  have hdescent : baseEnd_3449962 < baseStart_3449962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449975 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 6]
def baseStart_3449975 : Nat := 118140960795 + 3449975 * 2 ^ 59
def prefixEnd_3449975 : Nat := 4983230072969 + 3 ^ 40 * 3449975 * 2
def baseEnd_3449975 : Nat := 393665649110054375699191

theorem tailTrace_3449975 : CollatzResearch.WordTrace tailWord_3449975 prefixEnd_3449975 393665649110054375699191 := by
  unfold tailWord_3449975
  simp only [CollatzResearch.WordTrace]
  refine ⟨125830925676337258665799379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83887283784224839110532919 125830925676337258665799379)
  ·
    refine ⟨188746388514505887998699069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125830925676337258665799379 188746388514505887998699069)
    ·
      refine ⟨70779895692939707999512151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188746388514505887998699069 70779895692939707999512151)
      ·
        refine ⟨106169843539409561999268227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70779895692939707999512151 106169843539409561999268227)
        ·
          refine ⟨159254765309114342998902341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106169843539409561999268227 159254765309114342998902341)
          ·
            refine ⟨29860268495458939312294189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159254765309114342998902341 29860268495458939312294189)
            ·
              refine ⟨11197600685797102242110321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29860268495458939312294189 11197600685797102242110321)
              ·
                refine ⟨8398200514347826681582741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11197600685797102242110321 8398200514347826681582741)
                ·
                  refine ⟨393665649110054375699191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8398200514347826681582741 393665649110054375699191)
                  ·
                    rfl

theorem cell22_3449975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 6].length) (baseStart_3449975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3449975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3449975 prefixEnd_3449975 := by exact prefixLift 3449975
  have htrace : WordTrace (prefixWord ++ tailWord_3449975) baseStart_3449975 baseEnd_3449975 := by
    simpa [prefixWord, tailWord_3449975, baseEnd_3449975] using wordTrace_append hprefix tailTrace_3449975
  have hstable : (prefixWord ++ tailWord_3449975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449975).length < 2 ^ (prefixWord ++ tailWord_3449975).sum := by decide
  have hdescent : baseEnd_3449975 < baseStart_3449975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450120 : List Nat := [2, 1, 3, 2, 4, 2, 2, 2, 1, 3]
def baseStart_3450120 : Nat := 118140960795 + 3450120 * 2 ^ 59
def prefixEnd_3450120 : Nat := 4983230072969 + 3 ^ 40 * 3450120 * 2
def baseEnd_3450120 : Nat := 1181046583793431082222129

theorem tailTrace_3450120 : CollatzResearch.WordTrace tailWord_3450120 prefixEnd_3450120 1181046583793431082222129 := by
  unfold tailWord_3450120
  simp only [CollatzResearch.WordTrace]
  refine ⟨62918107130405974214913907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83890809507207965619885209 62918107130405974214913907)
  ·
    refine ⟨94377160695608961322370861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62918107130405974214913907 94377160695608961322370861)
    ·
      refine ⟨35391435260853360495889073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94377160695608961322370861 35391435260853360495889073)
      ·
        refine ⟨26543576445640020371916805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35391435260853360495889073 26543576445640020371916805)
        ·
          refine ⟨4976920583557503819734401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26543576445640020371916805 4976920583557503819734401)
          ·
            refine ⟨3732690437668127864800801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4976920583557503819734401 3732690437668127864800801)
            ·
              refine ⟨2799517828251095898600601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3732690437668127864800801 2799517828251095898600601)
              ·
                refine ⟨2099638371188321923950451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2799517828251095898600601 2099638371188321923950451)
                ·
                  refine ⟨3149457556782482885925677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099638371188321923950451 3149457556782482885925677)
                  ·
                    refine ⟨1181046583793431082222129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3149457556782482885925677 1181046583793431082222129)
                    ·
                      rfl

theorem cell22_3450120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_3450120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450120 prefixEnd_3450120 := by exact prefixLift 3450120
  have htrace : WordTrace (prefixWord ++ tailWord_3450120) baseStart_3450120 baseEnd_3450120 := by
    simpa [prefixWord, tailWord_3450120, baseEnd_3450120] using wordTrace_append hprefix tailTrace_3450120
  have hstable : (prefixWord ++ tailWord_3450120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450120).length < 2 ^ (prefixWord ++ tailWord_3450120).sum := by decide
  have hdescent : baseEnd_3450120 < baseStart_3450120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450144 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 6]
def baseStart_3450144 : Nat := 118140960795 + 3450144 * 2 ^ 59
def prefixEnd_3450144 : Nat := 4983230072969 + 3 ^ 40 * 3450144 * 2
def baseEnd_3450144 : Nat := 393684933161301006540685

theorem tailTrace_3450144 : CollatzResearch.WordTrace tailWord_3450144 prefixEnd_3450144 393684933161301006540685 := by
  unfold tailWord_3450144
  simp only [CollatzResearch.WordTrace]
  refine ⟨62918544806362500264350743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83891393075150000352467657 62918544806362500264350743)
  ·
    refine ⟨94377817209543750396526115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62918544806362500264350743 94377817209543750396526115)
    ·
      refine ⟨141566725814315625594789173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94377817209543750396526115 141566725814315625594789173)
      ·
        refine ⟨13271880545092089899511485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141566725814315625594789173 13271880545092089899511485)
        ·
          refine ⟨4976955204409533712316807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13271880545092089899511485 4976955204409533712316807)
          ·
            refine ⟨7465432806614300568475211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976955204409533712316807 7465432806614300568475211)
            ·
              refine ⟨11198149209921450852712817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465432806614300568475211 11198149209921450852712817)
              ·
                refine ⟨8398611907441088139534613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11198149209921450852712817 8398611907441088139534613)
                ·
                  refine ⟨393684933161301006540685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8398611907441088139534613 393684933161301006540685)
                  ·
                    rfl

theorem cell22_3450144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_3450144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450144 prefixEnd_3450144 := by exact prefixLift 3450144
  have htrace : WordTrace (prefixWord ++ tailWord_3450144) baseStart_3450144 baseEnd_3450144 := by
    simpa [prefixWord, tailWord_3450144, baseEnd_3450144] using wordTrace_append hprefix tailTrace_3450144
  have hstable : (prefixWord ++ tailWord_3450144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450144).length < 2 ^ (prefixWord ++ tailWord_3450144).sum := by decide
  have hdescent : baseEnd_3450144 < baseStart_3450144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450161 : List Nat := [1, 2, 2, 3, 3, 2, 2, 3, 4]
def baseStart_3450161 : Nat := 118140960795 + 3450161 * 2 ^ 59
def prefixEnd_3450161 : Nat := 4983230072969 + 3 ^ 40 * 3450161 * 2
def baseEnd_3450161 : Nat := 393686872977106880649001

theorem tailTrace_3450161 : CollatzResearch.WordTrace tailWord_3450161 prefixEnd_3450161 393686872977106880649001 := by
  unfold tailWord_3450161
  simp only [CollatzResearch.WordTrace]
  refine ⟨125837709653663412432070337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83891806435775608288046891 125837709653663412432070337)
  ·
    refine ⟨94378282240247559324052753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125837709653663412432070337 94378282240247559324052753)
    ·
      refine ⟨70783711680185669493039565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94378282240247559324052753 70783711680185669493039565)
      ·
        refine ⟨26543891880069626059889837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70783711680185669493039565 26543891880069626059889837)
        ·
          refine ⟨9953959455026109772458689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26543891880069626059889837 9953959455026109772458689)
          ·
            refine ⟨7465469591269582329344017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9953959455026109772458689 7465469591269582329344017)
            ·
              refine ⟨5599102193452186747008013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7465469591269582329344017 5599102193452186747008013)
              ·
                refine ⟨2099663322544570030128005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5599102193452186747008013 2099663322544570030128005)
                ·
                  refine ⟨393686872977106880649001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2099663322544570030128005 393686872977106880649001)
                  ·
                    rfl

theorem cell22_3450161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_3450161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450161 prefixEnd_3450161 := by exact prefixLift 3450161
  have htrace : WordTrace (prefixWord ++ tailWord_3450161) baseStart_3450161 baseEnd_3450161 := by
    simpa [prefixWord, tailWord_3450161, baseEnd_3450161] using wordTrace_append hprefix tailTrace_3450161
  have hstable : (prefixWord ++ tailWord_3450161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450161).length < 2 ^ (prefixWord ++ tailWord_3450161).sum := by decide
  have hdescent : baseEnd_3450161 < baseStart_3450161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450172 : List Nat := [2, 2, 2, 2, 1, 4, 9]
def baseStart_3450172 : Nat := 118140960795 + 3450172 * 2 ^ 59
def prefixEnd_3450172 : Nat := 4983230072969 + 3 ^ 40 * 3450172 * 2
def baseEnd_3450172 : Nat := 43743125350226677034147

theorem tailTrace_3450172 : CollatzResearch.WordTrace tailWord_3450172 prefixEnd_3450172 43743125350226677034147 := by
  unfold tailWord_3450172
  simp only [CollatzResearch.WordTrace]
  refine ⟨62919055428311780655360385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83892073904415707540480513 62919055428311780655360385)
  ·
    refine ⟨47189291571233835491520289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62919055428311780655360385 47189291571233835491520289)
    ·
      refine ⟨35391968678425376618640217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47189291571233835491520289 35391968678425376618640217)
      ·
        refine ⟨26543976508819032463980163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35391968678425376618640217 26543976508819032463980163)
        ·
          refine ⟨39815964763228548695970245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26543976508819032463980163 39815964763228548695970245)
          ·
            refine ⟨7465493393105352880494421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39815964763228548695970245 7465493393105352880494421)
            ·
              refine ⟨43743125350226677034147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7465493393105352880494421 43743125350226677034147)
              ·
                rfl

theorem cell22_3450172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 9].length) (baseStart_3450172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450172 prefixEnd_3450172 := by exact prefixLift 3450172
  have htrace : WordTrace (prefixWord ++ tailWord_3450172) baseStart_3450172 baseEnd_3450172 := by
    simpa [prefixWord, tailWord_3450172, baseEnd_3450172] using wordTrace_append hprefix tailTrace_3450172
  have hstable : (prefixWord ++ tailWord_3450172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450172).length < 2 ^ (prefixWord ++ tailWord_3450172).sum := by decide
  have hdescent : baseEnd_3450172 < baseStart_3450172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450174 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3450174 : Nat := 118140960795 + 3450174 * 2 ^ 59
def prefixEnd_3450174 : Nat := 4983230072969 + 3 ^ 40 * 3450174 * 2
def baseEnd_3450174 : Nat := 1181065069096992941371963

theorem tailTrace_3450174 : CollatzResearch.WordTrace tailWord_3450174 prefixEnd_3450174 1181065069096992941371963 := by
  unfold tailWord_3450174
  simp only [CollatzResearch.WordTrace]
  refine ⟨15729772975327039456536697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83892122535077543768195717 15729772975327039456536697)
  ·
    refine ⟨11797329731495279592402523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15729772975327039456536697 11797329731495279592402523)
    ·
      refine ⟨17695994597242919388603785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11797329731495279592402523 17695994597242919388603785)
      ·
        refine ⟨13271995947932189541452839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17695994597242919388603785 13271995947932189541452839)
        ·
          refine ⟨19907993921898284312179259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13271995947932189541452839 19907993921898284312179259)
          ·
            refine ⟨29861990882847426468268889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19907993921898284312179259 29861990882847426468268889)
            ·
              refine ⟨22396493162135569851201667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29861990882847426468268889 22396493162135569851201667)
              ·
                refine ⟨33594739743203354776802501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22396493162135569851201667 33594739743203354776802501)
                ·
                  refine ⟨6299013701850629020650469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33594739743203354776802501 6299013701850629020650469)
                  ·
                    refine ⟨1181065069096992941371963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299013701850629020650469 1181065069096992941371963)
                    ·
                      rfl

theorem cell22_3450174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3450174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450174 prefixEnd_3450174 := by exact prefixLift 3450174
  have htrace : WordTrace (prefixWord ++ tailWord_3450174) baseStart_3450174 baseEnd_3450174 := by
    simpa [prefixWord, tailWord_3450174, baseEnd_3450174] using wordTrace_append hprefix tailTrace_3450174
  have hstable : (prefixWord ++ tailWord_3450174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450174).length < 2 ^ (prefixWord ++ tailWord_3450174).sum := by decide
  have hdescent : baseEnd_3450174 < baseStart_3450174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450202 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_3450202 : Nat := 118140960795 + 3450202 * 2 ^ 59
def prefixEnd_3450202 : Nat := 4983230072969 + 3 ^ 40 * 3450202 * 2
def baseEnd_3450202 : Nat := 1181074654069210201671877

theorem tailTrace_3450202 : CollatzResearch.WordTrace tailWord_3450202 prefixEnd_3450202 1181074654069210201671877 := by
  unfold tailWord_3450202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31459801261628719108578215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83892803364343250956208573 31459801261628719108578215)
  ·
    refine ⟨47189701892443078662867323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31459801261628719108578215 47189701892443078662867323)
    ·
      refine ⟨70784552838664617994300985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47189701892443078662867323 70784552838664617994300985)
      ·
        refine ⟨53088414628998463495725739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70784552838664617994300985 53088414628998463495725739)
        ·
          refine ⟨79632621943497695243588609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53088414628998463495725739 79632621943497695243588609)
          ·
            refine ⟨59724466457623271432691457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79632621943497695243588609 59724466457623271432691457)
            ·
              refine ⟨44793349843217453574518593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59724466457623271432691457 44793349843217453574518593)
              ·
                refine ⟨33595012382413090180888945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44793349843217453574518593 33595012382413090180888945)
                ·
                  refine ⟨25196259286809817635666709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33595012382413090180888945 25196259286809817635666709)
                  ·
                    refine ⟨1181074654069210201671877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25196259286809817635666709 1181074654069210201671877)
                    ·
                      rfl

theorem cell22_3450202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_3450202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450202 prefixEnd_3450202 := by exact prefixLift 3450202
  have htrace : WordTrace (prefixWord ++ tailWord_3450202) baseStart_3450202 baseEnd_3450202 := by
    simpa [prefixWord, tailWord_3450202, baseEnd_3450202] using wordTrace_append hprefix tailTrace_3450202
  have hstable : (prefixWord ++ tailWord_3450202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450202).length < 2 ^ (prefixWord ++ tailWord_3450202).sum := by decide
  have hdescent : baseEnd_3450202 < baseStart_3450202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450311 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 2, 3]
def baseStart_3450311 : Nat := 118140960795 + 3450311 * 2 ^ 59
def prefixEnd_3450311 : Nat := 4983230072969 + 3 ^ 40 * 3450311 * 2
def baseEnd_3450311 : Nat := 1181111966996770250696543

theorem tailTrace_3450311 : CollatzResearch.WordTrace tailWord_3450311 prefixEnd_3450311 1181111966996770250696543 := by
  unfold tailWord_3450311
  simp only [CollatzResearch.WordTrace]
  refine ⟨125843180603119988050030787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83895453735413325366687191 125843180603119988050030787)
  ·
    refine ⟨188764770904679982075046181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125843180603119988050030787 188764770904679982075046181)
    ·
      refine ⟨35393394544627496639071159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188764770904679982075046181 35393394544627496639071159)
      ·
        refine ⟨53090091816941244958606739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35393394544627496639071159 53090091816941244958606739)
        ·
          refine ⟨79635137725411867437910109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53090091816941244958606739 79635137725411867437910109)
          ·
            refine ⟨29863176647029450289216291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79635137725411867437910109 29863176647029450289216291)
            ·
              refine ⟨44794764970544175433824437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29863176647029450289216291 44794764970544175433824437)
              ·
                refine ⟨4199509215988516446921041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44794764970544175433824437 4199509215988516446921041)
                ·
                  refine ⟨3149631911991387335190781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4199509215988516446921041 3149631911991387335190781)
                  ·
                    refine ⟨1181111966996770250696543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3149631911991387335190781 1181111966996770250696543)
                    ·
                      rfl

theorem cell22_3450311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_3450311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450311 prefixEnd_3450311 := by exact prefixLift 3450311
  have htrace : WordTrace (prefixWord ++ tailWord_3450311) baseStart_3450311 baseEnd_3450311 := by
    simpa [prefixWord, tailWord_3450311, baseEnd_3450311] using wordTrace_append hprefix tailTrace_3450311
  have hstable : (prefixWord ++ tailWord_3450311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450311).length < 2 ^ (prefixWord ++ tailWord_3450311).sum := by decide
  have hdescent : baseEnd_3450311 < baseStart_3450311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450450 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_3450450 : Nat := 118140960795 + 3450450 * 2 ^ 59
def prefixEnd_3450450 : Nat := 4983230072969 + 3 ^ 40 * 3450450 * 2
def baseEnd_3450450 : Nat := 1181159549537420221471117

theorem tailTrace_3450450 : CollatzResearch.WordTrace tailWord_3450450 prefixEnd_3450450 1181159549537420221471117 := by
  unfold tailWord_3450450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31462062587404103697335201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83898833566410943192893869 31462062587404103697335201)
  ·
    refine ⟨23596546940553077773001401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31462062587404103697335201 23596546940553077773001401)
    ·
      refine ⟨17697410205414808329751051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23596546940553077773001401 17697410205414808329751051)
      ·
        refine ⟨26546115308122212494626577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17697410205414808329751051 26546115308122212494626577)
        ·
          refine ⟨19909586481091659370969933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26546115308122212494626577 19909586481091659370969933)
          ·
            refine ⟨7466094930409372264113725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19909586481091659370969933 7466094930409372264113725)
            ·
              refine ⟨2799785598903514599042647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7466094930409372264113725 2799785598903514599042647)
              ·
                refine ⟨4199678398355271898563971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799785598903514599042647 4199678398355271898563971)
                ·
                  refine ⟨6299517597532907847845957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199678398355271898563971 6299517597532907847845957)
                  ·
                    refine ⟨1181159549537420221471117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299517597532907847845957 1181159549537420221471117)
                    ·
                      rfl

theorem cell22_3450450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_3450450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450450 prefixEnd_3450450 := by exact prefixLift 3450450
  have htrace : WordTrace (prefixWord ++ tailWord_3450450) baseStart_3450450 baseEnd_3450450 := by
    simpa [prefixWord, tailWord_3450450, baseEnd_3450450] using wordTrace_append hprefix tailTrace_3450450
  have hstable : (prefixWord ++ tailWord_3450450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450450).length < 2 ^ (prefixWord ++ tailWord_3450450).sum := by decide
  have hdescent : baseEnd_3450450 < baseStart_3450450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450493 : List Nat := [1, 4, 1, 1, 4, 2, 3, 6]
def baseStart_3450493 : Nat := 118140960795 + 3450493 * 2 ^ 59
def prefixEnd_3450493 : Nat := 4983230072969 + 3 ^ 40 * 3450493 * 2
def baseEnd_3450493 : Nat := 131241585479575826960665

theorem tailTrace_3450493 : CollatzResearch.WordTrace tailWord_3450493 prefixEnd_3450493 131241585479575826960665 := by
  unfold tailWord_3450493
  simp only [CollatzResearch.WordTrace]
  refine ⟨125849818688460633133156133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83899879125640422088770755 125849818688460633133156133)
  ·
    refine ⟨23596841004086368712466775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125849818688460633133156133 23596841004086368712466775)
    ·
      refine ⟨35395261506129553068700163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23596841004086368712466775 35395261506129553068700163)
      ·
        refine ⟨53092892259194329603050245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35395261506129553068700163 53092892259194329603050245)
        ·
          refine ⟨9954917298598936800571921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53092892259194329603050245 9954917298598936800571921)
          ·
            refine ⟨7466187973949202600428941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9954917298598936800571921 7466187973949202600428941)
            ·
              refine ⟨2799820490230950975160853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7466187973949202600428941 2799820490230950975160853)
              ·
                refine ⟨131241585479575826960665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2799820490230950975160853 131241585479575826960665)
                ·
                  rfl

theorem cell22_3450493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 6].length) (baseStart_3450493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450493 prefixEnd_3450493 := by exact prefixLift 3450493
  have htrace : WordTrace (prefixWord ++ tailWord_3450493) baseStart_3450493 baseEnd_3450493 := by
    simpa [prefixWord, tailWord_3450493, baseEnd_3450493] using wordTrace_append hprefix tailTrace_3450493
  have hstable : (prefixWord ++ tailWord_3450493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450493).length < 2 ^ (prefixWord ++ tailWord_3450493).sum := by decide
  have hdescent : baseEnd_3450493 < baseStart_3450493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450514 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3450514 : Nat := 118140960795 + 3450514 * 2 ^ 59
def prefixEnd_3450514 : Nat := 4983230072969 + 3 ^ 40 * 3450514 * 2
def baseEnd_3450514 : Nat := 1181181458045345387870921

theorem tailTrace_3450514 : CollatzResearch.WordTrace tailWord_3450514 prefixEnd_3450514 1181181458045345387870921 := by
  unfold tailWord_3450514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31462646155346138429917649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83900389747589702479780397 31462646155346138429917649)
  ·
    refine ⟨23596984616509603822438237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31462646155346138429917649 23596984616509603822438237)
    ·
      refine ⟨8848869231191101433414339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23596984616509603822438237 8848869231191101433414339)
      ·
        refine ⟨13273303846786652150121509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8848869231191101433414339 13273303846786652150121509)
        ·
          refine ⟨2488744471272497278147783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13273303846786652150121509 2488744471272497278147783)
          ·
            refine ⟨3733116706908745917221675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488744471272497278147783 3733116706908745917221675)
            ·
              refine ⟨5599675060363118875832513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733116706908745917221675 5599675060363118875832513)
              ·
                refine ⟨4199756295272339156874385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5599675060363118875832513 4199756295272339156874385)
                ·
                  refine ⟨3149817221454254367655789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4199756295272339156874385 3149817221454254367655789)
                  ·
                    refine ⟨1181181458045345387870921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3149817221454254367655789 1181181458045345387870921)
                    ·
                      rfl

theorem cell22_3450514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3450514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450514 prefixEnd_3450514 := by exact prefixLift 3450514
  have htrace : WordTrace (prefixWord ++ tailWord_3450514) baseStart_3450514 baseEnd_3450514 := by
    simpa [prefixWord, tailWord_3450514, baseEnd_3450514] using wordTrace_append hprefix tailTrace_3450514
  have hstable : (prefixWord ++ tailWord_3450514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450514).length < 2 ^ (prefixWord ++ tailWord_3450514).sum := by decide
  have hdescent : baseEnd_3450514 < baseStart_3450514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450521 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 5]
def baseStart_3450521 : Nat := 118140960795 + 3450521 * 2 ^ 59
def prefixEnd_3450521 : Nat := 4983230072969 + 3 ^ 40 * 3450521 * 2
def baseEnd_3450521 : Nat := 393727951429466567648633

theorem tailTrace_3450521 : CollatzResearch.WordTrace tailWord_3450521 prefixEnd_3450521 393727951429466567648633 := by
  unfold tailWord_3450521
  simp only [CollatzResearch.WordTrace]
  refine ⟨125850839932359193915175417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83900559954906129276783611 125850839932359193915175417)
  ·
    refine ⟨94388129949269395436381563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125850839932359193915175417 94388129949269395436381563)
    ·
      refine ⟨141582194923904093154572345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94388129949269395436381563 141582194923904093154572345)
      ·
        refine ⟨106186646192928069865929259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141582194923904093154572345 106186646192928069865929259)
        ·
          refine ⟨159279969289392104798893889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106186646192928069865929259 159279969289392104798893889)
          ·
            refine ⟨119459976967044078599170417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159279969289392104798893889 119459976967044078599170417)
            ·
              refine ⟨89594982725283058949377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119459976967044078599170417 89594982725283058949377813)
              ·
                refine ⟨4199764815247643388252085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89594982725283058949377813 4199764815247643388252085)
                ·
                  refine ⟨393727951429466567648633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4199764815247643388252085 393727951429466567648633)
                  ·
                    rfl

theorem cell22_3450521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_3450521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450521 prefixEnd_3450521 := by exact prefixLift 3450521
  have htrace : WordTrace (prefixWord ++ tailWord_3450521) baseStart_3450521 baseEnd_3450521 := by
    simpa [prefixWord, tailWord_3450521, baseEnd_3450521] using wordTrace_append hprefix tailTrace_3450521
  have hstable : (prefixWord ++ tailWord_3450521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450521).length < 2 ^ (prefixWord ++ tailWord_3450521).sum := by decide
  have hdescent : baseEnd_3450521 < baseStart_3450521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450568 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_3450568 : Nat := 118140960795 + 3450568 * 2 ^ 59
def prefixEnd_3450568 : Nat := 4983230072969 + 3 ^ 40 * 3450568 * 2
def baseEnd_3450568 : Nat := 1181199943348907247020755

theorem tailTrace_3450568 : CollatzResearch.WordTrace tailWord_3450568 prefixEnd_3450568 1181199943348907247020755 := by
  unfold tailWord_3450568
  simp only [CollatzResearch.WordTrace]
  refine ⟨62926277081594460471068179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83901702775459280628090905 62926277081594460471068179)
  ·
    refine ⟨94389415622391690706602269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62926277081594460471068179 94389415622391690706602269)
    ·
      refine ⟨35396030858396884014975851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94389415622391690706602269 35396030858396884014975851)
      ·
        refine ⟨53094046287595326022463777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35396030858396884014975851 53094046287595326022463777)
        ·
          refine ⟨39820534715696494516847833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53094046287595326022463777 39820534715696494516847833)
          ·
            refine ⟨29865401036772370887635875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39820534715696494516847833 29865401036772370887635875)
            ·
              refine ⟨44798101555158556331453813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29865401036772370887635875 44798101555158556331453813)
              ·
                refine ⟨4199822020796114656073795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44798101555158556331453813 4199822020796114656073795)
                ·
                  refine ⟨6299733031194171984110693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199822020796114656073795 6299733031194171984110693)
                  ·
                    refine ⟨1181199943348907247020755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6299733031194171984110693 1181199943348907247020755)
                    ·
                      rfl

theorem cell22_3450568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_3450568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450568 prefixEnd_3450568 := by exact prefixLift 3450568
  have htrace : WordTrace (prefixWord ++ tailWord_3450568) baseStart_3450568 baseEnd_3450568 := by
    simpa [prefixWord, tailWord_3450568, baseEnd_3450568] using wordTrace_append hprefix tailTrace_3450568
  have hstable : (prefixWord ++ tailWord_3450568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450568).length < 2 ^ (prefixWord ++ tailWord_3450568).sum := by decide
  have hdescent : baseEnd_3450568 < baseStart_3450568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450589 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 5]
def baseStart_3450589 : Nat := 118140960795 + 3450589 * 2 ^ 59
def prefixEnd_3450589 : Nat := 4983230072969 + 3 ^ 40 * 3450589 * 2
def baseEnd_3450589 : Nat := 393735710692690064081897

theorem tailTrace_3450589 : CollatzResearch.WordTrace tailWord_3450589 prefixEnd_3450589 393735710692690064081897 := by
  unfold tailWord_3450589
  simp only [CollatzResearch.WordTrace]
  refine ⟨125853320096112841528650821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83902213397408561019100547 125853320096112841528650821)
  ·
    refine ⟨23597497518021157786622029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125853320096112841528650821 23597497518021157786622029)
    ·
      refine ⟨8849061569257934169983261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23597497518021157786622029 8849061569257934169983261)
      ·
        refine ⟨3318398088471725313743723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8849061569257934169983261 3318398088471725313743723)
        ·
          refine ⟨4977597132707587970615585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3318398088471725313743723 4977597132707587970615585)
          ·
            refine ⟨3733197849530690977961689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4977597132707587970615585 3733197849530690977961689)
            ·
              refine ⟨2799898387148018233471267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3733197849530690977961689 2799898387148018233471267)
              ·
                refine ⟨4199847580722027350206901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799898387148018233471267 4199847580722027350206901)
                ·
                  refine ⟨393735710692690064081897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4199847580722027350206901 393735710692690064081897)
                  ·
                    rfl

theorem cell22_3450589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_3450589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450589 prefixEnd_3450589 := by exact prefixLift 3450589
  have htrace : WordTrace (prefixWord ++ tailWord_3450589) baseStart_3450589 baseEnd_3450589 := by
    simpa [prefixWord, tailWord_3450589, baseEnd_3450589] using wordTrace_append hprefix tailTrace_3450589
  have hstable : (prefixWord ++ tailWord_3450589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450589).length < 2 ^ (prefixWord ++ tailWord_3450589).sum := by decide
  have hdescent : baseEnd_3450589 < baseStart_3450589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450611 : List Nat := [1, 1, 1, 2, 2, 3, 4, 8]
def baseStart_3450611 : Nat := 118140960795 + 3450611 * 2 ^ 59
def prefixEnd_3450611 : Nat := 4983230072969 + 3 ^ 40 * 3450611 * 2
def baseEnd_3450611 : Nat := 131246073680852163132847

theorem tailTrace_3450611 : CollatzResearch.WordTrace tailWord_3450611 prefixEnd_3450611 131246073680852163132847 := by
  unfold tailWord_3450611
  simp only [CollatzResearch.WordTrace]
  refine ⟨125854122502033139285951687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83902748334688759523967791 125854122502033139285951687)
  ·
    refine ⟨188781183753049708928927531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125854122502033139285951687 188781183753049708928927531)
    ·
      refine ⟨283171775629574563393391297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188781183753049708928927531 283171775629574563393391297)
      ·
        refine ⟨212378831722180922545043473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283171775629574563393391297 212378831722180922545043473)
        ·
          refine ⟨159284123791635691908782605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212378831722180922545043473 159284123791635691908782605)
          ·
            refine ⟨59731546421863384465793477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159284123791635691908782605 59731546421863384465793477)
            ·
              refine ⟨11199664954099384587336277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59731546421863384465793477 11199664954099384587336277)
              ·
                refine ⟨131246073680852163132847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11199664954099384587336277 131246073680852163132847)
                ·
                  rfl

theorem cell22_3450611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 8].length) (baseStart_3450611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450611 prefixEnd_3450611 := by exact prefixLift 3450611
  have htrace : WordTrace (prefixWord ++ tailWord_3450611) baseStart_3450611 baseEnd_3450611 := by
    simpa [prefixWord, tailWord_3450611, baseEnd_3450611] using wordTrace_append hprefix tailTrace_3450611
  have hstable : (prefixWord ++ tailWord_3450611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450611).length < 2 ^ (prefixWord ++ tailWord_3450611).sum := by decide
  have hdescent : baseEnd_3450611 < baseStart_3450611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450658 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3450658 : Nat := 118140960795 + 3450658 * 2 ^ 59
def prefixEnd_3450658 : Nat := 4983230072969 + 3 ^ 40 * 3450658 * 2
def baseEnd_3450658 : Nat := 1181230752188177012270479

theorem tailTrace_3450658 : CollatzResearch.WordTrace tailWord_3450658 prefixEnd_3450658 1181230752188177012270479 := by
  unfold tailWord_3450658
  simp only [CollatzResearch.WordTrace]
  refine ⟨31463959183215716578228157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83903891155241910875275085 31463959183215716578228157)
  ·
    refine ⟨11798984693705893716835559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31463959183215716578228157 11798984693705893716835559)
    ·
      refine ⟨17698477040558840575253339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11798984693705893716835559 17698477040558840575253339)
      ·
        refine ⟨26547715560838260862880009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17698477040558840575253339 26547715560838260862880009)
        ·
          refine ⟨19910786670628695647160007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26547715560838260862880009 19910786670628695647160007)
          ·
            refine ⟨29866180005943043470740011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19910786670628695647160007 29866180005943043470740011)
            ·
              refine ⟨44799270008914565206110017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29866180005943043470740011 44799270008914565206110017)
              ·
                refine ⟨33599452506685923904582513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44799270008914565206110017 33599452506685923904582513)
                ·
                  refine ⟨25199589380014442928436885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33599452506685923904582513 25199589380014442928436885)
                  ·
                    refine ⟨1181230752188177012270479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25199589380014442928436885 1181230752188177012270479)
                    ·
                      rfl

theorem cell22_3450658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3450658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450658 prefixEnd_3450658 := by exact prefixLift 3450658
  have htrace : WordTrace (prefixWord ++ tailWord_3450658) baseStart_3450658 baseEnd_3450658 := by
    simpa [prefixWord, tailWord_3450658, baseEnd_3450658] using wordTrace_append hprefix tailTrace_3450658
  have hstable : (prefixWord ++ tailWord_3450658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450658).length < 2 ^ (prefixWord ++ tailWord_3450658).sum := by decide
  have hdescent : baseEnd_3450658 < baseStart_3450658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450660 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_3450660 : Nat := 118140960795 + 3450660 * 2 ^ 59
def prefixEnd_3450660 : Nat := 4983230072969 + 3 ^ 40 * 3450660 * 2
def baseEnd_3450660 : Nat := 1181231436829049673720473

theorem tailTrace_3450660 : CollatzResearch.WordTrace tailWord_3450660 prefixEnd_3450660 1181231436829049673720473 := by
  unfold tailWord_3450660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62927954839427810327242717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83903939785903747102990289 62927954839427810327242717)
  ·
    refine ⟨23597983064785428872716019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62927954839427810327242717 23597983064785428872716019)
    ·
      refine ⟨35396974597178143309074029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23597983064785428872716019 35396974597178143309074029)
      ·
        refine ⟨13273865473941803740902761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35396974597178143309074029 13273865473941803740902761)
        ·
          refine ⟨9955399105456352805677071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13273865473941803740902761 9955399105456352805677071)
          ·
            refine ⟨14933098658184529208515607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955399105456352805677071 14933098658184529208515607)
            ·
              refine ⟨22399647987276793812773411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933098658184529208515607 22399647987276793812773411)
              ·
                refine ⟨33599471980915190719160117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22399647987276793812773411 33599471980915190719160117)
                ·
                  refine ⟨3149950498210799129921261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33599471980915190719160117 3149950498210799129921261)
                  ·
                    refine ⟨1181231436829049673720473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3149950498210799129921261 1181231436829049673720473)
                    ·
                      rfl

theorem cell22_3450660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_3450660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450660 prefixEnd_3450660 := by exact prefixLift 3450660
  have htrace : WordTrace (prefixWord ++ tailWord_3450660) baseStart_3450660 baseEnd_3450660 := by
    simpa [prefixWord, tailWord_3450660, baseEnd_3450660] using wordTrace_append hprefix tailTrace_3450660
  have hstable : (prefixWord ++ tailWord_3450660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450660).length < 2 ^ (prefixWord ++ tailWord_3450660).sum := by decide
  have hdescent : baseEnd_3450660 < baseStart_3450660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450694 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3450694 : Nat := 118140960795 + 3450694 * 2 ^ 59
def prefixEnd_3450694 : Nat := 4983230072969 + 3 ^ 40 * 3450694 * 2
def baseEnd_3450694 : Nat := 1181243075723884918370369

theorem tailTrace_3450694 : CollatzResearch.WordTrace tailWord_3450694 prefixEnd_3450694 1181243075723884918370369 := by
  unfold tailWord_3450694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933035930022888889413223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83904766507154962974148757 3933035930022888889413223)
  ·
    refine ⟨5899553895034333334119835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3933035930022888889413223 5899553895034333334119835)
    ·
      refine ⟨8849330842551500001179753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5899553895034333334119835 8849330842551500001179753)
      ·
        refine ⟨6636998131913625000884815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8849330842551500001179753 6636998131913625000884815)
        ·
          refine ⟨9955497197870437501327223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6636998131913625000884815 9955497197870437501327223)
          ·
            refine ⟨14933245796805656251990835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955497197870437501327223 14933245796805656251990835)
            ·
              refine ⟨22399868695208484377986253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933245796805656251990835 22399868695208484377986253)
              ·
                refine ⟨8399950760703181641744845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22399868695208484377986253 8399950760703181641744845)
                ·
                  refine ⟨3149981535263693115654317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8399950760703181641744845 3149981535263693115654317)
                  ·
                    refine ⟨1181243075723884918370369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3149981535263693115654317 1181243075723884918370369)
                    ·
                      rfl

theorem cell22_3450694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3450694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450694 prefixEnd_3450694 := by exact prefixLift 3450694
  have htrace : WordTrace (prefixWord ++ tailWord_3450694) baseStart_3450694 baseEnd_3450694 := by
    simpa [prefixWord, tailWord_3450694, baseEnd_3450694] using wordTrace_append hprefix tailTrace_3450694
  have hstable : (prefixWord ++ tailWord_3450694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450694).length < 2 ^ (prefixWord ++ tailWord_3450694).sum := by decide
  have hdescent : baseEnd_3450694 < baseStart_3450694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450720 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_3450720 : Nat := 118140960795 + 3450720 * 2 ^ 59
def prefixEnd_3450720 : Nat := 4983230072969 + 3 ^ 40 * 3450720 * 2
def baseEnd_3450720 : Nat := 1181251976055229517220289

theorem tailTrace_3450720 : CollatzResearch.WordTrace tailWord_3450720 prefixEnd_3450720 1181251976055229517220289 := by
  unfold tailWord_3450720
  simp only [CollatzResearch.WordTrace]
  refine ⟨62929049029319125450834807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83905398705758833934446409 62929049029319125450834807)
  ·
    refine ⟨94393573543978688176252211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62929049029319125450834807 94393573543978688176252211)
    ·
      refine ⟨141590360315968032264378317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94393573543978688176252211 141590360315968032264378317)
      ·
        refine ⟨53096385118488012099141869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141590360315968032264378317 53096385118488012099141869)
        ·
          refine ⟨19911144419433004537178201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53096385118488012099141869 19911144419433004537178201)
          ·
            refine ⟨14933358314574753402883651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19911144419433004537178201 14933358314574753402883651)
            ·
              refine ⟨22400037471862130104325477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933358314574753402883651 22400037471862130104325477)
              ·
                refine ⟨4200007025974149394561027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22400037471862130104325477 4200007025974149394561027)
                ·
                  refine ⟨6300010538961224091841541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200007025974149394561027 6300010538961224091841541)
                  ·
                    refine ⟨1181251976055229517220289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300010538961224091841541 1181251976055229517220289)
                    ·
                      rfl

theorem cell22_3450720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_3450720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450720 prefixEnd_3450720 := by exact prefixLift 3450720
  have htrace : WordTrace (prefixWord ++ tailWord_3450720) baseStart_3450720 baseEnd_3450720 := by
    simpa [prefixWord, tailWord_3450720, baseEnd_3450720] using wordTrace_append hprefix tailTrace_3450720
  have hstable : (prefixWord ++ tailWord_3450720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450720).length < 2 ^ (prefixWord ++ tailWord_3450720).sum := by decide
  have hdescent : baseEnd_3450720 < baseStart_3450720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450752 : List Nat := [2, 1, 1, 2, 1, 2, 7, 2, 4]
def baseStart_3450752 : Nat := 118140960795 + 3450752 * 2 ^ 59
def prefixEnd_3450752 : Nat := 4983230072969 + 3 ^ 40 * 3450752 * 2
def baseEnd_3450752 : Nat := 393754310103064033473397

theorem tailTrace_3450752 : CollatzResearch.WordTrace tailWord_3450752 prefixEnd_3450752 393754310103064033473397 := by
  unfold tailWord_3450752
  simp only [CollatzResearch.WordTrace]
  refine ⟨62929632597261160183417255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83906176796348213577889673 62929632597261160183417255)
  ·
    refine ⟨94394448895891740275125883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62929632597261160183417255 94394448895891740275125883)
    ·
      refine ⟨141591673343837610412688825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94394448895891740275125883 141591673343837610412688825)
      ·
        refine ⟨106193755007878207809516619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141591673343837610412688825 106193755007878207809516619)
        ·
          refine ⟨159290632511817311714274929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106193755007878207809516619 159290632511817311714274929)
          ·
            refine ⟨119467974383862983785706197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159290632511817311714274929 119467974383862983785706197)
            ·
              refine ⟨2800030649621788682477489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119467974383862983785706197 2800030649621788682477489)
              ·
                refine ⟨2100022987216341511858117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800030649621788682477489 2100022987216341511858117)
                ·
                  refine ⟨393754310103064033473397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2100022987216341511858117 393754310103064033473397)
                  ·
                    rfl

theorem cell22_3450752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_3450752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450752 prefixEnd_3450752 := by exact prefixLift 3450752
  have htrace : WordTrace (prefixWord ++ tailWord_3450752) baseStart_3450752 baseEnd_3450752 := by
    simpa [prefixWord, tailWord_3450752, baseEnd_3450752] using wordTrace_append hprefix tailTrace_3450752
  have hstable : (prefixWord ++ tailWord_3450752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450752).length < 2 ^ (prefixWord ++ tailWord_3450752).sum := by decide
  have hdescent : baseEnd_3450752 < baseStart_3450752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450780 : List Nat := [2, 2, 3, 3, 1, 1, 2, 8]
def baseStart_3450780 : Nat := 118140960795 + 3450780 * 2 ^ 59
def prefixEnd_3450780 : Nat := 4983230072969 + 3 ^ 40 * 3450780 * 2
def baseEnd_3450780 : Nat := 131252501697934373413345

theorem tailTrace_3450780 : CollatzResearch.WordTrace tailWord_3450780 prefixEnd_3450780 131252501697934373413345 := by
  unfold tailWord_3450780
  simp only [CollatzResearch.WordTrace]
  refine ⟨62930143219210440574426897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83906857625613920765902529 62930143219210440574426897)
  ·
    refine ⟨47197607414407830430820173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62930143219210440574426897 47197607414407830430820173)
    ·
      refine ⟨17699102780402936411557565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47197607414407830430820173 17699102780402936411557565)
      ·
        refine ⟨6637163542651101154334087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17699102780402936411557565 6637163542651101154334087)
        ·
          refine ⟨9955745313976651731501131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637163542651101154334087 9955745313976651731501131)
          ·
            refine ⟨14933617970964977597251697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955745313976651731501131 14933617970964977597251697)
            ·
              refine ⟨11200213478223733197938773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14933617970964977597251697 11200213478223733197938773)
              ·
                refine ⟨131252501697934373413345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11200213478223733197938773 131252501697934373413345)
                ·
                  rfl

theorem cell22_3450780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 8].length) (baseStart_3450780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450780 prefixEnd_3450780 := by exact prefixLift 3450780
  have htrace : WordTrace (prefixWord ++ tailWord_3450780) baseStart_3450780 baseEnd_3450780 := by
    simpa [prefixWord, tailWord_3450780, baseEnd_3450780] using wordTrace_append hprefix tailTrace_3450780
  have hstable : (prefixWord ++ tailWord_3450780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450780).length < 2 ^ (prefixWord ++ tailWord_3450780).sum := by decide
  have hdescent : baseEnd_3450780 < baseStart_3450780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450917 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_3450917 : Nat := 118140960795 + 3450917 * 2 ^ 59
def prefixEnd_3450917 : Nat := 4983230072969 + 3 ^ 40 * 3450917 * 2
def baseEnd_3450917 : Nat := 1181319413181186670044685

theorem tailTrace_3450917 : CollatzResearch.WordTrace tailWord_3450917 prefixEnd_3450917 1181319413181186670044685 := by
  unfold tailWord_3450917
  simp only [CollatzResearch.WordTrace]
  refine ⟨125865283238924553546591005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83910188825949702364394003 125865283238924553546591005)
  ·
    refine ⟨47199481214596707579971627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125865283238924553546591005 47199481214596707579971627)
    ·
      refine ⟨70799221821895061369957441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47199481214596707579971627 70799221821895061369957441)
      ·
        refine ⟨53099416366421296027468081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70799221821895061369957441 53099416366421296027468081)
        ·
          refine ⟨39824562274815972020601061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53099416366421296027468081 39824562274815972020601061)
          ·
            refine ⟨7467105426527994753862699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39824562274815972020601061 7467105426527994753862699)
            ·
              refine ⟨11200658139791992130794049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467105426527994753862699 11200658139791992130794049)
              ·
                refine ⟨8400493604843994098095537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11200658139791992130794049 8400493604843994098095537)
                ·
                  refine ⟨6300370203632995573571653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8400493604843994098095537 6300370203632995573571653)
                  ·
                    refine ⟨1181319413181186670044685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300370203632995573571653 1181319413181186670044685)
                    ·
                      rfl

theorem cell22_3450917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_3450917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450917 prefixEnd_3450917 := by exact prefixLift 3450917
  have htrace : WordTrace (prefixWord ++ tailWord_3450917) baseStart_3450917 baseEnd_3450917 := by
    simpa [prefixWord, tailWord_3450917, baseEnd_3450917] using wordTrace_append hprefix tailTrace_3450917
  have hstable : (prefixWord ++ tailWord_3450917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450917).length < 2 ^ (prefixWord ++ tailWord_3450917).sum := by decide
  have hdescent : baseEnd_3450917 < baseStart_3450917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450981 : List Nat := [1, 3, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_3450981 : Nat := 118140960795 + 3450981 * 2 ^ 59
def prefixEnd_3450981 : Nat := 4983230072969 + 3 ^ 40 * 3450981 * 2
def baseEnd_3450981 : Nat := 1181341321689111836444489

theorem tailTrace_3450981 : CollatzResearch.WordTrace tailWord_3450981 prefixEnd_3450981 1181341321689111836444489 := by
  unfold tailWord_3450981
  simp only [CollatzResearch.WordTrace]
  refine ⟨125867617510692692476920797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83911745007128461651280531 125867617510692692476920797)
  ·
    refine ⟨47200356566509759678845299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125867617510692692476920797 47200356566509759678845299)
    ·
      refine ⟨70800534849764639518267949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47200356566509759678845299 70800534849764639518267949)
      ·
        refine ⟨26550200568661739819350481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70800534849764639518267949 26550200568661739819350481)
        ·
          refine ⟨19912650426496304864512861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26550200568661739819350481 19912650426496304864512861)
          ·
            refine ⟨7467243909936114324192323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19912650426496304864512861 7467243909936114324192323)
            ·
              refine ⟨11200865864904171486288485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467243909936114324192323 11200865864904171486288485)
              ·
                refine ⟨2100162349669532153679091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11200865864904171486288485 2100162349669532153679091)
                ·
                  refine ⟨3150243524504298230518637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100162349669532153679091 3150243524504298230518637)
                  ·
                    refine ⟨1181341321689111836444489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3150243524504298230518637 1181341321689111836444489)
                    ·
                      rfl

theorem cell22_3450981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_3450981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450981 prefixEnd_3450981 := by exact prefixLift 3450981
  have htrace : WordTrace (prefixWord ++ tailWord_3450981) baseStart_3450981 baseEnd_3450981 := by
    simpa [prefixWord, tailWord_3450981, baseEnd_3450981] using wordTrace_append hprefix tailTrace_3450981
  have hstable : (prefixWord ++ tailWord_3450981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450981).length < 2 ^ (prefixWord ++ tailWord_3450981).sum := by decide
  have hdescent : baseEnd_3450981 < baseStart_3450981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450992 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_3450992 : Nat := 118140960795 + 3450992 * 2 ^ 59
def prefixEnd_3450992 : Nat := 4983230072969 + 3 ^ 40 * 3450992 * 2
def baseEnd_3450992 : Nat := 1181345087213911474419455

theorem tailTrace_3450992 : CollatzResearch.WordTrace tailWord_3450992 prefixEnd_3450992 1181345087213911474419455 := by
  unfold tailWord_3450992
  simp only [CollatzResearch.WordTrace]
  refine ⟨62934009356826420677785615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83912012475768560903714153 62934009356826420677785615)
  ·
    refine ⟨94401014035239631016678423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62934009356826420677785615 94401014035239631016678423)
    ·
      refine ⟨141601521052859446525017635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94401014035239631016678423 141601521052859446525017635)
      ·
        refine ⟨212402281579289169787526453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141601521052859446525017635 212402281579289169787526453)
        ·
          refine ⟨19912713898058359667580605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212402281579289169787526453 19912713898058359667580605)
          ·
            refine ⟨7467267711771884875342727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19912713898058359667580605 7467267711771884875342727)
            ·
              refine ⟨11200901567657827313014091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467267711771884875342727 11200901567657827313014091)
              ·
                refine ⟨16801352351486740969521137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11200901567657827313014091 16801352351486740969521137)
                ·
                  refine ⟨12601014263615055727140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16801352351486740969521137 12601014263615055727140853)
                  ·
                    refine ⟨1181345087213911474419455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12601014263615055727140853 1181345087213911474419455)
                    ·
                      rfl

theorem cell22_3450992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_3450992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3450992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3450992 prefixEnd_3450992 := by exact prefixLift 3450992
  have htrace : WordTrace (prefixWord ++ tailWord_3450992) baseStart_3450992 baseEnd_3450992 := by
    simpa [prefixWord, tailWord_3450992, baseEnd_3450992] using wordTrace_append hprefix tailTrace_3450992
  have hstable : (prefixWord ++ tailWord_3450992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450992).length < 2 ^ (prefixWord ++ tailWord_3450992).sum := by decide
  have hdescent : baseEnd_3450992 < baseStart_3450992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451028 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 5]
def baseStart_3451028 : Nat := 118140960795 + 3451028 * 2 ^ 59
def prefixEnd_3451028 : Nat := 4983230072969 + 3 ^ 40 * 3451028 * 2
def baseEnd_3451028 : Nat := 393785803583206460173115

theorem tailTrace_3451028 : CollatzResearch.WordTrace tailWord_3451028 prefixEnd_3451028 393785803583206460173115 := by
  unfold tailWord_3451028
  simp only [CollatzResearch.WordTrace]
  refine ⟨62934665870761209751940869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83912887827681613002587825 62934665870761209751940869)
  ·
    refine ⟨11800249850767726828488913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62934665870761209751940869 11800249850767726828488913)
    ·
      refine ⟨8850187388075795121366685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11800249850767726828488913 8850187388075795121366685)
      ·
        refine ⟨3318820270528423170512507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8850187388075795121366685 3318820270528423170512507)
        ·
          refine ⟨4978230405792634755768761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3318820270528423170512507 4978230405792634755768761)
          ·
            refine ⟨3733672804344476066826571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4978230405792634755768761 3733672804344476066826571)
            ·
              refine ⟨5600509206516714100239857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733672804344476066826571 5600509206516714100239857)
              ·
                refine ⟨4200381904887535575179893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5600509206516714100239857 4200381904887535575179893)
                ·
                  refine ⟨393785803583206460173115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4200381904887535575179893 393785803583206460173115)
                  ·
                    rfl

theorem cell22_3451028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_3451028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451028 prefixEnd_3451028 := by exact prefixLift 3451028
  have htrace : WordTrace (prefixWord ++ tailWord_3451028) baseStart_3451028 baseEnd_3451028 := by
    simpa [prefixWord, tailWord_3451028, baseEnd_3451028] using wordTrace_append hprefix tailTrace_3451028
  have hstable : (prefixWord ++ tailWord_3451028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451028).length < 2 ^ (prefixWord ++ tailWord_3451028).sum := by decide
  have hdescent : baseEnd_3451028 < baseStart_3451028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451039 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 6]
def baseStart_3451039 : Nat := 118140960795 + 3451039 * 2 ^ 59
def prefixEnd_3451039 : Nat := 4983230072969 + 3 ^ 40 * 3451039 * 2
def baseEnd_3451039 : Nat := 393787058758139672831437

theorem tailTrace_3451039 : CollatzResearch.WordTrace tailWord_3451039 prefixEnd_3451039 393787058758139672831437 := by
  unfold tailWord_3451039
  simp only [CollatzResearch.WordTrace]
  refine ⟨125869732944482568382532171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83913155296321712255021447 125869732944482568382532171)
  ·
    refine ⟨188804599416723852573798257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125869732944482568382532171 188804599416723852573798257)
    ·
      refine ⟨141603449562542889430348693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188804599416723852573798257 141603449562542889430348693)
      ·
        refine ⟨6637661698244197942047595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141603449562542889430348693 6637661698244197942047595)
        ·
          refine ⟨9956492547366296913071393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637661698244197942047595 9956492547366296913071393)
          ·
            refine ⟨7467369410524722684803545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9956492547366296913071393 7467369410524722684803545)
            ·
              refine ⟨5600527057893542013602659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7467369410524722684803545 5600527057893542013602659)
              ·
                refine ⟨8400790586840313020403989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5600527057893542013602659 8400790586840313020403989)
                ·
                  refine ⟨393787058758139672831437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8400790586840313020403989 393787058758139672831437)
                  ·
                    rfl

theorem cell22_3451039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 6].length) (baseStart_3451039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451039 prefixEnd_3451039 := by exact prefixLift 3451039
  have htrace : WordTrace (prefixWord ++ tailWord_3451039) baseStart_3451039 baseEnd_3451039 := by
    simpa [prefixWord, tailWord_3451039, baseEnd_3451039] using wordTrace_append hprefix tailTrace_3451039
  have hstable : (prefixWord ++ tailWord_3451039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451039).length < 2 ^ (prefixWord ++ tailWord_3451039).sum := by decide
  have hdescent : baseEnd_3451039 < baseStart_3451039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451159 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3451159 : Nat := 118140960795 + 3451159 * 2 ^ 59
def prefixEnd_3451159 : Nat := 4983230072969 + 3 ^ 40 * 3451159 * 2
def baseEnd_3451159 : Nat := 1181402254726778705493943

theorem tailTrace_3451159 : CollatzResearch.WordTrace tailWord_3451159 prefixEnd_3451159 1181402254726778705493943 := by
  unfold tailWord_3451159
  simp only [CollatzResearch.WordTrace]
  refine ⟨125874109704047828876900531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83916073136031885917933687 125874109704047828876900531)
  ·
    refine ⟨188811164556071743315350797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125874109704047828876900531 188811164556071743315350797)
    ·
      refine ⟨70804186708526903743256549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188811164556071743315350797 70804186708526903743256549)
      ·
        refine ⟨13275785007848794451860603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70804186708526903743256549 13275785007848794451860603)
        ·
          refine ⟨19913677511773191677790905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13275785007848794451860603 19913677511773191677790905)
          ·
            refine ⟨14935258133829893758343179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19913677511773191677790905 14935258133829893758343179)
            ·
              refine ⟨22402887200744840637514769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14935258133829893758343179 22402887200744840637514769)
              ·
                refine ⟨16802165400558630478136077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22402887200744840637514769 16802165400558630478136077)
                ·
                  refine ⟨6300812025209486429301029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16802165400558630478136077 6300812025209486429301029)
                  ·
                    refine ⟨1181402254726778705493943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300812025209486429301029 1181402254726778705493943)
                    ·
                      rfl

theorem cell22_3451159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3451159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451159 prefixEnd_3451159 := by exact prefixLift 3451159
  have htrace : WordTrace (prefixWord ++ tailWord_3451159) baseStart_3451159 baseEnd_3451159 := by
    simpa [prefixWord, tailWord_3451159, baseEnd_3451159] using wordTrace_append hprefix tailTrace_3451159
  have hstable : (prefixWord ++ tailWord_3451159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451159).length < 2 ^ (prefixWord ++ tailWord_3451159).sum := by decide
  have hdescent : baseEnd_3451159 < baseStart_3451159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451189 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3451189 : Nat := 118140960795 + 3451189 * 2 ^ 59
def prefixEnd_3451189 : Nat := 4983230072969 + 3 ^ 40 * 3451189 * 2
def baseEnd_3451189 : Nat := 1181412524339868627243851

theorem tailTrace_3451189 : CollatzResearch.WordTrace tailWord_3451189 prefixEnd_3451189 1181412524339868627243851 := by
  unfold tailWord_3451189
  simp only [CollatzResearch.WordTrace]
  refine ⟨125875203893939144000492621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83916802595959429333661747 125875203893939144000492621)
  ·
    refine ⟨47203201460227179000184733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125875203893939144000492621 47203201460227179000184733)
    ·
      refine ⟨17701200547585192125069275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47203201460227179000184733 17701200547585192125069275)
      ·
        refine ⟨26551800821377788187603913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17701200547585192125069275 26551800821377788187603913)
        ·
          refine ⟨19913850616033341140702935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26551800821377788187603913 19913850616033341140702935)
          ·
            refine ⟨29870775924050011711054403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19913850616033341140702935 29870775924050011711054403)
            ·
              refine ⟨44806163886075017566581605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29870775924050011711054403 44806163886075017566581605)
              ·
                refine ⟨8401155728639065793734051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44806163886075017566581605 8401155728639065793734051)
                ·
                  refine ⟨12601733592958598690601077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401155728639065793734051 12601733592958598690601077)
                  ·
                    refine ⟨1181412524339868627243851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12601733592958598690601077 1181412524339868627243851)
                    ·
                      rfl

theorem cell22_3451189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3451189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451189 prefixEnd_3451189 := by exact prefixLift 3451189
  have htrace : WordTrace (prefixWord ++ tailWord_3451189) baseStart_3451189 baseEnd_3451189 := by
    simpa [prefixWord, tailWord_3451189, baseEnd_3451189] using wordTrace_append hprefix tailTrace_3451189
  have hstable : (prefixWord ++ tailWord_3451189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451189).length < 2 ^ (prefixWord ++ tailWord_3451189).sum := by decide
  have hdescent : baseEnd_3451189 < baseStart_3451189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451193 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 1, 4]
def baseStart_3451193 : Nat := 118140960795 + 3451193 * 2 ^ 59
def prefixEnd_3451193 : Nat := 4983230072969 + 3 ^ 40 * 3451193 * 2
def baseEnd_3451193 : Nat := 1181413893621613950143839

theorem tailTrace_3451193 : CollatzResearch.WordTrace tailWord_3451193 prefixEnd_3451193 1181413893621613950143839 := by
  unfold tailWord_3451193
  simp only [CollatzResearch.WordTrace]
  refine ⟨125875349785924652683638233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83916899857283101789092155 125875349785924652683638233)
  ·
    refine ⟨94406512339443489512728675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125875349785924652683638233 94406512339443489512728675)
    ·
      refine ⟨141609768509165234269093013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94406512339443489512728675 141609768509165234269093013)
      ·
        refine ⟨6637957898867120356363735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141609768509165234269093013 6637957898867120356363735)
        ·
          refine ⟨9956936848300680534545603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637957898867120356363735 9956936848300680534545603)
          ·
            refine ⟨14935405272451020801818405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9956936848300680534545603 14935405272451020801818405)
            ·
              refine ⟨2800388488584566400340951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14935405272451020801818405 2800388488584566400340951)
              ·
                refine ⟨4200582732876849600511427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800388488584566400340951 4200582732876849600511427)
                ·
                  refine ⟨6300874099315274400767141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200582732876849600511427 6300874099315274400767141)
                  ·
                    refine ⟨1181413893621613950143839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300874099315274400767141 1181413893621613950143839)
                    ·
                      rfl

theorem cell22_3451193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_3451193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3451193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3451193 prefixEnd_3451193 := by exact prefixLift 3451193
  have htrace : WordTrace (prefixWord ++ tailWord_3451193) baseStart_3451193 baseEnd_3451193 := by
    simpa [prefixWord, tailWord_3451193, baseEnd_3451193] using wordTrace_append hprefix tailTrace_3451193
  have hstable : (prefixWord ++ tailWord_3451193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451193).length < 2 ^ (prefixWord ++ tailWord_3451193).sum := by decide
  have hdescent : baseEnd_3451193 < baseStart_3451193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
